#!/usr/bin/env python3
"""
Patch the MotiveWave:

    python patch_wave.py MotiveWave.jar MotiveWave.exe

The JAR patch is bytecode-aware: it parses the class files inside the archive
and rewrites only the known target methods/ranges. The EXE patch rewrites the
embedded launcher jar path from lib\\MotiveWave.jar to the jar filename passed on
the command line, then bypasses the native launcher image check that rejects the
modified jar.
"""

from __future__ import annotations

import argparse
import hashlib
import shutil
import sys
import tempfile
import zipfile
from dataclasses import dataclass
from pathlib import Path


FEATURE_CLASS = "com/motivewave/platform/common/ah.class"
FEATURE_METHOD = "a"
FEATURE_DESCRIPTOR = (
    "(Lcom/motivewave/platform/common/Enums$Feature;"
    "Lcom/motivewave/platform/common/Enums$Edition;Ljava/util/List;)Z"
)

LICENSE_CLASS = "cj/p.class"
LICENSE_RESPONSE_DESCRIPTOR = "(Lcj/c;)Lcj/m;"
LICENSE_BOOLEAN_DESCRIPTOR = "(Lcj/c;)Z"

STARTUP_CLASS = "MotiveWave.class"
STARTUP_METHOD = "doStart"
STARTUP_DESCRIPTOR = "(Ljavafx/stage/Stage;)V"

CONSOLE_CLASS = "com/motivewave/platform/ui/console/Console.class"
CONSOLE_VERIFY_METHOD = "Q"
VOID_NO_ARGS_DESCRIPTOR = "()V"

EXIT_GUARD_CLASSES = {
    "EdgeProX.class",
    "MotiveWave.class",
    "bb/c.class",
    "bb/j.class",
    "bb/k.class",
    "bb/p.class",
    "cj/e.class",
    "com/motivewave/platform/ui/console/dock/ScannerDock.class",
    "com/motivewave/platform/ui/console/dock/bq.class",
    "com/motivewave/platform/ui/console/dock/i.class",
    "com/motivewave/platform/ui/startup/e.class",
    "com/motivewave/platform/ui/startup/g.class",
    "com/motivewave/platform/ui/util/gt.class",
}

LICENSE_RESPONSE_CODE = bytes(
    [
        0xBB,
        0x00,
        0x6F,  # new cj/m (#111)
        0x59,  # dup
        0xB7,
        0x01,
        0x17,  # invokespecial cj/m.<init> (#279)
        0x59,
        0x04,
        0xB5,
        0x00,
        0x9F,  # putfield cj/m.a:Z (#159)
        0x59,
        0x04,
        0xB5,
        0x00,
        0xA1,  # putfield cj/m.b:Z (#161)
        0x59,
        0x12,
        0x16,  # ldc "ORDER_FLOW" (#22)
        0xB8,
        0x01,
        0x33,  # invokestatic Enums$Edition.valueOf (#307)
        0xB5,
        0x00,
        0x9C,  # putfield cj/m.a:Edition (#156)
        0xB0,  # areturn
    ]
)
TRUE_RETURN_CODE = b"\x04\xAC"
VOID_RETURN_CODE = b"\xB1"


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest().upper()


def u2(value: int) -> bytes:
    return value.to_bytes(2, "big")


def u4(value: int) -> bytes:
    return value.to_bytes(4, "big")


def read_u2(data: bytes | bytearray, offset: int) -> int:
    return int.from_bytes(data[offset : offset + 2], "big")


def read_u4(data: bytes | bytearray, offset: int) -> int:
    return int.from_bytes(data[offset : offset + 4], "big")


@dataclass(frozen=True)
class CpInfo:
    tag: int
    value: str | None = None
    ref1: int = 0
    ref2: int = 0


class Cursor:
    def __init__(self, data: bytes | bytearray) -> None:
        self.data = data
        self.pos = 0

    def u1(self) -> int:
        value = self.data[self.pos]
        self.pos += 1
        return value

    def u2(self) -> int:
        value = read_u2(self.data, self.pos)
        self.pos += 2
        return value

    def u4(self) -> int:
        value = read_u4(self.data, self.pos)
        self.pos += 4
        return value

    def skip(self, count: int) -> None:
        self.pos += count
        if self.pos > len(self.data):
            raise ValueError("class parser ran past end of file")


def read_constant_pool(cursor: Cursor) -> list[CpInfo | None]:
    count = cursor.u2()
    cp: list[CpInfo | None] = [None] * count
    i = 1
    while i < count:
        tag = cursor.u1()
        if tag == 1:
            size = cursor.u2()
            value = bytes(cursor.data[cursor.pos : cursor.pos + size]).decode("utf-8")
            cursor.skip(size)
            cp[i] = CpInfo(tag, value=value)
        elif tag in (3, 4):
            cursor.skip(4)
            cp[i] = CpInfo(tag)
        elif tag in (5, 6):
            cursor.skip(8)
            cp[i] = CpInfo(tag)
            i += 1
        elif tag in (7, 8, 16, 19, 20):
            cp[i] = CpInfo(tag, ref1=cursor.u2())
        elif tag in (9, 10, 11, 12, 17, 18):
            cp[i] = CpInfo(tag, ref1=cursor.u2(), ref2=cursor.u2())
        elif tag == 15:
            cp[i] = CpInfo(tag, ref1=cursor.u1(), ref2=cursor.u2())
        else:
            raise ValueError(f"unsupported constant-pool tag {tag}")
        i += 1
    return cp


def cp_utf8(cp: list[CpInfo | None], index: int) -> str:
    item = cp[index]
    if item is None or item.tag != 1 or item.value is None:
        raise ValueError(f"expected UTF8 constant-pool entry {index}")
    return item.value


def cp_class(cp: list[CpInfo | None], index: int) -> str:
    item = cp[index]
    if item is None or item.tag != 7:
        raise ValueError(f"expected Class constant-pool entry {index}")
    return cp_utf8(cp, item.ref1)


def cp_string(cp: list[CpInfo | None], index: int) -> str:
    item = cp[index]
    if item is None or item.tag != 8:
        raise ValueError(f"expected String constant-pool entry {index}")
    return cp_utf8(cp, item.ref1)


def cp_member(cp: list[CpInfo | None], index: int) -> tuple[str, str, str]:
    item = cp[index]
    if item is None or item.tag not in (9, 10, 11):
        raise ValueError(f"expected member ref constant-pool entry {index}")
    owner = cp_class(cp, item.ref1)
    name_type = cp[item.ref2]
    if name_type is None or name_type.tag != 12:
        raise ValueError(f"expected NameAndType entry {item.ref2}")
    return owner, cp_utf8(cp, name_type.ref1), cp_utf8(cp, name_type.ref2)


def parse_class_header(data: bytes | bytearray) -> tuple[Cursor, list[CpInfo | None]]:
    cursor = Cursor(data)
    if cursor.u4() != 0xCAFEBABE:
        raise ValueError("not a Java class file")
    cursor.skip(4)  # minor_version, major_version
    cp = read_constant_pool(cursor)
    return cursor, cp


def skip_attributes(cursor: Cursor) -> None:
    count = cursor.u2()
    for _ in range(count):
        cursor.skip(2)
        cursor.skip(cursor.u4())


def skip_to_methods(data: bytes | bytearray) -> tuple[Cursor, list[CpInfo | None]]:
    cursor, cp = parse_class_header(data)
    cursor.skip(2)  # access_flags
    cursor.skip(2)  # this_class
    cursor.skip(2)  # super_class
    cursor.skip(cursor.u2() * 2)  # interfaces

    for _ in range(cursor.u2()):
        cursor.skip(6)
        skip_attributes(cursor)
    return cursor, cp


def code_attribute(attr_name_index: int, max_stack: int, max_locals: int, code: bytes) -> bytes:
    return (
        u2(attr_name_index)
        + u4(12 + len(code))
        + u2(max_stack)
        + u2(max_locals)
        + u4(len(code))
        + code
        + u2(0)
        + u2(0)
    )


def replace_code_attributes(data: bytes, replacer) -> tuple[bytes, int, int]:
    cursor, cp = skip_to_methods(data)
    method_count = cursor.u2()
    output = bytearray(data[: cursor.pos])
    changed = 0
    already = 0

    for _ in range(method_count):
        method_start = cursor.pos
        cursor.skip(2)
        name = cp_utf8(cp, cursor.u2())
        descriptor = cp_utf8(cp, cursor.u2())
        attr_count = cursor.u2()
        output.extend(data[method_start : cursor.pos])

        for _ in range(attr_count):
            attr_start = cursor.pos
            attr_name_index = cursor.u2()
            attr_name = cp_utf8(cp, attr_name_index)
            attr_len = cursor.u4()
            attr_info_start = cursor.pos
            replacement = None
            if attr_name == "Code":
                replacement = replacer(
                    cp, name, descriptor, attr_name_index, attr_start, attr_info_start, attr_len
                )
            if replacement is None:
                output.extend(data[attr_start : attr_info_start + attr_len])
            else:
                current = data[attr_start : attr_info_start + attr_len]
                output.extend(replacement)
                if current == replacement:
                    already += 1
                else:
                    changed += 1
            cursor.pos = attr_info_start + attr_len

    output.extend(data[cursor.pos :])
    return bytes(output), changed, already


def validate_license_constants(cp: list[CpInfo | None]) -> None:
    expected = {
        "class #111": cp_class(cp, 111) == "cj/m",
        "ctor #279": cp_member(cp, 279) == ("cj/m", "<init>", "()V"),
        "field #159": cp_member(cp, 159) == ("cj/m", "a", "Z"),
        "field #161": cp_member(cp, 161) == ("cj/m", "b", "Z"),
        "edition string #22": cp_string(cp, 22) == "ORDER_FLOW",
        "edition field #156": cp_member(cp, 156)[0:2] == ("cj/m", "a"),
        "valueOf #307": cp_member(cp, 307)[1] == "valueOf",
    }
    bad = [name for name, ok in expected.items() if not ok]
    if bad:
        raise ValueError("unexpected cj/p.class constant pool: " + ", ".join(bad))


def patch_license_service(data: bytes) -> tuple[bytes, int, int]:
    validated = False

    def replacer(cp, name, descriptor, attr_name_index, _attr_start, attr_info_start, _attr_len):
        nonlocal validated
        if not validated:
            validate_license_constants(cp)
            validated = True

        target_response = descriptor == LICENSE_RESPONSE_DESCRIPTOR and name in ("a", "b")
        target_boolean = descriptor == LICENSE_BOOLEAN_DESCRIPTOR and name == "a"
        if not target_response and not target_boolean:
            return None

        max_locals = max(1, read_u2(data, attr_info_start + 2))
        if target_response:
            return code_attribute(attr_name_index, 3, max_locals, LICENSE_RESPONSE_CODE)
        return code_attribute(attr_name_index, 1, max_locals, TRUE_RETURN_CODE)

    patched, changed, already = replace_code_attributes(data, replacer)
    if changed + already != 3:
        raise ValueError(f"expected 3 cj/p.class methods, matched {changed + already}")
    return patched, changed, already


def patch_void_method(data: bytes, method_name: str, descriptor: str) -> tuple[bytes, int, int]:
    def replacer(_cp, name, desc, attr_name_index, _attr_start, _attr_info_start, _attr_len):
        if name == method_name and desc == descriptor:
            return code_attribute(attr_name_index, 0, 0, VOID_RETURN_CODE)
        return None

    patched, changed, already = replace_code_attributes(data, replacer)
    if changed + already != 1:
        raise ValueError(f"expected one {method_name}{descriptor} method, matched {changed + already}")
    return patched, changed, already


def patch_feature_gate(data: bytes) -> tuple[bytes, int, int]:
    buf = bytearray(data)
    cursor, cp = skip_to_methods(buf)
    matched = False
    method_count = cursor.u2()
    for _ in range(method_count):
        cursor.skip(2)
        name = cp_utf8(cp, cursor.u2())
        descriptor = cp_utf8(cp, cursor.u2())
        attr_count = cursor.u2()
        for _ in range(attr_count):
            attr_name = cp_utf8(cp, cursor.u2())
            attr_len = cursor.u4()
            attr_info_start = cursor.pos
            if name == FEATURE_METHOD and descriptor == FEATURE_DESCRIPTOR and attr_name == "Code":
                matched = True
                code_len = read_u4(buf, attr_info_start + 4)
                code_start = attr_info_start + 8
                if code_len != 107:
                    raise ValueError(f"unexpected feature gate code length {code_len}")
                final_iconst = code_start + 105
                final_return = code_start + 106
                if buf[final_iconst] == 0x04 and buf[final_return] == 0xAC:
                    return bytes(buf), 0, 1
                if buf[final_iconst] != 0x03 or buf[final_return] != 0xAC:
                    raise ValueError("unexpected feature gate tail bytes")
                buf[final_iconst] = 0x04
                return bytes(buf), 1, 0
            cursor.pos = attr_info_start + attr_len
    if not matched:
        raise ValueError("feature gate method not found")
    return bytes(buf), 0, 0


def patch_startup_gate(data: bytes) -> tuple[bytes, int, int]:
    buf = bytearray(data)
    cursor, cp = skip_to_methods(buf)
    matched = False
    method_count = cursor.u2()
    for _ in range(method_count):
        cursor.skip(2)
        name = cp_utf8(cp, cursor.u2())
        descriptor = cp_utf8(cp, cursor.u2())
        attr_count = cursor.u2()
        for _ in range(attr_count):
            attr_name = cp_utf8(cp, cursor.u2())
            attr_len = cursor.u4()
            attr_info_start = cursor.pos
            if name == STARTUP_METHOD and descriptor == STARTUP_DESCRIPTOR and attr_name == "Code":
                matched = True
                code_len = read_u4(buf, attr_info_start + 4)
                code_start = attr_info_start + 8
                if code_len < 59:
                    raise ValueError(f"unexpected startup code length {code_len}")
                offset = code_start + 29
                patched_bytes = b"\x57\x00\x00\xA7\x00\x1A"
                if bytes(buf[offset : offset + 6]) == patched_bytes:
                    return bytes(buf), 0, 1
                if buf[offset] != 0xB8 or buf[offset + 3] != 0x99:
                    raise ValueError("unexpected startup gate bytes")
                buf[offset : offset + 6] = patched_bytes
                return bytes(buf), 1, 0
            cursor.pos = attr_info_start + attr_len
    if not matched:
        raise ValueError("startup gate method not found")
    return bytes(buf), 0, 0


def find_system_exit_methodref(cp: list[CpInfo | None]) -> int:
    for i, item in enumerate(cp):
        if item is None or item.tag != 10:
            continue
        owner = cp_class(cp, item.ref1)
        if owner != "java/lang/System":
            continue
        name_type = cp[item.ref2]
        if name_type is None or name_type.tag != 12:
            continue
        if cp_utf8(cp, name_type.ref1) == "exit" and cp_utf8(cp, name_type.ref2) == "(I)V":
            return i
    return -1


def patch_system_exit_calls(data: bytes) -> tuple[bytes, int]:
    buf = bytearray(data)
    cursor, cp = skip_to_methods(buf)
    methodref = find_system_exit_methodref(cp)
    if methodref < 0:
        return bytes(buf), 0

    patched = 0
    method_count = cursor.u2()
    for _ in range(method_count):
        cursor.skip(6)
        attr_count = cursor.u2()
        for _ in range(attr_count):
            attr_name = cp_utf8(cp, cursor.u2())
            attr_len = cursor.u4()
            attr_info_start = cursor.pos
            if attr_name == "Code":
                code_len = read_u4(buf, attr_info_start + 4)
                code_start = attr_info_start + 8
                code_end = code_start + code_len - 2
                for offset in range(code_start, code_end):
                    if buf[offset] == 0xB8 and read_u2(buf, offset + 1) == methodref:
                        buf[offset : offset + 3] = b"\x57\x00\x00"
                        patched += 1
            cursor.pos = attr_info_start + attr_len
    return bytes(buf), patched


def is_signature_artifact(name: str) -> bool:
    upper = name.upper()
    return upper.startswith("META-INF/") and upper.endswith((".SF", ".RSA", ".DSA", ".EC"))


def clone_zip_info(info: zipfile.ZipInfo) -> zipfile.ZipInfo:
    cloned = zipfile.ZipInfo(info.filename, date_time=info.date_time)
    cloned.compress_type = info.compress_type
    cloned.comment = info.comment
    cloned.extra = info.extra
    cloned.internal_attr = info.internal_attr
    cloned.external_attr = info.external_attr
    cloned.create_system = info.create_system
    return cloned


def backup_file(path: Path) -> Path:
    backup = path.with_name(path.name + ".bak")
    if backup.exists():
        print(f"  backup exists:  {backup}")
    else:
        shutil.copy2(path, backup)
        print(f"  created backup: {backup}")
    return backup


def patch_jar(path: Path, *, dry_run: bool, make_backup: bool) -> bool:
    print(f"\n== {path}")
    if not path.exists():
        raise FileNotFoundError(path)

    changed = False
    stats = {
        "license": 0,
        "feature": 0,
        "startup": 0,
        "console": 0,
        "system_exit": 0,
        "signatures": 0,
    }
    seen = set()

    with zipfile.ZipFile(path, "r") as zin:
        with tempfile.NamedTemporaryFile(delete=False, suffix=".jar") as tmp:
            tmp_path = Path(tmp.name)

        try:
            with zipfile.ZipFile(tmp_path, "w") as zout:
                for info in zin.infolist():
                    name = info.filename
                    if is_signature_artifact(name):
                        stats["signatures"] += 1
                        changed = True
                        continue
                    if name in seen:
                        changed = True
                        continue
                    seen.add(name)

                    data = b"" if info.is_dir() else zin.read(info)
                    if name == LICENSE_CLASS:
                        data, c, a = patch_license_service(data)
                        stats["license"] = c + a
                        changed = changed or c > 0
                    elif name == FEATURE_CLASS:
                        data, c, a = patch_feature_gate(data)
                        stats["feature"] = c + a
                        changed = changed or c > 0
                    elif name == STARTUP_CLASS:
                        data, c, a = patch_startup_gate(data)
                        stats["startup"] = c + a
                        changed = changed or c > 0
                    elif name == CONSOLE_CLASS:
                        data, c, a = patch_void_method(data, CONSOLE_VERIFY_METHOD, VOID_NO_ARGS_DESCRIPTOR)
                        stats["console"] = c + a
                        changed = changed or c > 0

                    if name in EXIT_GUARD_CLASSES:
                        data, exit_count = patch_system_exit_calls(data)
                        stats["system_exit"] += exit_count
                        changed = changed or exit_count > 0

                    zout.writestr(clone_zip_info(info), data)

            for key in ("license", "feature", "startup", "console"):
                if stats[key] != 1 and key != "license":
                    raise ValueError(f"expected one {key} patch target, matched {stats[key]}")
            if stats["license"] != 3:
                raise ValueError(f"expected three license patch targets, matched {stats['license']}")

            print(f"  sha256 before: {sha256(path)}")
            print(f"  license service methods matched: {stats['license']}")
            print(f"  feature gate methods matched:    {stats['feature']}")
            print(f"  startup gate methods matched:    {stats['startup']}")
            print(f"  console verify methods matched:  {stats['console']}")
            print(f"  System.exit calls neutralized:   {stats['system_exit']}")
            print(f"  signature artifacts removed:     {stats['signatures']}")

            if dry_run:
                print("  dry run: no file written")
                tmp_path.unlink(missing_ok=True)
                return changed

            if changed:
                if make_backup:
                    backup_file(path)
                shutil.move(str(tmp_path), path)
                print(f"  wrote file: {path}")
                print(f"  sha256 after:  {sha256(path)}")
            else:
                tmp_path.unlink(missing_ok=True)
                print("  no changes needed")
            return changed
        except Exception:
            tmp_path.unlink(missing_ok=True)
            raise


def fixed_width(old: bytes, new: bytes) -> bytes:
    if len(new) > len(old):
        raise ValueError("replacement is longer than original")
    return new + (b"\x00" * (len(old) - len(new)))


@dataclass(frozen=True)
class BinaryPatch:
    name: str
    candidates: tuple[bytes, ...]
    patched: bytes
    expected_count: int = 1
    expected_patched_count: int = 1
    exclude_agent_prefix: bool = False

    def __post_init__(self) -> None:
        for candidate in self.candidates:
            if len(candidate) != len(self.patched):
                raise ValueError(f"{self.name}: original and patched lengths differ")


def launcher_jar_target(jar_path: Path, exe_path: Path) -> str:
    try:
        target = jar_path.resolve().relative_to(exe_path.resolve().parent)
    except ValueError:
        target = Path(jar_path.name)

    text = str(target).replace("/", "\\")
    if text.startswith(".\\"):
        text = text[2:]
    if not text.lower().endswith(".jar"):
        raise ValueError(f"launcher jar target must be a jar path, got {text!r}")
    try:
        text.encode("ascii")
    except UnicodeEncodeError as exc:
        raise ValueError(f"launcher jar target must be ASCII, got {text!r}") from exc
    return text


def padded(width_sample: bytes, text: str) -> bytes:
    return fixed_width(width_sample, text.encode("ascii"))


def padded_wide(width_sample: bytes, text: str) -> bytes:
    return fixed_width(width_sample, text.encode("utf-16le"))


def make_exe_patches(jar_target: str) -> list[BinaryPatch]:
    if "/" in jar_target or not jar_target.lower().endswith(".jar"):
        raise ValueError(f"launcher jar target must be a jar path, got {jar_target!r}")

    old_agent = b"-javaagent:lib\\MotiveWave.jar"
    old_agent_wide = "-javaagent:lib\\MotiveWave.jar".encode("utf-16le")
    old_image = b"lib\\MotiveWave.jar"

    known_targets = ("lib\\MotiveWave.jar", "MotiveWave.jar", "wave.jar")
    agent_candidates = tuple(padded(old_agent, f"-javaagent:{target}") for target in known_targets)
    wide_agent_candidates = tuple(
        padded_wide(old_agent_wide, f"-javaagent:{target}") for target in known_targets
    )
    image_candidates = tuple(padded(old_image, target) for target in known_targets)

    image_guard_original = bytes.fromhex("3B FB 74 23 45 33 C9 4C 8D 05")
    image_guard_patched = bytes.fromhex("3B FB EB 23 45 33 C9 4C 8D 05")

    return [
        BinaryPatch(
            f"UTF-16 javaagent jar path uses {jar_target}",
            wide_agent_candidates,
            padded_wide(old_agent_wide, f"-javaagent:{jar_target}"),
        ),
        BinaryPatch(
            f"ASCII javaagent jar path uses {jar_target}",
            agent_candidates,
            padded(old_agent, f"-javaagent:{jar_target}"),
        ),
        BinaryPatch(
            f"launcher image jar path uses {jar_target}",
            image_candidates,
            padded(old_image, jar_target),
            exclude_agent_prefix=True,
        ),
        BinaryPatch(
            "native launcher image-integrity guard is bypassed",
            (image_guard_original,),
            image_guard_patched,
        ),
    ]


def pe_checksum_offset(data: bytes | bytearray) -> int:
    if len(data) < 0x100:
        raise ValueError("file is too small to be a PE")
    if data[0:2] != b"MZ":
        raise ValueError("missing MZ header")
    e_lfanew = int.from_bytes(data[0x3C:0x40], "little")
    if e_lfanew + 4 + 20 + 0x44 > len(data):
        raise ValueError("PE header points outside file")
    if data[e_lfanew : e_lfanew + 4] != b"PE\0\0":
        raise ValueError("missing PE signature")
    return e_lfanew + 4 + 20 + 0x40


def compute_pe_checksum(data: bytes | bytearray) -> tuple[int, int]:
    checksum_offset = pe_checksum_offset(data)
    total = 0
    for index in range(0, len(data), 2):
        if checksum_offset <= index < checksum_offset + 4:
            word = 0
        elif index + 1 < len(data):
            word = data[index] | (data[index + 1] << 8)
        else:
            word = data[index]
        total = (total + word) & 0xFFFFFFFF
        total = (total & 0xFFFF) + (total >> 16)
    total = (total & 0xFFFF) + (total >> 16)
    return (total + len(data)) & 0xFFFFFFFF, checksum_offset


def update_pe_checksum(data: bytearray) -> tuple[int, int, int]:
    offset = pe_checksum_offset(data)
    old = int.from_bytes(data[offset : offset + 4], "little")
    new, computed_offset = compute_pe_checksum(data)
    data[computed_offset : computed_offset + 4] = new.to_bytes(4, "little")
    return old, new, computed_offset


def matching_offsets(data: bytearray, needle: bytes, *, exclude_agent_prefix: bool) -> list[int]:
    offsets: list[int] = []
    start = 0
    while True:
        offset = data.find(needle, start)
        if offset < 0:
            return offsets
        agent_substring = bytes(data[offset - 11 : offset]) == b"-javaagent:"
        lib_substring = bytes(data[offset - 4 : offset]) == b"lib\\"
        if not exclude_agent_prefix or (not agent_substring and not lib_substring):
            offsets.append(offset)
        start = offset + 1


def apply_binary_patch(data: bytearray, patch: BinaryPatch) -> tuple[int, int]:
    source_offsets: list[tuple[int, bytes]] = []
    for candidate in patch.candidates:
        if candidate == patch.patched:
            continue
        for offset in matching_offsets(
            data, candidate, exclude_agent_prefix=patch.exclude_agent_prefix
        ):
            source_offsets.append((offset, candidate))

    patched_count = len(
        matching_offsets(data, patch.patched, exclude_agent_prefix=patch.exclude_agent_prefix)
    )

    if not source_offsets and patched_count == patch.expected_patched_count:
        return 0, patched_count
    if len(source_offsets) != patch.expected_count:
        raise ValueError(
            f"{patch.name}: expected {patch.expected_count} original occurrence(s), "
            f"found {len(source_offsets)}; patched occurrences found {patched_count}"
        )

    replaced = 0
    for offset, candidate in source_offsets:
        data[offset : offset + len(candidate)] = patch.patched
        replaced += 1
    return replaced, 0


def patch_exe(path: Path, jar_target: str, *, dry_run: bool, make_backup: bool) -> bool:
    print(f"\n== {path}")
    if not path.exists():
        raise FileNotFoundError(path)

    data = bytearray(path.read_bytes())
    print(f"  sha256 before: {sha256(path)}")

    changed = False
    print(f"  launcher jar target: {jar_target}")
    for patch in make_exe_patches(jar_target):
        replaced, already = apply_binary_patch(data, patch)
        if replaced:
            print(f"  patching: {patch.name}")
            changed = True
        elif already:
            print(f"  already patched: {patch.name}")

    old_checksum, new_checksum, checksum_offset = update_pe_checksum(data)
    checksum_changed = old_checksum != new_checksum
    print(
        f"  PE checksum: 0x{old_checksum:08X} -> 0x{new_checksum:08X} "
        f"(field offset 0x{checksum_offset:X})"
    )

    if dry_run:
        print("  dry run: no file written")
        return changed or checksum_changed

    if changed or checksum_changed:
        if make_backup:
            backup_file(path)
        path.write_bytes(data)
        print(f"  wrote file: {path}")
        print(f"  sha256 after:  {sha256(path)}")
    else:
        print("  no changes needed")
    return changed or checksum_changed


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description="Patch MotiveWave.jar and MotiveWave.exe.")
    parser.add_argument("wave_jar", type=Path, help="Path to MotiveWave.jar")
    parser.add_argument("wave_exe", type=Path, help="Path to MotiveWave.exe")
    parser.add_argument("--dry-run", action="store_true", help="Validate patches without writing files")
    parser.add_argument("--no-backup", action="store_true", help="Do not create .bak backups")
    args = parser.parse_args(argv)

    try:
        patch_jar(args.wave_jar, dry_run=args.dry_run, make_backup=not args.no_backup)
        patch_exe(
            args.wave_exe,
            launcher_jar_target(args.wave_jar, args.wave_exe),
            dry_run=args.dry_run,
            make_backup=not args.no_backup,
        )
    except Exception as exc:
        print(f"\nERROR: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
