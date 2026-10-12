#!/usr/bin/env python3
"""Check release source identity against the preserved verification record.

This is a byte-integrity check. Run `lake --wfail build` to check the proof.
Uses only Python's standard library.
"""

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys
import zipfile


ARCHIVE_SHA256 = "149f867bc3f16682b07c8448752ebf885f2d6759c6daa99561d7b1feb858d481"
PINNED_FILES = (
    "lean-toolchain",
    "lakefile.toml",
    "lake-manifest.json",
    "verification/status.json",
    "verification/full-build.log",
)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(root):
    errors = []
    report = json.loads((root / "verification/status.json").read_text(encoding="utf-8-sig"))
    if report.get("buildExitCode") != 0 or report.get("warningsAreErrors") is not True:
        errors.append("The published record does not report a successful warning-free build.")

    expected = {}
    for entry in report["sources"]:
        relative = entry["path"]
        path = PurePosixPath(relative)
        if (not relative or path.is_absolute() or ".." in path.parts
                or "\\" in relative or ":" in relative or path.suffix != ".lean"):
            raise ValueError("Invalid source path in record: " + relative)
        if relative in expected:
            raise ValueError("Duplicate source path in record: " + relative)
        if not re.fullmatch(r"[0-9a-f]{64}", entry["sha256"]):
            raise ValueError("Invalid SHA256 in record: " + relative)
        resolved = (root / relative).resolve()
        try:
            resolved.relative_to(root)
        except ValueError:
            raise ValueError("Source path escapes repository: " + relative) from None
        expected[relative] = entry["sha256"]
    if not expected:
        raise ValueError("The verification record contains no source files.")

    actual = {
        path.relative_to(root).as_posix()
        for path in list(root.glob("*.lean")) + list((root / "ExceptionalTimes").rglob("*.lean"))
        if path.is_file()
    }
    for relative in sorted(expected.keys() - actual):
        errors.append("Missing source: " + relative)
    for relative in sorted(actual - expected.keys()):
        errors.append("Unrecorded source: " + relative)
    for relative in sorted(actual & expected.keys()):
        if sha256(root / relative) != expected[relative]:
            errors.append("Changed source: " + relative)

    audit = root / "ExceptionalTimes/AxiomAudit.lean"
    if audit.is_file():
        imports = set(re.findall(r"^import\s+(\S+)\s*$", audit.read_text(encoding="utf-8-sig"), re.M))
        for relative in sorted(actual):
            if relative in {"lakefile.lean", "ExceptionalTimes/AxiomAudit.lean"}:
                continue
            module = relative[:-5].replace("/", ".")
            if module not in imports:
                errors.append("Module not imported by AxiomAudit: " + module)

    archive = root / "verification/nearest-neighbor-31-36-lean.zip"
    if sha256(archive) != ARCHIVE_SHA256:
        errors.append("Changed standalone Lean archive.")
    else:
        with zipfile.ZipFile(archive) as snapshot:
            for relative in PINNED_FILES:
                path = root / relative
                if not path.is_file() or path.read_bytes() != snapshot.read(relative):
                    errors.append("File differs from verified archive: " + relative)

    if errors:
        for error in errors:
            print("FAIL: " + error, file=sys.stderr)
        return 1
    print(f"PASS: all {len(expected)} Lean source files match the completed verification record.")
    print("PASS: every project module is included in the axiom audit.")
    print("PASS: dependency pins, build records and standalone archive are unchanged.")
    print("Source identity checked; no new Lean build was run.")
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1],
                        help="repository root (default: this script's repository)")
    args = parser.parse_args()
    try:
        return check(args.root.resolve())
    except (OSError, ValueError, KeyError, TypeError, zipfile.BadZipFile) as error:
        print("FAIL: " + str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
