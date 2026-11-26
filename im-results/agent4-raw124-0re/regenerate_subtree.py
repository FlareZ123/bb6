#!/usr/bin/env python3
"""Regenerate selected Raw124 audit kids with a smaller recursive proof-tree cap.

The bundle, transition table, witness data, Base/Pumps/Data interfaces, and source
revision are held fixed. Only the recursive decomposition threshold used to
factor large Audit trees into kernel-checked sublemmas is changed.
"""
from __future__ import annotations

import hashlib
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path


def run(command: list[str], cwd: Path) -> None:
    print("$ " + " ".join(command), flush=True)
    subprocess.run(command, cwd=cwd, check=True)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def declaration(text: str, pattern: str, label: str) -> str:
    match = re.search(pattern, text, re.MULTILINE)
    if match is None:
        raise AssertionError(f"missing {label}")
    return match.group(0)


def main() -> None:
    if len(sys.argv) < 6:
        raise SystemExit(
            "usage: regenerate_subtree.py SOURCE_ROOT OUTPUT_DIR BRANCH LIMIT EXPECTED_SHA KID..."
        )
    source_root = Path(sys.argv[1]).resolve()
    output = Path(sys.argv[2]).resolve()
    branch = sys.argv[3]
    limit = int(sys.argv[4])
    expected_sha = sys.argv[5]
    kids = sys.argv[6:]

    if not re.fullmatch(r"[01][LR][A-F]", branch):
        raise ValueError(f"invalid Raw124 branch: {branch}")
    if not 1 <= limit < 500:
        raise ValueError("subtree limit must be in 1..499")
    if not kids or any(not re.fullmatch(r"K[0-2][0-9]", kid) for kid in kids):
        raise ValueError(f"invalid or empty kid list: {kids}")

    actual_sha = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=source_root, text=True
    ).strip()
    if actual_sha != expected_sha:
        raise AssertionError(
            f"source checkout mismatch: expected {expected_sha}, got {actual_sha}"
        )

    raw124 = source_root / "im-results/agent2-tnf-raw124"
    generator = raw124 / "generate_bundle.py"
    original_generator = generator.read_text(encoding="utf-8")
    old_threshold = 'if node[0]!="split" or size(node)<=500:'
    if original_generator.count(old_threshold) != 1:
        raise AssertionError("expected exactly one recursive size<=500 threshold")

    run(["python", "im-results/agent13-coverage/unpack.py"], source_root)
    run(["python", "im-results/agent31-three-hole-tnf/generate_sweeps.py"], source_root)
    run(["python", "im-results/agent31-three-hole-tnf/generate_four_hole.py"], source_root)
    run(["python", str(generator), branch], source_root)

    stem = "Raw124B" + branch
    stable_names = [stem + suffix + ".lean" for suffix in ("Base", "Pumps", "Data")]
    baseline_stable = {name: digest(raw124 / name) for name in stable_names}
    baseline_kids = {}
    baseline_statements = {}
    for kid in kids:
        name = f"{stem}Kid{kid}.lean"
        text = (raw124 / name).read_text(encoding="utf-8")
        baseline_kids[kid] = {
            "sha256": digest(raw124 / name),
            "bytes": (raw124 / name).stat().st_size,
            "lines": len(text.splitlines()),
        }
        baseline_statements[kid] = {
            "tree": declaration(text, rf"^def tree{kid} : Audit :=", f"tree{kid}"),
            "check": declaration(
                text, rf"^theorem check{kid} :[^\n]*", f"check{kid}"
            ),
        }

    patched_generator = original_generator.replace(
        old_threshold, f'if node[0]!="split" or size(node)<={limit}:'
    )
    generator.write_text(patched_generator, encoding="utf-8")
    run(["python", str(generator), branch], source_root)

    after_stable = {name: digest(raw124 / name) for name in stable_names}
    if after_stable != baseline_stable:
        raise AssertionError(
            "changing only the recursive Audit threshold changed a stable "
            f"interface/source file: before={baseline_stable}, after={after_stable}"
        )

    output.mkdir(parents=True, exist_ok=True)
    kid_manifest = {}
    for kid in kids:
        name = f"{stem}Kid{kid}.lean"
        path = raw124 / name
        text = path.read_text(encoding="utf-8")
        if re.search(r"\b(?:sorry|admit|native_decide)\b", text):
            raise AssertionError(f"forbidden proof escape in {name}")
        statements = {
            "tree": declaration(text, rf"^def tree{kid} : Audit :=", f"tree{kid}"),
            "check": declaration(
                text, rf"^theorem check{kid} :[^\n]*", f"check{kid}"
            ),
        }
        if statements != baseline_statements[kid]:
            raise AssertionError(f"{kid}: root interface changed under subdivision")
        target = output / name
        shutil.copy2(path, target)
        kid_manifest[kid] = {
            "original": baseline_kids[kid],
            "subdivided": {
                "sha256": digest(target),
                "bytes": target.stat().st_size,
                "lines": len(text.splitlines()),
                "top_level_declarations": len(
                    re.findall(r"^(?:abbrev|def|theorem)\s+", text, re.MULTILINE)
                ),
                "by_decide_count": text.count("by decide"),
            },
            "root_statements": statements,
        }

    shutil.copy2(generator, output / "generate_bundle.subdivided.py")
    (output / "generate_bundle.original.py").write_text(
        original_generator, encoding="utf-8"
    )
    input_bundles = {}
    for path in sorted(raw124.glob("complete-bundle*.json.zlib.b64")):
        input_bundles[path.name] = digest(path)
    for name in ("open.txt", "tree.json"):
        path = raw124 / name
        if path.exists():
            input_bundles[name] = digest(path)

    manifest = {
        "source_commit": actual_sha,
        "branch": branch,
        "recursive_audit_subtree_limit": limit,
        "stable_source_sha256": after_stable,
        "input_sha256": input_bundles,
        "original_generator_sha256": hashlib.sha256(
            original_generator.encode()
        ).hexdigest(),
        "subdivided_generator_sha256": digest(generator),
        "kids": kid_manifest,
        "claim": (
            "Only the recursive Audit subtree factoring threshold changes. "
            "The exact input bundle, transition table, witness data, Base, Pumps, "
            "Data, and each selected kid's root theorem statements are held fixed. "
            "The resulting Lean declarations still require original-source CI."
        ),
    }
    (output / "SPLIT_MANIFEST.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps({
        "source_commit": actual_sha,
        "branch": branch,
        "limit": limit,
        "stable_interfaces_unchanged": True,
        "kids": {
            kid: {
                "original_bytes": kid_manifest[kid]["original"]["bytes"],
                "subdivided_bytes": kid_manifest[kid]["subdivided"]["bytes"],
                "original_lines": kid_manifest[kid]["original"]["lines"],
                "subdivided_lines": kid_manifest[kid]["subdivided"]["lines"],
                "subdivided_by_decide": kid_manifest[kid]["subdivided"]["by_decide_count"],
            }
            for kid in kids
        },
    }, indent=2), flush=True)


if __name__ == "__main__":
    main()
