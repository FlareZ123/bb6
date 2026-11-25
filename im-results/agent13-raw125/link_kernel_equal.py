"""Link already source-audited single-part Lean artifacts, with explicit
kernel-data equality checks for every non-byte-identical common module.

This is a logical-interface audit, not a substitute for successful pinned
source builds. Only use verified input artifacts from the same Lean toolchain.
Do not overwrite linked files. Compile new consumer modules in the output.
"""
from argparse import ArgumentParser
from collections import defaultdict
from hashlib import file_digest
from pathlib import Path
import json
import os
import shutil
import subprocess


def sha256(path):
    with path.open("rb") as f:
        return file_digest(f, "sha256").hexdigest()


def main():
    ap = ArgumentParser(description=__doc__)
    ap.add_argument("--lean", default="lean")
    ap.add_argument("--out", required=True, type=Path)
    ap.add_argument("parts", nargs="+", type=Path)
    args = ap.parse_args()
    checker = Path(__file__).with_name("CompareKernelImports.lean").resolve()
    lean = shutil.which(args.lean)
    if lean is None:
        raise FileNotFoundError(args.lean)
    groups = defaultdict(list)
    sources = defaultdict(list)
    for part in args.parts:
        if not part.is_dir():
            raise NotADirectoryError(part)
        for path in sorted(part.rglob("*")):
            if not path.is_file():
                continue
            if ".olean." in path.name or path.suffix == ".ir":
                raise ValueError(f"split object/IR unsupported: {path}")
            if path.suffix == ".olean":
                groups[path.relative_to(part)].append(path.resolve())
            elif path.suffix == ".lean":
                sources[path.relative_to(part)].append(path.resolve())
    if not groups:
        raise ValueError("no object files")
    for name, paths in sources.items():
        if len({sha256(p) for p in paths}) != 1:
            raise ValueError(f"source collision: {name}")
    manifest = {"compiler_sha256": sha256(Path(lean)), "objects": {}, "collisions": []}
    for name, paths in sorted(groups.items()):
        chosen = paths[0]
        h = sha256(chosen)
        manifest["objects"][str(name)] = {"path": str(chosen), "sha256": h}
        for other in paths[1:]:
            other_hash = sha256(other)
            if other_hash != h:
                subprocess.run([lean, "--run", str(checker), str(chosen), str(other)], check=True)
                manifest["collisions"].append({"module": str(name), "chosen": h,
                                               "other": other_hash, "other_path": str(other)})
    args.out.mkdir(parents=True, exist_ok=False)
    for group in (groups, sources):
        for name, paths in group.items():
            dest = args.out / name
            dest.parent.mkdir(parents=True, exist_ok=True)
            try:
                os.link(paths[0], dest)
            except OSError:
                shutil.copy2(paths[0], dest)
    (args.out / "kernel-link-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"Linked {len(groups)} modules; checked {len(manifest['collisions'])} non-identical collisions")


if __name__ == "__main__":
    main()
