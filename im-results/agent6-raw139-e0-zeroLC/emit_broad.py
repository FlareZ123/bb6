"""Emit the twelve broad D0 child Covers for the E0=0LC residual."""
from pathlib import Path
import json
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))

from assemble_broad_specs import build_specs, BROAD_CODES
from emit_chunks import emit


def main():
    if len(sys.argv) != 3:
        raise SystemExit("usage: emit_broad.py WORKDIR OUTPUT_DIR")
    work = Path(sys.argv[1])
    out = Path(sys.argv[2])
    out.mkdir(parents=True, exist_ok=True)

    specs, trees, summary = build_specs(work)
    manifests = []
    for code in BROAD_CODES:
        manifest = emit(code, specs[str(code)], out, tr=trees[code])
        manifests.append(manifest)
        print(
            code,
            "bound=", manifest["bound"],
            "parts=", len(manifest["part_modules"]),
            "blocks=", manifest["block_count"],
            flush=True,
        )

    (out / "broad_chunk_manifest.json").write_text(json.dumps({
        "branches": manifests,
        "summary": summary,
    }, indent=2))


if __name__ == "__main__":
    main()
