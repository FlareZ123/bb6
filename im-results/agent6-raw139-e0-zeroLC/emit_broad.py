"""Emit the twelve broad D0 child Covers for the E0=0LC residual."""
from pathlib import Path
import json
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))

from assemble_broad_specs import build_specs, BROAD_CODES
from emit_chunks import emit
from emit_family import emit as emit_family, block_source, HEADER
from search import generate


def main():
    if len(sys.argv) != 3:
        raise SystemExit("usage: emit_broad.py WORKDIR OUTPUT_DIR")
    work = Path(sys.argv[1])
    out = Path(sys.argv[2])
    out.mkdir(parents=True, exist_ok=True)

    specs, trees, summary = build_specs(work)
    manifests = []
    for code in BROAD_CODES:
        spec = specs[str(code)]

        # Generate the ordinary open-leaf block modules. The monolithic tree is
        # intentionally omitted; emit_chunks.py supplies the bounded chunks.
        emit_family(code, spec, out, blocks_only=True, tr=trees[code])

        nested = spec.get("nested_blocks", [])
        if nested:
            source = HEADER
            for item in nested:
                recipe = item["recipe"]
                cert = generate(
                    item["table"], *recipe[1:5], False, 60000,
                    recipe[0] == "phase",
                )
                assert cert and [
                    cert["left_states"], cert["right_nodes"]
                ] == recipe[5:]
                source += block_source(
                    spec["namespace"], item["id"], item["table"], cert
                )
            (out / (spec["nested_block_module"] + ".lean")).write_text(source)

        manifest = emit(code, spec, out, tr=trees[code])
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
