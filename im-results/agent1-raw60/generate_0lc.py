"""Generate raw60 A1=0LC without modifying the historical audit generator."""
import json
import subprocess
import sys
import tempfile
from pathlib import Path
import recursive_fill
from generate_1lf import load_audit

ROOT = Path(__file__).resolve().parent
SPARSE = ROOT.parent / "agent47-raw111-cut"
sys.path.insert(0, str(SPARSE))
from emit_sparse import emit

def main():
    recursive_fill.main("0LC")
    spec = json.loads((ROOT / "spec-0LC.json").read_text())
    with tempfile.TemporaryDirectory() as tmp:
        exe = Path(tmp) / "ngram"
        subprocess.run(["g++", "-std=c++17", "-O3", str(SPARSE / "ngram_sparse.cpp"), "-o", str(exe)], check=True)
        for ident, width, expected in [(309, 13, (1158, 45, 122)), (310, 13, (775, 44, 99))]:
            module, _, table = spec["manual"][str(ident)]
            output = subprocess.check_output([str(exe), str(width)], input=f"{ident} {table}\n", text=True)
            label, data = output.strip().split(maxsplit=1)
            assert int(label) == ident
            emit(ROOT, ident, table, data, width=width, module_name=module, expected=expected)
    generate = load_audit()
    generate.SPECS["0LC"] = spec
    generate.main("0LC")

if __name__ == "__main__":
    main()
