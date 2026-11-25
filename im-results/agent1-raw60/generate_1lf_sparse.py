"""Generate leaf 1596's complete sparse n-gram invariant (width 22)."""
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SPARSE = ROOT.parent / "agent47-raw111-cut"
sys.path.insert(0, str(SPARSE))
from emit_sparse import emit

TABLE = "1RB1LF_1RC0LB_0RD0RD_1LD1RE_0RA1RA_---1LB"

def main():
    with tempfile.TemporaryDirectory() as tmp:
        exe = Path(tmp) / "ngram"
        subprocess.run(["g++", "-std=c++17", "-O3", str(SPARSE / "ngram_sparse.cpp"), "-o", str(exe)], check=True)
        output = subprocess.check_output([str(exe), "22"], input=f"1596 {TABLE}\n", text=True)
        ident, data = output.strip().split(maxsplit=1)
        assert ident == "1596"
        emit(ROOT, 1596, TABLE, data, width=22, module_name="Raw60LFSparse", expected=(14522, 176, 2550))

if __name__ == "__main__":
    main()
