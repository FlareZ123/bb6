"""Reproduce two raw60 leaf certificates by context-quotienting exact sparse windows.

No discovery code is trusted: IndexedBiDFA checks the resulting primitive
stack relation in Lean, and the exact original child consumer uses its theorem.
"""
import subprocess
import tempfile
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
WIDE = ROOT.parent / "agent1-bidfa-sat"
sys.path.insert(0, str(WIDE))
from wide_cert import compress, emit

CASES = {
    "1LF": (1596, "1RB1LF_1RC0LB_0RD0RD_1LD1RE_0RA1RA_---1LB", 22, 14522,
            "Raw60LFSparse", (2324, 154, 268, 522)),
    "1RE": (495, "1RB1RE_1RC0LB_0RD1LF_1LD1RE_1LC1RA_---1LB", 25, 93002,
            "Raw60RESparse", (7889, 101, 513, 859)),
}

def generate(child):
    i, table, width, raw, module, expected = CASES[child]
    with tempfile.TemporaryDirectory() as temp:
        tmp = Path(temp)
        exe = tmp / "ngram"
        subprocess.run(["g++", "-O3", "-std=c++17", str(WIDE/"ngram_wide.cpp"), "-o", str(exe)], check=True)
        data = subprocess.check_output([str(exe), str(width)], input=f"{i} {table}\n", text=True)
        assert tuple(map(int, data.split()[:3])) == (i, width, raw)
        d, original, projected = compress(data)
        states, edges = emit(i, table, *d, tmp/"generated")
        assert states <= projected
        actual = (states, len(d[0])//2, len(d[1])//2, edges)
        assert actual == expected, (child, actual, expected)
        # Preserve the exact module and namespace interface used by the existing
        # child generator, without mutating shared Raw118 proof source.
        old = f"Raw118Wide{i}"
        old_ns = f"BB6Coverage.Agent1BiDFAWide.M{i}"
        new_ns = f"BB6.Agent47SparseNGram.{module}"
        for f in (tmp/"generated").glob("*.lean"):
            source = f.read_text().replace(old_ns, new_ns).replace(old, module)
            (ROOT/f.name.replace(old,module)).write_text(source)
        print(child, "raw", original, "quotient", actual)

def full_child(child):
    if child == "1LF":
        import generate_1lf
        generate_1lf.generate_1lf_sparse.main = lambda: generate(child)
        generate_1lf.main()
    elif child == "1RE":
        import generate_1re
        generate_1re.emit = lambda *args, **kwargs: generate(child)
        generate_1re.main()
    else:
        raise ValueError(child)

if __name__ == "__main__":
    full_child(sys.argv[1])
