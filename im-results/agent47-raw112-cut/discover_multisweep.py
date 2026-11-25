"""Search for a multi-block affine return family for raw112 hard leaves 10 and 15.

Discovery output is experimental; only the generated Lean source and its successful
kernel compilation establish a theorem.
"""
from pathlib import Path
import argparse
import sys
import tarfile

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "agent31-three-hole-tnf"))
sys.path.insert(0, str(ROOT.parent / "agent47-raw114-cut"))
import multi_sweep as ms
import generate_sweeps as pump

def load_hard_rows():
    with tarfile.open(ROOT / "inductive-generators.tar.xz", "r:xz") as archive:
        return archive.extractfile("hard.txt").read().decode().splitlines()

def try_hard23_family(i, p):
    # The solved hard[23] cylinder differs from hard[10]/hard[15] only at E0/F1.
    # Reuse its discovered family as an adversarial transfer test.
    q = 1
    st = ms.Config(q, ms.Word(), ms.Word.of(
        "011" * 4 + "000011", ms.Rep("000011" * 3), "000001100"
    ))
    target = ms.Config(q, ms.Word(), ms.Word.of(
        "011" * 4 + "000011" * 4, ms.Rep("000011" * 3), "000001100"
    ))
    ans = ms.execute(p, st, target, limit=3000)
    if ans is None:
        print(f"HARD23_FAMILY_NO_MACRO index={i}")
        return
    source, (entry, fixed, affine) = ms.generate(i, p, (632, st, target, ans))
    out = ROOT / f"Raw112Hard23Family{i}.lean"
    out.write_text(source)
    print(f"HARD23_FAMILY_MACRO index={i} entry={entry} fixed={fixed} affine={affine} file={out.name}")
    print(f"macro_steps={len(ans[0])}")

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--limit", type=int, default=5000)
    ap.add_argument("--indices", type=int, nargs="+", default=[10, 15])
    args = ap.parse_args()
    rows = load_hard_rows()
    for i in args.indices:
        p = pump.parse(rows[i])
        try_hard23_family(i, p)
        ans = ms.discover(p, limit=args.limit)
        if ans is None:
            print(f"NO_FAMILY index={i} limit={args.limit}")
            continue
        source, (entry, fixed, affine) = ms.generate(i, p, ans)
        out = ROOT / f"Raw112Multisweep{i}.lean"
        out.write_text(source)
        print(f"FOUND index={i} entry={entry} fixed={fixed} affine={affine} file={out.name}")
        print(f"start={ans[1]!r}")
        print(f"target={ans[2]!r}")
        print(f"macro_steps={len(ans[3][0])}")

if __name__ == "__main__":
    main()
