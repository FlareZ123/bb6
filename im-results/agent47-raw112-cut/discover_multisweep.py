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

def discover_extended(p, limit=100000, max_events=250, window=15, maxrep=4, maxlen=24):
    """Broader multi-block search than multi_sweep.discover's default 60x9 window."""
    from collections import defaultdict
    events = pump.concrete_events(p, limit)
    groups = defaultdict(list)
    for t, side, config in events:
        if (side == "L" and config.l.pre == "") or (side == "R" and config.r.pre == ""):
            groups[(side, config.q)].append((t, config.r.pre if side == "L" else config.l.pre))
    attempts = 0
    for (side, q), group in groups.items():
        for i, (t, a) in enumerate(group[:max_events]):
            for j in range(i + 1, min(i + window, len(group))):
                _, b = group[j]
                diff = len(b) - len(a)
                if not 1 <= diff <= maxlen:
                    continue
                for k in range(j + 1, min(j + window, len(group))):
                    _, cword = group[k]
                    if len(cword) - len(b) != diff:
                        continue
                    for w in ms.infer(a, b, cword, maxrep=maxrep, maxlen=maxlen):
                        if sum(isinstance(x, ms.Rep) for x in w.parts) < 2:
                            continue
                        v = w.inc()
                        start = ms.Config(q, ms.Word(), w) if side == "L" else ms.Config(q, w, ms.Word())
                        target = ms.Config(q, ms.Word(), v) if side == "L" else ms.Config(q, v, ms.Word())
                        attempts += 1
                        result = ms.execute(p, start, target, limit=5000)
                        if result:
                            print(f"EXTENDED_ATTEMPTS={attempts}")
                            return t, start, target, result
    print(f"EXTENDED_ATTEMPTS={attempts}")
    return None

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
            print(f"DEFAULT_NO_FAMILY index={i} limit={args.limit}")
            ans = discover_extended(p, limit=max(args.limit, 100000))
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
