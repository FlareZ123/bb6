"""Generate Lean proofs for quarter cones using t = 7*Y-(q+2).

Produces full arithmetic cases checked by Lean's kernel against unmodified
Agent1, Agent50 and ConeKernel source, and an abstract all-residue power bound.
"""
import re
from pathlib import Path
from sys import argv

import emit
from scan import Aff
from scan4 import check4, ancestors4, gap4


def shift(x: Aff) -> Aff:
    return Aff(x.a, x.c + 2 * x.a)


def unshift(x: Aff) -> Aff:
    return Aff(x.a, x.c - 2 * x.a)


def generate(r: int) -> str:
    def get(i: int):
        raw = check4(i)
        if not raw:
            raise ValueError("quarter inverse cone does not close")
        return [
            (shift(b), shift(d),
             [(shift(x), shift(y), kind, gap) for x, y, kind, gap in children])
            for b, d, children in raw
        ]

    emit.check = get
    emit.ancestors = lambda b, d: [
        (shift(k), shift(v))
        for k, v in ancestors4(unshift(b), unshift(d), r)
    ]
    emit.gap = lambda x: gap4(unshift(x), r)
    source = emit.generate(r, source=True)

    # Both pinned generator revisions are supported: one includes an optional
    # last theorem while the other already ends after the no_hub proof.
    marker = f"theorem no_critical_{r}"
    if marker in source:
        source = source[:source.index(marker)] + "end BB6.Agent45Generator\n"
    source = source.replace("65536*q+", "262144*q+")
    source = source.replace(f"({r}-16)", f"({r}-18)")
    source = source.replace("223 ≤ t", f"222+224*{r} ≤ t")

    first = source.index("theorem X_bound ")
    last = source.index("theorem not_between ", first)
    bound = f"""theorem Y_bound_{r} (q : Nat) :
    32*(q+{r}+1) ≤ 2^(262144*q+({r}-18)) :=
  BB6.Agent45Quarter.quarter_exponent_bound {r} q (by omega)

"""
    source = source[:first] + bound + source[last:]
    source = source.replace(
        f"32*(q+1) ≤ X := by simpa [X] using X_bound q {r} (by omega)",
        f"32*(q+{r}+1) ≤ X := by simpa [X] using Y_bound_{r} q",
    )
    source = source.replace(
        f"by have hX := X_bound q {r} (by omega); omega",
        f"by have hX := Y_bound_{r} q; omega",
    )
    source = re.sub(
        r"apply power_gap_of_bounds (\(262144\*q\+\(" + str(r) + r"-18\)\)) (\d+)",
        lambda m: f"apply power_gap_of_bounds {m.group(1)} {int(m.group(2)) + 2}",
        source,
    )
    source = re.sub(
        r"\(14:Nat\)\*2\^(\d+)=(\d+)",
        lambda m: f"(14:Nat)*2^{int(m.group(1))+2}={4*int(m.group(2))}",
        source,
    )
    source = re.sub(
        r"\(14:Nat\)\*2\^\((\d+)\+1\)=(\d+)",
        lambda m: f"(14:Nat)*2^({int(m.group(1))+2}+1)={4*int(m.group(2))}",
        source,
    )
    source = re.sub(
        r"change (\d+)\*X <",
        lambda m: f"change {4*int(m.group(1))}*X <",
        source,
    )
    source = re.sub(
        r"< (\d+)\*X",
        lambda m: f"< {4*int(m.group(1))}*X",
        source,
    )

    source = source.replace("import P1Gate", "import P1Gate\nimport GeneralQuarterBound")
    source = source.replace("(q+1)", "(q+2)")
    source = source.replace(f"32*(q+{r}+2) ≤ 2^", f"32*(q+{r}+1) ≤ 2^")
    source = source.replace(f"32*(q+{r}+2) ≤ X", f"32*(q+{r}+1) ≤ X")

    # A symbolic lemma avoids expanding the numeral 224*r in omega.
    source = source.replace(
        f"theorem instantiated_{r} (q : Nat) :",
        f"""private theorem generic_t_bound (q r X : Nat)
    (hX : 32*(q+r+1)≤X) : 222+224*r≤7*X-(q+2) := by omega

theorem instantiated_{r} (q : Nat) :""",
    )
    source = source.replace(
        f"exact closed_{r} _ (by have hX := Y_bound_{r} q; omega) (powerOK_{r} q)",
        f"exact closed_{r} _ (generic_t_bound q {r} _ (Y_bound_{r} q)) (powerOK_{r} q)",
    )
    source = source.replace(
        "namespace BB6.Agent45Generator",
        "namespace BB6.Agent45Generator\nset_option maxRecDepth 8192\nset_option maxHeartbeats 1000000",
        1,
    )
    return source


if __name__ == "__main__":
    residue = int(argv[1])
    path = Path(argv[2])
    path.write_text(generate(residue))
    print(path, path.stat().st_size)
