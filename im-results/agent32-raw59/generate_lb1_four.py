"""Generate the four final known raw59/1LB nonhalting candidates.

Uses the existing finite block-FAR checker for 190 and 194, and the
existing two-sided DFA checker for 189 and 191. No search at proof time.
"""
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
BLOCK = ROOT.parent / "agent13-block-far"
sys.path.insert(0, str(BLOCK))
from generate_multi import generate

CASES = {
    190: ("1RB1LB_1RC0LB_0RD0RF_1LD1RE_1LC1LA_---1RA", 4, 1, 7, 6),
    194: ("1RB1LB_1RC0LB_0RD0RF_1LD1RE_1RD1LA_---1RA", 2, 3, 2, 3),
}

EXTRA = {
    "0LB": {
        127: ("1RB0LB_1RC0LB_0RD0RF_1LD1RE_0RA1LA_---1RA", 4, 1, 7, 6),
        270: ("1RB0LB_1RC0LF_0RD---_1LD1RE_0RA1LA_0LE1RC", 4, 1, 7, 6),
        638: ("1RB0LB_1RC1LA_0RD0RE_1LD1RE_1RF1LA_---1RB", 4, 1, 7, 6),
        1141: ("1RB0LB_1RC1LF_0RD1RA_1LD1RE_---1LA_1LB0RC", 4, 1, 7, 6),
        1590: ("1RB0LB_1RC1RF_0RD1RC_1LD1RE_0RA1LA_0LA---", 4, 1, 7, 6),
    },
    "1LE": {
        564: ("1RB1LE_1RC0LF_0RD0RF_1LD1RE_---1LA_0RC1LB", 4, 1, 7, 6),
        869: ("1RB1LE_1RC0RB_0RD---_1LD1RE_0LF1LA_0LF0RA", 2, 1, 3, 2),
        1570: ("1RB1LE_1RC0RF_0RD0LA_1LD1RE_0RB1LA_---0LA", 2, 2, 3, 3),
        2173: ("1RB1LE_1RC0RF_0RD0RC_1LD1RE_---1LA_1LC1RF", 4, 1, 7, 6),
        3820: ("1RB1LE_1RC1RF_0RD0LA_1LD1RE_0RB1LA_---1RC", 2, 2, 3, 3),
    },
}

def cases_for(branch, opens=None):
    cases = dict(CASES if branch == "1LB" else EXTRA.get(branch, {}))
    if opens is not None:
        for row in (ROOT / "block_groups.txt").read_text().splitlines():
            if not row or row.startswith("#"): continue
            left, right = row.split(":")
            b, w, c, m, r, *offset = left.split()
            if b != branch: continue
            for i in map(int, right.split()):
                assert i not in cases
                cases[i] = (opens[i], *map(int, (w,c,m,r)), *map(int,offset))
        for i,(table,*_) in cases.items():
            assert opens[i] == table
    return cases

def main(branch="1LB", opens=None, override=None):
    # The specialization script produces a finite-width kernel checker.
    cases = cases_for(branch, opens) if override is None else override
    if any(row[1] == 4 for row in cases.values()):
        subprocess.run([sys.executable, str(BLOCK / "specialize.py"), "4"], check=True)
    # Frontier defines the BB6Coverage types used by raw59 (via RootShift/Symmetry).
    bridge = (BLOCK / "BlockFARBridge.lean").read_text()
    prefix = "Raw59LB1" if branch == "1LB" else f"Raw59{branch}"
    for i, (table, width, cap, mod, runs, *offset) in cases.items():
        name = f"{prefix}M{i}"
        ns = "BB6BlockFAR" if width == 3 else f"BB6BlockFAR{width}"
        data = generate(table, ROOT, width=width, cap=cap, mod=mod, runs=runs,
                 name=name, minimize_left=True, offset=offset[0] if offset else 0)
        if branch in ('0LA','0LB','0LF','1LB'):
            from emit_blockmask import emit
            emit(ROOT, name, data, offset[0] if offset else 0)
        # Reuse the exact Frontier source bridge with the specialized block types.
        bridge_mod = "BlockFARBridge" if width == 3 else f"Raw59LB1BlockBridge{width}"
        if width == 2:
            # BlockMacro2 exports the SAME primitive types and run as BlockMacro.
            text = """import BlockFAR2
import BlockFARBridge
namespace BB6BlockFAR2
abbrev partialTable := BB6BlockFAR.partialTable
abbrev transfer_never := BB6BlockFAR.transfer_never
end BB6BlockFAR2
"""
            (ROOT / f"{bridge_mod}.lean").write_text(text)
        elif width != 3:
            text = bridge.replace("import BlockFAR\n", f"import BlockFAR{width}\n").replace("BB6BlockFAR", ns)
            (ROOT / f"{bridge_mod}.lean").write_text(text)
        (ROOT / f"{prefix}Block{i}.lean").write_text(f"""import {name}Proof
import {bridge_mod}
namespace BB6.Agent32{prefix}Block{i}
def table : BB6Coverage.PartialMachine := {ns}.partialTable {ns}.{name}.machine
theorem never (m : BB6Coverage.Machine) (hm : BB6Coverage.compatible table m) :
    BB6Coverage.NeverHalts m :=
  {ns}.transfer_never {ns}.{name}.machine m hm {ns}.{name}.never
#print axioms never
end BB6.Agent32{prefix}Block{i}
""")
    imports = [f"import {prefix}Block{i}" for i in cases]
    if branch == "1LB" and override is None:
        subprocess.run([sys.executable, str(ROOT / "emit_rungram.py")], check=True)
        imports.insert(0, "import Raw59LB1RunGram")
    (ROOT / f"{prefix}Four.lean").write_text("\n".join(imports)+"\n")

if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "1LB")
