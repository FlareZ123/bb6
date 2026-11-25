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

def main():
    # The specialization script produces a finite-width kernel checker.
    subprocess.run([sys.executable, str(BLOCK / "specialize.py"), "4"], check=True)
    # Frontier defines the BB6Coverage types used by raw59 (via RootShift/Symmetry).
    bridge = (BLOCK / "BlockFARBridge.lean").read_text()
    for i, (table, width, cap, mod, runs) in CASES.items():
        name = f"Raw59LB1M{i}"
        ns = f"BB6BlockFAR{width}"
        generate(table, ROOT, width=width, cap=cap, mod=mod, runs=runs,
                 name=name, minimize_left=True)
        # Reuse the exact Frontier source bridge with the specialized block types.
        text = bridge
        text = text.replace("import BlockFAR\n", f"import BlockFAR{width}\n")
        text = text.replace("BB6BlockFAR", ns)
        # The import is not namespaced and must not be renamed twice.
        (ROOT / f"Raw59LB1BlockBridge{width}.lean").write_text(text)
        (ROOT / f"Raw59LB1Block{i}.lean").write_text(f"""import {name}Proof
import Raw59LB1BlockBridge{width}
namespace BB6.Agent32Raw59LB1Block{i}
def table : BB6Coverage.PartialMachine := {ns}.partialTable {ns}.{name}.machine
theorem never (m : BB6Coverage.Machine) (hm : BB6Coverage.compatible table m) :
    BB6Coverage.NeverHalts m :=
  {ns}.transfer_never {ns}.{name}.machine m hm {ns}.{name}.never
#print axioms never
end BB6.Agent32Raw59LB1Block{i}
""")
    subprocess.run([sys.executable, str(ROOT / "emit_rungram.py")], check=True)
    (ROOT / "Raw59LB1Four.lean").write_text(
        "import Raw59LB1RunGram\nimport Raw59LB1Block190\nimport Raw59LB1Block194\n")

if __name__ == "__main__":
    main()
