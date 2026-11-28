"""Generate a monolithic *original-source* Lean nonhalting proof from an
independently closure-checked context-minimized two-sided certificate.

The generator is untrusted; Lean's existing TwoSidedAutomata.check is the
source truth and #print axioms is gated by the CI checker.
"""
from pathlib import Path
import argparse, importlib, sys

HERE = Path(__file__).resolve()
sys.path.insert(0, str(HERE.parent))
parser = argparse.ArgumentParser()
parser.add_argument("--machine", choices=("23706", "39232"), required=True)
parser.add_argument("--out", required=True)
args = parser.parse_args()
mod = importlib.import_module("m" + args.machine + "_min_cert")
raw = mod.TABLE.replace("_", "")
p = [raw[i:i+3] for i in range(0, len(raw), 3)]
assert len(p) == 12
cert = mod.abstract(p, mod.blockgram(mod.LEFT), mod.blockgram(mod.RIGHT))
got = (cert[1], len(cert[-1][0]), len(cert[-1][1]))
assert got == mod.EXPECTED, got
name = "M" + args.machine
namespace = "BB6.Agent4Raw56RootE11LB." + name + "Block"
source = (
    "import TwoSidedAutomata\n"
    "set_option maxRecDepth 100000\n"
    "set_option maxHeartbeats 0\n"
    f"namespace {namespace}\n"
    "open BB6Coverage\n"
    + mod.emit(args.machine, p, cert)
    + f"\nend {namespace}\n"
)
Path(args.out).write_text(source)
print("minimized single-source", name, "joint, left, right =", got)
