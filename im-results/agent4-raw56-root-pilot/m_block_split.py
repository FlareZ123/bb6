"""Emit sharded, original-source Lean stack certificates for the remaining 1LB machines.

This is a deterministic specialization of the already accepted M42763
emitter. It preserves the same trusted TwoSidedChunks checker and moves only
the literal Turing table, discovered finite relation, and theorem namespace.
The source generator is untrusted; kernel-checked theorem/axiom profiles are
the acceptance criterion.
"""
from pathlib import Path
import argparse
import sys

parser = argparse.ArgumentParser()
parser.add_argument("--machine", choices=("23706", "39232", "42763"), required=True)
parser.add_argument("--out-dir", required=True)
args = parser.parse_args()

here = Path(__file__).resolve()
reference = here.with_name("m42763_split.py")
template = reference.read_text()
assert template.count("42763") == 18, "Unexpected template revision"
assert "from m42763_block_cert import TABLE, LEFT, RIGHT, EXPECTED, abstract, blockgram, emit" in template
machine = args.machine
specialized = template.replace("42763", machine)
sys.argv = [str(here.with_name("m" + machine + "_split.py")), "--out-dir", args.out_dir]
exec(compile(specialized, sys.argv[0], "exec"),
     {"__name__": "__main__", "__file__":sys.argv[0]})
