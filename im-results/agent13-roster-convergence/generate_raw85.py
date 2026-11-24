"""Generate the raw85 / F1=1RA sibling with the shared four-hole checker.

The underlying generator is Agent31's source-checked four-hole sibling
pipeline. This wrapper changes only the root partial table and output
directory, keeping generated modules isolated from Agent11's F1=0RA run.
"""
from pathlib import Path
import sys

GENERATOR_DIR = Path(__file__).resolve().parents[1] / "agent31-three-hole-tnf"
sys.path.insert(0, str(GENERATOR_DIR))
import generate_four_hole_sibling as sibling

OUTPUT_DIR = Path(__file__).resolve().parent / "raw85"
OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

sibling.ROOT = OUTPUT_DIR
sibling.PARENT = "1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---1RA"
sibling.main()
