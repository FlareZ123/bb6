"""Reproducible n>=55 specialization of the source-audited two-reset Lean modules.

Run only after the original tar.xz archives have been SHA256 checked and unpacked.
The transformation changes the induction anchor from n=70 to n=55:
  growth exponent offset 70 -> 55; polynomial bases 72 -> 57, 73 -> 58;
  all theorem lower-bound hypotheses 70 -> 55.
All remaining mathematical statements and proofs stay byte-identical.
The output is separately compiled by the Lean kernel against original P1 sources.
"""
from pathlib import Path
import fcntl
import os
import re
import tempfile

ROOT = Path(__file__).resolve().parent
DEST = ROOT / "n55"
MODULES = (
    "TwoResetGrowth",
    "TwoResetTailBudget",
    "TwoResetWall",
    "DefectPositive",
    "TwoResetRemainder",
    "TwoResetDefectBridge",
    "FirstBlockDefect",
    "TwoResetExactEquations",
    "SourceTwoReset",
    "ThreeResets",
)

DEST.mkdir(exist_ok=True)
with (DEST / ".generation.lock").open("w") as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    for name in MODULES:
        source = (ROOT / (name + ".lean")).read_text(encoding="utf-8")
        transformed = source
        if name == "TwoResetGrowth":
            transformed = re.sub(r"\b72\b", "57", transformed)
            transformed = re.sub(r"\b73\b", "58", transformed)
        transformed = re.sub(r"\b70\b", "55", transformed)
        if name != "DefectPositive" and name != "TwoResetRemainder":
            assert source != transformed, name
        destination = DEST / (name + ".lean")
        fd, temp = tempfile.mkstemp(prefix=name + ".", suffix=".tmp", dir=DEST)
        try:
            with os.fdopen(fd, "w", encoding="utf-8") as output:
                output.write(transformed)
                output.flush()
                os.fsync(output.fileno())
            os.replace(temp, destination)
        finally:
            if os.path.exists(temp):
                os.unlink(temp)
    fcntl.flock(lock, fcntl.LOCK_UN)
print("Generated 10 n>=55 Lean modules from SHA-audited n>=70 source.")
