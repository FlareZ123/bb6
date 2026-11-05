"""Derive Machine C M192 source proofs from the previously audited M512 bridge.

This prints the generated Lean module to standard output.
"""
import base64
import lzma
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MODE = sys.argv[1]
if MODE == "quotient":
    encoded = (ROOT / "im-results/agent41-c-quotient512/Quotient512.lean.xz.b64").read_text().strip()
    source = lzma.decompress(base64.b64decode(encoded)).decode("utf-8")
elif MODE == "bridge":
    source = (ROOT / "im-results/agent41-c-quotient512/CMapBridge.lean").read_text(encoding="utf-8")
else:
    raise ValueError("Expected quotient or bridge")

for before, after in (("512", "192"), ("520", "200"), ("Agent41", "Agent41M192")):
    source = source.replace(before, after)
sys.stdout.write(source)
