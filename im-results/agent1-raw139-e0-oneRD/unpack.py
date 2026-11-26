"""Restore the exact locally checked Lean source (stdlib only)."""
import gzip, hashlib
from pathlib import Path
root=Path(__file__).resolve().parent
src=gzip.decompress((root/'E0OneRDLate.lean.gz').read_bytes())
assert hashlib.sha256(src).hexdigest()=='22daeffba368d37c910d2f8db41aa9024ac6a732c30547518ddcbae03a25b8b7'
(root/'E0OneRDLate.lean').write_bytes(src)
