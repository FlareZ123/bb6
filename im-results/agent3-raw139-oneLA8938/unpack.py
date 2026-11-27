import base64, gzip, hashlib
from pathlib import Path
p=Path(__file__).resolve().parent
s=gzip.decompress(base64.b64decode((p/"Raw139OneLA8938Sweep.lean.gz.b64").read_text()))
assert hashlib.sha256(s).hexdigest()=="72e9a4ebdeb28a996f9142a299690b7857dcd660894612a96bb4982f88bc4e8f"
(p/"Raw139OneLA8938Sweep.lean").write_bytes(s)
