from pathlib import Path
import base64, lzma, hashlib
p=Path(__file__).resolve().parent
s=lzma.decompress(base64.b64decode((p/'SignedDrift.lean.xz.b64').read_bytes()))
assert hashlib.sha256(s).hexdigest()=='94a1a7a4c25f98031b8d758048c05430ab5894bb51e2c144f8ee46f6f7846a0e'
(p/'SignedDrift.lean').write_bytes(s)
