from pathlib import Path
import base64, lzma, hashlib
p=Path(__file__).resolve().parent
for name,digest in [('SignedDrift','94a1a7a4c25f98031b8d758048c05430ab5894bb51e2c144f8ee46f6f7846a0e'),('SignedLift','46d78527203d0b4d61d32fec0f336325573730481158412d0cf863a4cdf8ff23')]:
    s=lzma.decompress(base64.b64decode((p/(name+'.lean.xz.b64')).read_bytes()))
    assert hashlib.sha256(s).hexdigest()==digest
    (p/(name+'.lean')).write_bytes(s)
