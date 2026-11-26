import base64, hashlib, json, lzma
from pathlib import Path
root = Path(__file__).resolve().parent
raw = lzma.decompress(base64.b64decode((root / 'density-lean.json.xz.b64').read_bytes()))
assert hashlib.sha256(raw).hexdigest() == 'afb74bc270d9a9d38899a3329ca9df22639cdf14b548e02408002bbee934c660'
files = json.loads(raw)
assert set(files) == {'NeedleOrderBound.lean','NeedleOrderCert.lean','NeedleOrderTable.lean','NeedleTerminalDensityArithmetic.lean','NeedleLowHits.lean'}
for name, src in files.items():
    (root / name).write_bytes(src.encode('utf-8'))
    print(name, hashlib.sha256(src.encode('utf-8')).hexdigest())
