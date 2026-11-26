#!/usr/bin/env python3
"""Materialize the deterministic Raw124 F1=0LF/F0=1RC certificate sources."""
from pathlib import Path
import base64,gzip,hashlib,json,sys,shutil
src=Path(__file__).resolve().parent
out=Path(sys.argv[1]).resolve()
raw=gzip.decompress(base64.b64decode(''.join((src/f'proof-bundle.part{i}.b64').read_text().strip() for i in range(6)),validate=True))
assert hashlib.sha256(raw).hexdigest()=='d0701d3a73927517054e12ff584de9a9fb3cf880721b432654e8606e68ff942b'
for f,s in json.loads(raw).items():
    p=out/f;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s,encoding='utf-8')
seven=src.parent/'agent32-raw124-0lf1rc'/'SevenRC.lean.gz.b64'
(out/'core'/'SevenRC.lean').write_bytes(gzip.decompress(base64.b64decode(seven.read_bytes())))
shutil.copyfile(src/'LateRCBridge.lean',out/'core'/'LateRCBridge.lean')
shutil.copyfile(src/'fix_late.py',out/'fix_late.py')
