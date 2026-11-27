#!/usr/bin/env python3
"""Materialize the locally checked H328 proof bundle exactly."""
import base64, hashlib, json, lzma, pathlib, re, sys
p=pathlib.Path(__file__).with_name('H328-proof.json.xz.b64')
raw=lzma.decompress(base64.b64decode(p.read_bytes()))
assert hashlib.sha256(raw).hexdigest()=='fe643963e9e92e585d250efddf06c266bc9e624a4f168a741fb39de90b8b0945'
out=pathlib.Path(sys.argv[1]);out.mkdir(parents=True,exist_ok=True)
sources=json.loads(raw)
assert len(sources)==13 and 'H328.lean' in sources
for name,code in sources.items():
    assert re.fullmatch(r'H328[A-Za-z0-9]*\.lean',name)
    (out/name).write_text(code)
