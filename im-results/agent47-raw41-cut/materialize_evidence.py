"""Restore exact witness files and optionally enumerate/generate the proof trees.
Run here, after building ../agent19-raw40-cut/enumerate_canon.cpp as ./enumerate.
No rediscovery or search of FAR or sweep witnesses is needed.
The archive contains candidates as well as compiled children; only Lean checks certify them.
"""
import base64,gzip,hashlib,json,subprocess,sys
from pathlib import Path

root=Path(__file__).resolve().parent
payload=gzip.decompress(base64.b64decode((root/'survey-evidence.json.gz.b64').read_text()))
assert hashlib.sha256(payload).hexdigest()=='fbc96884c0daf2ff5410c86379ff102010476d7ebec48e309107345ba80c4c24'
data=json.loads(payload)
ids=[x.zfill(3) for x in sys.argv[1:] if x!='--generate'] or list(data)
for i in ids:
 d=data[i];p=root/'survey'/i;p.mkdir(parents=True,exist_ok=True)
 for f,s in d['files'].items():(p/f).write_text(s)
 print(i,d['name'],d['bound'],d['table'],flush=True)
 if '--generate' in sys.argv:
  subprocess.run([str(root/'enumerate'),d['table']],cwd=p,check=True)
  subprocess.run([sys.executable,'gen_children.py',str(p),d['name'],str(d['bound']),d['table']],cwd=root,check=True)
