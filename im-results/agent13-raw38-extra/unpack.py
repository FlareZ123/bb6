"""Unpack immutable candidate bundles into the existing certificate generators."""
import base64, hashlib, json, zlib
from pathlib import Path
ROOT=Path(__file__).resolve().parent
SPEC={6:"9a50d9d0d9b0a628bb2c830e8d95cbaaf3613bfd1a86e7dfc7b3f09dcbfadb83",10:"a909923f9abc547728e9069dfc18c413623ff47e625acc5ce6c0070dbef16d9e",14:"1572930b46c95104ee5cd015f9e6495bfdf95ddaa02b7f5bc39291e1c8ca3824"}
def unpack():
    growth=[];special=[]
    for i,sha in SPEC.items():
        raw=zlib.decompress(base64.b64decode((ROOT/f"branch{i}.b64").read_text()))
        assert hashlib.sha256(raw).hexdigest()==sha
        x=json.loads(raw);growth.extend(x["growth"]);special.extend(x["special"])
    assert len(growth)==771 and len(special)==203
    (ROOT/"growth.b64").write_text(base64.b64encode(zlib.compress(json.dumps(growth,separators=(",",":")).encode(),9)).decode()+"\n")
    (ROOT/"special.txt").write_text("".join(f"{a} {b}\n" for a,b in special))
if __name__=="__main__":unpack()
