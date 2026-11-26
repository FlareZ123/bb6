from pathlib import Path
import gzip, base64, hashlib
base = Path(__file__).resolve().parent
sources = {
    "NeedleTerminalExtensionCore.lean": "9d81f756398184e4baf5e775fb2358c45ddde5ee7080cc3a8b0cc780ba34cda9",
    "terminal_extension.py": "d225b2611e9fd542bf9dcfd7f08e10d7adcf44aee011558654f9ccc87874345d",
}
for name, digest in sources.items():
    data = gzip.decompress(base64.b64decode((base/(name+".gz.b64")).read_text()))
    assert hashlib.sha256(data).hexdigest()==digest, name
    (base/name).write_bytes(data)
    print(name, len(data), digest)
