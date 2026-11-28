from pathlib import Path
import base64, hashlib, json, lzma, sys

here = Path(__file__).resolve().parent
out = Path(sys.argv[1] if len(sys.argv) > 1 else "raw10-box12-work").resolve()
out.mkdir(parents=True, exist_ok=True)
raw = lzma.decompress(base64.b64decode("".join((here / name).read_text().strip() for name in ("source-part-aa.b64", "source-part-ab.b64")), validate=True))
assert hashlib.sha256(raw).hexdigest() == "7f35bfdde7e0e64231af52ebc093bb45b4a3bd9b3cb7e2e573c2ff088f73edff"
for name, source in json.loads(raw).items():
    assert Path(name).name == name
    (out / name).write_text(source)
print(out)
