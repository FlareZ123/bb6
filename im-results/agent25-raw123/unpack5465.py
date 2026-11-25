"""Reconstruct the exact final residual proof from its compact checked source."""
from pathlib import Path
import base64, lzma, hashlib
ROOT = Path(__file__).resolve().parent
def unpack(out=ROOT):
    data = lzma.decompress(base64.b64decode((ROOT/"Raw1235465.lean.xz.b64").read_text()))
    assert hashlib.sha256(data).hexdigest() == "295911ae63b56c60246364e100cd9fa8cd7b11639b76d8f008c3790fd3ffd695"
    out.mkdir(exist_ok=True)
    (out/"Raw1235465.lean").write_bytes(data)
if __name__ == "__main__":
    unpack()
