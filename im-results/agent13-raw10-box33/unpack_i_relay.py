from pathlib import Path
import base64
import hashlib
import lzma
from unpack_i_parametric import unpack as unpack_base

HERE = Path(__file__).resolve().parent
ARCHIVE = HERE / "Box33D17V12IRelay.lean.xz.b64"
DEST = HERE / "Box33D17V12IRelay.lean"
EXPECTED_SHA256 = "41050fb6247dfdc906b94c03484c36934c53483d038931daf7c6aece4e8a00fb"

if __name__ == "__main__":
    unpack_base()
    data = lzma.decompress(base64.b64decode(ARCHIVE.read_text().strip()))
    actual = hashlib.sha256(data).hexdigest()
    if actual != EXPECTED_SHA256:
        raise ValueError(f"Hash mismatch: {actual}")
    DEST.write_bytes(data)
    print(f"Reconstructed {DEST} SHA256={actual}")
