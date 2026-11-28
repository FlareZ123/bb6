from pathlib import Path
import base64
import hashlib
import lzma
from unpack_i_parametric import unpack as unpack_base

HERE = Path(__file__).resolve().parent
ARCHIVE = HERE / "Box33D17V12IRelay.lean.xz.b64"
DEST = HERE / "Box33D17V12IRelay.lean"
EXPECTED_SHA256 = "7c6180466522fa9ee286bfc62cceb323a1c3573f00b0c71cd95d0f0813909b4f"

if __name__ == "__main__":
    unpack_base()
    data = lzma.decompress(base64.b64decode(ARCHIVE.read_text().strip()))
    actual = hashlib.sha256(data).hexdigest()
    if actual != EXPECTED_SHA256:
        raise ValueError(f"Hash mismatch: {actual}")
    DEST.write_bytes(data)
    print(f"Reconstructed {DEST} SHA256={actual}")
