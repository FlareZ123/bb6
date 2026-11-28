from pathlib import Path
import base64
import hashlib
import lzma
from unpack_i_parametric import unpack as unpack_base

HERE = Path(__file__).resolve().parent
ARCHIVE = HERE / "Box33D17V12ICarry.lean.xz.b64"
DEST = HERE / "Box33D17V12ICarry.lean"
EXPECTED_SHA256 = "0f6087e14fe831895e92a6248341724718ff9ef43183f55cfbb68f63908c9201"

if __name__ == "__main__":
    unpack_base()
    data = lzma.decompress(base64.b64decode(ARCHIVE.read_text().strip()))
    actual = hashlib.sha256(data).hexdigest()
    if actual != EXPECTED_SHA256:
        raise ValueError(f"Hash mismatch: {actual}")
    DEST.write_bytes(data)
    print(f"Reconstructed {DEST} SHA256={actual}")
