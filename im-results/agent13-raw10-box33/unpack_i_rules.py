from pathlib import Path
import base64, hashlib, lzma
from unpack_i_parametric import unpack as unpack_base
HERE = Path(__file__).resolve().parent
ENC = HERE / "Box33D17V12IRules.lean.xz.b64"
OUT = HERE / "Box33D17V12IRules.lean"
SHA256 = "a0c1e23eb4e1f09acf29c624e5f5a8657f7fd85508de82005bc9ed031997ef56"

if __name__ == "__main__":
    unpack_base()
    data = lzma.decompress(base64.b64decode(ENC.read_text().strip()))
    digest = hashlib.sha256(data).hexdigest()
    if digest != SHA256:
        raise ValueError(f"Rules SHA256 mismatch: {digest}")
    OUT.write_bytes(data)
    print(f"Reconstructed {OUT} SHA256={digest}")
