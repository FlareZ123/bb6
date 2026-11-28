from pathlib import Path
import base64, hashlib, lzma

HERE = Path(__file__).resolve().parent
ENC = HERE / "Box33D17V12IParametric.lean.xz.b64"
OUT = HERE / "Box33D17V12IParametric.lean"
EXPECTED = "77e88d80bdf0023a825a3e49bf27a48ebc9807e7336a5ae4690cbca016ec2f5f"

def unpack():
    source = lzma.decompress(base64.b64decode(ENC.read_text().strip()))
    actual = hashlib.sha256(source).hexdigest()
    if actual != EXPECTED:
        raise ValueError(f"Source digest mismatch: {actual} != {EXPECTED}")
    OUT.write_bytes(source)
    print(f"Reconstructed {OUT} SHA256={actual}")

if __name__ == "__main__":
    unpack()
