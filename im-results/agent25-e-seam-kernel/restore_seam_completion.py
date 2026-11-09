"""Restore both source E3 seed encoder and the finite-certificate composition."""
from pathlib import Path
from tempfile import NamedTemporaryFile
from filelock import FileLock
import base64
import hashlib
import lzma
import os
import sys

ROOT = Path(__file__).resolve().parent
DIGESTS = {
    "SourceSeedMatch": "b08761435e4615e4a873b8afb2a1cc255ea3d6a794d00b96d7b8899a70fafa15",
    "SourceSeamComplete": "282aeb8163f6b7790000614a44aa292b500a14c2162355e517b6d55ba8ca1dd9",
}

def restore(output_dir: Path) -> None:
    output_dir.mkdir(parents=True, exist_ok=True)
    for stem, expected in DIGESTS.items():
        data = lzma.decompress(base64.b64decode(
            (ROOT / f"{stem}.lean.xz.b64").read_text().strip(), validate=True))
        digest = hashlib.sha256(data).hexdigest()
        if digest != expected:
            raise ValueError(f"{stem}: source integrity mismatch {digest}")
        dest = output_dir / f"{stem}.lean"
        with FileLock(str(dest) + ".lock"):
            with NamedTemporaryFile(dir=output_dir, prefix=f".{stem}-", delete=False) as tmp:
                tmp.write(data)
                tmp.flush()
                os.fsync(tmp.fileno())
                temp_name = tmp.name
            os.replace(temp_name, dest)
        print(f"Restored {dest}, SHA256 {digest}")

if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("Usage: python restore_seam_completion.py OUTPUT_DIRECTORY")
    restore(Path(sys.argv[1]))
