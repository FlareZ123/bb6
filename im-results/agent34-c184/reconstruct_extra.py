"""Hash-check a Lean proof generator and its four generated source files."""
import base64
import fcntl
import hashlib
import lzma
import os
from pathlib import Path
import subprocess
import sys
import tempfile

DIRECTORY = Path(__file__).resolve().parent
ARCHIVE_SHA256 = "8ca72be67acbdd33365ab259326aeb6415c78bbb011c6a949c245af1c696613e"
GENERATOR_SHA256 = "dd41f0770e979f9526ea43bea5237dc8f34b08cb65dd659b341e25c9c91e2263"
OUTPUTS = {
    38: "c74a84aa02816c6519058e01f989733febce10028108cc1b07f5355bd8b91acf",
    130: "ad1e684137227ba55c96a94e11e3a81b2d0a7aa4a096f934d443492d7c2df2f1",
    642: "ed043fb431ec7a9f85d395a1ffdb7982995e54af9fbcb89018facc3a12f201e5",
    783: "0d4873589220403892fb4c57e10e8093583358b46eebbfd1253721b3349d4189",
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    compressed = base64.b64decode((DIRECTORY / "generate.py.xz.b64").read_bytes())
    assert sha256(compressed) == ARCHIVE_SHA256
    generator = lzma.decompress(compressed)
    assert sha256(generator) == GENERATOR_SHA256
    with (DIRECTORY / ".reconstruct-extra.lock").open("w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        with tempfile.TemporaryDirectory(dir=DIRECTORY) as directory:
            working = Path(directory)
            source = working / "generate.py"
            source.write_bytes(generator)
            generated = {}
            for r, digest in OUTPUTS.items():
                subprocess.run([sys.executable, str(source), str(r)], check=True, capture_output=True)
                name = f"CReset{r}.lean"
                generated[name] = (working / name).read_bytes()
                assert sha256(generated[name]) == digest, f"source mismatch at residue {r}"
            for name, data in generated.items():
                (working / name).write_bytes(data)
                os.replace(working / name, DIRECTORY / name)
    print("Verified generated Lean proofs:", ", ".join(map(str, OUTPUTS)))


if __name__ == "__main__":
    main()
