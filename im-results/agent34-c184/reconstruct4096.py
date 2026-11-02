"""Reconstruct hash-pinned formal exclusion proofs for fourteen C reset classes mod 4096."""
import base64
import fcntl
import hashlib
import lzma
import os
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
COMPRESSED_SHA = "8ca72be67acbdd33365ab259326aeb6415c78bbb011c6a949c245af1c696613e"
GENERATOR_SHA = "dd41f0770e979f9526ea43bea5237dc8f34b08cb65dd659b341e25c9c91e2263"
DERIVED_SHA = "6a0614c2d2230aaf156de0e25762c2192e8376899c6fae3cfae8dc733b486520"
SHARDS = {
  0: [3691, 3936, 992, 1079, 1792, 1867, 2112],
  1: [2283, 2379, 2688, 2827, 3648, 3979, 855],
}
SHARD_SHAS = {
  0: "25daa1c3333e57f389d4d110590f723a1ad77b2c54f3c24495d03a73854a99ca",
  1: "6d1f28936b973c28e7bb36146fa1dc1691a10eb1c9992bb44c77c0e5f1618a44",
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main(shard: int) -> None:
    compressed = base64.b64decode((HERE / "generate.py.xz.b64").read_bytes())
    assert sha(compressed) == COMPRESSED_SHA
    source = lzma.decompress(compressed)
    assert sha(source) == GENERATOR_SHA
    derived = source.decode("utf-8").replace("M=1024;r=", "M=4096;r=")
    derived = derived.replace("reset_mod1024_", "reset_mod4096_")
    derived = derived.replace("f'CReset{r}.lean'", "f'C4096R{r}.lean'").encode()
    assert sha(derived) == DERIVED_SHA
    with (HERE / ".reconstruct-4096.lock").open("w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        with tempfile.TemporaryDirectory(dir=HERE) as td:
            working = Path(td)
            generator = working / "generate4096.py"
            generator.write_bytes(derived)
            files = {}
            for r in SHARDS[shard]:
                subprocess.run([sys.executable, str(generator), str(r)], check=True, capture_output=True)
                name = f"C4096R{r}.lean"
                files[name] = (working / name).read_bytes()
            digest = hashlib.sha256()
            for name, data in files.items():
                digest.update(name.encode() + b"\0" + data + b"\0")
            assert digest.hexdigest() == SHARD_SHAS[shard], "Generated Lean source mismatch"
            for name in files:
                os.replace(working / name, HERE / name)
    print(f"SHA-256 verified {len(files)} Lean source proofs, mod4096 shard {shard}")


if __name__ == "__main__":
    main(int(sys.argv[1]))
