"""Atomically regenerate hash-pinned Lean source for 43 C reset classes modulo 2048."""
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
DERIVED_SHA = "5aec3495bcf2c1b22f870167e6103e5cff9703a3f59a8826c44756c650e3f7cc"
SHARDS = {
  0: [183, 267, 394, 654, 911, 978, 1239, 1322, 1472, 1896],
  1: [42, 128, 411, 498, 535, 792, 1056, 1099, 1458, 1778, 1862],
  2: [439, 474, 582, 747, 1003, 1070, 1248, 1416, 1646, 1871, 1954],
  3: [166, 546, 824, 952, 1119, 1160, 1344, 1498, 1504, 1766, 1994],
}
SHARD_SHAS = {
  0: "ec5be4651d618b1ee453618d48f7f2952b23292f31f16790d5f1ba582375e069",
  1: "d90519c1b746b6fedadf193e7de260e2d2f8cf9a926f7faa91855658d6a260a5",
  2: "b5bf62861c67b1a71ec371fd93d8c8e107ff9d81b7b62f0e9734f83d0d3f172e",
  3: "8d901ae1a4deb1bca8656bc46c796b926065e9eef165d681bae6f4a403308658",
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main(shard: int) -> None:
    compressed = base64.b64decode((HERE / "generate.py.xz.b64").read_bytes())
    assert sha(compressed) == COMPRESSED_SHA
    source = lzma.decompress(compressed)
    assert sha(source) == GENERATOR_SHA
    derived = source.decode("utf-8").replace("M=1024;r=", "M=2048;r=")
    derived = derived.replace("reset_mod1024_", "reset_mod2048_")
    derived = derived.replace("f'CReset{r}.lean'", "f'C2048R{r}.lean'").encode()
    assert sha(derived) == DERIVED_SHA
    with (HERE / ".reconstruct-2048.lock").open("w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        with tempfile.TemporaryDirectory(dir=HERE) as td:
            working = Path(td)
            generator = working / "generate2048.py"
            generator.write_bytes(derived)
            files = {}
            for r in SHARDS[shard]:
                subprocess.run([sys.executable, str(generator), str(r)], check=True, capture_output=True)
                name = f"C2048R{r}.lean"
                files[name] = (working / name).read_bytes()
            digest = hashlib.sha256()
            for name, data in files.items():
                digest.update(name.encode() + b"\0" + data + b"\0")
            assert digest.hexdigest() == SHARD_SHAS[shard], "Generated Lean source mismatch"
            for name in files:
                os.replace(working / name, HERE / name)
    print(f"SHA-256 verified {len(files)} universally quantified proof sources, shard {shard}")


if __name__ == "__main__":
    main(int(sys.argv[1]))
