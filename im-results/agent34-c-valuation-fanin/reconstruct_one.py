"""Atomically restore the SHA-pinned original-source valuation-one Lean proof."""
import base64
import hashlib
import lzma
import os
from pathlib import Path
import tempfile

source = Path(__file__).with_name("ValuationOne.lean.xz.b64")
payload = lzma.decompress(base64.b64decode(source.read_bytes()))
expected = "91200189350056af75c83cf433b3233cba91298ab6b36a3fd107103227ddba1d"
assert hashlib.sha256(payload).hexdigest() == expected

output = Path.cwd() / "ValuationOne.lean"
lock_path = output.with_suffix(".lock")
lock_fd = os.open(lock_path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
try:
    with tempfile.NamedTemporaryFile(dir=output.parent, delete=False) as temp:
        temp.write(payload)
        temporary_path = Path(temp.name)
    os.replace(temporary_path, output)
finally:
    os.close(lock_fd)
    lock_path.unlink()
print("ValuationOne.lean:", expected, "bytes:", len(payload))
