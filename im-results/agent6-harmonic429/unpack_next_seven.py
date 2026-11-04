"""Verify SHA256 and reconstruct seven Lean root-sector inverse certificates."""
import base64
import fcntl
import hashlib
import lzma
import os
import tempfile
from pathlib import Path

directory = Path(__file__).resolve().parent
input_file = directory / "BB429NextSeven.lean.xz.b64"
output_file = directory / "BB429NextSeven.lean"
expected_sha = "35c2d11c908ba58268b2c347bf7c92eabe9f5e75d95b74f1cb14459aef69ad59"
data = lzma.decompress(base64.b64decode(input_file.read_text().strip()))
assert hashlib.sha256(data).hexdigest() == expected_sha
with (directory / ".nextseven.lock").open("w") as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    with tempfile.NamedTemporaryFile(dir=directory, delete=False) as file:
        file.write(data)
        temp_name = file.name
    os.replace(temp_name, output_file)
    fcntl.flock(lock, fcntl.LOCK_UN)
print(f"Reconstructed {output_file.name}: SHA256 {expected_sha}")
