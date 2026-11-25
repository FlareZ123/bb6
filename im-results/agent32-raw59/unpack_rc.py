from pathlib import Path
import base64, hashlib, lzma
root=Path(__file__).resolve().parent
data=lzma.decompress(base64.b64decode((root/'Raw59RCShared.lean.xz.b64').read_text()))
assert hashlib.sha256(data).hexdigest()=='207cc91f598334ec6a927a43f8b6c087b6e87d87b8a5a6567842d73c713fe686'
(root/'Raw59RCShared.lean').write_bytes(data)

data=lzma.decompress(base64.b64decode((root/'Raw59RFCounters.lean.xz.b64').read_text()))
assert hashlib.sha256(data).hexdigest()=='eab6a9c4181a910febada11cf657d58cddcdf8bb01732558a86aaac1714fb229'
(root/'Raw59RFCounters.lean').write_bytes(data)

data=lzma.decompress(base64.b64decode((root/'Raw59RFTriple.lean.xz.b64').read_text()))
assert hashlib.sha256(data).hexdigest()=='7153412796e6a8fc41f95fdbb96b0684b44662222bae92927746fd15211379c6'
(root/'Raw59RFTriple.lean').write_bytes(data)

data=lzma.decompress(base64.b64decode((root/'Raw59RFScan.lean.xz.b64').read_text()))
assert hashlib.sha256(data).hexdigest()=='9420f855a4586e1fddfa830992d773eb4b5a654483eeefc71dc5bdc480b3232e'
(root/'Raw59RFScan.lean').write_bytes(data)
