"""Unpack the exact kernel-checked source of the seven remaining hard30 leaves."""
import base64, hashlib, io, lzma, pathlib, sys, tarfile
here = pathlib.Path(__file__).parent
out = pathlib.Path(sys.argv[1]) if len(sys.argv)>1 else here
out.mkdir(parents=True, exist_ok=True)
hashes = {
    "CounterInvariant.lean": "5f48c1f7916e927e56ec33f47852f64c790bab8442b59d4bb7971850490af0fa",
    "Raw47Hard21.lean": "d1b1ce613f50c828e734379e163a023a2ce21e91a70749a1aad2c63a5545cf93",
    "Raw47Counters.lean": "953900513f794930806ec9000752d0f792623f6744df09fccd1fea1902334295",
}
with tarfile.open(fileobj=io.BytesIO(lzma.decompress(base64.b64decode((here/"hard7.tar.xz.b64").read_text())))) as tar:
    for name, digest in hashes.items():
        data = tar.extractfile(name).read()
        assert hashlib.sha256(data).hexdigest() == digest, name
        (out/name).write_bytes(data)
