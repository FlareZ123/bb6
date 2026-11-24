"""Restore the exact checked terminal-extension research sources."""
import base64
import hashlib
import io
from pathlib import Path
import tarfile

root = Path(__file__).resolve().parent
raw = base64.b64decode((root / "terminal-extension.tar.xz.b64").read_text().strip(), validate=True)
assert hashlib.sha256(raw).hexdigest() == "883c39767fc8daa87ec748d9abe581ef01259a4cd1163718cec34015c69896c5"
expected = {
    "SheepTerminalInverse.lean": "db833a1192f0439c823c016e023aaf63d4bed89795fb64343180ef307b415f06",
    "terminal_extension.py": "b5683620bada833fa8fffa5dd0f45a8ecdc2e4de1d019a7ae622d0fb4f15e3c7",
    "replay.txt": "d361a8d6662ff87ac843af5900c8c20efa1480807ab8ba69fd8ca599cddbf6c7",
}
with tarfile.open(fileobj=io.BytesIO(raw), mode="r:xz") as archive:
    assert sorted(archive.getnames()) == sorted(expected)
    for name, digest in expected.items():
        member = archive.getmember(name)
        assert member.isfile()
        data = archive.extractfile(member).read()
        assert hashlib.sha256(data).hexdigest() == digest
        (root / name).write_bytes(data)
        print(name, digest)
