"""Materialize exact locally accepted Lean sweep proof sources."""
import argparse
import base64
import hashlib
import json
import lzma
from pathlib import Path

ROOT = Path(__file__).resolve().parent
EXPECTED = {
    "Raw391LEDFour.lean": "7aedf8648d5d889e518144d11838558b8d936af80b1b171f09fbeac5a0833415",
    "Raw391LEFMore.lean": "2752d2a3abfb84f9e5ed69a0f6036e77e37212205434bdcbb016d0b2213a6a35",
}

def unpack(output: Path):
    raw = lzma.decompress(base64.b64decode((ROOT / "Raw391LESweeps.json.xz.b64").read_text()))
    assert hashlib.sha256(raw).hexdigest() == "f45861cd014719b3e91d5ba54d4393b8f89c4b65d63a55785f2e91f33227b3ef"
    data = json.loads(raw)
    assert set(data) == set(EXPECTED)
    output.mkdir(parents=True, exist_ok=True)
    for name, source in data.items():
        b = source.encode("utf-8")
        assert hashlib.sha256(b).hexdigest() == EXPECTED[name]
        (output / name).write_bytes(b)
    return [Path(name).stem for name in EXPECTED]

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    print("\n".join(unpack(args.output)))
