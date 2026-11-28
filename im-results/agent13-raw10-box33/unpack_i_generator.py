from pathlib import Path
import base64, hashlib, lzma

HERE = Path(__file__).resolve().parent
ARCHIVE = HERE / "generate_i_relays.py.xz.b64"
DEST = HERE / "generate_i_relays.py"
EXPECTED = "e936ff293159f851a51c2e843d1bd779ce5f368e15529e574b7a8bfd0a07c3c0"

def main():
    data = lzma.decompress(base64.b64decode(ARCHIVE.read_text().strip()))
    got = hashlib.sha256(data).hexdigest()
    if got != EXPECTED:
        raise ValueError(f"Generator SHA256 mismatch: {got}")
    DEST.write_bytes(data)
    print(f"Reconstructed {DEST}, SHA256={got}")

if __name__ == "__main__":
    main()
