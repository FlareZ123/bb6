"""Generate 1LF without changing the SHA-pinned older nine-child generator."""
import json
from pathlib import Path
import generate_1lf_long
import generate

def main():
    generate_1lf_long.main()
    generate.SPECS["1LF"] = json.loads(Path(__file__).with_name("spec-1LF.json").read_text())
    generate.main("1LF")

if __name__ == "__main__":
    main()
