"""Report exact open Raw41 survey leaves after restoring the pinned evidence archive."""
import base64, gzip, hashlib, json, sys
from pathlib import Path

root = Path(__file__).resolve().parent
payload = gzip.decompress(base64.b64decode((root / "survey-evidence.json.gz.b64").read_text()))
assert hashlib.sha256(payload).hexdigest() == "fbc96884c0daf2ff5410c86379ff102010476d7ebec48e309107345ba80c4c24"
data = json.loads(payload)

known_manual = {
    "Raw41LC0LB": {29},
    "Raw41LB0LC": {3, 34, 42},
    "Raw41LC0RA": {0, 1, 2},
    "Raw41LC1LB": {1, 2, 7},
}

def read_indices(path, parse):
    if not path.exists():
        return set()
    return {parse(line) for line in path.read_text().splitlines() if line.strip()}

for arg in sys.argv[1:]:
    key = arg.zfill(3)
    d = data[key]
    folder = root / "survey" / key
    opens = (folder / "open.txt").read_text().splitlines()
    far = read_indices(folder / "far.txt", lambda line: int(line.split()[0]))
    late = read_indices(folder / "late.txt", lambda line: int(line.split()[0]))
    proven_path = folder / "proven.json"
    proven = set(json.loads(proven_path.read_text()).keys()) if proven_path.exists() else set()
    auto_path = folder / "auto.jsonl"
    auto = set()
    if auto_path.exists():
        for line in auto_path.read_text().splitlines():
            if line.strip():
                row = json.loads(line)
                auto.add(int(row[0] if isinstance(row, list) else row.get("index", row.get("i"))))
    known = far | late | {int(i) for i in proven} | auto | known_manual.get(d["name"], set())
    missing = [i for i in range(len(opens)) if i not in known]
    print(f"\n{key} {d['name']} bound={d['bound']} table={d['table']}")
    print(f"open={len(opens)} far={len(far)} late={len(late)} proven={len(proven)} auto={len(auto)} missing={len(missing)}")
    for i in missing:
        print(f"MISSING\t{i}\t{opens[i]}")
