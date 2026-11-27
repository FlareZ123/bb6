#!/usr/bin/env python3
"""Regenerate the exact Raw56 E1=0RC/C1=1RD kernel certificate."""
import hashlib
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PARENT = "1RB---_1RC---_0RD1RD_1LD1LE_---0RC_------"

def sha(path, expected):
    assert hashlib.sha256(path.read_bytes()).hexdigest() == expected, path

def blob(path, expected):
    data = path.read_bytes()
    assert hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest() == expected, path

def main():
    out = Path(sys.argv[1]).resolve()
    out.mkdir(parents=True, exist_ok=True)
    cut = ROOT / "im-results/agent7-raw49/cut.cpp"
    far = ROOT / "im-results/agent19-raw40-cut/farbank.cpp"
    blob(cut, "88d5dfc4994f8bd203fe3f3def5ea90efda86037")
    blob(far, "30cac1862b3b88d7ba596b359a9dc8503163593d")
    for name, src in [("cut", cut), ("farbank", far)]:
        subprocess.run(["g++", "-O3", "-std=c++20", str(src), "-o", str(out/name)], check=True)
    stem = out / "RC_RD"
    subprocess.run([str(out/"cut"), PARENT, "1000", "32", "6", str(stem)], check=True)
    tree, opens, witnesses, bank = [stem.with_suffix(s) for s in (".json", ".open", ".far", ".bank")]
    sha(tree, "2d0b27711437dfcb12fa51880cc407085ef29439c62a5a7dc03b8b1518672e86")
    sha(opens, "60c145c7d7f8fc43c434ae0cc07c89f8b86e46ef34469574e3da1ad28b2810c3")
    rows = opens.read_text().splitlines()
    query = "".join(f"{i} {s.replace('_','')}\n" for i,s in enumerate(rows))
    with witnesses.open("wb") as f:
        subprocess.run([str(out/"farbank"), "5"], input=query.encode(), stdout=f, check=True)
    sha(witnesses, "7e14695ec941db0e4a68e5879a8944fc01c2b0a11bfa859500053c196c930df4")
    bank.write_bytes(witnesses.read_bytes() + b"40 1012345214422\n73 1012345214422\n74 1012345214422\n")
    sha(bank, "d5d16cb5c317833bc6d112c3d5315ad7ed5c1ecedfd1d33d4f57d3c176e61aa3")
    subprocess.run([sys.executable, str(HERE/"emit_rc_rd.py"), str(tree), str(opens), str(bank), str(out/"generated")], check=True)

if __name__ == "__main__":
    main()
