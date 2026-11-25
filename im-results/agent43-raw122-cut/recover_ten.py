#!/usr/bin/env python3
"""Recompose the ten source-checked raw122 F1 cylinders from pinned CI artifacts.
Usage: python recover_ten.py ARTIFACT_DIRECTORY WORK_DIRECTORY
Requires Lean 4.36.0-rc2 on PATH; artifact ZIPs named github-actions-artifact-ID.zip.
"""
from pathlib import Path
import os
import subprocess
import sys
import zipfile

IDS = (3, 6, 7, 8, 9, 10, 15, 19, 21, 22)
ROOT = 15012128172
SOURCE = 15043765926
SHARDS = (
    15014140359, 15013281090, 15014370771, 15014000823,
    15012859158, 15014041207, 15013293367, 15014141313,
    15012829167, 15013393876, 15013229121, 15013228724,
    15015286011, 15013909733, 15014903049, 15014019773,
)

def main():
    artifacts, work = map(lambda x: Path(x).resolve(), sys.argv[1:])
    work.mkdir(parents=True, exist_ok=True)
    def archive(i):
        return zipfile.ZipFile(artifacts / f"github-actions-artifact-{i}.zip")
    for i in (ROOT, *SHARDS):
        with archive(i) as z:
            for item in z.infolist():
                name = Path(item.filename).name
                if not name.endswith(".olean"):
                    continue
                if name == "Raw122Data.olean" or name.startswith("Raw122Branch"):
                    continue
                data = z.read(item)
                dst = work / name
                if dst.exists() and dst.read_bytes() != data:
                    raise ValueError(f"conflicting object {name}, artifact {i}")
                dst.write_bytes(data)
    with archive(SOURCE) as z:
        for i in IDS:
            name = f"Raw122Branch{i:02}.lean"
            entries = [x for x in z.namelist() if Path(x).name == name]
            assert len(entries) == 1, name
            (work / name).write_bytes(z.read(entries[0]))
    env = dict(os.environ, LEAN_PATH=str(work))
    for i in IDS:
        name = f"Raw122Branch{i:02}"
        subprocess.run(["lean", "-o", name+".olean", name+".lean"], cwd=work, env=env, check=True)
    name = "Raw122RecoveredTen"
    (work / (name+".lean")).write_bytes(Path(__file__).with_name(name+".lean").read_bytes())
    result = subprocess.run(["lean", "-o", name+".olean", name+".lean"], cwd=work, env=env, check=True, text=True, capture_output=True)
    print(result.stdout, end="")
    assert "sorryAx" not in result.stdout and "Lean.ofReduceBool" not in result.stdout
    assert "BB6.Agent43Raw122Recovered.sound" in result.stdout

if __name__ == "__main__":
    main()
