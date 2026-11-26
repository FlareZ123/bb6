"""Retain deterministic disjoint Raw113 root groups without changing any audit."""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
CONFIG = json.loads((ROOT / "shard_groups.json").read_text())
GEN = ROOT / "generated"
GROUPS = CONFIG["groups"]
assert sorted(m for group in GROUPS.values() for m in group) == [
    f"Raw113Shard_root_{i:02}" for i in range(24)
]
ASSEMBLERS = ["Raw113Shard_root.lean", "Raw113Data.lean"]

def prepare():
    for modules in GROUPS.values():
        for module in modules:
            path = GEN / (module + ".lean")
            theorem = module.removeprefix("Raw113Shard_")
            with path.open("a") as f:
                f.write(f"\n#print axioms BB6.Agent25Raw113.c_{theorem}\n")
    for name in ASSEMBLERS:
        assert (GEN / name).is_file(), name

def select(group, output):
    output.mkdir(parents=True, exist_ok=True)
    modules = GROUPS[group]
    (output / "roots.txt").write_text("".join(str(GEN / (m + ".lean")) + "\n" for m in modules))
    (output / "theorems.txt").write_text("".join("BB6.Agent25Raw113.c_" + m.removeprefix("Raw113Shard_") + "\n" for m in modules))
    for name in ASSEMBLERS:
        (output / name).write_bytes((GEN / name).read_bytes())

def restore(downloads):
    GEN.mkdir(parents=True, exist_ok=True)
    for name in ASSEMBLERS:
        copies = [(downloads / (CONFIG["artifact_prefix"] + "-" + group) / name).read_bytes() for group in GROUPS]
        assert all(x == copies[0] for x in copies), name
        (GEN / name).write_bytes(copies[0])

if __name__ == "__main__":
    op, *args = sys.argv[1:]
    if op == "prepare":
        prepare()
    elif op == "select":
        select(args[0], Path(args[1]))
    elif op == "restore":
        restore(Path(args[0]))
    else:
        raise ValueError(op)
