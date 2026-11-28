"""Split a generated Raw36 canonical kid audit into disjoint top-level branch modules.

The transformation is deliberately untrusted: Lean recompiles every emitted branch
and the final wrapper. We require the generated part-declaration graph to partition
exactly under the 24 children referenced by the root kid audit.
"""
import argparse
import re
from pathlib import Path

PART_DEF = r"^def ({root}_part\d+)\s*:"

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--source", type=Path, required=True)
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--root", required=True)
    ap.add_argument("--module", required=True)
    a = ap.parse_args()

    text = a.source.read_text()
    pat = PART_DEF.format(root=re.escape(a.root))
    first = re.search(pat, text, re.M)
    assert first, "no part declarations"
    root_match = re.search(rf"^def {re.escape(a.root)}\s*:.*$", text, re.M)
    assert root_match and root_match.start() > first.start(), "root declaration missing/misordered"
    root_pos = root_match.start()
    header = text[:first.start()]
    tail = text[root_pos:]

    starts = [(m.start(), m.group(1)) for m in re.finditer(pat, text, re.M)]
    blocks = {}
    order = []
    for i, (pos, name) in enumerate(starts):
        end = starts[i + 1][0] if i + 1 < len(starts) else root_pos
        blocks[name] = text[pos:end]
        order.append(name)
    refs = {
        name: set(re.findall(rf"\b({re.escape(a.root)}_part\d+)\b", block)) - {name}
        for name, block in blocks.items()
    }

    rm = re.search(rf"def {re.escape(a.root)}\s*:.*?byMove \[([^\]]+)\]", tail, re.S)
    assert rm, "root byMove list not found"
    roots = [x.strip() for x in rm.group(1).split(",")]
    assert len(roots) == 24, roots
    assert all(re.fullmatch(rf"{re.escape(a.root)}_part\d+", x) for x in roots), roots

    def closure(name):
        seen = set()
        todo = [name]
        while todo:
            x = todo.pop()
            assert x in blocks, x
            if x in seen:
                continue
            seen.add(x)
            todo.extend(refs[x])
        return seen

    closures = [closure(x) for x in roots]
    union = set().union(*closures)
    assert union == set(blocks), (len(union), len(blocks), sorted(set(blocks) - union)[:5])
    for i in range(len(closures)):
        for j in range(i):
            assert not closures[i] & closures[j], (i, j, sorted(closures[i] & closures[j])[:5])

    namespaces = re.findall(r"^namespace ([A-Za-z0-9_.]+)$", header, re.M)
    assert len(namespaces) == 1, namespaces
    namespace = namespaces[0]
    nonimports = "\n".join(line for line in header.splitlines() if not line.startswith("import ")) + "\n"

    a.out.mkdir(parents=True, exist_ok=True)
    modules = []
    rows = []
    for i, (top, cl) in enumerate(zip(roots, closures)):
        module = f"{a.module}Branch{i:02d}"
        body = "".join(blocks[name] for name in order if name in cl)
        (a.out / f"{module}.lean").write_text(header + body + f"\nend {namespace}\n")
        modules.append(module)
        rows.append((i, top, len(cl), body.count("\n")))

    wrapper = "".join(f"import {module}\n" for module in modules) + nonimports + tail
    (a.out / f"{a.module}.lean").write_text(wrapper)
    print(f"split {a.module}: parts={len(blocks)} branches={len(modules)} wrapper_lines={wrapper.count(chr(10))}")
    for row in rows:
        print(*row)

if __name__ == "__main__":
    main()
