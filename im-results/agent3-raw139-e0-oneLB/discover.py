"""Exact C1=0LC subcover of Raw139 E0=1LB. Witness discovery is untrusted."""
import json, pathlib, sys
from collections import defaultdict
from blockcert import generate
from package6 import first_hole

HERE = pathlib.Path(__file__).resolve().parent
data = json.loads((HERE / "recipes.json").read_text())
part = json.loads(pathlib.Path(sys.argv[1]).read_text())
assert part["counts"] == data["expected"], part["counts"]
assert part["tree"][:3] == ["split",12,6], part["tree"][:3]
assert len({tuple(t) for t in part["open"]}) == len(part["open"])
assert 1 + 23*part["counts"]["split"] == sum(part["counts"][k] for k in ("cycle","last","far","open"))
lookup = {tuple(e["table"]):e for e in data["recipes"]}
groups, late = defaultdict(list), {}
for i, table in enumerate(part["open"]):
    row = lookup[tuple(table)]
    if "last" in row:
        n,s = row["last"]
        assert table.count(24) == 1 and first_hole(table,n) == ("hole",n,s)
        late[i] = [n,s]
    else:
        p = row["block"]
        assert p[0] in (2,3) and not p[4]
        assert generate(table,*p[:-1],phase=p[-1]) is not None, (i,table,p)
        groups[tuple(p)].append(i)
assert sum(map(len,groups.values())) == 27 and len(late) == 1
spec = dict(parent=data["parent"],counts=part["counts"],limit=450,maxd=2,bound=574,
    namespace="BB6.Agent3E0OneLBC1ZeroLC",prefix="Raw139E0OneLBC1ZeroLC",
    external_imports=[],block_groups=[[p,ids] for p,ids in sorted(groups.items())],
    late=late,proven={},max_module_leaves=350,independent_root_children=True)
pathlib.Path(sys.argv[2]).write_text(json.dumps(spec,separators=(",",":"))+"\n")
print("complete exact partition:",part["counts"],"27 block invariants + late query",late)
