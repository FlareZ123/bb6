"""Partition the original generated proof by first move and witness imports."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent
REPO=ROOT.parents[1]
PLAN={
 "la0-a":list(range(6)), "la0-b":list(range(6,12)),
 "la0-c":list(range(12,18)), "la0-d":list(range(18,24)),
 "lb0-a":[0,1,2,3,4,5,7,8,9,10,13,15,19,21,22],
 "lb0-b":[6], "lb0-c":[11], "lb0-d":[12,14,16,17,20],
 "lb0-e":[18], "lb0-f":[23],
}
for c in ("la0","lb0"):
 assert sorted(i for g,ids in PLAN.items() if g.startswith(c+"-") for i in ids)==list(range(24))
def prefix(g): return "Raw108B0L"+g[1].upper()
IMPORT=re.compile(r"^import (\w+)[ \t]*$",re.M)
NS=re.compile(r"^namespace ([\w.]+)[ \t]*$",re.M)
PROVEN=re.compile(r"\.proven\s+([\w.]+)\.table\s+\1\.never")
def run(path,*args):
 subprocess.run([sys.executable,str(REPO/path),*map(str,args)],cwd=REPO,check=True)
def isolate(pre,root=ROOT):
 base=root/(pre+"Base.lean")
 s=base.read_text()
 imports=IMPORT.findall(s)
 assert imports and imports[0] in ("ZipThreeHoleAudit","Raw108LongAudit"),imports
 providers={}
 def add(ns,mod): providers.setdefault(ns,set()).add(mod)
 for mod in imports[1:]:
  content=(root/(mod+".lean")).read_text()
  if mod.startswith("Raw108Auto"):
   for shard in IMPORT.findall(content):
    names=NS.findall((root/(shard+".lean")).read_text())
    assert names and names[0]=="BB6.Agent10"+mod,(shard,names)
    for ns in names[1:]:
     assert re.fullmatch(r"M\d+",ns),(shard,ns)
     add(names[0]+"."+ns,shard)
  else:
   for ns in NS.findall(content): add(ns,mod)
 base.write_text(IMPORT.sub(lambda m:m[0] if m[1]==imports[0] else "",s))
 for i in range(24):
  p=root/f"{pre}Kid{i:02}.lean"
  s=p.read_text()
  names=PROVEN.findall(s)
  assert len(names)==s.count(".proven "),(p,len(names))
  needed=set()
  for ns in names:
   choices=providers.get(ns,set())
   assert len(choices)==1,(p,ns,choices)
   needed.update(choices)
  assert IMPORT.findall(s)==[pre+"Base"]
  p.write_text("".join("import "+m+"\n" for m in sorted(needed))+s)
  print(p.name,len(needed),"witness imports")
def prepare(g,out):
 pre=prefix(g)
 out.mkdir(parents=True,exist_ok=False)
 # The original generator and common generators have already run.
 isolate(pre)
 run("im-results/agent10-tnf-multipump/chunk_checks.py",ROOT,pre,"--limit",180)
 mods=[f"{pre}Kid{i:02}" for i in PLAN[g]]
 for i,m in zip(PLAN[g],mods):
  with (ROOT/(m+".lean")).open("a") as f:
   f.write(f"\n#print axioms BB6.Agent10{pre}.check{i:02}\n")
 (out/"roots.txt").write_text("".join(str((ROOT/(m+".lean")).relative_to(REPO))+"\n" for m in mods))
 (out/"theorems.txt").write_text("".join(f"BB6.Agent10{pre}.check{i:02}\n" for i in PLAN[g]))
 data=pre+"Data.lean"
 (out/data).write_bytes((ROOT/data).read_bytes())
def composition_config(pins):
 c=json.loads((ROOT/"shard_groups.json").read_text())
 for child in ("la0","lb0"):
  if child not in pins:
   del c["groups"][child]
   for g,ids in PLAN.items():
    if g.startswith(child+"-"): c["groups"][g]=[f"{prefix(g)}Kid{i:02}" for i in ids]
 assert set(pins)==set(c["groups"]),(set(pins),set(c["groups"]))
 return c
def restore(downloads,config):
 groups=config["groups"]
 for child in ("la0","lb0"):
  if child in groups: continue
  split=[g for g in groups if g.startswith(child+"-")]
  assert split
  data=prefix(split[0])+"Data.lean"
  copies=[(downloads/(config["artifact_prefix"]+"-"+g)/data).read_bytes() for g in split]
  assert all(s==copies[0] for s in copies),data
  (ROOT/data).write_bytes(copies[0])
 required={}
 for g in groups:
  m=json.loads((downloads/(config["artifact_prefix"]+"-"+g)/"manifest.json").read_text())
  for item in m["modules"]:
   if item["module"] in {"BlockMacro2","BlockFAR2","RangeCheck2"}:
    path=item["source_path"]
    assert path=="im-results/agent13-block-far/"+item["module"]+".lean",path
    required.setdefault(path,set()).add(item["source_sha256"])
 assert all(len(h)==1 for h in required.values()),required
 def matches():
  return all(hashlib.sha256((REPO/p).read_bytes()).hexdigest() in h for p,h in required.items())
 if not matches(): run("im-results/agent13-block-far/specialize.py",2)
 assert matches(),required
if __name__=="__main__":
 op,*args=sys.argv[1:]
 if op=="prepare": prepare(args[0],Path(args[1]))
 elif op=="restore": restore(Path(args[0]),json.loads(Path(args[1]).read_text()))
 else: raise ValueError(op)
