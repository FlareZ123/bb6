#!/usr/bin/env python3
"""Reproduce the Round8/9 candidate audits from compressed witness data.
Generated Lean proofs, not the search process, establish acceptance."""
import base64, gzip, hashlib, json, os, pathlib, subprocess, sys
root = pathlib.Path(__file__).resolve().parent
roundno=int(sys.argv[1])
p,B,mod,nopen,nfar,npumps={
    8: ("1RB0LA_1RC---_0RD0RB_1LD1LA_------_------",1213,"Raw40C0LA0RB",415,373,34),
    9: ("1RB0LB_1RC0RE_0RD---_1LD1LA_------_------",408,"Raw40C0LB0RE",1571,1495,47),
}[roundno]
raw=gzip.decompress(base64.b64decode((root/"round89-witnesses.json.gz.b64").read_text()))
assert hashlib.sha256(raw).hexdigest()=="50485a3685fd33d020e4003c8ef2b21a2706e495112995b59aed6a1f5c5aae17"
data=json.loads(raw)[str(roundno)]
out=root/f"round{roundno}"/"shards-input"
out.mkdir(parents=True,exist_ok=True)
def run(args,**kw): return subprocess.run(args,check=True,**kw)
for f in ("enumerate_canon","farbank"):
    run(["g++","-O3","-std=c++20",str(root/(f+".cpp")),"-o",str(out/f)])
with (out/"stats.txt").open("w") as log:
    run([str(out/"enumerate_canon"),p],cwd=out,stdout=log)
opens=(out/"open.txt").read_text().splitlines()
assert len(opens)==nopen
for n,s in data.items(): (out/n).write_text(s)
pumps={int(row[0]):row for row in map(json.loads,data["pumps.jsonl"].splitlines())}
assert len(pumps)==npumps
for i,row in pumps.items(): assert opens[i].replace("_","")==row[1]
with (out/"far5.txt").open("w") as log,(out/"far.log").open("w") as err:
    run([str(out/"farbank"),"5"],input="".join(f"{i} {s.replace('_','')}\n" for i,s in enumerate(opens)),text=True,cwd=out,stdout=log,stderr=err)
far_ids={int(x.split()[0]) for x in (out/"far5.txt").read_text().splitlines()}
assert len(far_ids)==nfar
extra_ids={int(x.split()[0]) for x in data["far_extra.txt"].splitlines()}
late_ids={opens.index(x.split()[0]) for x in data["late.txt"].splitlines()}
groups=[far_ids,extra_ids,late_ids,set(pumps)]
assert sum(map(len,groups))==nopen and set.union(*groups)==set(range(nopen))
ns=f"BB6.Agent19Raw40.Round{roundno}"
(out/"proven.txt").write_text("".join(f"{opens[i]} {ns}.Leaf{i}\n" for i in sorted(pumps)))
pumpmod=f"Raw40Round{roundno}Pump"
with (root/(pumpmod+".lean")).open("w") as f:
    run([sys.executable,str(root/"emit_autopump.py"),str(out/"pumps.jsonl"),ns],stdout=f)
src=(root/"certify_canonical.py").read_text()
anchor="if any('Counter17' in v for v in proven.values()):imports+='import Raw40Counter17\\n'"
assert anchor in src
src=src.replace(anchor,anchor+f"\nimports+='import {pumpmod}\\n'")
sys.argv=[str(root/"certify_canonical.py"),str(out),str(out/"shards"),p,str(B),mod,"96"]
os.environ["RAW40_STANDALONE"]="1"
exec(compile(src,sys.argv[0],"exec"),{"__file__":sys.argv[0],"__name__":"__main__"})
