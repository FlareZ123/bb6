#!/usr/bin/env python3
"""Regenerate the complete Round6 or Round7 canonical proof."""
import json, os, pathlib, subprocess, sys
root = pathlib.Path(__file__).resolve().parent
roundno = int(sys.argv[1])
p, B, mod, nopen, nfar, npumps = {
    6: ("1RB0LA_1RC---_0RD1RC_1LD1LA_------_------",1766,"Raw40C0LA1RC",171,146,23),
    7: ("1RB0LB_1RC1RB_0RD---_1LD1LA_------_------",119,"Raw40C0LB1RB",594,570,7),
}[roundno]
out = root / f"round{roundno}" / "shards-input"
out.mkdir(parents=True, exist_ok=True)
def run(args, **kw):
    return subprocess.run(args, check=True, **kw)
for f in ("enumerate_canon","farbank"):
    run(["g++","-O3","-std=c++20",str(root/(f+".cpp")),"-o",str(out/f)])
with (out/"stats.txt").open("w") as log:
    run([str(out/"enumerate_canon"),p],cwd=out,stdout=log)
opens=(out/"open.txt").read_text().splitlines()
assert len(opens)==nopen
pumps={int(row[0]):row for row in map(json.loads,(root/f"round{roundno}-pumps.jsonl").read_text().splitlines())}
assert len(pumps)==npumps
for i,row in pumps.items(): assert opens[i].replace("_","")==row[1]
with (out/"far5.txt").open("w") as log,(out/"far.log").open("w") as err:
    run([str(out/"farbank"),"5"],input="".join(f"{i} {s.replace('_','')}\n" for i,s in enumerate(opens)),text=True,cwd=out,stdout=log,stderr=err)
far_ids={int(x.split()[0]) for x in (out/"far5.txt").read_text().splitlines()}
assert len(far_ids)==nfar
extra=json.loads((root/"round67-extras.json").read_text())[f"round{roundno}"]
late=extra.get("late",[]);other=extra.get("proven",[]);far=extra.get("far",[])
late_ids={opens.index(x.split()[0]) for x in late}
other_ids={opens.index(x.split()[0]) for x in other}
extra_ids={x[0] for x in far}
groups=[far_ids,late_ids,other_ids,extra_ids,set(pumps)]
assert sum(map(len,groups))==nopen and set.union(*groups)==set(range(nopen))
(out/"late.txt").write_text("".join(x+"\n" for x in late))
(out/"far_extra.txt").write_text("".join(f"{i} {s}\n" for i,s in far))
ns=f"BB6.Agent19Raw40.Round{roundno}"
(out/"proven.txt").write_text("".join(f"{opens[i]} {ns}.Leaf{i}\n" for i in sorted(pumps))+"".join(x+"\n" for x in other))
pumpmod=f"Raw40Round{roundno}Pump"
with (root/(pumpmod+".lean")).open("w") as f:
    run([sys.executable,str(root/"emit_autopump.py"),str(root/f"round{roundno}-pumps.jsonl"),ns],stdout=f)
src=(root/"certify_canonical.py").read_text()
anchor="if any('Counter17' in v for v in proven.values()):imports+='import Raw40Counter17\\n'"
assert anchor in src
src=src.replace(anchor,anchor+f"\nimports+='import {pumpmod}\\n'\n"+("imports+='import Raw40BinaryPair\\n'\n" if roundno==7 else ""))
sys.argv=[str(root/"certify_canonical.py"),str(out),str(out/"shards"),p,str(B),mod,"96"]
os.environ["RAW40_STANDALONE"]="1"
exec(compile(src,sys.argv[0],"exec"),{"__file__":sys.argv[0],"__name__":"__main__"})
