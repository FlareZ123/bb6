#!/usr/bin/env python3
"""Regenerate the closed Raw40 Round20 canonical audit."""
import os, pathlib, subprocess, sys
root=pathlib.Path(__file__).resolve().parent
out=root/"round20"/"shards-input"
out.mkdir(parents=True,exist_ok=True)
p="1RB1RC_1RC---_0RD1LB_1LD1LA_------_------"
for f in ("enumerate_canon","farbank"):
    subprocess.run(["g++","-O3","-std=c++20",str(root/(f+".cpp")),"-o",str(out/f)],check=True)
with (out/"stats.txt").open("w") as log:
    subprocess.run([str(out/"enumerate_canon"),p],cwd=out,stdout=log,check=True)
opens=(out/"open.txt").read_text().splitlines()
assert len(opens)==81
with (out/"far5.txt").open("w") as log,(out/"far.log").open("w") as err:
    subprocess.run([str(out/"farbank"),"5"],input="".join(f"{i} {s.replace('_','')}\n" for i,s in enumerate(opens)),text=True,cwd=out,stdout=log,stderr=err,check=True)
ids={int(x.split()[0]) for x in (out/"far5.txt").read_text().splitlines()}
assert ids==set(range(81))-{68,75}
assert opens[68]=="1RB1RC_1RC1RE_0RD1LB_1LD1LA_1LF0RF_---0LB"
(out/"far_extra.txt").write_text("75 1012343514441\n")
(out/"proven.txt").write_text(opens[68]+" BB6.Agent19Raw40.OneRC1LB\n")
src=(root/"certify_canonical.py").read_text()
anchor="if any('Counter17' in v for v in proven.values()):imports+='import Raw40Counter17\\n'"
assert anchor in src
src=src.replace(anchor,anchor+"\nimports+='import Raw40MoreTwoSided\\n'")
sys.argv=[str(root/"certify_canonical.py"),str(out),str(out/"shards"),p,"85","Raw40C1RC1LB","96"]
os.environ["RAW40_STANDALONE"]="1"
exec(compile(src,sys.argv[0],"exec"),{"__file__":sys.argv[0],"__name__":"__main__"})
