#!/usr/bin/env python3
"""Discover (not yet prove) affine AutoPump invariants in unclosed Raw41 leaves."""
import argparse,json,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/"im-results/agent46-raw13-cut"))
from autoword import infer,Word
SKIP={21,24,49,54,55,81,83,84,88,90,92,99,101,116,123,125,128,134}
def word(w:Word):
 return w.pre if not w.block else [w.pre,w.block,word(w.post)]
def fixture(table,limit,budget):
 x=infer(table.replace("_",""),limit=limit,budget=budget)
 if not x or x[0]=="hole":return None
 entry,f,(inc,path,(a,b)),end=x
 ops=[]
 for _,_,info in path:
  if info is None:
   if ops and isinstance(ops[-1],int):ops[-1]+=1
   else:ops.append(1)
  else:
   d,lp,rp,I,O,k,L,R=info
   if d=="L":lp,rp,L,R=rp,lp,R,L
   ops.append([d,lp,rp,I,O,word(L),word(R),k])
 return {"table":table,"entry":entry,"family":[f.q,word(f.l),word(f.r)],
  "inc":inc,"ops":ops,"a":a,"b":b}
def main():
 p=argparse.ArgumentParser()
 p.add_argument("--batch",type=Path,required=True)
 p.add_argument("--out",type=Path,required=True)
 p.add_argument("--seconds",type=int,default=3)
 p.add_argument("--limit",type=int,default=20000)
 a=p.parse_args()
 obj=json.loads(a.batch.read_text());found=[];failed=[];n=0
 for row in obj["rows"]:
  idx=row["canonical_index"]
  if idx in SKIP:continue
  for m in row["missing"]:
   leaf=m["leaf"];table=m["table"];st=time.monotonic();n+=1
   try:
    v=fixture(table,a.limit,a.seconds)
    if v:
     found.append({"child":idx,"leaf":leaf,"fixture":v})
     print(f"AUTO_CANDIDATE child{idx} leaf{leaf} entry{v['entry']} cost{v['a']}n+{v['b']}",flush=True)
    else:failed.append({"child":idx,"leaf":leaf,"seconds":time.monotonic()-st})
   except Exception as ex:failed.append({"child":idx,"leaf":leaf,"exception":repr(ex)})
 out={"proof_status":"untrusted AutoPump candidates","source_run":46080134973,
  "shard":obj["shard"],"studied":n,"successes":found,"failures":failed}
 a.out.parent.mkdir(parents=True,exist_ok=True)
 a.out.write_text(json.dumps(out,indent=2)+"\n")
 groups={}
 for x in found:groups.setdefault(x["child"],[]).append(x["leaf"])
 print("SUMMARY",json.dumps({"shard":obj["shard"],"studied":n,"found":len(found),"by_child":groups}),flush=True)
if __name__=="__main__":main()
