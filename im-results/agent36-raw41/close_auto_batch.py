#!/usr/bin/env python3
"""Reconstruct exact source Lean proof from independently inferred AutoPump set."""
import argparse,json,subprocess,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
def main():
 p=argparse.ArgumentParser()
 p.add_argument("--batch",type=Path,required=True)
 p.add_argument("--index",type=int,required=True)
 p.add_argument("--out",type=Path,required=True)
 a=p.parse_args()
 a.out.mkdir(parents=True,exist_ok=True)
 batch=json.loads(a.batch.read_text())
 objs=[r for r in batch["successes"] if r["child"]==a.index]
 assert objs,len(batch["successes"])
 args=[sys.executable,str(HERE/"close_candidate.py"),"--index",str(a.index),
       "--dfa","5","--time","900","--out",str(a.out)]
 folder=a.out/"fixtures";folder.mkdir(exist_ok=True)
 for x in sorted(objs,key=lambda x:x["leaf"]):
  fn=folder/f'leaf{x["leaf"]}.json'
  fn.write_text(json.dumps({"leaf":x["leaf"],"found":True,
         "fixture":x["fixture"]},indent=2)+"\n")
  args+=["--auto-json",str(fn)]
 print("FAMILY",a.index,"SUBMITTED AUTO LEAVES",[x["leaf"] for x in objs],flush=True)
 subprocess.run(args,check=True)
 summary=json.loads((a.out/"summary.json").read_text())
 print("SUMMARY",json.dumps(summary),flush=True)
 assert summary["remaining_after_auto"]==0,summary
if __name__=="__main__":main()
