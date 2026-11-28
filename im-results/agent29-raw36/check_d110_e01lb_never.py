#!/usr/bin/env python3
"""Independently kernel-check the FIRST certificate for hard Raw36 E0=1LB.

A deterministic targeted search (source run 46155586176) discovered finite
inverse-stack rule ('r', k=6, c=9, m=5) with exact 1318 reachable abstract
configurations. Replay and source emission rederive the certificate from
only the original literal table; Lean TwoSidedAutomata checks all transition
closure and proves NeverHalts for *every* completion. There are no axioms
about the certificate, simulations or behavior of this machine.
"""
import argparse,hashlib,json,os,re,subprocess,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
REPO=HERE.parents[1]
sys.path.insert(0,str(HERE))
sys.path.insert(0,str(HERE.parent/"agent7-raw36-b1le"))
import compose_accepted as base
from stack_candidates import emit
TARGET="1RB---_1RC1LC_0RD1RF_0LD0RE_1LB1RA_1RE0LF"
NS="BB6.Agent29Raw36D110OneLB"
ALLOWED={"propext","Classical.choice","Quot.sound"}
def main():
    a=argparse.ArgumentParser(description=__doc__)
    a.add_argument("--archives",required=True,type=Path)
    a.add_argument("--work",required=True,type=Path)
    p=a.parse_args()
    work=p.work.resolve()
    p.archives.resolve().mkdir(parents=True,exist_ok=True)
    # Build exact minimal data before consuming any downloads/CI compute.
    raw=TARGET.replace("_","")
    assert len(raw)==36
    source,n,shape=emit(0,raw,["r",6,9,5,1318])
    assert n==1318,n
    generated="\n".join([
       "import TwoSidedAutomata",
       "set_option maxRecDepth 100000",
       "set_option maxHeartbeats 0",
       "namespace "+NS,
       "open BB6Coverage",
       source,
       "end "+NS,
       ""])
    staging=work.with_name(work.name+"-inputs")
    staging.mkdir(parents=True,exist_ok=False)
    payload=staging/"Raw36D110E01LB.lean"
    payload.write_text(generated)
    subprocess.run([sys.executable,str(HERE/"compose_accepted.py"),
        "--inputs",str(p.archives.resolve()),"--work",str(work),"--download"],check=True)
    parent=json.loads((work/"manifest.json").read_text())
    assert parent["claim"]["theorem"]=="BB6.Agent29Raw36.parent_cover_from_nine"
    target=work/"Raw36D110E01LB.lean"
    target.write_bytes(payload.read_bytes())
    env=dict(os.environ,LEAN_PATH=str(work))
    result=subprocess.run(["lean","-o","Raw36D110E01LB.olean",target.name],
       cwd=work,env=env,text=True,capture_output=True)
    (work/"d110-e01lb-source.log").write_text(result.stdout+"\n"+result.stderr)
    print(result.stdout[-24000:],flush=True)
    if result.returncode:
        print(result.stderr[-24000:],file=sys.stderr,flush=True)
        raise RuntimeError("Lean rejected the candidate regular-stack proof")
    assert "sorryAx" not in result.stdout+result.stderr and "native_decide" not in result.stdout
    observed=dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",result.stdout))
    observed.update({x:"" for x in re.findall(
       r"'([^']+)' does not depend on any axioms",result.stdout)})
    expected=NS+".M0.never"
    assert expected in observed,observed
    assert all(set(s.strip() for s in ax.split(",") if s.strip())<=ALLOWED
               for ax in observed.values()),observed
    receipt={
      "status":"original-source accepted NeverHalts for hard D1=0RE E0=1LB literal",
      "source_revision":subprocess.check_output(
         ["git","rev-parse","HEAD"],cwd=REPO,text=True).strip(),
      "source_literal":TARGET,
      "source_literal_sha256":hashlib.sha256(TARGET.encode()).hexdigest(),
      "certificate_kind":"r","parameters":{"k":6,"c":9,"m":5,"reachable":1318},
      "abstract_stack_shape":list(shape),
      "theorem":expected,"axioms":observed,
      "source_sha256":base.file_sha(target),
      "root_olean_sha256":base.file_sha(work/"Raw36D110E01LB.olean"),
      "dependent_accepted_parent":parent["claim"],
      "note":"This source theorem NeverHalts applies to every ordinary complete extension of the literal parent"}
    (work/"d110-e01lb-never-accepted.json").write_text(
       json.dumps(receipt,indent=2,sort_keys=True)+"\n")
    print("PASS: Lean kernel rechecked entire 1318-node finite "
          "inverse-stack certificate for hard D110 E0=1LB",flush=True)

if __name__=="__main__":main()
