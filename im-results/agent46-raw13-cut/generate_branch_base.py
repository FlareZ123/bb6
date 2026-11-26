"""Generate a six-hole parent from its authentic first-hole assignment path."""
from generate import ROOT as RAW_ROOT, scan, move, slot, DECODE
from pathlib import Path

def describe(raw):
    assert len(raw)==36
    target=[raw[i:i+3] if raw[i:i+3]!="---" else None for i in range(0,36,3)]
    p=RAW_ROOT[:];cut=3;steps=[]
    assert all(x is None or x==y for x,y in zip(p,target))
    while p!=target:
        r=scan(p)
        assert r[0]=="hole", (raw,r)
        _,n,s=r
        mv=target[s]
        assert mv is not None and DECODE[mv][2]<=cut, (raw,n,s,mv,cut)
        q=max(cut,DECODE[mv][2]+1)
        steps.append((s,mv,cut,q))
        p[s]=mv;cut=q
    r=scan(p)
    assert r[0]=="hole" and 4<=cut<=6 and p.count(None)==6,(raw,r,cut)
    return steps,r[1],r[2]

def emit_base(raw,module,dest):
    steps,query,qs=describe(raw)
    assert len(steps)==3
    ns="BB6."+module
    lines=["import Agent46Raw13Base","set_option maxRecDepth 100000","set_option maxHeartbeats 0",f"namespace {ns}","open BB6Coverage BB6.Agent13BlankDelay BB6.Agent46CanonicalCut","open BB6.Agent46Raw13"]
    prev="raw13"; hprev="raw13_support"; nh="raw13_nohalt"; proof=[]
    for i,(s,mv,cut,nxt) in enumerate(steps,1):
        name="parent" if i==len(steps) else f"p{i}"
        lines.append(f"def {name} := refine {prev} {slot(s)} (some {move(mv)})")
        expr=f"refine_support {prev} {slot(s)} {move(mv)} {cut} {nxt} {hprev} (by decide) (by decide) (by decide)"
        if i==len(steps):proof.append("  exact "+expr)
        else:proof.append(f"  have h{i} : TNFSupport {name} {nxt} :=\n    "+expr)
        nh=f"(weightedTNFNoAssignedHalt_refine _ _ _ {nh})"
        prev=name;hprev=f"h{i}"
    lines+=[f"theorem parent_support : TNFSupport parent {steps[-1][3]} := by",*proof,
        f"theorem parent_nohalt : weightedTNFNoAssignedHalt parent := {nh}",
        f"def next (mv : Move) := refine parent {slot(qs)} (some mv)",
        """theorem compatible_quotient (m : Machine) (hm : compatible parent m) :
    TNFQuotientCompatible parent m := by
  let e : StatePerm := ⟨id,id,fun _ => rfl,fun _ => rfl⟩
  refine ⟨e,rfl,?_⟩
  have he : renameTable e m = m := by
    funext s
    rcases s with ⟨q,b⟩
    unfold renameTable
    change (m (q,b)).map (renameMove e) = m (q,b)
    cases h : m (q,b) with
    | none => rfl
    | some mv => cases mv <;> rfl
  rw [he]
  exact hm""",f"end {ns}"]
    Path(dest).write_text("\n".join(lines)+"\n",encoding="utf-8")
    return query,qs
