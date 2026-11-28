"""Reconstruct exact late-arrival proofs from frozen miss lists and scan ledger.
All generated claims are checked with ordinary Lean kernel reduction."""
from pathlib import Path
import argparse

def rowdata(code):
    code=code.replace('_','')
    assert len(code)==36
    return [None if code[i:i+3]=='---' else (code[i]=='1',code[i+1]=='R',ord(code[i+2])-65) for i in range(0,36,3)]
def b(v):return str(bool(v)).lower()
def mv(x):return f'⟨{b(x[0])},{b(x[1])},{x[2]}⟩'
def slot(i):return f'({i//2},{b(i%2)})'
def traces(t,n,chunk):
    q=0;l=r='';out=[]
    for i in range(n):
        x=t[2*q+int(l[:1] or '0')];assert x is not None
        w,right,q=x;w=str(int(w))
        if right:l,r=(r[:1] or '0')+w+l[1:],r[1:]
        else:l,r=l[1:],w+r
        if (i+1)%chunk==0 or i+1==n:out.append((i+1,q,l,r))
    assert t[2*q+int(l[:1] or '0')] is None
    return out

def maxdelay(t):
    longest=0
    for q in range(6):
        seen=set();k=0
        while q not in seen:
            if q==0:longest=max(k,longest);break
            seen.add(q);x=t[2*q]
            if x is None or x[0]:break
            q=x[2];k+=1
    return longest

def generate(kind,idx,code,record,outdir,chunk,*,label=None):
    label=label or 'E1'+kind.upper()
    t=rowdata(code);name=f'Raw54{label}Late{idx}';ns=f'BB6.Agent8Raw54.{label}Late{idx}'
    lines=['import Raw54LateBridge','set_option maxRecDepth 100000','set_option maxHeartbeats 0','set_option Elab.async false','set_option autoImplicit false',f'namespace {ns}',
    'open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6Coverage.Agent50Zipper BB6Coverage.Agent31Pump BB6Coverage.Agent10ZipAudit BB6.Agent8Raw54.LateBridge',
    f'-- {code}',f'abbrev parent : PartialMachine := refine BB6.Agent8Raw54.raw54 (4,true) (some {mv(t[9])})',
    'theorem parent_nohalt : weightedTNFNoAssignedHalt parent := weightedTNFNoAssignedHalt_refine _ _ _ (weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 3) firstOneCylinder_no_assigned_halt))']
    previous='parent';refinements=[]
    for i,x in enumerate(t):
        if i in (0,2,4,6,7,9) or x is None:continue
        current=f'p{len(refinements)}';lines.append(f'def {current} : PartialMachine := refine {previous} {slot(i)} (some {mv(x)})');refinements.append((previous,current,i,x));previous=current
    lines += [f'abbrev table : PartialMachine := {previous}','def literalTable : PartialMachine := fun s => match s.1.val,s.2 with']
    lines += [f'  | {i//2},{b(i%2)} => some (some {mv(x)})' for i,x in enumerate(t) if x is not None]
    lines += ['  | _,_ => none','theorem literal_eq : literalTable = table := by','  funext s','  obtain ⟨q,a⟩ := s','  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega','  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl','  all_goals cases a <;> decide']
    if record[0]=='Z':
        e,k,r,boundary=map(int,record[1:]);lines += [f'theorem checked : zipCycle literalTable {e} {k} {b(r)} ({boundary}) = true := by decide',f'theorem never : ∀ m, compatible table m → NeverHalts m := by',f'  rw [← literal_eq]',f'  exact zipCycle_sound literalTable {e} {k} {b(r)} ({boundary}) (by decide) checked','#print axioms never',f'end {ns}'];(outdir/f'{name}.lean').write_text('\n'.join(lines)+'\n');return
    n,hole=map(int,record[1:]);assert t[hole] is None and sum(x is None for x in t)==1
    delay=maxdelay(t);B=n+1+delay
    lines += ['def bits (s : String) : List Bool := s.toList.map (· == \'1\')','def cfg (q : Fin 6) (l r : String) : Z0 := ⟨q,bits l,bits r⟩','def z0 : Z0 := ⟨0,[],[]⟩','theorem accum0 : run0 literalTable 0 z0 = some z0 := rfl']
    p=0;trace=traces(t,n,chunk)
    for j,(s,q,l,r) in enumerate(trace,1):
        lines += [f'def z{j} : Z0 := cfg {q} "{l}" "{r}"',f'theorem seg{j} : run0 literalTable {s-p} z{j-1} = some z{j} := rfl',f'theorem accum{j} : run0 literalTable {s} z0 = some z{j} := join0 (p := literalTable) (n := {p}) (k := {s-p}) (a := z0) (b := z{j-1}) (c := z{j}) accum{j-1} seg{j}'];p=s
    s=slot(hole);j=len(trace)
    lines += [f'theorem literal_query : zipQueryOK {B} literalTable {n} {s} = true :=',f'  query_of_run0 (p := literalTable) (n := {n}) (B := {B}) (z := z{j}) (s := {s}) accum{j} (by decide) (by decide) (by decide)',
    f'theorem query : zipQueryOK {B} table {n} {s} = true := literal_eq ▸ literal_query',f'theorem rest : restOK table {s} = true := by decide',f'theorem checked : zipCheck {B} table (.last {n} {s}) = true := by',f'  change (zipQueryOK {B} table {n} {s} && restOK table {s}) = true','  rw [query,rest]; rfl','theorem root_ok : table initialSlot = some (some ⟨true,true,1⟩) := by decide',
    'theorem nohalt : weightedTNFNoAssignedHalt table := '+('weightedTNFNoAssignedHalt_refine _ _ _ ('*len(refinements))+'parent_nohalt'+(')'*len(refinements)),f'theorem cover : ∀ m, compatible table m → WeightedBound {B} m :=',f'  (certifiedZip {B} table (.last {n} {s}) root_ok nohalt checked).sound',f'def witness : Machine := weightedTNFDefaultCompletion (refine table {s} none)',
    'theorem witness_parent : compatible parent witness := by',f'  have hfull : compatible (refine table {s} none) witness := weightedTNFDefaultCompletion_compatible _',f'  have htable : compatible table witness := refine_preserves_compat table witness {s} none (by decide) hfull']
    hp='htable'
    for j,(prev,current,i,x) in enumerate(reversed(refinements)):
        lines.append(f'  have h{j} : compatible {prev} witness := refine_preserves_compat {prev} witness {slot(i)} (some {mv(x)}) (by decide) {hp}');hp=f'h{j}'
    lines += [f'  exact {hp}',f'theorem witness_halts : HaltsAfter witness {n} := halt_of_query (p := table) (n := {n}) (B := {B}) (s := {s}) query witness (weightedTNFDefaultCompletion_compatible _)',f'theorem witness_delay : {delay} ∈ delays (zeroNext witness) 0 := by decide',f'theorem attained : ∃ m, compatible parent m ∧ HaltsAfter m {n} ∧ {delay} ∈ delays (zeroNext m) 0 := ⟨witness,witness_parent,witness_halts,witness_delay⟩','#print axioms cover','#print axioms attained',f'end {ns}']
    (outdir/f'{name}.lean').write_text('\n'.join(lines)+'\n');print(name,n,hole,B,len(trace),max(len(l)+len(r) for _,_,l,r in trace))

def main():
    p=argparse.ArgumentParser();p.add_argument('data',type=Path);p.add_argument('outdir',type=Path);p.add_argument('--chunk',type=int,default=500);a=p.parse_args();a.outdir.mkdir(parents=True,exist_ok=True)
    for kind in ('ra','rb'):
        d=a.data/kind;codes=(d/'miss.txt').read_text().splitlines()
        for line in (d/'longcycle.txt').read_text().splitlines():
            i,*record=line.split();i=int(i)
            if record[0] in ('H','Z'):generate(kind,i,codes[i],record,a.outdir,a.chunk)
if __name__=='__main__':main()
