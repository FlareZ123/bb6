"""Generate exact finite-run and prefix-growth proofs from literal tables."""
from parametric import parse,step
from emit_parametric import table as lean_table,bl

def emit_pump_module(c,spec):
    ns=f'BB6.Agent19Raw40.A1LC{c}'
    source=f'import SweepPumping\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace {ns}\nopen BB6Coverage BB6Coverage.Agent31Pump\n'
    tables={v['id']:v['table'] for v in spec['unresolved']}
    for i,entry,cost,q,l,pre,period,tail in spec['pumps']:
        source+=f'''namespace Leaf{i}
{lean_table(parse(tables[i]))}abbrev pre : List Bool := {bl(pre)}
abbrev period : List Bool := {bl(period)}
abbrev tailWord : List Bool := {bl(tail)}
def family (n : Nat) : Z0 := ⟨{q},{bl(l)},pre++rep period n++tailWord⟩
theorem entry : run0 table {entry} ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem pump (R : List Bool) : run0 table {cost} ⟨{q},{bl(l)},pre++R⟩ = some ⟨{q},{bl(l)},pre++period++R⟩ := by rfl
theorem epoch (n : Nat) : run0 table {cost} (family n) = some (family (n+1)) := by
  simpa only [family,rep,List.append_assoc] using pump (rep period n++tailWord)
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family {entry} (fun _ => {cost}) entry (by intro n; decide) epoch m hm
#print axioms never
end Leaf{i}
'''
    return source+f'end {ns}\n'

def cfg(s):
    q,l,r=s
    return f'⟨{q},{bl(l)},{bl(r)}⟩'

HEADER='''import SweepPumping
import CanonicalPartial
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper BB6.Agent13BlankDelay
open BB6Coverage.Agent10ZipAudit BB6.Agent10ZipAudit BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial BB6.Agent50TNFPilot
'''

def emit_late_module(c,records,B):
    ns=f'BB6.Agent19Raw40.A1LC{c}Late'
    source=HEADER+f'namespace {ns}\n'
    names={}
    for v in records:
        i,t,n,slot=(v[k] for k in ('id','table','n','slot'))
        p=parse(t);q,a=divmod(slot,2);bit=str(bool(a)).lower()
        assert p[slot]=='---' and p.count('---')==1
        names[t]=f'{ns}.Leaf{i}'
        source+=f'namespace Leaf{i}\n'+lean_table(p)
        cur=(0,'','');segments=[]
        for j in range(0,n,256):
            length=min(256,n-j);old=cur
            for _ in range(length):cur=step(p,*cur)
            label=f'seg{len(segments)}';segments.append(label)
            source+=f'theorem {label} : run0 table {length} {cfg(old)} = some {cfg(cur)} := by rfl\n'
        assert cur[0]==q and int((cur[1] or '0')[0])==a
        source+=f'theorem query : run0 table {n} (project start) = some {cfg(cur)} := by\n  have h := {segments[0]}\n'
        for label in segments[1:]:source+=f'  have h := join0 h {label}\n'
        source+='  exact h\n'
        source+=f'''theorem read_query : zipRead table {n} = some ({q},{bit}) := by
  have hz : (zrun table {n} start).map project = some {cfg(cur)} := (run_project table {n} start).trans query
  cases h : zrun table {n} start with
  | none => simp [h] at hz
  | some z =>
    have hq : project z = {cfg(cur)} := by simpa only [h,Option.map_some,Option.some.injEq] using hz
    have hq1 := congrArg Z0.q hq
    have hl := congrArg Z0.l hq
    change z.q = {q} at hq1
    change z.l = {bl(cur[1])} at hl
    simp only [zipRead,h,Option.map_some,hq1,hl]
    rfl

theorem checked (cut : Nat) : canonicalCheck {B} table cut (.closed (.last {n} ({q},{bit}))) = true := by
  simp only [canonicalCheck,prefixCheck_eq,zipCheck,zipQueryOK,read_query]
  decide +kernel

def witness : Machine := fun s => (table s).bind id
theorem witness_compatible : compatible table witness := by
  intro s t ht; simp only [witness,ht,Option.bind_some,id_eq]
theorem witness_halts : HaltsAfter witness {n} := by
  have hz : (zrun table {n} start).map project = some {cfg(cur)} := (run_project table {n} start).trans query
  cases h : zrun table {n} start with
  | none => simp [h] at hz
  | some z =>
    have hq : project z = {cfg(cur)} := by simpa only [h,Option.map_some,Option.some.injEq] using hz
    have H := zrun_sound table witness witness_compatible _ start z h
    rw [start_embed] at H
    have hread : readSlot (embed z) = ({q},{bit}) := by
      rw [read_embed]
      have hq1 := congrArg Z0.q hq
      have hl := congrArg Z0.l hq
      change z.q = {q} at hq1
      change z.l = {bl(cur[1])} at hl
      rw [hq1,hl]; rfl
    constructor
    · rw [H]; rfl
    · rw [run_append,H,Option.bind_some]
      change rawStep witness (embed z) = none
      rw [rawStep,hread]; rfl
#print axioms checked
#print axioms witness_halts
end Leaf{i}
'''
    return source+f'end {ns}\n',names

if __name__=='__main__':
    import json,sys
    from pathlib import Path
    path=Path(sys.argv[1]);c=sys.argv[2];spec=json.loads(path.read_text())
    print(emit_late_module(c,spec['late'],spec['bound'])[0])
