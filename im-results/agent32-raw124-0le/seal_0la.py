"""Close only the 70 residual tables of the archived 0LA partial cut.

No partition or proof search is repeated. Each candidate is independently
replayed, compressed and converted to a source Lean certificate.
"""
import argparse,json,tempfile
from pathlib import Path
from replay_0le import discover,from_runs,witness,emit

HERE=Path(__file__).resolve().parent

def main(out):
    out.mkdir(parents=True,exist_ok=True)
    spec=json.loads((HERE/'0LA-residuals.json').read_text())
    tables=spec['tables'];params=spec['params'];late=spec['late'];B=spec['bound']
    assert len(tables)==70 and len(params)==68 and len(late)==2
    assert set(tables)==set(params)|set(late) and not set(params)&set(late)
    refs={}
    for i,(kind,*p) in params.items():
        t=tables[i];d,n=discover(t,kind,p);assert len(witness(t,*d)[1])==n
        d=from_runs(t,d);name='Raw124ZeroLAResidual'+i;ns='BB6.Agent32'+name
        with tempfile.TemporaryDirectory() as tmp:
            tmp=Path(tmp);n2,e=emit(int(i),t,*d,tmp);assert n2<=n
            for f in tmp.glob('*.lean'):
                (out/f.name.replace('Raw118Wide'+i,name)).write_text(f.read_text().replace('Raw118Wide'+i,name).replace('BB6Coverage.Agent1BiDFAWide.M'+i,ns))
        refs[i]=(name,ns);print(i,kind,n,n2,e,flush=True)
    def bit(x):return str(bool(x)).lower()
    lines=['import ResidualCover','set_option maxRecDepth 100000','set_option maxHeartbeats 0','namespace BB6.Agent32Raw124ZeroLALate','open BB6Coverage BB6.Agent13BlankDelay BB6.Agent10ZipAudit BB6.Agent31ThreeHole']
    for i,(n,s) in late.items():
        t=tables[i];assert t.count('---')==1 and t[3*s:3*s+3]=='---'
        lines.append(f'def table{i} : PartialMachine := fun s => match s.1.val,s.2 with')
        for j in range(12):
            m=t[3*j:3*j+3]
            if m!='---':lines.append(f'  | {j//2},{bit(j%2)} => some (some ⟨{bit(m[0]=="1")},{bit(m[1]=="R")},{ord(m[2])-65}⟩)')
        lines+=['  | _,_ => none',f'theorem bound{i} : ∀ m, compatible table{i} m → WeightedBound {B} m := by',
            f'  apply (certifiedZip {B} table{i} (.last {n} ({s//2},{bit(s%2)})) (by decide) ?_ (by decide)).sound',
            '  intro s','  rcases s with ⟨q,b⟩',
            '  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega',
            '  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide',f'#print axioms bound{i}']
    lines.append('end BB6.Agent32Raw124ZeroLALate')
    (out/'Raw124ZeroLALate.lean').write_text('\n'.join(lines)+'\n')
    lines=[f'import {name}' for name,ns in refs.values()]+['import Raw124ZeroLALate','import ResidualCover','set_option maxRecDepth 100000','set_option maxHeartbeats 0','namespace BB6.Agent32Raw124ZeroLAResidual','open BB6Coverage BB6.Agent13BlankDelay BB6.Agent16ResidualCover',f'def accepted : List (Accepted {B}) := [']
    for name,ns in refs.values():lines.append(f'  nonhalt {B} {ns}.table {ns}.never,')
    for i in late:lines.append(f'  ⟨BB6.Agent32Raw124ZeroLALate.table{i}, BB6.Agent32Raw124ZeroLALate.bound{i}⟩,')
    lines+= [']','theorem accepted_count : accepted.length = 70 := by decide','end BB6.Agent32Raw124ZeroLAResidual']
    (out/'Raw124ZeroLAResidual.lean').write_text('\n'.join(lines)+'\n')
    (out/'Raw124ZeroLAComplete.lean').write_text(f"""import Raw124New0LACut
import Raw124ZeroLAResidual
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32Raw124ZeroLAComplete
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent16ResidualCover
open BB6.Agent2Raw124New0LA BB6.Agent32Raw124ZeroLAResidual

theorem no_open : (remaining accepted residuals).length = 0 := by decide

theorem bound_all : ∀ m, compatible branch m → WeightedBound {B} m := by
  intro m hm
  rcases branch_sound m hm with hb | ⟨e,he,hc⟩
  · exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
  · have hnil : remaining accepted residuals = [] := List.length_eq_zero_iff.mp no_open
    have hcov : covered accepted e.2 = true := by
      cases hv : covered accepted e.2 with
      | true => rfl
      | false =>
        have hh : e ∈ remaining accepted residuals := List.mem_filter.mpr ⟨he, by simp [hv]⟩
        rw [hnil] at hh
        simp at hh
    exact covered_sound hcov m hc

#print axioms no_open
#print axioms bound_all
end BB6.Agent32Raw124ZeroLAComplete
""")

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--out',required=True,type=Path);main(parser.parse_args().out)
