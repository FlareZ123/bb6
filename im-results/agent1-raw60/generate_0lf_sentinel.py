"""Emit exact unary-fill witnesses from a small finite phase graph.
Only Lean's checked transition equalities and induction establish nonhalting.
"""
from pathlib import Path

DATA={1063:(37,5,5,[(3,4,11),(2,1,6)],'01',4,4),1064:(40,3,3,[(0,3,8)],'01101',1,8),1067:(41,4,3,[(0,3,8)],'01',0,4),1078:(109,12,4,[(3,4,11)],'00',4,4),1079:(37,5,3,[(0,3,8)],'00',4,4),1084:(41,7,4,[(3,4,11)],'00',0,4)}

def generate(opens):
    out=['import Raw60LFDelimiterCore','namespace BB6.Agent1Raw60LFSentinel','open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1Raw60LFUnaryCore BB6.Agent1Raw60LFDelimiterCore','set_option maxRecDepth 4000','set_option maxHeartbeats 4000000']
    manual={}
    for i,(entry,k0,d,epochs,sent,q,base) in DATA.items():
        S="["+",".join(str(x=="1").lower() for x in sent)+"]"
        code=opens[i].replace('_','');p=[code[j:j+3] for j in range(0,36,3)]
        lines=[f'namespace M{i}',f'-- {code}','def table : PartialMachine := fun s =>','  match s.1.val,s.2 with']
        for j,m in enumerate(p):
            if m!='---':lines.append(f'  | {j//2},{str(bool(j%2)).lower()} => some (some ⟨{str(m[0]=="1").lower()},{str(m[1]=="R").lower()},{ord(m[2])-65}⟩)')
        lines.append('  | _,_ => none')
        lines += [f'theorem base : FillS table {S} 1 {q} := by',f'  intro b L R; cases b <;> exact ⟨{base},by rfl⟩']
        def advance(q,h):
            m=p[2*q+1]
            if m=='0LF':return ord(p[2*q][2])-65,f'resetS {h} (by rfl) (by rfl) (by rfl)'
            assert m.startswith('1R'),(i,q,m)
            return ord(m[2])-65,f'directS {h} (by rfl)'
        def chain(q,k,N,first,indent='  ',tag='a'):
            h=first
            for j in range(1,N+1):
                q,expr=advance(q,h);h=f'{tag}{j}'
                lines.append(f'{indent}have {h} : FillS table {S} ({k}+{j}) {q} := {expr}')
            return q,h
        q0,h=chain(q,'1',k0-1,'base')
        lines.insert(len(lines)-(k0-1),f'theorem basePhase : FillS table {S} {k0} {epochs[0][0]} := by')
        assert q0==epochs[0][0],(i,q0,epochs)
        lines.append(f'  exact {h}')
        lines += [f'theorem fillPhase (n : Nat) : FillS table {S} ({d}*n+{k0}) {q0} := by','  induction n with','  | zero => exact basePhase','  | succ n ih =>']
        q,h=chain(q0,f'{d}*n+{k0}',d,'ih','    ','a')
        assert q==q0
        lines += [f'    rw [show {d}*(n+1)+{k0}={d}*n+{k0}+{d} by omega]',f'    exact {h}']
        for j,(q,inc,t) in enumerate(epochs):
            lines += [f'theorem epoch{j} (k : Nat) (h : FillS table {S} (k+1) {q}) :',f'    ∃ t, 0<t ∧ run0 table t (F {S} (U (k+1)++[false])) = some (F {S} (U (k+1+{inc})++[false])) := by',
            '  obtain ⟨a,ha⟩ := h false [] []',f'  have hb : run0 table {t} (Q {q} (false::(U (k+1)++{S})) []) = some (F (U (k+1+{inc})++{S}) [false]) := by rfl',
            f'  have hc := sweep table (by rfl) (k+1+{inc}) {S} [false]',f'  exact ⟨a+{t}+(k+1+{inc}),by omega,join0 (join0 ha hb) hc⟩']
        lines += [f'def family (n : Nat) : Z0 := F {S} (U ({d}*n+{k0})++[false])',f'theorem entry : run0 table {entry} ⟨0,[],[]⟩ = some (family 0) := by rfl','theorem growth_exists (n : Nat) : ∃ t, 0<t ∧ run0 table t (family n) = some (family (n+1)) := by','  have h := fillPhase n']
        off=0;q=q0;h='h';proof=None
        for j,(expect,inc,t) in enumerate(epochs):
            assert q==expect
            k=f'{d}*n+{k0-1+off}'
            lines.append(f'  obtain ⟨t{j},pos{j},e{j}⟩ := epoch{j} ({k}) {h}')
            proof=f'e{j}' if proof is None else f'join0 ({proof}) e{j}'
            if j+1<len(epochs):q,h=chain(q,f'{d}*n+{k0+off}',inc,h,tag=f'b{j}_')
            off+=inc
        assert off==d
        lines += ['  unfold family',f'  rw [show {d}*(n+1)+{k0}={d}*n+{k0}+{d} by omega]',f'  exact ⟨{"+".join(f"t{j}" for j in range(len(epochs)))},by omega,{proof}⟩',
          'noncomputable def cost (n : Nat) : Nat := Classical.choose (growth_exists n)',
          'theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=',f'  never_of_growth table family {entry} cost entry',
          '    (fun n => (Classical.choose_spec (growth_exists n)).1)',
          '    (fun n => (Classical.choose_spec (growth_exists n)).2) m hm', '#print axioms never', f'end M{i}']
        out.extend(lines);manual[str(i)]=["Raw60LFSentinel",f"BB6.Agent1Raw60LFSentinel.M{i}",opens[i]]
    out.append('end BB6.Agent1Raw60LFSentinel')
    return '\n'.join(out)+'\n',manual

if __name__=='__main__':
    import sys
    path=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parent/'generated_0LF'/'open.txt'
    src,manual=generate(path.read_text().splitlines())
    Path(__file__).with_name('Raw60LFSentinel.lean').write_text(src)
