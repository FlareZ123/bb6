"""Second-order unary fill induction, with phase-dependent finite restoration."""
from pathlib import Path
DATA={1099:(39,7,5,[(2,1,6),(3,4,11)],'BCDEABCDE',4,9),1129:(43,7,5,[(2,1,6),(3,4,11)],'BCDEABCDE',4,13),
1222:(29,6,5,[(3,4,11),(2,1,6)],'DEABCDEAB',2,3),1223:(29,6,2,[(1,2,7)],'DEABABAB',2,3),1227:(29,6,2,[(1,2,7)],'DEABABAB',2,3),1228:(29,6,5,[(3,4,11),(2,1,6)],'DEABCDEAB',2,3),
1239:(33,5,2,[(1,2,7)],'EABCBCBC',2,3),1242:(33,5,2,[(1,2,7)],'EABCBCBC',2,3),1244:(33,5,5,[(3,4,11),(2,1,6)],'EABCDEAB',2,3),1292:(33,5,5,[(3,4,11),(2,1,6)],'EABCDEAB',2,3),
1315:(35,4,2,[(1,2,7)],'ABCBCBC',2,7),1318:(35,4,2,[(1,2,7)],'ABCBCBC',2,7),1320:(35,4,5,[(3,4,11),(2,1,6)],'ABCDEABC',2,7),1350:(41,4,5,[(3,4,11),(2,1,6)],'ABCDEABC',2,7)}

def generate(opens):
    out=['import Raw60LFUnaryCore','namespace BB6.Agent1Raw60LFSecond','open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1Raw60LFUnaryCore','set_option maxRecDepth 4000','set_option maxHeartbeats 4000000']
    manual={}
    for i,(entry,k0,d,epochs,seq,t1,t2) in DATA.items():
        code=opens[i].replace('_','');p=[code[j:j+3] for j in range(0,36,3)]
        lines=[f'namespace M{i}',f'-- {code}','def table : PartialMachine := fun s =>','  match s.1.val,s.2 with']
        for j,m in enumerate(p):
            if m!='---':lines.append(f'  | {j//2},{str(bool(j%2)).lower()} => some (some ⟨{str(m[0]=="1").lower()},{str(m[1]=="R").lower()},{ord(m[2])-65}⟩)')
        lines.append('  | _,_ => none')
        if p[3]=='0LA':
            lines += ['theorem leftA (k : Nat) (g : Fill table (k+1) 0) (h : Fill table (k+2) 1) : Fill table (k+3) 2 := by',
              '  apply extend h','  intro b L R',
              '  have ha : run0 table 2 (Q 1 (true::(U (k+2)++false::L)) (b::R)) = some (F (U (k+1)++false::L) (false::false::b::R)) := by rfl',
              '  have hb := sweep table (by rfl) (k+1) (false::L) (false::false::b::R)',
              '  have hc := g false L (false::b::R)',
              '  have hd : run0 table 2 (Q 0 (false::(U (k+1)++false::L)) (false::b::R)) = some (Q 2 (b::(U (k+3)++false::L)) R) := by rfl',
              '  exact reachTrans ⟨2,ha⟩ (reachTrans ⟨_,hb⟩ (reachTrans hc ⟨2,hd⟩))']
            if i in (1239,1242,1315,1318):
                lines += ['theorem leftC (k : Nat) (g : Fill table (k+1) 2) (h : Fill table (k+2) 1) : Fill table (k+3) 2 := by',
                  '  apply extend h','  intro b L R',
                  '  have ha : run0 table 2 (Q 1 (true::(U (k+2)++false::L)) (b::R)) = some (F (U (k+1)++false::L) (false::false::b::R)) := by rfl',
                  '  have hb := sweep table (by rfl) (k+1) (false::L) (false::false::b::R)',
                  '  have hc := g false L (false::b::R)',
                  '  have hd : run0 table 6 (Q 2 (false::(U (k+1)++false::L)) (false::b::R)) = some (F (U (k+2)++false::L) (false::b::R)) := by rfl',
                  '  have he := sweep table (by rfl) (k+2) (false::L) (false::b::R)',
                  '  have hf := h false L (b::R)',
                  '  have hg : run0 table 1 (Q 1 (false::(U (k+2)++false::L)) (b::R)) = some (Q 2 (b::(U (k+3)++false::L)) R) := by rfl',
                  '  exact reachTrans ⟨2,ha⟩ (reachTrans ⟨_,hb⟩ (reachTrans hc (reachTrans ⟨6,hd⟩ (reachTrans ⟨_,he⟩ (reachTrans hf ⟨1,hg⟩)))))']
        if p[3]=='1LE':
            lines += ['theorem leftE (k : Nat) (h : Fill table (k+1) 1) : Fill table (k+2) 2 := by',
              '  apply extend h','  intro b L R',
              '  have ha : run0 table 3 (Q 1 (true::(U (k+1)++false::L)) (b::R)) = some (F (U (k+1)++false::L) (false::b::R)) := by rfl',
              '  have hb := sweep table (by rfl) (k+1) (false::L) (false::b::R)',
              '  have hc := h false L (b::R)',
              '  have hd : run0 table 1 (Q 1 (false::(U (k+1)++false::L)) (b::R)) = some (Q 2 (b::(U (k+2)++false::L)) R) := by rfl',
              '  exact reachTrans ⟨3,ha⟩ (reachTrans ⟨_,hb⟩ (reachTrans hc ⟨1,hd⟩))']
        detours={}
        if p[3] in ('0LC','1LD'):detours[1]=(0,5 if p[3]=='0LC' else 3)
        if p[5]=='0LE':detours[2]=(1,3)
        for q,(z,t) in detours.items():
            lines += [f'theorem detour{q} (k : Nat) (h : Fill table (k+1) {q}) : Fill table (k+2) {z} := by',
              '  apply extend h','  intro b L R',f'  exact ⟨{t},by rfl⟩']
        qs=[ord(x)-65 for x in seq]
        lines += [f'theorem base1 : Fill table 1 {qs[0]} := by',f'  intro b L R; cases b <;> exact ⟨{t1},by rfl⟩',f'theorem base2 : Fill table 2 {qs[1]} := by',f'  intro b L R; cases b <;> exact ⟨{t2},by rfl⟩']
        def advance(prev,q,g,h,k):
            m=p[2*q+1]
            if m=='0LF':return ord(p[2*q][2])-65,f'reset {h} (by rfl) (by rfl) (by rfl)'
            if m.startswith('1R'):return ord(m[2])-65,f'direct {h} (by rfl)'
            if q in detours:return detours[q][0],f'detour{q} ({k}+1) {h}'
            if m=='0LA':assert prev in (0,2);return 2,f'left{chr(prev+65)} ({k}) {g} {h}'
            if m=='1LE':return 2,f'leftE ({k}+1) {h}'
            raise ValueError((i,prev,q,m))
        def chain(prev,q,k,N,g,h,indent='  ',tag='a'):
            for j in range(N):
                z,expr=advance(prev,q,g,h,f'{k}+{j}');g,h=h,f'{tag}{j}'
                lines.append(f'{indent}have {h} : Fill table ({k}+{j}+3) {z} := {expr}')
                prev,q=q,z
            return prev,q,g,h
        lines.append(f'theorem basePhase : Fill table {k0-1} {qs[k0-2]} ∧ Fill table {k0} {qs[k0-1]} := by')
        prev,q,g,h=chain(qs[0],qs[1],'0',k0-2,'base1','base2')
        assert (prev,q)==(qs[k0-2],qs[k0-1]);assert q==epochs[0][0]
        lines.append(f'  exact ⟨{g},{h}⟩');q0=q;prev0=prev
        lines += [f'theorem fillPhase (n : Nat) : Fill table ({d}*n+{k0-1}) {prev} ∧ Fill table ({d}*n+{k0}) {q} := by','  induction n with','  | zero => exact basePhase','  | succ n ih =>']
        prev,q,g,h=chain(prev,q,f'{d}*n+{k0-2}',d,'ih.1','ih.2','    ')
        assert (prev,q)==(prev0,q0)
        lines += [f'    rw [show {d}*(n+1)+{k0-1}={d}*n+{k0-2}+{d-2}+3 by omega, show {d}*(n+1)+{k0}={d}*n+{k0-2}+{d-1}+3 by omega]',f'    exact ⟨{g},{h}⟩']
        for j,(q,inc,t) in enumerate(epochs):
            lines += [f'theorem epoch{j} (k : Nat) (h : Fill table (k+1) {q}) :',f'    ∃ t, 0<t ∧ run0 table t (F [false] (U (k+1)++[false])) = some (F [false] (U (k+1+{inc})++[false])) := by',
            '  obtain ⟨a,ha⟩ := h false [] []',f'  have hb : run0 table {t} (Q {q} (false::(U (k+1)++[false])) []) = some (F (U (k+1+{inc})++[false]) [false]) := by rfl',
            f'  have hc := sweep table (by rfl) (k+1+{inc}) [false] [false]',f'  exact ⟨a+{t}+(k+1+{inc}),by omega,join0 (join0 ha hb) hc⟩']
        lines += [f'def family (n : Nat) : Z0 := F [false] (U ({d}*n+{k0})++[false])',f'theorem entry : run0 table {entry} ⟨0,[],[]⟩ = some (family 0) := by rfl','theorem growth_exists (n : Nat) : ∃ t, 0<t ∧ run0 table t (family n) = some (family (n+1)) := by','  obtain ⟨g,h⟩ := fillPhase n']
        off=0;prev=prev0;q=q0;g='g';h='h';proof=None
        for j,(expect,inc,t) in enumerate(epochs):
            assert q==expect
            k=f'{d}*n+{k0-1+off}'
            lines.append(f'  obtain ⟨t{j},pos{j},e{j}⟩ := epoch{j} ({k}) {h}')
            proof=f'e{j}' if proof is None else f'join0 ({proof}) e{j}'
            if j+1<len(epochs):prev,q,g,h=chain(prev,q,f'{d}*n+{k0-2+off}',inc,g,h,tag=f'b{j}_')
            off+=inc
        assert off==d
        lines += ['  unfold family',f'  rw [show {d}*(n+1)+{k0}={d}*n+{k0}+{d} by omega]',f'  exact ⟨{"+".join(f"t{j}" for j in range(len(epochs)))},by omega,{proof}⟩',
          'noncomputable def cost (n : Nat) : Nat := Classical.choose (growth_exists n)',
          'theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=',f'  never_of_growth table family {entry} cost entry',
          '    (fun n => (Classical.choose_spec (growth_exists n)).1)',
          '    (fun n => (Classical.choose_spec (growth_exists n)).2) m hm', '#print axioms never', f'end M{i}']
        out.extend(lines);manual[str(i)]=["Raw60LFSecond",f"BB6.Agent1Raw60LFSecond.M{i}",opens[i]]
    out.append('end BB6.Agent1Raw60LFSecond')
    return '\n'.join(out)+'\n',manual
if __name__=='__main__':
    import sys
    path=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parent/'generated_0LF'/'open.txt'
    src,manual=generate(path.read_text().splitlines())
    Path(__file__).with_name('Raw60LFSecond.lean').write_text(src)
