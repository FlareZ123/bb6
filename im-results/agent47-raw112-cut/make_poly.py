"""Generate proofs for raw112 IDs 32–35 and 51."""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'agent47-raw115-cut'))
import counter as c
R,W,C=c.R,c.W,c.C
def literal(s):
    if s.endswith(('X','Y')):return c.app(c.bits(s[:-1]),s[-1])
    return c.bits(s)
c.literal=literal
def macro(p,name,st,target,vs,expected):
    out=c.macro(p,name,st,target,bool(vs),expected)
    if len(vs)==2:out=out.replace('(X : List Bool)','(X Y : List Bool)').replace(' n X)', ' n X Y)').replace(' n X]', ' n X Y]')
    return out
def generate(idx,p):
    ls=[f'import Raw115CounterBase\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nset_option linter.unusedVariables false\nset_option linter.unusedSimpArgs false\nnamespace BB6Coverage.Agent31Pump.Raw112Counter{idx}\nopen BB6Coverage BB6Coverage.Agent31Pump.Raw115CounterBase\n',c.pump.tab(p)]
    if idx==51:
        st=C(1,W('0',R('00'),'1',R('0')),W());ta=C(1,W('000',R('00'),'10',R('0')),W())
        ls.append(c.macro(p,'growthCore',st,ta,False,(11,10)))
        ls.append(f'''def fam (n : Nat) : Z0 := {c.cfg(st)}
theorem growth (n : Nat) : run0 table (11+10*n) (fam n) = some (fam (n+1)) := by
  simpa only [fam,rep,List.cons_append,List.append_assoc,List.nil_append] using growthCore n
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_returns table fam (fun _ => True) 0 trivial 1 (by rfl)
    (fun n _ => ⟨n+1,11+10*n,trivial,by omega,growth n⟩) m hm
#print axioms never
end BB6Coverage.Agent31Pump.Raw112Counter51
''')
        return '\n\n'.join(ls)
    ls.append(macro(p,'transferCore',C(0,W('00X'),W(R('10'),'010Y')),C(0,W('00X'),W('10',R('10'),'0Y')),'XY',(6,4)))
    ls.append(macro(p,'lastCore',C(0,W('00X'),W(R('10'),'011')),C(0,W('00X'),W('10',R('10'),'1')),'X',(6,4)))
    ls.append(macro(p,'finishCore',C(0,W('00X'),W(R('10'),'1')),C(3,W('001111',R('11'),'0X'),W()),'X',(5,2)))
    ls.append('''abbrev P (n : Nat) := rep [true,false] n
abbrev Q (n : Nat) := rep [true,true] n
def A (a b : Nat) (X : List Bool) : Z0 := ⟨0,[false,false] ++ X,P a ++ [false] ++ P b ++ [true,true]⟩
def ready (a : Nat) (X : List Bool) : Z0 := ⟨0,[false,false] ++ X,P a ++ [true]⟩
def D (n : Nat) (X : List Bool) : Z0 := ⟨3,[false,false,true,true,true,true] ++ Q n ++ [false] ++ X,[]⟩

theorem transfer (a b : Nat) (X : List Bool) : run0 table (6+4*a) (A a (b+1) X) = some (A (a+1) b X) := by
  simpa only [A,P,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using transferCore a X (P b ++ [true,true])

theorem drain (a b : Nat) (X : List Bool) : ∃ t, run0 table t (A a b X) = some (A (a+b) 0 X) := by
  induction b generalizing a with
  | zero => exact ⟨0,by simp [run0]⟩
  | succ b ih =>
    obtain ⟨t,h⟩ := ih (a+1)
    exact ⟨6+4*a+t,by simpa only [Nat.add_assoc,Nat.add_comm 1 b] using join0 (transfer a b X) h⟩

theorem last (a : Nat) (X : List Bool) : run0 table (6+4*a) (A a 0 X) = some (ready (a+1) X) := by
  simpa only [A,ready,P,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using lastCore a X

theorem finish (a : Nat) (X : List Bool) : run0 table (5+2*a) (ready a X) = some (D a X) := by
  simpa only [ready,D,P,Q,List.append_assoc] using finishCore a X

theorem exhaust (a b : Nat) (X : List Bool) : ∃ t, 0<t ∧ run0 table t (A a b X) = some (D (a+b+1) X) := by
  obtain ⟨t,h⟩ := drain a b X
  exact ⟨t+(6+4*(a+b))+(5+2*(a+b+1)),by omega,join0 (join0 h (last (a+b) X)) (finish (a+b+1) X)⟩
''')
    if idx in (32,33):
        k=15 if idx==32 else 17
        ls.append(macro(p,'beginCore',C(3,W('001111',R('11'),'0X'),W()),C(0,W('0010X'),W('0',R('10'),'11')),'X',(k,2)))
        ls.append(f'''def fam (n : Nat) : Z0 := D n (P (n+1))
theorem beginRun (n : Nat) (X : List Bool) : run0 table ({k}+2*n) (D n X) = some (A 0 n ([true,false] ++ X)) := by
  simpa only [D,A,P,Q,rep,List.append_assoc,List.nil_append,List.cons_append] using beginCore n X
theorem growth (n : Nat) : ∃ t, 0<t ∧ run0 table t (fam n) = some (fam (n+1)) := by
  obtain ⟨t,ht,h⟩ := exhaust 0 n ([true,false] ++ P (n+1))
  exact ⟨{k}+2*n+t,by omega,by simpa only [fam,Nat.zero_add,P,rep] using join0 (beginRun n (P (n+1))) h⟩
''')
        entry=21 if idx==32 else 23
    else:
        a,b,k,entry=(3,4,39,113) if idx==34 else (1,3,25,41)
        d=a+b-2
        ls.append(macro(p,'beginCore',C(3,W('00'+'1'*(4+2*d),R('111111'),'0'),W()),C(0,W('00'),W('10'*a+'0'+'10'*b,R('101010'),'11')),'',(k,6)))
        ls.append(f'''def fam (n : Nat) : Z0 := D ({d}+3*n) []
theorem beginRun (n : Nat) : run0 table ({k}+6*n) (fam n) = some (A {a} ({b}+3*n) []) := by
  have h := beginCore n
  have hQ := rep_group [true,true] 3 n
  have hP := rep_group [true,false] 3 n
  change rep [true,true,true,true,true,true] n = rep [true,true] (3*n) at hQ
  change rep [true,false,true,false,true,false] n = rep [true,false] (3*n) at hP
  rw [hQ,hP] at h
  unfold fam D A P Q
  rw [rep_add [true,true] {d} (3*n),rep_add [true,false] {b} (3*n)]
  simpa only [rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using h
theorem growth (n : Nat) : ∃ t, 0<t ∧ run0 table t (fam n) = some (fam (n+1)) := by
  obtain ⟨t,ht,h⟩ := exhaust {a} ({b}+3*n) []
  exact ⟨{k}+6*n+t,by omega,by simpa only [fam,show {a}+({b}+3*n)+1={d}+3*(n+1) by omega] using join0 (beginRun n) h⟩
''')
    ls.append(f'''theorem entry : run0 table {entry} ⟨0,[],[]⟩ = some (fam 0) := by rfl
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_returns table fam (fun _ => True) 0 trivial {entry} entry
    (fun n _ => by obtain ⟨t,ht,h⟩ := growth n; exact ⟨n+1,t,trivial,ht,h⟩) m hm
#print axioms never
end BB6Coverage.Agent31Pump.Raw112Counter{idx}
''')
    return '\n\n'.join(ls)
if __name__=='__main__':
    rows=(ROOT/'hard.txt').read_text().splitlines()
    for i in [32,33,34,35,51]:
        (ROOT/f'Raw112Counter{i}.lean').write_text(generate(i,c.pump.parse(rows[i])))
