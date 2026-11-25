"""Recursive suffix certificates for the three remaining 0LA leaves."""
from tagmacro import *
from generate_sweeps import parse

machines=[(4117,'1RB0LE_1RC---_0RD1RF_1LD1RE_0LA1LE_0RC0RA',14,'topZero'),(4119,'1RB0LE_1RC---_0RD1RF_1LD1RE_0LA1LE_0RE0RA',18,'topOne'),(4123,'1RB0LE_1RC---_0RD1RF_1LD1RE_0LA1LE_1RB0RA',16,'topOne')]
def emit(opens,folder):
 parts=['import SweepPumping\nnamespace BB6.Agent3LAGrammar\nopen BB6Coverage BB6Coverage.Agent31Pump\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nset_option linter.unusedVariables false\nset_option linter.unusedSimpArgs false\n']
 Y=rep('Y','x');X=rep('X','x');L=lit;R=rep;cl=clean
 for i,code,ct,top in machines:
  assert opens[i]==code
  p=parse(code);parts.extend([f'namespace M{i}',tab(p)])
  for name,st,stop in [
  ('Zero',C(4,cl(L('00')+Y),cl(R('1100','n')+L('00'))),lambda c:c.q==4 and c.l==Y),
  ('One',C(4,cl(L('00')+Y),cl(R('1100','n')+L('01'))),lambda c:c.q==4 and c.l==Y),
  ('Middle',C(4,cl(L('00')+Y),cl(R('1100','n')+L('10000'))),lambda c:c.q==4 and c.l==Y),
  ('Pop',C(4,cl(L('00')+Y),cl(R('1100','n')+L('111')+X)),lambda c:c.q==4 and c.l==Y),
  ('Node0',C(4,cl(L('00')+Y),cl(R('1100','n')+L('011')+X)),lambda c:c.q==4 and c.l==Y),
  ('Node100',C(4,cl(L('00')+Y),cl(R('1100','n')+L('10011')+X)),lambda c:c.q==(1 if i==4123 else 4) and c.r==cl(L('11')+X) and c.l!=Y),
  ('Unwind',C(4,cl(L('111')+R('0111','n')+Y),X),lambda c:c.q==4 and c.l==Y),
  ]:
   rr=walk(p,st,stop);s,cost=generate(p,name,st,rr);parts.append(s)
  parts.append('''abbrev P := [true,true,false,false]

theorem shiftRep (a b : List Bool) (n : Nat) : a ++ rep (b++a) n = rep (a++b) n ++ a := by
  induction n with
  | zero => simp [rep]
  | succ n ih =>
    simp only [rep,List.append_assoc]
    rw [← List.append_assoc a b (a ++ rep (b ++ a) n),ih]
    simp only [List.append_assoc]

theorem rot11 (n : Nat) (R : List Bool) : [true,true] ++ rep [false,false,true,true] n ++ R = rep P n ++ [true,true] ++ R := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append] using congrArg (fun w => w ++ R) (shiftRep [true,true] [false,false] n)

theorem rot1 (n : Nat) (R : List Bool) : [true] ++ rep [true,false,false,true] n ++ R = rep P n ++ [true] ++ R := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append] using congrArg (fun w => w ++ R) (shiftRep [true] [true,false,false] n)

inductive Tail where
  | zero (n : Nat)
  | one (n : Nat)
  | middle (n : Nat)
  | topZero (n : Nat)
  | topOne (n : Nat)
  | node0 (n : Nat) (t : Tail)
  | node100 (n : Nat) (t : Tail)
  | node111 (n : Nat) (t : Tail)
  deriving Repr

def word : Tail → List Bool
  | .zero n => rep P (n+1) ++ [false,false]
  | .one n => rep P (n+1) ++ [false,true]
  | .middle n => rep P (n+1) ++ [true,false,false,false,false]
  | .topZero n => rep P n ++ [true,true,true,false]
  | .topOne n => rep P n ++ [true,true,true,true]
  | .node0 n t => rep P (n+1) ++ [false] ++ word t
  | .node100 n t => rep P (n+1) ++ [true,false,false] ++ word t
  | .node111 n t => rep P n ++ [true,true,true] ++ word t

def next : Tail → Tail
  | .zero n => .topOne (n+1)
  | .one n => .middle n
  | .middle n => .node111 (n+1) (TOP 0)
  | .topZero n => .zero n
  | .topOne n => .one n
  | .node0 n t => .node100 n t
  | .node100 n t => .node111 (n+1) (next t)
  | .node111 n t => .node0 n t

theorem wordHead (t : Tail) : ∃ R, word t = true::true::R := by
  cases t with
  | zero n => exact ⟨_,rfl⟩
  | one n => exact ⟨_,rfl⟩
  | middle n => exact ⟨_,rfl⟩
  | topZero n => cases n <;> exact ⟨_,rfl⟩
  | topOne n => cases n <;> exact ⟨_,rfl⟩
  | node0 n t => exact ⟨_,rfl⟩
  | node100 n t => exact ⟨_,rfl⟩
  | node111 n t => cases n <;> exact ⟨_,rfl⟩

def cfg (L : List Bool) (t : Tail) : Z0 := ⟨4,L,word t⟩

/-- Every legal suffix has a finite positive return, popping exactly two
    zero cells. The recursive call consumes a strict subterm of Tail. -/
theorem process (t : Tail) (L : List Bool) : ∃ k, 2≤k ∧ run0 table k (cfg (false::false::L) t) = some (cfg L (next t)) := by
  induction t generalizing L with
  | zero n =>
    have h := Zero.equation (n+1) L
    rw [rot11] at h
    exact ⟨10+8*(n+1),by omega,by simpa only [cfg,word,next,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using h⟩
  | one n =>
    have h := One.equation (n+1) L
    rw [rot1] at h
    exact ⟨10+8*(n+1),by omega,by simpa only [cfg,word,next,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using h⟩
  | middle n =>
    have h := Middle.equation (n+1) L
    rw [rot11] at h
    exact ⟨CT+8*(n+1),by omega,by simpa only [cfg,word,next,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using h⟩
  | topZero n =>
    have h := Pop.equation n [false] L
    exact ⟨10+8*n,by omega,by simpa only [cfg,word,next,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using h⟩
  | topOne n =>
    have h := Pop.equation n [true] L
    exact ⟨10+8*n,by omega,by simpa only [cfg,word,next,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using h⟩
  | node0 n t ih =>
    obtain ⟨R,hr⟩ := wordHead t
    have h := Node0.equation (n+1) R L
    rw [rot1] at h
    exact ⟨10+8*(n+1),by omega,by simpa only [cfg,word,next,hr,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using h⟩
  | node100 n t ih =>
    obtain ⟨R,hr⟩ := wordHead t
    have h1 := Node100.equation (n+1) R L
    obtain ⟨k,hk,h2⟩ := ih ([true,true,true]++rep [false,true,true,true] (n+1)++L)
    PRELUDE
    have h3 := Unwind.equation (n+1) (word (next t)) L
    rw [rot11] at h3
    have h3' : run0 table (3+4*(n+1)) (cfg ([true,true,true]++rep [false,true,true,true] (n+1)++L) (next t)) = some (cfg L (.node111 (n+1) (next t))) := by
      simpa only [cfg,word,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using h3
    exact ⟨_,by omega,join0 (join0 h1' h2) h3'⟩
  | node111 n t ih =>
    have h := Pop.equation n (word t) L
    exact ⟨10+8*n,by omega,by simpa only [cfg,word,next,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using h⟩

theorem twoZeros (k : Nat) (R : List Bool) : run0 table (k+2) ⟨4,[],R⟩ = run0 table (k+2) ⟨4,[false,false],R⟩ := by rfl

theorem advance (t : Tail) : ∃ k, 0<k ∧ run0 table k (cfg [] t) = some (cfg [] (next t)) := by
  obtain ⟨k,hk,hr⟩ := process t []
  have h := twoZeros (k-2) (word t)
  rw [show k-2+2=k by omega] at h
  exact ⟨k,by omega,h.trans hr⟩

def orbit : Nat → Tail
  | 0 => .topOne 0
  | n+1 => next (orbit n)

def family (n : Nat) : Z0 := cfg [] (orbit n)
noncomputable def cost (n : Nat) : Nat := Classical.choose (advance (orbit n))
theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := (Classical.choose_spec (advance (orbit n))).2
theorem positive (n : Nat) : 0<cost n := (Classical.choose_spec (advance (orbit n))).1
theorem entry : run0 table 9 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := never_of_growth table family 9 cost entry positive growth m hm
#print axioms never
'''.replace('TOP','.'+top).replace('CT',str(ct)).replace('PRELUDE',
'''have h1' : run0 table (5+4*(n+1)) (cfg (false::false::L) (.node100 n t)) = some ⟨1,false::true::([true,true,true]++rep [false,true,true,true] (n+1)++L),word t⟩ := by
      simpa only [cfg,word,hr,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using h1
    rw [show k=2+(k-2) by omega,run0_add] at h2
    change run0 table (k-2) ⟨1,false::true::([true,true,true]++rep [false,true,true,true] (n+1)++L),word t⟩ = _ at h2''' if i==4123 else
'''have h1' : run0 table (PC+4*(n+1)) (cfg (false::false::L) (.node100 n t)) = some (cfg (false::false::([true,true,true]++rep [false,true,true,true] (n+1)++L)) t) := by
      simpa only [cfg,word,hr,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using h1'''.replace('PC','9' if i==4117 else '5'))+f'\nend M{i}')
 parts.append('end BB6.Agent3LAGrammar')
 (folder/'Raw120LAGrammar.lean').write_text('\n\n'.join(parts)+'\n')
