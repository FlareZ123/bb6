import Raw55Sweep
set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace BB6.Agent25Raw55M418
open BB6Coverage BB6Coverage.Agent31Pump
open BB6.Agent25Raw55Sweep (z o)

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,true,3⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def q (b : Bool) : Fin 6 := if b then 4 else 3

theorem scan (b : Bool) (n k : Nat) (L : List Bool) :
    run0 table (2*n+2) ⟨q b,true :: z k ++ L,o (2*n+1)⟩ =
      some ⟨q b,false :: z (k+2*n+2) ++ L,[]⟩ := by
  induction n generalizing k with
  | zero => cases b <;> rfl
  | succ n ih =>
    have h := ih (k+2)
    rw [show k+2+2*n+2=k+2*(n+1)+2 by omega] at h
    rw [show 2*(n+1)+2=2*n+2+2 by omega, show 2*(n+1)+1=2*n+1+2 by omega]
    cases b <;> exact h

theorem refill (n k : Nat) (L : List Bool) :
    run0 table n ⟨3,z n ++ L,o k⟩ = some ⟨3,L,o (k+n)⟩ := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    have h := ih (k+1)
    rw [show k+1+n=k+(n+1) by omega] at h
    exact h

theorem leftPump (n k : Nat) (L : List Bool) :
    run0 table (7*n) ⟨0,true :: z n ++ L,o (k+2)⟩ =
      some ⟨0,true :: L,o (k+n+2)⟩ := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    have h := ih (k+1)
    rw [show k+1+n+2=k+(n+1)+2 by omega] at h
    rw [show 7*(n+1)=7*n+7 by omega]
    exact h

theorem z_tail (n : Nat) (L : List Bool) : z n ++ false :: L = z (n+1) ++ L := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [z, List.cons_append, ih]

def family (k : Nat) : Z0 := ⟨0,[true],false :: o (4*k+4)⟩
def cost (k : Nat) : Nat := 40*k+69

theorem first : run0 table 28 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (k : Nat) : run0 table (cost k) (family k) = some (family (k+1)) := by
  have h1 : run0 table 4 (family k) = some ⟨3,[true,false,true,true],o (4*k+3)⟩ := by
    unfold family
    rw [show 4*k+4=(4*k+3)+1 by omega]
    rfl
  have h2 := scan false (2*k+1) 0 [false,true,true]
  rw [Nat.zero_add,show 2*(2*k+1)+1=4*k+3 by omega,show 2*(2*k+1)+2=4*k+4 by omega] at h2
  change run0 table (4*k+4) ⟨3,[true,false,true,true],o (4*k+3)⟩ =
      some ⟨3,z (4*k+5) ++ false :: [true,true],[]⟩ at h2
  rw [z_tail,show 4*k+5+1=4*k+6 by omega] at h2
  have h2' : run0 table (4*k+4) ⟨3,[true,false,true,true],o (4*k+3)⟩ =
      some ⟨3,z (4*k+6) ++ [true,true],[]⟩ := by
    exact h2
  have h3 := refill (4*k+6) 0 [true,true]
  rw [Nat.zero_add] at h3
  have h4 : run0 table 1 ⟨3,[true,true],o (4*k+6)⟩ =
      some ⟨4,[true,false,true],o (4*k+5)⟩ := by
    rw [show 4*k+6=(4*k+5)+1 by omega]
    rfl
  have h5 := scan true (2*k+2) 0 [false,true]
  rw [Nat.zero_add,show 2*(2*k+2)+1=4*k+5 by omega,show 2*(2*k+2)+2=4*k+6 by omega] at h5
  change run0 table (4*k+6) ⟨4,[true,false,true],o (4*k+5)⟩ =
      some ⟨4,z (4*k+7) ++ false :: [true],[]⟩ at h5
  rw [z_tail,show 4*k+7+1=4*k+8 by omega] at h5
  have h5' : run0 table (4*k+6) ⟨4,[true,false,true],o (4*k+5)⟩ =
      some ⟨4,z (4*k+8) ++ [true],[]⟩ := by
    exact h5
  have h6 : run0 table 5 ⟨4,z (4*k+8) ++ [true],[]⟩ =
      some ⟨0,true :: z (4*k+6) ++ [true],[true,true]⟩ := by
    rw [show 4*k+8=(4*k+6)+1+1 by omega]
    rfl
  have h7 := leftPump (4*k+6) 0 [true]
  simp only [Nat.zero_add] at h7
  have h8 : run0 table 1 ⟨0,[true,true],o (4*k+6+2)⟩ = some (family (k+1)) := by
    unfold family
    rw [show 4*(k+1)+4=4*k+6+2 by omega]
    rfl
  have h := join0 (join0 (join0 (join0 (join0 (join0 (join0 h1 h2') h3) h4) h5') h6) h7) h8
  unfold cost
  rw [show 4+(4*k+4)+(4*k+6)+1+(4*k+6)+5+7*(4*k+6)+1=40*k+69 by omega] at h
  exact h
#print axioms first
#print axioms growth
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 28 cost first (by intro k; unfold cost; omega) growth m hm
#print axioms never
end BB6.Agent25Raw55M418

namespace BB6.Agent25Raw55M419
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,true,3⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,true,0⟩)
  | _,_ => none

def I : List Bool := [true,true,false]
def O : List Bool := [false,false,true]

theorem rightOne (L R : List Bool) :
    run0 table 3 ⟨0,[false]++L,[]++I++R⟩ =
      some ⟨0,[false]++O++L,[]++R⟩ := by rfl

theorem leftOne (L R : List Bool) :
    run0 table 3 ⟨0,[true]++O++L,[]++R⟩ =
      some ⟨0,[true]++L,[]++I++R⟩ := by rfl

def family (k : Nat) : Z0 := ⟨0,[],rep I (3*k+2) ++ [true,true]⟩
def cost (k : Nat) : Nat := 18*k+37

theorem first : run0 table 19 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (k : Nat) : run0 table (cost k) (family k) = some (family (k+1)) := by
  have h1 : run0 table 3 (family k) =
      some ⟨0,[false]++rep O 1,rep I (3*k+1)++[true,true]⟩ := by rfl
  have h2 := sweepR table 0 [false] [] I O 3 rightOne (3*k+1) (rep O 1) [true,true]
  simp only [List.nil_append] at h2
  have h2' : run0 table (3*(3*k+1)) ⟨0,[false]++rep O 1,rep I (3*k+1)++[true,true]⟩ =
      some ⟨0,[false]++rep O (3*k+2),[true,true]⟩ := by
    change run0 table (3*(3*k+1)) ⟨0,[false]++O,rep I (3*k+1)++[true,true]⟩ = some ⟨0,[false]++rep O (3*k+2),[true,true]⟩
    change run0 table (3*(3*k+1)) ⟨0,[false]++O,rep I (3*k+1)++[true,true]⟩ = some ⟨0,([false]++rep O (3*k+1))++O,[true,true]⟩ at h2
    rw [List.append_assoc, rep_snoc] at h2
    exact h2
  have h3 : run0 table 3 ⟨0,[false]++rep O (3*k+2),[true,true]⟩ =
      some ⟨0,[false]++rep O (3*k+3),[]⟩ := by rfl
  have h4 : run0 table 13 ⟨0,[false]++rep O (3*k+3),[]⟩ =
      some ⟨0,[true]++rep O (3*k+4),[true,true]⟩ := by rfl
  have h5 := sweepL table 0 [true] [] O I 3 leftOne (3*k+4) [] [true,true]
  simp only [List.nil_append,List.append_nil] at h5
  have h6 : run0 table 3 ⟨0,[true],rep I (3*k+4)++[true,true]⟩ =
      some (family (k+1)) := by
    unfold family
    rw [show 3*(k+1)+2=(3*k+4)+1 by omega]
    rfl
  have h := join0 (join0 (join0 (join0 (join0 h1 h2') h3) h4) h5) h6
  unfold cost
  rw [show 3+3*(3*k+1)+3+13+3*(3*k+4)+3=18*k+37 by omega] at h
  exact h
#print axioms first
#print axioms growth
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 19 cost first (by intro k; unfold cost; omega) growth m hm
#print axioms never
end BB6.Agent25Raw55M419

namespace BB6.Agent25Raw55M513
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,4⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨false,true,3⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | _,_ => none

def I : List Bool := [true,true,false,false,true]
def O : List Bool := [false,false,true,false,false]
def R0 : List Bool := [false,false,true,true]
def L0 : List Bool := [false,false,false]
def R1 : List Bool := [false,false,true]
def L1 : List Bool := [true,true]

theorem rightOne (L R : List Bool) :
    run0 table 25 ⟨0,L0++L,R0++I++R⟩ =
      some ⟨0,L0++O++L,R0++R⟩ := by rfl

theorem leftOne (L R : List Bool) :
    run0 table 23 ⟨0,L1++O++L,R1++R⟩ =
      some ⟨0,L1++L,R1++I++R⟩ := by rfl

def family (k : Nat) : Z0 := ⟨0,[],[false,false,true,true,false,false,true] ++ rep I k⟩
def cost (k : Nat) : Nat := 48*k+74

theorem first : run0 table 26 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (k : Nat) : run0 table (cost k) (family k) = some (family (k+1)) := by
  have h1 : run0 table 19 (family k) = some ⟨0,L0++[true],R0++rep I k⟩ := by rfl
  have h2 := sweepR table 0 L0 R0 I O 25 rightOne k [true] []
  simp only [List.append_nil] at h2
  have h3 : run0 table 28 ⟨0,L0++rep O k++[true],R0⟩ =
      some ⟨0,L1++rep O (k+1)++[true],R1⟩ := by rfl
  have h4 := sweepL table 0 L1 R1 O I 23 leftOne (k+1) [true] []
  simp only [List.append_nil] at h4
  have h5 : run0 table 4 ⟨0,L1++[true],R1++rep I (k+1)⟩ = some (family (k+1)) := by rfl
  have h := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  unfold cost
  rw [show 19+25*k+28+23*(k+1)+4=48*k+74 by omega] at h
  exact h
#print axioms first
#print axioms growth
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 26 cost first (by intro k; unfold cost; omega) growth m hm
#print axioms never
end BB6.Agent25Raw55M513

namespace BB6.Agent25Raw55M612
open BB6Coverage BB6Coverage.Agent31Pump
open BB6.Agent25Raw55Sweep (z o)

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,3⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none

def q (b : Bool) : Fin 6 := if b then 4 else 3

theorem scan (b : Bool) (n j : Nat) (L : List Bool) :
    run0 table (2*n+2) ⟨q b,true :: z j ++ L,o (2*n+1)⟩ =
      some ⟨q b,false :: z (j+2*n+2) ++ L,[]⟩ := by
  induction n generalizing j with
  | zero => cases b <;> rfl
  | succ n ih =>
    have h := ih (j+2)
    rw [show j+2+2*n+2=j+2*(n+1)+2 by omega] at h
    rw [show 2*(n+1)+2=2*n+2+2 by omega,show 2*(n+1)+1=2*n+1+2 by omega]
    cases b <;> exact h

theorem scanOdd (n j : Nat) (L : List Bool) :
    run0 table (2*n+1) ⟨3,true :: z j ++ L,o (2*n+1)⟩ =
      some ⟨4,true :: z (j+2*n+1) ++ L,[]⟩ := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    have h := ih (j+2)
    rw [show j+2+2*n+1=j+2*(n+1)+1 by omega] at h
    rw [show 2*(n+1)+1=2*n+1+2 by omega]
    exact h

theorem refill (n j : Nat) (L : List Bool) :
    run0 table n ⟨3,z n ++ L,o j⟩ = some ⟨3,L,o (j+n)⟩ := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    have h := ih (j+1)
    rw [show j+1+n=j+(n+1) by omega] at h
    exact h

theorem leftPump (n j : Nat) (L : List Bool) :
    run0 table (11*n) ⟨0,[false,true,true]++z n++L,o (j+2)⟩ =
      some ⟨0,[false,true,true]++L,o (j+n+2)⟩ := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    have h := ih (j+1)
    rw [show j+1+n+2=j+(n+1)+2 by omega] at h
    rw [show 11*(n+1)=11*n+11 by omega]
    exact h

def family (k : Nat) : Z0 := ⟨4,true :: z (2*k+2) ++ [true,true] ++ z (k+4),[]⟩
def cost (k : Nat) : Nat := 28*k+85

theorem first : run0 table 59 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (k : Nat) : run0 table (cost k) (family k) = some (family (k+1)) := by
  have h1 : run0 table 1 (family k) = some ⟨3,z (2*k+4) ++ [true,true] ++ z (k+4),[]⟩ := by rfl
  have h2 := refill (2*k+4) 0 ([true,true]++z (k+4))
  rw [Nat.zero_add] at h2
  simp only [← List.append_assoc] at h2
  have h3 : run0 table 1 ⟨3,[true,true]++z (k+4),o (2*k+4)⟩ =
      some ⟨4,[true,false,true]++z (k+4),o (2*k+3)⟩ := by rfl
  have h4 := scan true (k+1) 1 (true::z (k+4))
  rw [show 2*(k+1)+2=2*k+4 by omega,show 2*(k+1)+1=2*k+3 by omega,
      show 1+2*(k+1)+2=2*k+5 by omega] at h4
  have h4' : run0 table (2*k+4) ⟨4,[true,false,true]++z (k+4),o (2*k+3)⟩ =
      some ⟨4,z (2*k+6)++true::z (k+4),[]⟩ := h4
  have h5 : run0 table 11 ⟨4,z (2*k+6)++true::z (k+4),[]⟩ =
      some ⟨0,[false,true,true]++z (2*k+2)++true::z (k+4),o 2⟩ := by rfl
  have h6 := leftPump (2*k+2) 0 (true::z (k+4))
  simp only [Nat.zero_add] at h6
  have h7 : run0 table 31 ⟨0,[false,true,true,true]++z (k+4),o (2*k+4)⟩ =
      some ⟨4,z (k+9),o (2*k+3)⟩ := by rfl
  have h8 : run0 table 8 ⟨4,z (k+9),o (2*k+3)⟩ =
      some ⟨3,[true,false,true,true]++z (k+5),o (2*k+3)⟩ := by rfl
  have h9 := scanOdd (k+1) 1 ([true,true]++z (k+5))
  rw [show 2*(k+1)+1=2*k+3 by omega,show 1+2*(k+1)+1=2*(k+1)+2 by omega] at h9
  have h9' : run0 table (2*k+3) ⟨3,[true,false,true,true]++z (k+5),o (2*k+3)⟩ =
      some (family (k+1)) := by
    unfold family
    rw [show k+1+4=k+5 by omega]
    simpa only [z, List.append_assoc, List.cons_append, List.nil_append] using h9
  have h := join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 h1 h2) h3) h4') h5) h6) h7) h8) h9'
  unfold cost
  rw [show 1+(2*k+4)+1+(2*k+4)+11+11*(2*k+2)+31+8+(2*k+3)=28*k+85 by omega] at h
  exact h
#print axioms first
#print axioms growth
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 59 cost first (by intro k; unfold cost; omega) growth m hm
#print axioms never
end BB6.Agent25Raw55M612
