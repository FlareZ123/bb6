import PartialAudit
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent6E0OneRE1873
open BB6Coverage BB6Coverage.Agent31Pump
open BB6Coverage.Agent50Zipper BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent10ZipAudit BB6.Agent47PartialAudit BB6Coverage.Agent10ZipAudit

def p : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨true,false,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,true,2⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none

def O (n : Nat) : List Bool := rep [true] n
def Zeros (n : Nat) : List Bool := rep [false] n
@[simp] theorem O_zero : O 0 = [] := rfl
@[simp] theorem O_succ (n : Nat) : O (n+1) = true :: O n := rfl
@[simp] theorem O_one : O 1 = [true] := rfl
@[simp] theorem z_zero : Zeros 0 = [] := rfl
@[simp] theorem z_succ (n : Nat) : Zeros (n+1) = false :: Zeros n := rfl

def tail (c : Nat) : List Bool := match c with
  | 0 => []
  | c+1 => false :: O (c+1)
/-- r counts the ones strictly to the right of the scanned one. -/
def G (a r c : Nat) : Z0 := ⟨5,[true,false] ++ O a ++ tail c,O r⟩
def E (a r c : Nat) : Z0 := ⟨4,[false] ++ O a ++ [false] ++ O (c+1),O r⟩

theorem fblock (L R : List Bool) : run0 p 3 ⟨5,[true,false]++[true]++L,R⟩ = some ⟨5,[true,false]++L,[false]++R⟩ := rfl
theorem fleft (a r c : Nat) : run0 p (3*a) (G a r c) = some ⟨5,[true,false]++tail c,Zeros a++O r⟩ := by
  exact sweepL p 5 [true,false] [] [true] [false] 3 fblock a (tail c) (O r)
theorem fturnZ (c : Nat) (R : List Bool) : run0 p 4 ⟨5,[true,false]++tail c,false::R⟩ = some ⟨4,[false,false]++O (c+1),false::R⟩ := by
  cases c <;> rfl

theorem eblock (L R : List Bool) : run0 p 1 ⟨4,[false]++L,[false]++R⟩ = some ⟨4,[false]++[true]++L,R⟩ := rfl
theorem eright (a r c : Nat) : run0 p a ⟨4,[false,false]++O (c+1),Zeros a++O r⟩ = some (E a r c) := by
  have h := sweepR p 4 [false] [] [false] [true] 1 eblock a ([false]++O (c+1)) (O r)
  simpa [E,O,Zeros,List.append_assoc] using h

theorem common (a r c : Nat) : run0 p (4*(a+1)+4) (G (a+1) r c) = some (E (a+1) r c) := by
  have h := join0 (fleft (a+1) r c) (fturnZ c (Zeros a++O r))
  have H := join0 h (eright (a+1) r c)
  rw [show 4*(a+1)+4=3*(a+1)+4+(a+1) by omega]
  exact H

theorem large (a r c : Nat) : run0 p 4 (E a (r+1+4) c) = some (G (a+3) (r+1) (c+1)) := by
  have h (L R : List Bool) : run0 p 4 ⟨4,false::L,true::true::true::true::true::R⟩ = some ⟨5,true::false::true::true::true::L,true::R⟩ := rfl
  simpa only [E,G,tail,O_succ,List.cons_append,List.nil_append,List.append_assoc] using h (O a ++ [false] ++ O (c+1)) (O r)

theorem long (a r c : Nat) : run0 p (4*(a+1)+8) (G (a+1) (r+1+4) c) = some (G (a+1+3) (r+1) (c+1)) := by
  rw [show 4*(a+1)+8=4*(a+1)+4+4 by omega]
  exact join0 (common a (r+1+4) c) (large (a+1) r c)

def K (a r c : Nat) : Z0 := ⟨4,O a ++ [false] ++ O (c+1),[false]++O r⟩
theorem turn2 (a c : Nat) : run0 p 4 (E a 1 c) = some (K (a+1) 1 c) := by
  simp only [E,K,O_succ,List.cons_append,List.nil_append]
  rfl
theorem turn3 (a c : Nat) : run0 p 7 (E a 2 c) = some (K (a+4) 1 c) := by
  simp only [E,K,O_succ,List.cons_append,List.nil_append]
  rfl
theorem kblock (L R : List Bool) : run0 p 3 ⟨4,[true]++L,[false]++R⟩ = some ⟨4,L,[false]++[true]++R⟩ := rfl
theorem kleft (a r c : Nat) : run0 p (3*a) (K a r c) = some (K 0 (a+r) c) := by
  have h := sweepL p 4 [] [false] [true] [true] 3 kblock a ([false]++O (c+1)) (O r)
  have add (n m : Nat) : O n ++ O m = O (n+m) := by
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.succ_add]; simp [ih]
  have h' : run0 p (3*a) (K a r c) = some ⟨4,[false]++O (c+1),[false]++(O a++O r)⟩ := by
    simpa only [K,O,List.append_assoc,List.nil_append] using h
  rw [add] at h'
  exact h'

theorem finish (r c : Nat) : run0 p 5 (K 0 (r+4) c) = some (G (c+5) r 0) := by
  simp only [K,G,tail,O_zero,O_succ,List.nil_append,List.cons_append,List.append_nil]
  rfl

theorem short2 (a c : Nat) : run0 p (7*(a+2)+16) (G (a+2) 1 c) = some (G (c+5) a 0) := by
  have h := join0 (common (a+1) 1 c) (turn2 (a+2) c)
  have H := join0 h (kleft (a+2+1) 1 c)
  have J := join0 H (finish a c)
  rw [show 7*(a+2)+16=4*(a+1+1)+4+4+3*(a+2+1)+5 by omega]
  exact J

theorem short3 (a c : Nat) : run0 p (7*(a+1)+28) (G (a+1) 2 c) = some (G (c+5) (a+2) 0) := by
  have h := join0 (common a 2 c) (turn3 (a+1) c)
  have H := join0 h (kleft (a+1+4) 1 c)
  have J := join0 H (finish (a+2) c)
  rw [show 7*(a+1)+28=4*(a+1)+4+7+3*(a+1+4)+5 by omega]
  exact J

def cost : Nat → Nat → Nat
  | 0,_ => 0
  | n+1,a => 4*(a+1)+8 + cost n (a+3)

theorem many (n a r c : Nat) :
    run0 p (cost n a) (G (a+1) (r+1+4*n) c) = some (G (a+1+3*n) (r+1) (c+n)) := by
  induction n generalizing a c with
  | zero => simp [cost,run0]
  | succ n ih =>
    have h := long a (r+4*n) c
    rw [show a+1+3=a+3+1 by omega,show r+4*n+1=r+1+4*n by omega] at h
    have H := join0 h (ih (a+3) (c+1))
    rw [show r+1+4*(n+1)=r+1+4*n+4 by omega]
    rw [show a+3+1+3*n=a+1+3*(n+1) by omega,show c+1+n=c+(n+1) by omega] at H
    exact H

def family (k : Nat) := G (4+2*k) (2+8*k) 0

def cA (k : Nat) := cost (2*k) (3+2*k) + (7*(4+8*k)+28)
def cB (k : Nat) := cost (2*k+1) (4+2*k) + (7*(8+8*k)+16)
def cC (k : Nat) := cost (2*k+1) (5+2*k) + (7*(9+8*k)+28)

theorem stageA (k : Nat) : run0 p (cA k) (family k) = some (G (5+2*k) (5+8*k) 0) := by
  have h := many (2*k) (3+2*k) 1 0
  rw [show 3+2*k+1=4+2*k by omega,show 1+1+4*(2*k)=2+8*k by omega,
    show 4+2*k+3*(2*k)=3+8*k+1 by omega] at h
  simp only [Nat.zero_add] at h
  have H := join0 h (short3 (3+8*k) (2*k))
  simpa only [cA,family,show 2*k+5=5+2*k by omega,show 3+8*k+2=5+8*k by omega,
    show 3+8*k+1=4+8*k by omega] using H

theorem stageB (k : Nat) : run0 p (cB k) (G (5+2*k) (5+8*k) 0) = some (G (6+2*k) (6+8*k) 0) := by
  have h := many (2*k+1) (4+2*k) 0 0
  rw [show 4+2*k+1=5+2*k by omega,show 0+1+4*(2*k+1)=5+8*k by omega,
    show 5+2*k+3*(2*k+1)=6+8*k+2 by omega] at h
  simp only [Nat.zero_add] at h
  have H := join0 h (short2 (6+8*k) (2*k+1))
  simpa only [cB,show 2*k+1+5=6+2*k by omega,show 6+8*k+2=8+8*k by omega] using H

theorem stageC (k : Nat) : run0 p (cC k) (G (6+2*k) (6+8*k) 0) = some (family (k+1)) := by
  have h := many (2*k+1) (5+2*k) 1 0
  rw [show 5+2*k+1=6+2*k by omega,show 1+1+4*(2*k+1)=6+8*k by omega,
    show 6+2*k+3*(2*k+1)=8+8*k+1 by omega] at h
  simp only [Nat.zero_add] at h
  have H := join0 h (short3 (8+8*k) (2*k+1))
  simpa only [cC,family,show 2*k+1+5=4+2*(k+1) by omega,show 8+8*k+2=2+8*(k+1) by omega,
    show 8+8*k+1=9+8*k by omega] using H

def period (k : Nat) := cA k + cB k + cC k

theorem seed : run0 p 35 ⟨0,[],[]⟩ = some (family 0) := rfl

theorem growth (k : Nat) : run0 p (period k) (family k) = some (family (k+1)) :=
  join0 (join0 (stageA k) (stageB k)) (stageC k)

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  never_of_growth p family 35 period seed (by intro k; unfold period cA cB cC; omega) growth m hm

#print axioms growth
#print axioms never
end BB6.Agent6E0OneRE1873
