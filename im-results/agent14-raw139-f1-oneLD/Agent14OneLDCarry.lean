import SweepPumping
import F0SiblingCover
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent14OneLD.H25
open BB6Coverage BB6Coverage.Agent31Pump

def ctr : PartialMachine := FAR.fromCodes [7,11,11,24,14,21,3,16,12,11,3,14]
inductive Digit where
  | lowEnd | highEnd | low (d : Digit) | high (d : Digit)
  deriving Repr

def body : Digit → List Bool
  | .lowEnd => [true,true,true]
  | .highEnd => [true,true,true,true]
  | .low d => [true,true,true,false,false] ++ body d
  | .high d => [true,true,true,true,false] ++ body d

def tail1 (d : Digit) : List Bool := false :: body d
def tail2 (d : Digit) : List Bool := false :: tail1 d

def next : Digit → Digit
  | .lowEnd => .highEnd
  | .highEnd => .low .lowEnd
  | .low d => .high d
  | .high d => .low (next d)

def coreCost : Digit → Nat
  | .lowEnd => 29
  | .highEnd => 41
  | .low _ => 29
  | .high d => 7 + coreCost d + 11

/-- The complete recursive carry, for an arbitrary left exterior. -/
theorem carry (d : Digit) (L : List Bool) :
    run0 ctr (coreCost d) ⟨2,[true,true,true,true,true] ++ L,tail1 d⟩ =
      some ⟨4,L,[false,true,true,true] ++ tail2 (next d)⟩ := by
  induction d generalizing L with
  | lowEnd => rfl
  | highEnd => rfl
  | low d => rfl
  | high d ih =>
    have h1 : run0 ctr 7 ⟨2,[true,true,true,true,true] ++ L,tail1 (.high d)⟩ =
      some ⟨2,[true,true,true,true,true] ++ ([false,true,true,true,true] ++ L),tail1 d⟩ := rfl
    have h2 := ih ([false,true,true,true,true] ++ L)
    have h3 : run0 ctr 11
      ⟨4,[false,true,true,true,true] ++ L,[false,true,true,true] ++ tail2 (next d)⟩ =
      some ⟨4,L,[false,true,true,true] ++ tail2 (.low (next d))⟩ := rfl
    exact join0 (join0 h1 h2) h3

def ones (n : Nat) : List Bool := rep [true] n

theorem ones_add (m n : Nat) : ones (m+n) = ones m ++ ones n := by
  induction m with
  | zero => simp [ones,rep]
  | succ m ih =>
    rw [show m+1+n=m+n+1 by omega]
    change true :: ones (m+n) = true :: (ones m ++ ones n)
    rw [ih]

theorem pair_rep (n : Nat) : rep [true,true] n = ones (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1)=2+2*n by omega,ones_add]
    change [true,true] ++ rep [true,true] n = [true,true] ++ ones (2*n)
    rw [ih]

theorem enter (R : List Bool) : run0 ctr 7 ⟨4,[],false::true::true::R⟩ = some ⟨0,ones 5,R⟩ := rfl

theorem rightPairs (k : Nat) (R : List Bool) :
    run0 ctr (4*k) ⟨0,ones 5,ones (2*k) ++ R⟩ = some ⟨0,ones (2*k+5),R⟩ := by
  have h := sweepR ctr 0 [true] [] [true,true] [true,true] 4 (by intro L R; rfl) k (ones 4) R
  rw [pair_rep] at h
  rw [show 2*k+5=1+(2*k+4) by omega,ones_add 1,ones_add (2*k)]
  simp only [ones,rep,List.nil_append,List.append_assoc,List.cons_append] at h ⊢; exact h

theorem leftOnes (k : Nat) (R : List Bool) :
    run0 ctr (3*k) ⟨4,ones k,false::R⟩ = some ⟨4,[],false::(ones k ++ R)⟩ := by
  simpa only [List.nil_append,List.append_nil,List.cons_append,ones] using
    (sweepL ctr 4 [] [false] [true] [true] 3 (by intro L R; rfl) k [] R)

theorem phase1 (n : Nat) (d : Digit) :
    run0 ctr (20*n+42) ⟨4,[],false::(ones (6+4*n) ++ tail2 d)⟩ =
      some ⟨4,[],false::(ones (9+4*n) ++ tail1 d)⟩ := by
  let k := 2+2*n
  have h1 := enter (ones (2*k) ++ tail2 d)
  have h2 := rightPairs k (tail2 d)
  have h3 : run0 ctr 3 ⟨0,ones (2*k+5),tail2 d⟩ =
      some ⟨4,ones (2*k+4),false::true::tail1 d⟩ := by
    rw [show 2*k+5=2*k+4+1 by omega]
    rfl
  have h4 := leftOnes (2*k+4) (true::tail1 d)
  have h := join0 (join0 (join0 h1 h2) h3) h4
  have hc : 7+4*k+3+3*(2*k+4)=20*n+42 := by dsimp [k]; omega
  rw [hc] at h
  have e1 : 6+4*n = 2+2*k := by dsimp [k]; omega
  have e2 : 9+4*n = (2*k+4)+1 := by dsimp [k]; omega
  rw [e1,e2,ones_add 2,ones_add (2*k+4)]
  simp only [ones,rep,List.append_assoc,List.cons_append,List.nil_append] at h ⊢; exact h

theorem phase2 (n : Nat) (d : Digit) :
    run0 ctr (20*n+41+coreCost d) ⟨4,[],false::(ones (9+4*n) ++ tail1 d)⟩ =
      some ⟨4,[],false::(ones (10+4*n) ++ tail2 (next d))⟩ := by
  let k := 3+2*n
  have h1 := enter (ones (2*k) ++ true::tail1 d)
  have h2 := rightPairs k (true::tail1 d)
  have h3 : run0 ctr 1 ⟨0,ones (2*k+5),true::tail1 d⟩ =
      some ⟨2,ones (2*k+6),tail1 d⟩ := by
    rw [show 2*k+6=2*k+5+1 by omega]
    rw [show 2*k+5=2*k+4+1 by omega]
    rfl
  have h4 := carry d (ones (2*k+1))
  have eq : ones (2*k+6) = [true,true,true,true,true] ++ ones (2*k+1) := by
    rw [show 2*k+6=5+(2*k+1) by omega,ones_add]
    rfl
  rw [← eq] at h4
  have h5 := leftOnes (2*k+1) ([true,true,true] ++ tail2 (next d))
  have h := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  have hc : 7+4*k+1+coreCost d+3*(2*k+1)=20*n+41+coreCost d := by dsimp [k]; omega
  rw [hc] at h
  have e1 : 9+4*n=2+(2*k+1) := by dsimp [k]; omega
  have e2 : 10+4*n=(2*k+1)+3 := by dsimp [k]; omega
  rw [e1,e2,ones_add 2,ones_add (2*k) 1,ones_add (2*k+1)]
  simp only [ones,rep,List.append_assoc,List.cons_append,List.nil_append] at h ⊢; exact h

def digitAt : Nat → Digit
  | 0 => .lowEnd
  | n+1 => next (digitAt n)
def family (n : Nat) : Z0 := ⟨4,[],false::(ones (6+4*n) ++ tail2 (digitAt n))⟩
def cost (n : Nat) : Nat := 40*n+83+coreCost (digitAt n)
theorem entry : run0 ctr 73 ⟨0,[],[]⟩ = some (family 0) := rfl
theorem growth (n : Nat) : run0 ctr (cost n) (family n) = some (family (n+1)) := by
  have h := join0 (phase1 n (digitAt n)) (phase2 n (digitAt n))
  rw [show 20*n+42+(20*n+41+coreCost (digitAt n))=cost n by unfold cost; omega] at h
  unfold family
  rw [show 6+4*(n+1)=10+4*n by omega]
  exact h
theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m :=
  never_of_growth ctr family 73 cost entry (fun k => by unfold cost; omega) growth m hm
#print axioms never
#print axioms carry
#print axioms growth
end BB6.Agent14OneLD.H25
