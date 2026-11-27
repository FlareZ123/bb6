import SweepPumping
import WeightedTNFCertificate
set_option maxHeartbeats 0
namespace BB6.Agent44Extra68Sweep
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent13BlankDelay

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,false,3⟩)
  | 3,false => some (some ⟨true,true,4⟩)
  | 3,true => some (some ⟨true,false,2⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨true,true,3⟩)
  | _,_ => none

def U : List Bool := [true,false,true]
def I : List Bool := [true,false,false,true,false,false]
def O : List Bool := U++U
def F : List Bool := [false,true,true,false,true]
def J : List Bool := F++[true]
def K : List Bool := [false,false,true,false,false,true]
def P : List Bool := [false,true,false,false,false]

def cfg (k : Nat) : Z0 := ⟨3,[],P++rep I k⟩

theorem enter (R : List Bool) :
  run0 table 3 ⟨3,[],P++R⟩ = some ⟨3,false::U,[false,false]++R⟩ := by rfl

theorem oneR (L R : List Bool) :
  run0 table 16 ⟨3,[false]++L,[false,false]++I++R⟩ =
    some ⟨3,[false]++O++L,[false,false]++R⟩ := by rfl

theorem turn (L : List Bool) :
  run0 table 10 ⟨3,false::L,[false,false]⟩ = some ⟨3,U++L,[false,false]⟩ := by rfl

theorem oneL (L R : List Bool) :
  run0 table 10 ⟨3,[true]++J++L,[]++R⟩ = some ⟨3,[true]++L,[]++K++R⟩ := by rfl

theorem finish (R : List Bool) :
  run0 table 17 ⟨3,O,[false,false]++R⟩ = some ⟨3,[],P++I++R⟩ := by rfl

/-- Rotate a repeated word by an arbitrary prefix, rather than one bit. -/
theorem rotateWord (A B : List Bool) (n : Nat) :
    rep (A++B) n ++ A = A ++ rep (B++A) n := by
  induction n with
  | zero => simp [rep]
  | succ n ih => simp only [rep,List.append_assoc]; rw [ih]

theorem commuteU (k : Nat) : U++rep O k = rep O k++U := by
  induction k with
  | zero => simp [rep]
  | succ k ih => simp only [rep,O,List.append_assoc]; change U++U++U++rep O k = U++U++rep O k++U; simpa only [List.append_assoc] using congrArg (fun x => U++U++x) ih

theorem leftShape (k : Nat) : U++rep O k++U = [true]++rep J k++F := by
  rw [commuteU]
  change (rep O k++U)++U = _
  rw [List.append_assoc]
  change rep ([true]++F) k ++ ([true]++F) = [true]++rep (F++[true]) k++F
  rw [← List.append_assoc, rotateWord]

theorem rightShape (k : Nat) : rep K k++[false,false] = [false,false]++rep I k := by
  exact rotateWord [false,false] [true,false,false,true] k

theorem growth (k : Nat) : run0 table (30+26*k) (cfg k) = some (cfg (k+1)) := by
  have h1 := enter (rep I k)
  have h2 := sweepR table 3 [false] [false,false] I O 16 oneR k U []
  simp only [List.append_nil] at h2
  have h3 := turn (rep O k++U)
  have h12 := join0 h1 h2
  have h123 := join0 h12 h3
  rw [← List.append_assoc U (rep O k) U, leftShape] at h123
  have h4 := sweepL table 3 [true] [] J K 10 oneL k F [false,false]
  simp only [List.nil_append] at h4
  have h1234 := join0 h123 h4
  rw [rightShape] at h1234
  have h5 := finish (rep I k)
  have h := join0 h1234 h5
  rw [show 30+26*k=3+16*k+10+10*k+17 by omega]
  exact h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table cfg 13 (fun k => 30+26*k) (by rfl) (by intro k; omega) growth m hm

theorem safe (B : Nat) (m : Machine) (hm : compatible table m) : WeightedBound B m :=
  weighted_never B m (never m hm)

#print axioms never
#print axioms safe
end BB6.Agent44Extra68Sweep
