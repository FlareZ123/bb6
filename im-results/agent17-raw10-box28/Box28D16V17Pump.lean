import C9PairConjugacy

namespace BB6.Agent17.Box28D16V17Pump
open C9Pair
def zeros : Stream := fun _ => false
@[simp] theorem zero_head : zeros 0 = false := rfl
@[simp] theorem zero_pop : pop zeros = zeros := rfl
@[simp] theorem zero_push : push false zeros = zeros := by funext n; cases n <;> rfl
def rep (b : Bool) : Nat → Stream → Stream
  | 0,s => s
  | n+1,s => push b (rep b n s)
def ones (n : Nat) : Stream := rep true n zeros
@[simp] theorem ones_succ (n : Nat) : ones (n+1) = push true (ones n) := rfl

-- Exact code row [8,10,11,22,11,13,16,17,20,4,0,12].
def step (c : Config) : Option Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (right .C false c)
  | .B,false => some (left .C true c)
  | .B,true => some (right .F false c)
  | .C,false => some (left .C true c)
  | .C,true => some (left .D false c)
  | .D,false => some (right .D true c)
  | .D,true => some (left .E false c)
  | .E,false => some (right .E true c)
  | .E,true => some (right .A true c)
  | .F,false => none
  | .F,true => some (right .C true c)

def run : Nat → Config → Option Config
  | 0,c => some c
  | n+1,c => (step c).bind (run n)
theorem run_add (m n : Nat) (c : Config) : run (m+n) c = (run m c).bind (run n) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih =>
    simp only [Nat.succ_add,run]
    cases step c <;> simp [ih]

def root (l r : Nat) : Config := ⟨.E,ones l,true,ones r⟩
def transfer (l r : Nat) : Config := ⟨.E,ones l,true,push false (push false (ones r))⟩
set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem transfer_step (l r : Nat) : run 5 (transfer (l+1) r) = some (transfer l (r+1)) := by
  simp [transfer,run,step,left,right,ones,rep]
theorem transfer_done (r : Nat) : run 8 (transfer 0 r) = some (root 3 r) := by
  simp [transfer,root,run,step,left,right,ones,rep,zeros,push,pop]
theorem transfer_all (l r : Nat) : run (5*l+8) (transfer l r) = some (root 3 (r+l)) := by
  induction l generalizing r with
  | zero => exact transfer_done r
  | succ l ih =>
    rw [show 5*(l+1)+8=5+(5*l+8) by omega,run_add,transfer_step,Option.bind_some,ih]
    congr 2 <;> omega

theorem root_one_entry (l : Nat) : run 5 (root (l+1) 0) = some (transfer l 1) := by
  simp [root,transfer,run,step,left,right,ones,rep,zeros,push,pop]
theorem root_one (l : Nat) : run (5*l+8) (root l 0) = some (root 3 l) := by
  cases l with
  | zero => rfl
  | succ l =>
    rw [show 5*(l+1)+8=5+(5*l+8) by omega,run_add,root_one_entry,Option.bind_some,transfer_all]
    congr 2 <;> omega

theorem root_two_entry (l : Nat) : run 6 (root (l+2) 1) = some (transfer l 2) := by
  simp [root,transfer,run,step,left,right,ones,rep,zeros,push,pop]
theorem root_two (l : Nat) (hl : 2 ≤ l) : run (5*l+4) (root l 1) = some (root 3 l) := by
  obtain ⟨k,rfl⟩ : ∃ k, l=k+2 := ⟨l-2,by omega⟩
  rw [show 5*(k+2)+4=6+(5*k+8) by omega,run_add,root_two_entry,Option.bind_some,transfer_all]
  congr 2 <;> omega
theorem root_four (l : Nat) : run 6 (root l 3) = some (root (l+2) 0) := by
  simp [root,run,step,left,right,ones,rep,zeros,push,pop]
theorem root_six (l : Nat) : run 15 (root l 5) = some (root (l+5) 0) := by
  simp [root,run,step,left,right,ones,rep,zeros,push,pop]
theorem root_large (l r : Nat) : run 15 (root l (r+7)) = some (root (l+7) r) := by
  simp [root,run,step,left,right,ones,rep,zeros,push,pop]
def Good (l r : Nat) : Prop :=
  (3 ≤ l ∧ l%7=3 ∧ (r%7=0 ∨ r%7=1 ∨ r%7=3 ∨ r%7=5)) ∨
  (r=0 ∧ (l%7=5 ∨ l%7=1))

theorem progress (l r : Nat) (h : Good l r) :
    ∃ n l' r', 0 < n ∧ Good l' r' ∧ run n (root l r) = some (root l' r') := by
  unfold Good at h
  rcases h with ⟨hl,hm,hr⟩ | ⟨rfl,hm⟩
  · by_cases hlarge : 7 ≤ r
    · obtain ⟨k,rfl⟩ : ∃ k, r=k+7 := ⟨r-7,by omega⟩
      refine ⟨15,l+7,k,by decide,?_,root_large l k⟩
      unfold Good
      left
      omega
    · have hcases : r=0 ∨ r=1 ∨ r=3 ∨ r=5 := by omega
      rcases hcases with rfl|rfl|rfl|rfl
      · refine ⟨5*l+8,3,l,by omega,?_,root_one l⟩
        unfold Good; omega
      · refine ⟨5*l+4,3,l,by omega,?_,root_two l (by omega)⟩
        unfold Good; omega
      · refine ⟨6,l+2,0,by decide,?_,root_four l⟩
        unfold Good; omega
      · refine ⟨15,l+5,0,by decide,?_,root_six l⟩
        unfold Good; omega
  · refine ⟨5*l+8,3,l,by omega,?_,root_one l⟩
    unfold Good; omega

theorem never_root (n l r : Nat) (hg : Good l r) : run n (root l r) ≠ none := by
  induction n using Nat.strongRecOn generalizing l r with
  | ind n ih =>
    intro h
    obtain ⟨k,l',r',hk,hg',hr⟩ := progress l r hg
    by_cases hn : n ≤ k
    · rw [show k=n+(k-n) by omega,run_add,h] at hr
      contradiction
    · rw [show n=k+(n-k) by omega,run_add,hr,Option.bind_some] at h
      exact ih _ (by omega) l' r' hg' h

def blank : Config := ⟨.A,zeros,false,zeros⟩
theorem init : run 6 blank = some (root 1 0) := by
  simp [blank,root,run,step,left,right,ones,rep]

theorem never_blank (n : Nat) : run n blank ≠ none := by
  intro h
  by_cases hn : n ≤ 6
  · have hi := init
    rw [show 6=n+(6-n) by omega,run_add,h] at hi
    contradiction
  · rw [show n=6+(n-6) by omega,run_add,init,Option.bind_some] at h
    exact never_root _ 1 0 (by unfold Good; omega) h

#print axioms never_blank
end BB6.Agent17.Box28D16V17Pump
