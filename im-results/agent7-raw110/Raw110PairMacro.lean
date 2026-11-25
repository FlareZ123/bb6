import SweepPumping
set_option maxHeartbeats 0
namespace BB6.Agent7Raw110Pair
open BB6Coverage BB6Coverage.Agent31Pump

/-- The two final block-FAR misses differ solely in the F1 row.
    false = child5/161, true = child5/790. -/
def table (slow : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => none
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,1⟩)
  | 4,true => some (some ⟨false,false,2⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some (if slow then ⟨true,true,3⟩ else ⟨false,false,5⟩))
  | _,_ => none

/-- Every visit to F in the fast machine has just written a zero to its
    immediate right. Retaining that explicit zero avoids finite-list padding
    ambiguities in the five-step exact zipper identity. -/
def Good (z : Z0) : Prop := z.q = 5 → ∃ R, z.r = false::R

def blankZ : Z0 := ⟨0,[],[]⟩

theorem good_blank : Good blankZ := by
  intro h
  contradiction

theorem five (L R : List Bool) :
    run0 (table true) 5 ⟨5,true::L,false::R⟩ =
      run0 (table false) 1 ⟨5,true::L,false::R⟩ := by rfl

theorem good_step {z w : Z0} (h : step0 (table false) z = some w) : Good w := by
  rcases z with ⟨q,L,R⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;>
    cases L with
    | nil => simp [step0,table,move0,show (3:Fin 6).val = 3 by decide,show (4:Fin 6).val = 4 by decide,show (5:Fin 6).val = 5 by decide] at h; subst w; simp [Good]
    | cons b L => cases b <;> simp [step0,table,move0,show (3:Fin 6).val = 3 by decide,show (4:Fin 6).val = 4 by decide,show (5:Fin 6).val = 5 by decide] at h <;> subst w <;> simp [Good]

theorem simulate_step {z w : Z0} (hg : Good z)
    (h : step0 (table false) z = some w) :
    ∃ t, 0 < t ∧ run0 (table true) t z = some w := by
  rcases z with ⟨q,L,R⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals try (
    cases L with
    | nil => exact ⟨1,by decide,h⟩
    | cons b L => cases b <;> exact ⟨1,by decide,h⟩)
  cases L with
  | nil => exact ⟨1,by decide,h⟩
  | cons b L =>
    cases b with
    | false => exact ⟨1,by decide,h⟩
    | true =>
      obtain ⟨S,hR⟩ := hg rfl
      change R = false::S at hR
      subst R
      exact ⟨5,by decide,by rw [five]; exact h⟩

theorem same_failure {z : Z0} (h : step0 (table false) z = none) :
    step0 (table true) z = none := by
  rcases z with ⟨q,L,R⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;>
    cases L with
    | nil => simp [step0,table,move0,show (3:Fin 6).val = 3 by decide,show (4:Fin 6).val = 4 by decide,show (5:Fin 6).val = 5 by decide] at h
    | cons b L => cases b <;> simp [step0,table,move0,show (3:Fin 6).val = 3 by decide,show (4:Fin 6).val = 4 by decide,show (5:Fin 6).val = 5 by decide] at h ⊢

/-- Each successful fast primitive step expands to one or five slow
    primitive steps, with exactly the same head-relative configuration. -/
theorem simulate_prefix (n : Nat) (z w : Z0) (hg : Good z)
    (h : run0 (table false) n z = some w) :
    ∃ t, n ≤ t ∧ run0 (table true) t z = some w := by
  induction n generalizing z with
  | zero => exact ⟨0,by omega,h⟩
  | succ n ih =>
    cases hs : step0 (table false) z with
    | none => simp [run0,hs] at h
    | some x =>
      have htail : run0 (table false) n x = some w := by simpa [run0,hs] using h
      obtain ⟨a,ha,hfirst⟩ := simulate_step hg hs
      obtain ⟨b,hb,hlast⟩ := ih x (good_step hs) htail
      exact ⟨a+b,by omega,join0 hfirst hlast⟩

def Forever (slow : Bool) : Prop := ∀ n, ∃ z, run0 (table slow) n blankZ = some z

theorem forever_iff : Forever false ↔ Forever true := by
  constructor
  · intro hf n
    obtain ⟨z,hz⟩ := hf n
    obtain ⟨t,ht,hr⟩ := simulate_prefix n blankZ z good_blank hz
    rw [show t=n+(t-n) by omega,run0_add] at hr
    cases h : run0 (table true) n blankZ with
    | none => simp [h] at hr
    | some x => exact ⟨x,rfl⟩
  · intro hs n
    induction n with
    | zero => exact ⟨blankZ,rfl⟩
    | succ n ih =>
      obtain ⟨z,hz⟩ := ih
      rw [show n+1=n+1 by rfl,run0_add,hz]
      cases h : step0 (table false) z with
      | some x => exact ⟨x,by simp [run0,h]⟩
      | none =>
        obtain ⟨t,ht,hr⟩ := simulate_prefix n blankZ z good_blank hz
        obtain ⟨w,hw⟩ := hs (t+1)
        rw [run0_add,hr] at hw
        simp [run0,same_failure h] at hw

#print axioms five
#print axioms simulate_prefix
#print axioms forever_iff
end BB6.Agent7Raw110Pair
