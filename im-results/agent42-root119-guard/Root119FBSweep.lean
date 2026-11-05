import Root119BShield
set_option linter.unusedSimpArgs false
namespace BB6Root119

/-- F/0, B/1 retreats left two cells; F's former zero is filled with 1. -/
def fbPair (c : Conf) : Conf :=
  ⟨.F, c.h-2, setBit c.tape c.h true⟩

def fbValid (c : Conf) : Prop :=
  c.q = .F ∧ c.tape c.h = false ∧ c.tape (c.h-1) = true

theorem fb_two_step (c : Conf) (hv : fbValid c) :
    run 2 c = some (fbPair c) := by
  rcases c with ⟨q,h,t⟩
  obtain ⟨hq,h0,h1⟩ := hv
  cases q <;> try contradiction
  change t h = false at h0
  change t (h-1) = true at h1
  have hne : h-1 ≠ h := by omega
  have hh : h-1-1 = h-2 := by omega
  simp [run,next,fbPair,setBit,h0,h1,hne,hh]
  funext x
  simp only [setBit]
  by_cases hx : x=h <;> by_cases hy : x=h-1 <;> simp_all <;> omega

/-- Retreat cannot create any new forbidden four-word entirely left of the head. -/
theorem fb_pair_preserves_noLeft4 (p q r : Bool) (c : Conf)
    (hs : NoLeft4 p q r c) :
    NoLeft4 p q r (fbPair c) := by
  intro x hx hw
  change x+3 < c.h-2 at hx
  change (fbPair c).tape x = p ∧ (fbPair c).tape (x+1) = q ∧
    (fbPair c).tape (x+2) = r ∧ (fbPair c).tape (x+3) = false at hw
  apply hs x (by omega)
  have unchanged (y : Int) (hy : y < c.h) :
      (fbPair c).tape y = c.tape y := by
    simp [fbPair,setBit,show y ≠ c.h by omega]
  refine ⟨?_,?_,?_,?_⟩
  · rw [unchanged x (by omega)] at hw
    exact hw.1
  · rw [unchanged (x+1) (by omega)] at hw
    exact hw.2.1
  · rw [unchanged (x+2) (by omega)] at hw
    exact hw.2.2.1
  · rw [unchanged (x+3) (by omega)] at hw
    exact hw.2.2.2

/-- Recursive exact full-tape F/0-B/1 left retreat across n alternating pairs. -/
def fbMany : Nat → Conf → Conf
  | 0, c => c
  | n+1, c => fbMany n (fbPair c)

def fbExtended (n : Nat) (c : Conf) : Prop :=
  c.q = .F ∧
  ∀ i : Nat, i < n →
    c.tape (c.h-2*(i:Int)) = false ∧
    c.tape (c.h-2*(i:Int)-1) = true

theorem fbExtended_head (n : Nat) (c : Conf) (hv : fbExtended (n+1) c) :
    fbValid c := by
  obtain ⟨hq,hrest⟩ := hv
  obtain ⟨h0,h1⟩ := hrest 0 (by omega)
  exact ⟨hq,by simpa using h0,by simpa using h1⟩

theorem fbExtended_tail (n : Nat) (c : Conf) (hv : fbExtended (n+1) c) :
    fbExtended n (fbPair c) := by
  obtain ⟨hq,hrest⟩ := hv
  refine ⟨rfl,?_⟩
  intro i hi
  obtain ⟨hi0,hi1⟩ := hrest (i+1) (by omega)
  constructor
  · change setBit c.tape c.h true (c.h-2-2*(i:Int)) = false
    rw [show c.h-2-2*(i:Int) = c.h-2*((i+1:Int)) by omega]
    simp only [setBit, if_neg (show c.h-2*((i+1:Int)) ≠ c.h by omega)]
    have heq : c.h-2*((i+1:Int)) = c.h-2*((i+1:Nat):Int) := by omega
    rw [heq]
    exact hi0
  · change setBit c.tape c.h true (c.h-2-2*(i:Int)-1) = true
    rw [show c.h-2-2*(i:Int)-1 = c.h-2*((i+1:Int))-1 by omega]
    simp only [setBit, if_neg (show c.h-2*((i+1:Int))-1 ≠ c.h by omega)]
    have heq : c.h-2*((i+1:Int))-1 = c.h-2*((i+1:Nat):Int)-1 := by omega
    rw [heq]
    exact hi1

theorem fb_run_add (m n : Nat) (c : Conf) :
    run (m+n) c = (run m c).bind (run n) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih =>
    have heq : m+1+n=(m+n)+1 := by omega
    rw [heq]
    simp only [run, Option.bind_assoc]
    congr 1
    funext y
    exact ih y

/-- Exactly 2n source instructions, for every n and arbitrary exterior. -/
theorem fb_two_n (n : Nat) (c : Conf) (hv : fbExtended n c) :
    run (2*n) c = some (fbMany n c) := by
  induction n generalizing c with
  | zero => simp [run,fbMany]
  | succ n ih =>
    have hhead := fbExtended_head n c hv
    have htail := fbExtended_tail n c hv
    have htwo := fb_two_step c hhead
    have hrest := ih (fbPair c) htail
    have hsplit : 2*(n+1) = 2+2*n := by omega
    rw [hsplit,fb_run_add,htwo]
    simpa [fbMany] using hrest

theorem fb_many_preserves_noLeft4 (p q r : Bool) (n : Nat) (c : Conf)
    (hv : fbExtended n c) (hs : NoLeft4 p q r c) :
    NoLeft4 p q r (fbMany n c) := by
  induction n generalizing c with
  | zero => simpa [fbMany] using hs
  | succ n ih =>
    have htail := fbExtended_tail n c hv
    have hnew := fb_pair_preserves_noLeft4 p q r c hs
    simpa [fbMany] using ih (fbPair c) htail hnew

theorem reached_fb_sweep_safe (n : Nat) (c : Conf)
    (hc : Reach c) (hv : fbExtended n c) (hs : NoLeft4 true true false c) :
    Reach (fbMany n c) ∧ NoLeft4 true true false (fbMany n c) := by
  exact ⟨reachable_of_run (2*n) c (fbMany n c) hc (fb_two_n n c hv),
    fb_many_preserves_noLeft4 true true false n c hv hs⟩

#print axioms BB6Root119.fb_two_n
#print axioms BB6Root119.fb_many_preserves_noLeft4
#print axioms BB6Root119.reached_fb_sweep_safe
end BB6Root119
