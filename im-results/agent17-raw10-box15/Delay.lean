import Box15Source
import SparseBlankDelay

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent17Box15Delay
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box
open BB6.Agent49BoxBridge BB6.Agent17Raw10BoxFar

def allowedE : List (Fin 25) := [0,3,4,12,18,20,21,22,23,24]

def fixedCode (q : Fin 6) : Fin 25 :=
  match q.val with
  | 0 => 8
  | 1 => 11
  | 2 => 17
  | _ => 11

def zeroDomains (q : Fin 6) : List (Fin 25) :=
  if q = 4 then allowedE
  else if q = 5 then List.finRange 25
  else [fixedCode q]

/-- Only the six zero-symbol rows matter for blank-delay weighting. -/
theorem even_domain (q : Fin 6) :
    raw10Remainder[15]! (q,false) = (zeroDomains q).map decodeCode := by
  rw [BB6.Agent13.Box15.sourceDomainEq]
  revert q
  decide +kernel

def testMachine (e f : Fin 25) : Machine := fun s =>
  if s.2 then none
  else decodeCode (if s.1 = 4 then e else if s.1 = 5 then f else fixedCode s.1)

def delayList (e f : Fin 25) : List Nat :=
  if f = 1 ∨ f = 2 then
    if e = 21 ∨ e = 22 then [0,1,2,3] else [0,1]
  else [0]

def delayMax (e f : Fin 25) : Nat :=
  if f = 1 ∨ f = 2 then
    if e = 21 ∨ e = 22 then 3 else 1
  else 0

/-- Exact graph calculation on the 250 allowed E0,F0 combinations. -/
theorem test_delays (e f : Fin 25) (he : e ∈ allowedE) :
    delays (zeroNext (testMachine e f)) 0 = delayList e f := by
  revert e f
  decide +kernel

theorem source_delay_shape (m : Machine) (hm : Fits raw10Remainder[15]! m) :
    ∃ e f : Fin 25, e ∈ allowedE ∧
      m (4,false) = decodeCode e ∧ m (5,false) = decodeCode f ∧
      delays (zeroNext m) 0 = delayList e f := by
  have getCode (q : Fin 6) : ∃ v, v ∈ zeroDomains q ∧ decodeCode v = m (q,false) := by
    have h := hm (q,false)
    rw [even_domain] at h
    exact List.mem_map.mp h
  obtain ⟨e,he,hee⟩ := getCode 4
  obtain ⟨f,_,hff⟩ := getCode 5
  have he' : e ∈ allowedE := by simpa [zeroDomains] using he
  have hrows (q : Fin 6) : m (q,false) = testMachine e f (q,false) := by
    by_cases h4 : q = 4
    · subst q
      simpa [testMachine] using hee.symm
    · by_cases h5 : q = 5
      · subst q
        simpa [testMachine] using hff.symm
      · obtain ⟨v,hv,hv'⟩ := getCode q
        have heq : v = fixedCode q := by simpa [zeroDomains,h4,h5] using hv
        simpa [testMachine,h4,h5,heq] using hv'.symm
  have hz : zeroNext m = zeroNext (testMachine e f) := by
    funext q
    unfold zeroNext
    rw [hrows q]
  exact ⟨e,f,he',hee.symm,hff.symm,by rw [hz,test_delays e f he']⟩

theorem max_mem (e f : Fin 25) : delayMax e f ∈ delayList e f := by
  by_cases hf : f = 1 ∨ f = 2
  · by_cases he : e = 21 ∨ e = 22 <;> simp [delayList,delayMax,hf,he]
  · simp [delayList,delayMax,hf]

theorem le_max (e f : Fin 25) (d : Nat) (hd : d ∈ delayList e f) :
    d ≤ delayMax e f := by
  by_cases hf : f = 1 ∨ f = 2
  · by_cases he : e = 21 ∨ e = 22 <;>
      simp [delayList,delayMax,hf,he] at hd ⊢ <;> omega
  · simp [delayList,delayMax,hf] at hd ⊢
    omega

theorem max_le_three (e f : Fin 25) : delayMax e f ≤ 3 := by
  by_cases hf : f = 1 ∨ f = 2
  · by_cases he : e = 21 ∨ e = 22 <;> simp [delayMax,hf,he]
  · simp [delayMax,hf]

theorem source_delay_cap (m : Machine) (hm : Fits raw10Remainder[15]! m)
    (d : Nat) (hd : d ∈ delays (zeroNext m) 0) : d ≤ 3 := by
  obtain ⟨e,f,_,_,_,h⟩ := source_delay_shape m hm
  rw [h] at hd
  exact Nat.le_trans (le_max e f d hd) (max_le_three e f)

/-- The largest actual incoming delay, not the generic five-step allowance,
    is both necessary and sufficient for the source machine's weighted bound. -/
theorem source_weighted_iff (m : Machine) (hm : Fits raw10Remainder[15]! m)
    (B : Nat) :
    ∃ e f : Fin 25, e ∈ allowedE ∧
      m (4,false) = decodeCode e ∧ m (5,false) = decodeCode f ∧
      (WeightedBound B m ↔ ∀ k, HaltsAfter m k → k+1+delayMax e f ≤ B) := by
  obtain ⟨e,f,he,hee,hff,hds⟩ := source_delay_shape m hm
  refine ⟨e,f,he,hee,hff,?_⟩
  constructor
  · intro h k hk
    have hd : delayMax e f ∈ delays (zeroNext m) 0 := by
      rw [hds]
      exact max_mem e f
    have hh := h k (delayMax e f) hk hd
    omega
  · intro h k d hk hd
    rw [hds] at hd
    have hd' := le_max e f d hd
    have hh := h k hk
    omega

theorem source_weighted_from_ordinary (m : Machine) (hm : Fits raw10Remainder[15]! m)
    (B : Nat) (h : ∀ k, HaltsAfter m k → k+1 ≤ B) :
    WeightedBound (B+3) m := by
  intro k d hk hd
  have h1 := h k hk
  have h2 := source_delay_cap m hm d hd
  omega

#print axioms even_domain
#print axioms test_delays
#print axioms source_delay_shape
#print axioms source_delay_cap
#print axioms source_weighted_iff
#print axioms source_weighted_from_ordinary

end BB6.Agent17Box15Delay
