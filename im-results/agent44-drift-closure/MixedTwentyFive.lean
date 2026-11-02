import DirectedDrift
import LeafRules

namespace BB6Coverage

/-- A/0 is an assigned 0RB; B/0 is genuinely unassigned and actually
    consulted after exactly one physical move. B/1 and C-F/0 halt. -/
def mixedParent : PartialMachine := fun slot =>
  if slot = (0, false) then some (some ⟨false,true,1⟩)
  else if slot = (1, true) then some none
  else if slot = (2, false) then some none
  else if slot = (3, false) then some none
  else if slot = (4, false) then some none
  else if slot = (5, false) then some none
  else none

private theorem raw_first (m : Machine)
  (hA : m (0,false) = some ⟨false,true,1⟩) :
  run m 1 blank = some {state:=1,head:=1,tape:=fun _=>false} := by
  simp [run,rawStep,readSlot,blank,applyMove,hA]

private theorem raw_second (m : Machine) (w r : Bool) (q : Fin 6)
  (hA : m (0,false) = some ⟨false,true,1⟩)
  (hB : m (1,false) = some ⟨w,r,q⟩) :
  run m 2 blank = some
    {state:=q, head:=if r then 2 else 0, tape:=fun x=>if x=1 then w else false} := by
  change (run m 1 blank).bind (rawStep m) = _
  rw [raw_first m hA]
  cases r
  · simp [rawStep,readSlot,hB,applyMove]
  · simp [rawStep,readSlot,hB,applyMove]

private theorem raw_early_halt (m : Machine)
  (hA : m (0,false) = some ⟨false,true,1⟩)
  (hB : m (1,false) = none) : HaltsAfter m 1 := by
  constructor
  · simp [raw_first m hA]
  · change (run m 1 blank).bind (rawStep m) = none
    rw [raw_first m hA]
    simp [rawStep,readSlot,hB]

private theorem raw_third_halt (m : Machine) (w r : Bool) (q : Fin 6)
  (hA : m (0,false) = some ⟨false,true,1⟩)
  (hB : m (1,false) = some ⟨w,r,q⟩)
  (hq : m (q,false) = none) : HaltsAfter m 2 := by
  constructor
  · simp [raw_second m w r q hA hB]
  · change (run m 2 blank).bind (rawStep m) = none
    rw [raw_second m w r q hA hB]
    cases r <;> simp [rawStep,readSlot,hq]

private theorem raw_third_B_one (m : Machine)
  (hA : m (0,false) = some ⟨false,true,1⟩)
  (hB : m (1,false) = some ⟨true,false,0⟩) :
  run m 3 blank = some
    {state:=1,head:=1,tape:=fun x=>if x=1 then true else false} := by
  change (run m 2 blank).bind (rawStep m) = _
  rw [raw_second m true false 0 hA hB]
  simp [rawStep,readSlot,hA,applyMove]
  funext x
  by_cases hx : x = 0
  · simp [hx]
  · simp [hx]

private theorem raw_fourth_halt (m : Machine)
  (hA : m (0,false) = some ⟨false,true,1⟩)
  (hB : m (1,false) = some ⟨true,false,0⟩)
  (hB1 : m (1,true) = none) : HaltsAfter m 3 := by
  constructor
  · simp [raw_third_B_one m hA hB]
  · change (run m 3 blank).bind (rawStep m) = none
    rw [raw_third_B_one m hA hB]
    simp [rawStep,readSlot,hB1]

private theorem raw_left_blank_cycle (m : Machine)
  (hA : m (0,false) = some ⟨false,true,1⟩)
  (hB : m (1,false) = some ⟨false,false,0⟩) :
  run m 2 blank = some blank := by
  change (run m 1 blank).bind (rawStep m) = _
  rw [raw_first m hA]
  simp [rawStep,readSlot,hB,applyMove,blank]

private theorem raw_left_B_two (m : Machine) (w : Bool)
  (hA : m (0,false) = some ⟨false,true,1⟩)
  (hB : m (1,false) = some ⟨w,false,1⟩) :
  run m 2 blank = some
    {state:=1,head:=0,tape:=fun x=>if x=1 then w else false} := by
  simpa using raw_second m w false 1 hA hB

private theorem raw_right_A_never (m : Machine) (w : Bool)
  (hA : m (0,false) = some ⟨false,true,1⟩)
  (hB : m (1,false) = some ⟨w,true,0⟩) : NeverHalts m := by
  apply directed_drift_never m (fun s => s=0 ∨ s=1) true (Or.inl rfl)
  intro s hs
  rcases hs with hs | hs
  · subst s
    exact ⟨false, 1, hA, Or.inr rfl⟩
  · subst s
    exact ⟨w, 0, hB, Or.inl rfl⟩

private theorem raw_right_B_never (m : Machine) (w : Bool)
  (hA : m (0,false) = some ⟨false,true,1⟩)
  (hB : m (1,false) = some ⟨w,true,1⟩) : NeverHalts m := by
  apply prefix_drift_never m (fun s => s=1) true 1
    {state:=1,head:=1,tape:=fun _=>false} (raw_first m hA) rfl
    (by intro x hx; rfl)
  intro s hs
  subst s
  exact ⟨w, 1, hB, rfl⟩

private theorem raw_left_B_never (m : Machine) (w : Bool)
  (hA : m (0,false) = some ⟨false,true,1⟩)
  (hB : m (1,false) = some ⟨w,false,1⟩) : NeverHalts m := by
  apply prefix_drift_never m (fun s => s=1) false 2
    {state:=1,head:=0,tape:=fun x=>if x=1 then w else false}
    (raw_left_B_two m w hA hB) rfl
    (by
      intro x hx
      have h : x ≠ 1 := by simp [Ahead] at hx; omega
      simp [h])
  intro s hs
  subst s
  exact ⟨w, 1, hB, rfl⟩

private theorem raw_left_A_never (m : Machine)
  (hA : m (0,false) = some ⟨false,true,1⟩)
  (hB : m (1,false) = some ⟨false,false,0⟩) : NeverHalts m := by
  exact eventually_cycle_never m blank 0 2 (by decide) rfl
    (raw_left_blank_cycle m hA hB)

/-- Every one of the 25 possible, genuinely visited B/0 outcomes leads to
    either a certified nonhalting infinite run or a halt by step four. -/
theorem mixed_decided (B : Nat) (hbound : 4 ≤ B)
    (m : Machine) (hm : compatible mixedParent m) : DecidedBelow B m := by
  have hA : m (0,false) = some ⟨false,true,1⟩ :=
    hm (0,false) (some ⟨false,true,1⟩) (by decide)
  have hB1 : m (1,true) = none := hm (1,true) none (by decide)
  have h2 : m (2,false) = none := hm (2,false) none (by decide)
  have h3 : m (3,false) = none := hm (3,false) none (by decide)
  have h4 : m (4,false) = none := hm (4,false) none (by decide)
  have h5 : m (5,false) = none := hm (5,false) none (by decide)
  cases hB : m (1,false) with
  | none =>
      exact Or.inr ⟨1, by omega, raw_early_halt m hA hB⟩
  | some mv =>
      rcases mv with ⟨w,r,q⟩
      have hcases : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by
        exact (show ∀ u : Fin 6, u=0 ∨ u=1 ∨ u=2 ∨ u=3 ∨ u=4 ∨ u=5 from by decide) q
      rcases hcases with h0 | h1 | h2q | h3q | h4q | h5q
      · subst q
        cases r with
        | true => exact Or.inl (raw_right_A_never m w hA hB)
        | false =>
          cases w with
          | false => exact Or.inl (raw_left_A_never m hA hB)
          | true => exact Or.inr ⟨3, by omega, raw_fourth_halt m hA hB hB1⟩
      · subst q
        cases r with
        | true => exact Or.inl (raw_right_B_never m w hA hB)
        | false => exact Or.inl (raw_left_B_never m w hA hB)
      · subst q
        exact Or.inr ⟨2, by omega, raw_third_halt m w r 2 hA hB h2⟩
      · subst q
        exact Or.inr ⟨2, by omega, raw_third_halt m w r 3 hA hB h3⟩
      · subst q
        exact Or.inr ⟨2, by omega, raw_third_halt m w r 4 hA hB h4⟩
      · subst q
        exact Or.inr ⟨2, by omega, raw_third_halt m w r 5 hA hB h5⟩

/-- An actual all-25-children proof tree at the first unknown *reachable*
    slot, rather than a branch on a slot the computation never consults. -/
theorem mixed_reached_branch (B : Nat) (hbound : 4 ≤ B) :
    Cover (DecidedBelow B) mixedParent := by
  apply Cover.branch mixedParent (1,false) (by decide)
  intro t ht
  apply Cover.leaf
  intro m hm
  have hp : compatible mixedParent m :=
    ((compatible_refine_iff mixedParent m (1,false) (by decide) t).mp hm).1
  exact mixed_decided B hbound m hp

#print axioms mixed_decided
#print axioms mixed_reached_branch
#print axioms raw_early_halt
#print axioms raw_third_halt
#print axioms raw_fourth_halt

end BB6Coverage
