import Root119EvenSweep

namespace BB6Root119

/-- The final F1 step on any nonempty even run erased the penultimate cell. -/
theorem evenSweepTape_last (n : Nat) (t : Int → Bool) (h : Int) :
    evenSweepTape (n+1) t h (h+2*(n+1)-1) = false := by
  induction n generalizing t h with
  | zero =>
    simp [evenSweepTape,setBit]
    omega
  | succ n ih =>
    change evenSweepTape (n+1) (setBit (setBit t h true) (h+1) false) (h+2)
      (h+2*(n+2)-1) = false
    have he : h+2*(n+2)-1 = (h+2)+2*(n+1)-1 := by omega
    rw [he]
    exact ih (setBit (setBit t h true) (h+1) false) (h+2)

/-- Any positive even run of ones terminated by zero has a uniform D0,E0,A0
    triple, ending in B on the cell immediately right of the run. -/
theorem evenSweep_to_B (n : Nat) (t : Int → Bool) (h : Int)
    (ones : ∀ j : Nat, j < 2*(n+1) → t (h+(j:Int)) = true)
    (zero : t (h+(2*(n+1):Int)) = false) :
    ∃ u, shuttleRun (2*(n+1)+3) ⟨.D,h,t⟩ = some u ∧
      u.q = .B ∧ u.h = h+2*(n+1)+1 := by
  let p : Int := h+2*(n+1)
  let v := evenSweepTape (n+1) t h
  have ds := evenSweep (n+1) t h ones
  have hz : v p = false := by
    have hh := evenSweepTape_right (n+1) t h p (by dsimp [p]; omega)
    dsimp [p,v] at hh ⊢
    exact hh.trans zero
  have hl : v (p-1) = false := by
    dsimp [p,v]
    exact evenSweepTape_last n t h
  let v1 := setBit v p false
  let v2 := setBit v1 (p-1) true
  let v3 := setBit v2 p true
  have hleft : v1 (p-1) = false := by
    have hne : p-1 ≠ p := by omega
    simp [v1,setBit,hne,hl]
  have hright : v2 p = false := by
    have hne : p ≠ p-1 := by omega
    simp [v2,setBit,hne,v1,hz]
  have hs1 : next ⟨Q.D,p,v⟩ = some ⟨Q.E,p-1,v1⟩ := by
    simp [next,hz,v1]
  have hs2 : next ⟨Q.E,p-1,v1⟩ = some ⟨Q.A,p,v2⟩ := by
    simp [next,hleft,v2]
  have hs3 : next ⟨Q.A,p,v2⟩ = some ⟨Q.B,p+1,v3⟩ := by
    simp [next,hright,v3]
  have ht : shuttleRun 3 ⟨Q.D,p,v⟩ = some ⟨Q.B,p+1,v3⟩ := by
    simp [shuttleRun,hs1,hs2,hs3]
  refine ⟨⟨.B,p+1,v3⟩,?_,rfl,?_⟩
  · calc
      shuttleRun (2*(n+1)+3) ⟨.D,h,t⟩ =
        (shuttleRun (2*(n+1)) ⟨.D,h,t⟩).bind (shuttleRun 3) := by
          rw [shuttleRun_add]
      _ = shuttleRun 3 ⟨.D,p,v⟩ := by
        simpa [p,v] using congrArg (fun o => o.bind (shuttleRun 3)) ds
      _ = some ⟨.B,p+1,v3⟩ := ht
  · dsimp [p]

#print axioms BB6Root119.evenSweep_to_B
end BB6Root119
