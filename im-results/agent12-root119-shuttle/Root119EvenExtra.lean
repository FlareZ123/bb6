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



/-- An even sweep preserves every cell strictly left of its start. -/
theorem evenSweepTape_left_of_lt (n : Nat) (t : Int → Bool) (h x : Int)
    (hx : x < h) : evenSweepTape n t h x = t x := by
  induction n generalizing t h x with
  | zero => rfl
  | succ n ih =>
      change evenSweepTape n (setBit (setBit t h true) (h+1) false) (h+2) x = t x
      have hx' : x < h+2 := by omega
      rw [ih (setBit (setBit t h true) (h+1) false) (h+2) x hx']
      have h0 : x ≠ h := by omega
      have h1 : x ≠ h+1 := by omega
      simp [setBit,h0,h1]

/-- The D/even cells of an even sweep are all one. -/
theorem evenSweepTape_evenCell (n : Nat) (t : Int → Bool) (h : Int)
    (j : Nat) (hj : j < n) :
    evenSweepTape n t h (h+2*(j:Int)) = true := by
  induction n generalizing t h j with
  | zero => omega
  | succ n ih =>
      cases j with
      | zero =>
          simp only [evenSweepTape]
          have hidx : h+2*((0:Nat):Int) = h := by omega
          rw [hidx]
          have hleft := evenSweepTape_left_of_lt n
            (setBit (setBit t h true) (h+1) false) (h+2) h (by omega)
          rw [hleft]
          simp [setBit,show h ≠ h+1 by omega]
      | succ j =>
          have hj' : j < n := by omega
          have hidx : h+2*((j+1:Nat):Int) = (h+2)+2*(j:Int) := by omega
          simp only [evenSweepTape]
          rw [hidx]
          exact ih (setBit (setBit t h true) (h+1) false) (h+2) j hj'

/-- The F/odd cells of an even sweep are all zero. -/
theorem evenSweepTape_oddCell (n : Nat) (t : Int → Bool) (h : Int)
    (j : Nat) (hj : j < n) :
    evenSweepTape n t h (h+2*(j:Int)+1) = false := by
  induction n generalizing t h j with
  | zero => omega
  | succ n ih =>
      cases j with
      | zero =>
          simp only [evenSweepTape]
          have hidx : h+2*((0:Nat):Int)+1 = h+1 := by omega
          rw [hidx]
          have hleft := evenSweepTape_left_of_lt n
            (setBit (setBit t h true) (h+1) false) (h+2) (h+1) (by omega)
          rw [hleft]
          simp [setBit,show h+1 ≠ h by omega]
      | succ j =>
          have hj' : j < n := by omega
          have hidx : h+2*((j+1:Nat):Int)+1 = (h+2)+2*(j:Int)+1 := by omega
          simp only [evenSweepTape]
          rw [hidx]
          exact ih (setBit (setBit t h true) (h+1) false) (h+2) j hj'

#print axioms BB6Root119.evenSweepTape_left_of_lt
#print axioms BB6Root119.evenSweepTape_evenCell
#print axioms BB6Root119.evenSweepTape_oddCell

#print axioms BB6Root119.evenSweep_to_B
end BB6Root119
