import Root119ShuttleSupport

namespace BB6Root119

/-- Tape transformation after n alternating D1/F1 pairs. -/
def evenSweepTape : Nat → (Int → Bool) → Int → (Int → Bool)
  | 0, t, _ => t
  | n+1, t, h => evenSweepTape n (setBit (setBit t h true) (h+1) false) (h+2)

/-- Every D1/F1 pair consumes precisely two ones, advancing D by two cells. -/
theorem evenSweep (n : Nat) (t : Int → Bool) (h : Int)
    (ones : ∀ j : Nat, j < 2*n → t (h+(j:Int)) = true) :
    shuttleRun (2*n) ⟨.D,h,t⟩ =
    some ⟨.D,h+2*n,evenSweepTape n t h⟩ := by
  induction n generalizing t h with
  | zero =>
    simp [evenSweepTape,shuttleRun]
  | succ n ih =>
    have h0 : t h = true := by simpa using ones 0 (by omega)
    have h1 : t (h+1) = true := by simpa using ones 1 (by omega)
    let t2 := setBit (setBit t h true) (h+1) false
    have hp : ∀ j : Nat, j < 2*n → t2 (h+2+(j:Int)) = true := by
      intro j hj
      have hi : 2+j < 2*(n+1) := by omega
      have hsrc := ones (2+j) hi
      have heq : h+2+(j:Int) = h+((2+j:Nat):Int) := by omega
      have ne0 : h+2+(j:Int) ≠ h := by omega
      have ne1 : h+2+(j:Int) ≠ h+1 := by omega
      have ha : t2 (h+2+(j:Int)) = t (h+2+(j:Int)) := by
        simp [t2,setBit,ne0,ne1] <;> omega
      rw [ha,heq]
      exact hsrc
    have h2 : shuttleRun 2 ⟨Q.D,h,t⟩ = some ⟨Q.D,h+2,t2⟩ := by
      let t1 := setBit t h true
      have fRead : t1 (h+1) = true := by
        have hn : h+1 ≠ h := by omega
        simp [t1,setBit,hn,h1]
      have hs1 : next ⟨Q.D,h,t⟩ = some ⟨Q.F,h+1,t1⟩ := by
        simp [next,h0,t1]
      have hs2 : next ⟨Q.F,h+1,t1⟩ = some ⟨Q.D,h+2,t2⟩ := by
        simp [next,fRead,t2,t1]
        omega
      simpa [shuttleRun,hs1,hs2]
    have hi := ih t2 (h+2) hp
    calc
      shuttleRun (2*(n+1)) ⟨Q.D,h,t⟩ =
          (shuttleRun 2 ⟨Q.D,h,t⟩).bind (shuttleRun (2*n)) := by
        rw [show 2*(n+1)=2+2*n by omega,shuttleRun_add]
      _ = some ⟨Q.D,h+2+(2*n),evenSweepTape n t2 (h+2)⟩ := by
        simp [h2,hi]
      _ = some ⟨Q.D,h+2*(n+1),evenSweepTape (n+1) t h⟩ := by
        have heq : h+2+(2*n:Int) = h+2*(n+1) := by omega
        rw [heq]
        rfl

/-- Sweeping n pairs never changes any cell at or right of h+2n. -/
theorem evenSweepTape_right (n : Nat) (t : Int → Bool) (h x : Int)
    (hx : h+2*n ≤ x) : evenSweepTape n t h x = t x := by
  induction n generalizing t h with
  | zero => simp [evenSweepTape]
  | succ n ih =>
    simp only [evenSweepTape]
    have hp : h+2+2*n ≤ x := by omega
    rw [ih (setBit (setBit t h true) (h+1) false) (h+2) hp]
    have ha : x ≠ h := by omega
    have hb : x ≠ h+1 := by omega
    simp [setBit,ha,hb]

/-- The terminating 0 following an even run is still read in D after 2n steps. -/
theorem evenSweep_to_Dzero (n : Nat) (t : Int → Bool) (h : Int)
    (ones : ∀ j : Nat, j < 2*n → t (h+(j:Int)) = true)
    (zero : t (h+(2*n:Int)) = false) :
    ∃ u, shuttleRun (2*n) ⟨.D,h,t⟩ = some u ∧
      u.q = .D ∧ u.h = h+2*n ∧ u.tape u.h = false := by
  let u : Conf := ⟨.D,h+2*n,evenSweepTape n t h⟩
  refine ⟨u,evenSweep n t h ones,rfl,rfl,?_⟩
  have hh : evenSweepTape n t h (h+2*n) = t (h+2*n) :=
    evenSweepTape_right n t h (h+2*n) (by omega)
  exact hh.trans zero

#print axioms BB6Root119.evenSweep
#print axioms BB6Root119.evenSweep_to_Dzero
end BB6Root119
