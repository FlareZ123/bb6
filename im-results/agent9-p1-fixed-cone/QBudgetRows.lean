import Lean
set_option maxHeartbeats 2000000

namespace BB6.Agent9BudgetRows

/-- A single source row is checked against every possible dyadic edge depth
    below K. Each stored row contains only the z-coordinates for one m. -/
def checkRow (B K L m : Nat) (rows : Array (List Nat)) : Bool :=
  (rows[m]!).all fun z =>
    decide (0<z ∧ z<2^K) &&
    (List.range K).all fun t =>
      let num := L+m+t+z/2^t
      decide (z%2^t ≠ 0 ∨ num%2 ≠ 1 ∨
        (m+t+1≤B ∧ 0<num/2 ∧ num/2<2^K ∧ num/2 ∈ rows[m+t+1]!))

theorem bounds_of_checkRow (B K L m : Nat) (rows : Array (List Nat))
    (hc : checkRow B K L m rows = true) (z : Nat) (hz : z∈rows[m]!) :
    0<z ∧ z<2^K := by
  have h := (List.all_eq_true.mp hc) z hz
  have hparts : decide (0<z ∧ z<2^K) = true ∧
      (List.range K).all (fun t =>
        let num := L+m+t+z/2^t
        decide (z%2^t ≠ 0 ∨ num%2 ≠ 1 ∨
          (m+t+1≤B ∧ 0<num/2 ∧ num/2<2^K ∧ num/2 ∈ rows[m+t+1]!))) = true := by
    simpa only [Bool.and_eq_true] using h
  exact of_decide_eq_true hparts.1

theorem closed_of_checkRow (B K L m : Nat) (rows : Array (List Nat))
    (hc : checkRow B K L m rows = true) (z t v zp : Nat)
    (hz : z∈rows[m]!) (hdiv : z=2^t*v)
    (hn : 2*zp+1=L+m+t+v) :
    m+t+1≤B ∧ zp∈rows[m+t+1]! := by
  have h := (List.all_eq_true.mp hc) z hz
  have hparts : decide (0<z ∧ z<2^K) = true ∧
      (List.range K).all (fun t =>
        let num := L+m+t+z/2^t
        decide (z%2^t ≠ 0 ∨ num%2 ≠ 1 ∨
          (m+t+1≤B ∧ 0<num/2 ∧ num/2<2^K ∧ num/2 ∈ rows[m+t+1]!))) = true := by
    simpa only [Bool.and_eq_true] using h
  have hbound : 0<z ∧ z<2^K := of_decide_eq_true hparts.1
  have ht : t<K := by
    by_cases hlt : t<K
    · exact hlt
    have hp : 2^K∣2^t := Nat.pow_dvd_pow 2 (by omega)
    have hdivpow : 2^K∣z := Nat.dvd_trans hp ⟨v,hdiv⟩
    have hle : 2^K≤z := Nat.le_of_dvd hbound.1 hdivpow
    omega
  have hslot := (List.all_eq_true.mp hparts.2) t (List.mem_range.mpr ht)
  let num := L+m+t+z/2^t
  have hcond : z%2^t ≠ 0 ∨ num%2 ≠ 1 ∨
      (m+t+1≤B ∧ 0<num/2 ∧ num/2<2^K ∧ num/2∈rows[m+t+1]!) := by
    simpa [num] using of_decide_eq_true hslot
  have hmod : z%2^t=0 := Nat.mod_eq_zero_of_dvd ⟨v,hdiv⟩
  have hquot : z/2^t=v := by
    rw [hdiv]
    exact Nat.mul_div_cancel_left v (Nat.pow_pos (by decide))
  have hpar : num%2=1 := by
    dsimp [num]
    rw [hquot, ←hn]
    omega
  rcases hcond with hbad | hbad | hgood
  · exact False.elim (hbad hmod)
  · exact False.elim (hbad hpar)
  · rcases hgood with ⟨hm',_,_,hmem⟩
    have hhalf : num/2=zp := by
      dsimp [num]
      rw [hquot, ←hn]
      omega
    exact ⟨hm', by simpa [hhalf] using hmem⟩

end BB6.Agent9BudgetRows
