import PeriodCycle
namespace PeriodCycle

theorem minimal_return (S : Nat) (hS : 0<S)
    (q : Nat → Nat) (step : Nat → Nat)
    (hs : ∀ n, q (n+1)=step (q n))
    (hperiod : ∀ n, q (n+S)=q n)
    (hbound : ∀ i<S, 0<q i ∧ q i<S) :
    ∃ r, 0<r ∧ r<S ∧ q r=q 0 ∧ r∣S ∧
      ∀ s, 0<s → s<r → q s≠q 0 := by
  obtain ⟨r0,hr0pos,hr0lt,hr0ret⟩ :=
    shorter_return S hS q step hs hperiod hbound
  have hmin : ∀ r, 0<r → r<S → q r=q 0 →
      ∃ d, 0<d ∧ d<S ∧ q d=q 0 ∧
        ∀ s, 0<s → s<d → q s≠q 0 := by
    intro r
    exact Nat.strongRecOn r (fun r ih => by
      intro hpos hrlt hP
      by_cases hex : ∃ s, 0<s ∧ s<r ∧ q s=q 0
      · rcases hex with ⟨s,hs0,hslt,hsret⟩
        exact ih s hslt hs0 (by omega) hsret
      · exact ⟨r,hpos,hrlt,hP,fun s hs0 hslt hsret => hex ⟨s,hs0,hslt,hsret⟩⟩
    )
  obtain ⟨r,hrpos,hrlt,hret,hminimal⟩ :=
    hmin r0 hr0pos hr0lt hr0ret
  have hmultiple : ∀ k, q (r*k)=q 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hdet := deterministic_forward q step hs 0 r (r*k) hret.symm
      have hidx : r+r*k=r*(k+1) := by
        rw [Nat.mul_succ]
        omega
      calc
        q (r*(k+1)) = q (r+r*k) := by rw [hidx]
        _ = q (r*k) := by simpa using hdet.symm
        _ = q 0 := ih
  let k := S/r
  let s := S%r
  have hdecomp : s+r*k=S := by
    dsimp [k]
    exact Nat.mod_add_div S r
  have hshift := deterministic_forward q step hs 0 (r*k) s
    (hmultiple k).symm
  have hidx : r*k+s=S := by simpa [Nat.add_comm] using hdecomp
  have hsret : q s=q 0 := by
    calc
      q s = q (0+s) := by simp
      _ = q (r*k+s) := hshift
      _ = q S := by rw [hidx]
      _ = q 0 := by simpa using hperiod 0
  have hslt : s<r := by
    dsimp [s]
    exact Nat.mod_lt S (by omega)
  have hs0 : s=0 := by
    by_cases hz : s=0
    · exact hz
    · have hspos :0<s := by omega
      exact False.elim (hminimal s hspos hslt hsret)
  have hdiv : r∣S := (Nat.dvd_iff_mod_eq_zero).2 (by
    dsimp [s] at hs0
    exact hs0)
  exact ⟨r,hrpos,hrlt,hret,hdiv,hminimal⟩

end PeriodCycle
