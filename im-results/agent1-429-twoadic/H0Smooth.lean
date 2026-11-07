import H0TwoAdic
import ThreeAdicH0
import OddMulTwo
import Lean.Elab.Tactic.Omega

namespace H0Smooth

private theorem same_formula (c : Nat) :
    ThreeAdic.H0 c = H0TwoAdic.H0 c := rfl

private theorem three_pow_odd (e : Nat) : 3^e % 2 = 1 := by
  induction e with
  | zero => decide
  | succ e ih =>
      rw [Nat.pow_succ, Nat.mul_mod]
      simp [ih]

private theorem threeadic_preserved (e c t : Nat) (hc:2≤c) :
    ThreeAdic.H0 (c+(2*3^e)*t)%(3^e)=ThreeAdic.H0 c%(3^e) := by
  let N := 3^e
  let Q := 3^(e+1)
  have hQ : Q=3*N := by
    dsimp [Q,N]
    rw [Nat.pow_succ]
    omega
  have hshift := ThreeAdic.H0_shift_iterated e c t hc
  have hs : (ThreeAdic.H0 (c+(2*N)*t)+(2*N)*t)%N =
      ThreeAdic.H0 c%N := by
    have h := congrArg (fun z:Nat => z%N) hshift
    change ((ThreeAdic.H0 (c+(2*N)*t)+(2*N)*t)%Q)%N =
        (ThreeAdic.H0 c%Q)%N at h
    rw [hQ,Nat.mod_mul_left_mod,Nat.mod_mul_left_mod] at h
    exact h
  have hz : ((2*N)*t)%N=0 := by
    have hd : N ∣ (2*N)*t := ⟨2*t,by ac_rfl⟩
    exact Nat.mod_eq_zero_of_dvd hd
  rw [Nat.add_mod,hz] at hs
  simpa using hs

private theorem cancel_mod (M a b z : Nat) (hM:0<M)
    (h:(a+z)%M=(b+z)%M) : a%M=b%M := by
  have h' : ((a%M)+(z%M))%M=((b%M)+(z%M))%M := by
    calc
      _ = (a+z)%M := (Nat.add_mod _ _ _).symm
      _ = (b+z)%M := h
      _ = _ := Nat.add_mod _ _ _
  exact H0TwoAdic.mod_cancel_bounded M _ _ _
    (Nat.mod_lt _ hM) (Nat.mod_lt _ hM) (Nat.mod_lt _ hM) h'

private theorem H0_lift_two (E c t r N : Nat)
    (hc : max 2 E≤c) (ht : (r+2*N*t)%2^E=ThreeAdic.H0 c%2^E) :
    (ThreeAdic.H0 (c+2*N*t))%2^E=r%2^E := by
  have hc2 : max 2 E≤c+2*N*t := by omega
  have h1 := H0TwoAdic.H0_plus_input_mod E c hc
  have h2 := H0TwoAdic.H0_plus_input_mod E (c+2*N*t) hc2
  have hz : (ThreeAdic.H0 (c+2*N*t)+(c+2*N*t))%2^E =
      (r+(c+2*N*t))%2^E := by
    calc
      _ = 13%2^E := h2
      _ = (ThreeAdic.H0 c+c)%2^E := h1.symm
      _ = ((r+2*N*t)+c)%2^E := by
        have he := Nat.add_mod_eq_add_mod_right c ht
        simpa [Nat.add_assoc] using he.symm
      _ = (r+(c+2*N*t))%2^E := by congr 1; omega
  exact cancel_mod (2^E) _ _ _ (Nat.pow_pos (by decide)) hz

/-- Complete 2^A·3^E residue surjectivity for the exact two-burst H0
    synthetic-halting parameter, via parity-specific 3-adic lifting and
    odd-multiplier transitivity on the binary component. -/
theorem all_two_three_residues (A E r : Nat) :
    ∃ c, 2≤c ∧ ThreeAdic.H0 c % (2^A * 3^E) = r % (2^A * 3^E) := by
  cases A with
  | zero =>
      obtain ⟨n,hn⟩ :=
        ThreeAdic.H0_all_threeadic_residues_from_four 2 E r (by omega)
      refine ⟨2+4*n,by omega,?_⟩
      simpa using hn
  | succ a =>
      let A := a+1
      let c0 := 2*A+2+(r+1)%2
      have hc0 : 2≤c0 := by dsimp [c0]; omega
      obtain ⟨n,hthree⟩ :=
        ThreeAdic.H0_all_threeadic_residues_from_four c0 E r hc0
      let c := c0+4*n
      have hc : max 2 A≤c := by dsimp [c,c0]; omega
      have hc2 : 2≤c := by omega
      have hparc : c%2=(r+1)%2 := by dsimp[c,c0]; omega
      have hsum : (ThreeAdic.H0 c+c)%2=13%2 :=
        H0TwoAdic.H0_plus_input_mod 1 c (by omega)
      have hpar : ThreeAdic.H0 c%2=r%2 := by
        rw [Nat.add_mod] at hsum
        omega
      obtain ⟨t,ht⟩ :=
        BB6Modular.odd_double_shift A (ThreeAdic.H0 c) r (3^E)
          (by omega) (three_pow_odd E) hpar
      let c' := c+(2*3^E)*t
      have htwo : ThreeAdic.H0 c'%2^A=r%2^A :=
        H0_lift_two A c t r (3^E) hc ht
      have hthree' : ThreeAdic.H0 c'%3^E=r%3^E := by
        calc
          ThreeAdic.H0 c'%3^E = ThreeAdic.H0 c%3^E :=
            threeadic_preserved E c t hc2
          _ = r%3^E := by simpa [c] using hthree
      have hcop : Nat.Coprime (2^A) (3^E) :=
        Nat.Coprime.pow A E (by decide : Nat.Coprime 2 3)
      refine ⟨c',by dsimp[c'];omega,?_⟩
      simpa only [A] using
        (BB6Modular.coprime_mod_combine (2^A) (3^E)
          (ThreeAdic.H0 c') r hcop htwo hthree')

#print axioms all_two_three_residues
#print axioms threeadic_preserved
end H0Smooth
