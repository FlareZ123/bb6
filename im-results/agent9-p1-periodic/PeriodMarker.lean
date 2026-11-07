import PeriodCycle
import PeriodRotate
namespace PeriodMarker

def rot (N x : Nat) : Nat → Nat
  | 0 => x
  | n+1 => (2 * rot N x n) % N

theorem rot_eq (N x n : Nat) (hN : 0<N) (hx : x<N) :
    rot N x n = (2^n*x)%N := by
  induction n with
  | zero => simp [rot, Nat.mod_eq_of_lt hx]
  | succ n ih =>
    simp only [rot, ih]
    calc
      (2*((2^n*x)%N))%N = (2*(2^n*x))%N := by
        simp only [Nat.mul_mod, Nat.mod_mod]
      _ = (2^(n+1)*x)%N := by
        rw [Nat.pow_succ]
        congr 1
        ac_rfl

theorem odd_mersenne (S : Nat) (hS : 1<S) :
    (2^S-1)%2=1 := by
  have he : S = S-1+1 := by omega
  have hpow : 2^S = 2*(2^(S-1)) := by
    calc
      2^S = 2^((S-1)+1) := by congr 1
      _ = 2^(S-1)*2 := by rw [Nat.pow_succ]
      _ = 2*2^(S-1) := by ac_rfl
  have hp : 0<2^(S-1) := Nat.pow_pos (by decide)
  omega

theorem mersenne_mod (S:Nat) (hS:1<S) :
    (2^S) % (2^S-1) = 1 := by
  have hpow : 2<2^S := by
    have ht : 2^2≤2^S := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hB : 1<2^S-1 := by omega
  rw [Nat.mod_eq_sub_mod (show 2^S-1≤2^S by omega)]
  have heq : 2^S-(2^S-1)=1 := by omega
  rw [heq]
  exact Nat.mod_eq_of_lt hB

theorem rot_period (S x n : Nat) (hS:1<S)
    (hx:x<2^S-1) :
    rot (2^S-1) x (n+S) = rot (2^S-1) x n := by
  have hB : 0<2^S-1 := by
    have := mersenne_mod S hS
    omega
  rw [rot_eq _ _ _ hB hx,rot_eq _ _ _ hB hx]
  have hm := mersenne_mod S hS
  rw [Nat.pow_add]
  calc
    ((2^n*2^S)*x)%(2^S-1) =
      (2^S*(2^n*x))%(2^S-1) := by congr 1; ac_rfl
    _ = (2^S%(2^S-1)*((2^n*x)%(2^S-1)))%(2^S-1) := by
      rw [Nat.mul_mod]
    _ = (2^n*x)%(2^S-1) := by
      rw [hm]
      simp

/-- Every integral marker slope 0<Q<S forces a shorter cyclic bit shift.
    The proof is unbounded in S; no finite cost scan is used. -/
theorem shorter_marker_rotation (S H Q : Nat) (hS : 1<S)
    (hH : 0<H ∧ H<2^S-1) (hQ : 0<Q ∧ Q<S)
    (hratio : (2^S-1)*Q=S*H) :
    ∃ r, 0<r ∧ r<S ∧ (2^r*H)%(2^S-1)=H := by
  let B := 2^S-1
  have hB : 0<B := by
    have hp : 2<2^S := by
      have ht:2^2≤2^S:= Nat.pow_le_pow_right (by decide) (by omega)
      omega
    dsimp [B]
    omega
  have hOdd : B%2=1 := odd_mersenne S hS
  let hs : Nat→Nat := rot B H
  let qs : Nat→Nat := rot S Q
  have hinv : ∀ n,
      B*qs n=S*hs n ∧ 0<qs n ∧ qs n<S ∧ 0<hs n ∧ hs n<B := by
    intro n
    induction n with
    | zero =>
      simp only [hs, qs, rot]
      exact ⟨hratio,hQ.1,hQ.2,hH.1,hH.2⟩
    | succ n ih =>
      simpa only [hs,qs,rot] using
        PeriodRotate.ratio_rotates B S (qs n) (hs n) hB hOdd
          (by omega) ⟨ih.2.2.2.1,ih.2.2.2.2⟩
          ⟨ih.2.1,ih.2.2.1⟩ ih.1
  have hhperiod : ∀ n, hs (n+S)=hs n := by
    intro n
    exact rot_period S H n hS hH.2
  have hqperiod : ∀ n, qs (n+S)=qs n := by
    intro n
    have hh1 := (hinv (n+S)).1
    have hh2 := (hinv n).1
    rw [hhperiod n] at hh1
    have hc : B*qs (n+S)=B*qs n := by omega
    exact Nat.eq_of_mul_eq_mul_left hB hc
  have hstep : ∀ n, qs (n+1)=(2*qs n)%S := by
    intro n
    rfl
  obtain ⟨r, hrpos, hrlt, hret⟩ :=
    PeriodCycle.shorter_return S (by omega) qs (fun x => (2*x)%S)
      hstep hqperiod (fun i hi => ⟨(hinv i).2.1,(hinv i).2.2.1⟩)
  have heq : hs r = hs 0 := by
    have hh1 := (hinv r).1
    have hh2 := (hinv 0).1
    rw [hret] at hh1
    have hc : S*hs r=S*hs 0 := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0<S) hc
  refine ⟨r, hrpos, hrlt, ?_⟩
  have hs0 : hs 0=H := rfl
  rw [hs0] at heq
  simpa only [hs, rot_eq B H r hB hH.2] using heq

#print axioms shorter_marker_rotation
end PeriodMarker
