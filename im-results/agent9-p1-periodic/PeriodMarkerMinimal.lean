import PeriodMarker
import PeriodCycleMinimal
namespace PeriodMarker

theorem shorter_marker_rotation_minimal (S H Q : Nat) (hS : 1<S)
    (hH : 0<H ∧ H<2^S-1) (hQ : 0<Q ∧ Q<S)
    (hratio : (2^S-1)*Q=S*H) :
    ∃ r, 0<r ∧ r<S ∧ r∣S ∧
      (2^r*H)%(2^S-1)=H ∧
      ∀ s, 0<s → s<r → (2^s*H)%(2^S-1)≠H := by
  let B := 2^S-1
  have hB : 0<B := by
    have hp : 2<2^S := by
      have ht:2^2≤2^S:= Nat.pow_le_pow_right (by decide) (by omega)
      omega
    dsimp [B]
    omega
  have hOdd : B%2=1 := by simpa [B] using odd_mersenne S hS
  let hs : Nat→Nat := rot B H
  let qs : Nat→Nat := rot S Q
  have hinv : ∀ n,
      B*qs n=S*hs n ∧ 0<qs n ∧ qs n<S ∧ 0<hs n ∧ hs n<B := by
    intro n
    induction n with
    | zero =>
      simp only [hs,qs,rot]
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
  obtain ⟨r,hrpos,hrlt,hret,hrdiv,hminimal⟩ :=
    PeriodCycle.minimal_return S (by omega) qs (fun x => (2*x)%S)
      hstep hqperiod (fun i hi => ⟨(hinv i).2.1,(hinv i).2.2.1⟩)
  have heq : hs r=hs 0 := by
    have hh1 := (hinv r).1
    have hh2 := (hinv 0).1
    rw [hret] at hh1
    have hc : S*hs r=S*hs 0 := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0<S) hc
  have hs0 : hs 0=H := rfl
  have hrotR : (2^r*H)%B=H := by
    have hhs : hs r=H := by simpa [hs0] using heq
    simpa [hs,rot_eq B H r hB hH.2] using hhs
  have hminimalMarker : ∀ s, 0<s → s<r →
      (2^s*H)%B≠H := by
    intro s hspos hslt hrot
    have hhs : hs s=hs 0 := by
      calc
        hs s = (2^s*H)%B := by
          dsimp [hs]
          exact rot_eq B H s hB hH.2
        _ = H := hrot
        _ = hs 0 := by rfl
    have hh1 := (hinv s).1
    have hh2 := (hinv 0).1
    rw [hhs] at hh1
    have hc : B*qs s=B*qs 0 := by omega
    have hqeq : qs s=qs 0 := Nat.eq_of_mul_eq_mul_left hB hc
    exact hminimal s hspos hslt (by simpa [qs] using hqeq)
  exact ⟨r,hrpos,hrlt,hrdiv,hrotR,hminimalMarker⟩

end PeriodMarker
