import SpecialSourceCases
import SheepEvenReachInverse

namespace SheepChainRoot

/-- Three-level finite-inverse-cone obstruction with a genuine incoming edge at
every step of the induction. This is independent of the Sheep transition rules. -/
theorem no_root_of_chain
    (R m c z M C Z : Nat)
    (hbig : 100 ≤ R)
    (hAneq : m*10+c ≠ z*R)
    (hBneq : M*10+C ≠ Z*R)
    (hroot : ∀ x, SheepEven.EvenEdge x R → x%2=0 → m*x+c=z*R)
    (hmid : ∀ x y, SheepEven.EvenEdge x y → x%2=0 →
      m*y+c=z*R → M*x+C=Z*R)
    (hleaf : ∀ x y, SheepEven.EvenEdge x y → x%2=0 →
      M*y+C=Z*R → False) :
    ¬ SheepEven.EvenReach 10 R := by
  intro hr
  have hrneq : 10 ≠ R := by omega
  obtain ⟨A,hreachA,hEdgeA⟩ := SheepEvenReachInverse.reach_last_edge hr hrneq
  have hAeven : A%2=0 :=
    SheepEvenReachInverse.even_reach_preserves_even hreachA (by decide)
  have hAe := hroot A hEdgeA hAeven
  have hAneq' : 10 ≠ A := by
    intro h
    exact hAneq (by simpa [h] using hAe)
  obtain ⟨B,hreachB,hEdgeB⟩ :=
    SheepEvenReachInverse.reach_last_edge hreachA hAneq'
  have hBeven : B%2=0 :=
    SheepEvenReachInverse.even_reach_preserves_even hreachB (by decide)
  have hBe := hmid B A hEdgeB hBeven hAe
  have hBneq' : 10 ≠ B := by
    intro h
    exact hBneq (by simpa [h] using hBe)
  obtain ⟨X,hreachX,hEdgeX⟩ :=
    SheepEvenReachInverse.reach_last_edge hreachB hBneq'
  have hXeven : X%2=0 :=
    SheepEvenReachInverse.even_reach_preserves_even hreachX (by decide)
  exact hleaf X B hEdgeX hXeven hBe

private theorem pow_scale (r c k : Nat) :
    2^(r+c+4860*k) = 2^c*2^(r+4860*k) := by
  rw [show r+c+4860*k=c+(r+4860*k) by omega, Nat.pow_add]

/-- Actual original Sheep blank-even section avoids the entire 402 class. -/
theorem root402_unreachable (k : Nat) :
    ¬ SheepEven.EvenReach 10 (2^(402+4860*k)) := by
  let R := 2^(402+4860*k)
  have hbig : 100 ≤ R := by
    have hx : 2^7 ≤ 2^(402+4860*k) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hb : 100 ≤ 2^7 := by decide
    exact Nat.le_trans hb hx
  apply no_root_of_chain R 15 2 8 1485 4688 512 hbig
    (by dsimp [R]; omega) (by dsimp [R]; omega)
  · intro x he hx
    exact SheepFullSourceCases.complete_r402_n0 k x R
      (SheepEvenSourceAlgebra.even_edge_to_algebra hx he)
      (by dsimp [R]; omega)
  · intro x y he hx hy
    have heq : 15*y+2=2^(405+4860*k) := by
      have hp : 2^(405+4860*k)=8*R := by
        simpa only [show 402+3+4860*k=405+4860*k by omega, Nat.reducePow] using
          (pow_scale 402 3 k)
      dsimp [R] at hy
      omega
    simpa [R] using (SheepFullSourceCases.complete_r402_n1 k x y
      (SheepEvenSourceAlgebra.even_edge_to_algebra hx he) heq)
  · intro x y he hx hy
    have heq : 1485*y+4688=2^(411+4860*k) := by
      have hp : 2^(411+4860*k)=512*R := by
        simpa only [show 402+9+4860*k=411+4860*k by omega, Nat.reducePow] using
          (pow_scale 402 9 k)
      dsimp [R] at hy
      omega
    exact SheepFullSourceCases.complete_r402_n2 k x y
      (SheepEvenSourceAlgebra.even_edge_to_algebra hx he) heq

/-- Actual original Sheep blank-even section avoids the entire 1738 class. -/
theorem root1738_unreachable (k : Nat) :
    ¬ SheepEven.EvenReach 10 (2^(1738+4860*k)) := by
  let R := 2^(1738+4860*k)
  have hbig : 100 ≤ R := by
    have hx : 2^7 ≤ 2^(1738+4860*k) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hb : 100 ≤ 2^7 := by decide
    exact Nat.le_trans hb hx
  apply no_root_of_chain R 15 2 8 135 196 64 hbig
    (by dsimp [R]; omega) (by dsimp [R]; omega)
  · intro x he hx
    exact SheepFullSourceCases.complete_r1738_n0 k x R
      (SheepEvenSourceAlgebra.even_edge_to_algebra hx he)
      (by dsimp [R]; omega)
  · intro x y he hx hy
    have heq : 15*y+2=2^(1741+4860*k) := by
      have hp : 2^(1741+4860*k)=8*R := by
        simpa only [show 1738+3+4860*k=1741+4860*k by omega, Nat.reducePow] using
          (pow_scale 1738 3 k)
      dsimp [R] at hy
      omega
    simpa [R] using (SheepFullSourceCases.complete_r1738_n1 k x y
      (SheepEvenSourceAlgebra.even_edge_to_algebra hx he) heq)
  · intro x y he hx hy
    have heq : 135*y+196=2^(1744+4860*k) := by
      have hp : 2^(1744+4860*k)=64*R := by
        simpa only [show 1738+6+4860*k=1744+4860*k by omega, Nat.reducePow] using
          (pow_scale 1738 6 k)
      dsimp [R] at hy
      omega
    exact SheepFullSourceCases.complete_r1738_n2 k x y
      (SheepEvenSourceAlgebra.even_edge_to_algebra hx he) heq

#print axioms root402_unreachable
#print axioms root1738_unreachable
end SheepChainRoot
