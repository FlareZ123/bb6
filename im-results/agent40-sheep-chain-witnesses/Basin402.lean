import SheepFullBasinCore
namespace SheepFullBasin

private theorem pow_scale (r c k : Nat) :
    2^(r+c+4860*k) = 2^c*2^(r+4860*k) := by
  rw [show r+c+4860*k=c+(r+4860*k) by omega, Nat.pow_add]

theorem basin402_iff (k x : Nat) (hx : x%2=0) :
    SheepEven.EvenReach x (2^(402+4860*k)) ↔
      x=2^(402+4860*k) ∨
      15*x+2=8*2^(402+4860*k) ∨
      1485*x+4688=512*2^(402+4860*k) := by
  let R := 2^(402+4860*k)
  obtain ⟨A,B,hAR,hBA,hA,hB,hlo,hBAle,hARle⟩ := Audit.chain402_source k
  constructor
  · intro hr
    apply at_most_three R 15 2 8 1485 4688 512 _ _ _ hx hr
    · intro z he heven
      exact SheepFullSourceCases.complete_r402_n0 k z R
        (SheepEvenSourceAlgebra.even_edge_to_algebra heven he)
        (by dsimp [R]; omega)
    · intro z y he heven hy
      have heq : 15*y+2=2^(405+4860*k) := by
        have hp : 2^(405+4860*k)=8*R := by
          simpa only [show 402+3+4860*k=405+4860*k by omega, Nat.reducePow] using
            (pow_scale 402 3 k)
        dsimp [R] at hy
        omega
      simpa [R] using (SheepFullSourceCases.complete_r402_n1 k z y
        (SheepEvenSourceAlgebra.even_edge_to_algebra heven he) heq)
    · intro z y he heven hy
      have heq : 1485*y+4688=2^(411+4860*k) := by
        have hp : 2^(411+4860*k)=512*R := by
          simpa only [show 402+9+4860*k=411+4860*k by omega, Nat.reducePow] using
            (pow_scale 402 9 k)
        dsimp [R] at hy
        omega
      exact SheepFullSourceCases.complete_r402_n2 k z y
        (SheepEvenSourceAlgebra.even_edge_to_algebra heven he) heq
  · intro he
    rcases he with h0 | h1 | h2
    · subst x
      exact SheepEven.EvenReach.refl R
    · have heq : x=A := by omega
      subst x
      exact SheepEven.EvenReach.cons hAR (SheepEven.EvenReach.refl R)
    · have heq : x=B := by omega
      subst x
      exact SheepEven.EvenReach.cons hBA
        (SheepEven.EvenReach.cons hAR (SheepEven.EvenReach.refl R))

#print axioms basin402_iff
end SheepFullBasin
