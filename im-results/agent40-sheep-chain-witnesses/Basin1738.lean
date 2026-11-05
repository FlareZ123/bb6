import Basin402

namespace SheepFullBasin

theorem basin1738_iff (k x : Nat) (hx : x%2=0) :
    SheepEven.EvenReach x (2^(1738+4860*k)) ↔
      x=2^(1738+4860*k) ∨
      15*x+2=8*2^(1738+4860*k) ∨
      135*x+196=64*2^(1738+4860*k) := by
  let R := 2^(1738+4860*k)
  obtain ⟨A,B,hAR,hBA,hA,hB,hlo,hBAle,hARle⟩ := Audit.chain1738_source k
  constructor
  · intro hr
    apply at_most_three R 15 2 8 135 196 64 _ _ _ hx hr
    · intro z he heven
      exact SheepFullSourceCases.complete_r1738_n0 k z R
        (SheepEvenSourceAlgebra.even_edge_to_algebra heven he)
        (by dsimp [R]; omega)
    · intro z y he heven hy
      have heq : 15*y+2=2^(1741+4860*k) := by
        have hp : 2^(1741+4860*k)=8*R := by
          simpa only [show 1738+3+4860*k=1741+4860*k by omega, Nat.reducePow] using
            (pow_scale 1738 3 k)
        dsimp [R] at hy
        omega
      simpa [R] using (SheepFullSourceCases.complete_r1738_n1 k z y
        (SheepEvenSourceAlgebra.even_edge_to_algebra heven he) heq)
    · intro z y he heven hy
      have heq : 135*y+196=2^(1744+4860*k) := by
        have hp : 2^(1744+4860*k)=64*R := by
          simpa only [show 1738+6+4860*k=1744+4860*k by omega, Nat.reducePow] using
            (pow_scale 1738 6 k)
        dsimp [R] at hy
        omega
      exact SheepFullSourceCases.complete_r1738_n2 k z y
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

#print axioms basin1738_iff
end SheepFullBasin
