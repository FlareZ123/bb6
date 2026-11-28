import M8BoundarySource
import JointAllRoot
import ModularConeBlindHigh
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace BB6.Agent15Research
open BB6.Agent42ModularCone

/-- The new boundary index has the strongest possible old-sieve residue:
    its dyadic test coordinate is exactly the full stopping modulus. -/
theorem m8Boundary_index_exact (m : Nat) (hm8 : m%8=3) :
    m8BoundaryJThin m+3*m+3=2^(2*m+2) := by
  have hd := m8BoundaryD_eq m (by omega)
  have hb := m8BoundaryBQ m
  have hj := m8BoundaryJThin_plus m hm8
  calc
    m8BoundaryJThin m+3*m+3 =
        3*m8BoundaryD m+3*m+1 := by omega
    _ = 3*(m+m8BoundaryD m)+1 := by omega
    _ = 3*m8BoundaryQ m+1 := by rw [hd]
    _ = 2^(2*m+2) := hb.symm

/-- Every member of the explicit boundary family survives the complete
    earlier Agent19 high sieve. -/
theorem m8Boundary_legacy_allowed (m : Nat) (hm8 : m%8=3) :
    BB6.Agent19Joint.highAllowed (m8BoundaryJThin m) m := by
  let j := m8BoundaryJThin m
  have hm : m%2=1 := by omega
  have hjplus := m8BoundaryJThin_plus m hm8
  have hd8 := m8BoundaryD_mod8 m hm8
  have hj2 : j%2=0 := by
    dsimp [j]
    omega
  have hs : (j+m)%4=3 := by
    dsimp [j]
    omega
  have hbase : BB6.Agent3.jointHighAllowed j m := by
    dsimp [BB6.Agent3.jointHighAllowed]
    omega
  have hrect : BB6.Agent3.jointHighRectAllowed j m := by
    dsimp [BB6.Agent3.jointHighRectAllowed]
    exact ⟨hbase,by omega⟩
  have hidx : j+3*m+3=2^(2*m+2) := by
    simpa [j] using m8Boundary_index_exact m hm8
  have hz : ∀ n, n+4≤2*m+2 →
      (j+3*m+3)%2^(n+4)=0 := by
    intro n hn
    have hpowdiv : 2^(n+4) ∣ 2^(2*m+2) := by
      obtain ⟨e,he⟩ : ∃e,2*m+2=n+4+e :=
        ⟨2*m+2-(n+4),by omega⟩
      refine ⟨2^e,?_⟩
      rw [he,Nat.pow_add]
    rw [hidx]
    exact Nat.mod_eq_zero_of_dvd hpowdiv
  change BB6.Agent3.jointHighRectAllowed j m ∧
    (∀ n, ¬(n+4≤2*m+2 ∧
      (j+3*m+3)%2^(n+4)=2^(n+2) ∧
      (2*j+3)%8=(if n%2=0 then 7 else 3))) ∧
    ¬ (2≤m ∧ j%8=7 ∧ (j+3*m+15)%64=0) ∧
    ¬ (2≤m ∧ j%8=3 ∧ (j+3*m+47)%64=0) ∧
    ¬ (3≤m ∧ j%8=5 ∧ (j+3*m+27)%128=0) ∧
    ¬ (3≤m ∧ j%8=1 ∧ (j+3*m+91)%128=0)
  refine ⟨hrect,?_,?_,?_,?_,?_⟩
  · intro n
    rintro ⟨hn,hval,_⟩
    have hzero := hz n hn
    have hpos : 0<2^(n+2) := Nat.pow_pos (by decide)
    omega
  all_goals omega

/-- The same exact-divisibility identity places every boundary member in the
    generic blind cylinder of the adaptive modular high-stop component. -/
theorem m8Boundary_modular_cone_blind (m : Nat) (hm8 : m%8=3) :
    highStopExcluded (m8BoundaryJThin m+1) m=false := by
  have hjplus := m8BoundaryJThin_plus m hm8
  have hd8 := m8BoundaryD_mod8 m hm8
  have hj2 : m8BoundaryJThin m%2=0 := by omega
  have hjpos : 1≤m8BoundaryJThin m := by
    have hd : 2≤m8BoundaryD m := by omega
    dsimp [m8BoundaryJThin]
    omega
  have hm : m%2=1 := by omega
  have hdiv : 2^(2*m+2) ∣ m8BoundaryJThin m+3*m+3 := by
    rw [m8Boundary_index_exact m hm8]
  exact high_stop_blind_of_even_divisible
    (m8BoundaryJThin m) m hjpos hj2 hm hdiv

/-- Compact strictness package: an explicit infinite family accepted by the
    old Agent19 sieve and by the modular-cone component, yet excluded from
    the authentic blank-origin Machine-C orbit by the M8 source quotient. -/
theorem m8Boundary_strict_package (m : Nat) (hm8 : m%8=3) :
    BB6.Agent19Joint.highAllowed (m8BoundaryJThin m) m ∧
    highStopExcluded (m8BoundaryJThin m+1) m=false ∧
    ¬ BB6.Agent15.CReach
      (2*m8BoundaryJThin m+3) (m8BoundaryKThin m) :=
  ⟨m8Boundary_legacy_allowed m hm8,
   m8Boundary_modular_cone_blind m hm8,
   m8Boundary_unreachable_thin m hm8⟩

#print axioms m8Boundary_legacy_allowed
#print axioms m8Boundary_modular_cone_blind
#print axioms m8Boundary_strict_package

end BB6.Agent15Research
