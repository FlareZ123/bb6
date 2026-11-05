import Lean.Elab.Tactic.Omega
import EGenericTurn
import EAltBoundaryFirst
import PrefixENoFSource

set_option maxHeartbeats 15000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace BB6.Agent2EGenericFullFirst
open CryptidBoundary
open BB6.Agent2EGenericTurn
open BB6.Agent2EAltBoundaryFirst

/-- Generic exact ORIGINAL six-state first-physical-return compiler.
    If an A-on-zero local turn preserves the arbitrary left and right
    context and visits no F before a C-on-one endpoint, the complete
    F-on-zero E-branch return has no positive earlier physical F0,
    for arbitrary unary seed k, E scanner size q, and binary suffix Y. -/
theorem full_E_from_noF_turn_first (k q N : Nat)
    (front out ys : List Bool)
    (hTurn : ∀ L : List Bool,
      run N (⟨L,false,front++ys,0⟩ : Cfg) =
        ⟨L,true,out++ys,2⟩)
    (hTurnNoF : ∀ L : List Bool,
      BB6.Agent2ATurnFamily.NoF
        (⟨L,false,front++ys,0⟩ : Cfg) N) :
    let elapsed := 12*k*k+49*k+N+48+4*q
    let start := init (List.replicate (3*k+2) true ++
      false :: (pairs q ++ (front ++ ys)))
    run elapsed start =
      ⟨[],false,List.replicate (8*k+3) true ++
        outPacket q out ys,5⟩ ∧
    ∀ t, 0<t → t<elapsed →
      ¬ Physical (run t start) := by
  dsimp
  constructor
  · exact full_E_from_turn k q N front out ys hTurn
  · intro t hpos hlt hp
    by_cases hpre : t<12*k*k+41*k+33
    · exact (BB6.CryptidPrefixFirstReturn.prefixE_positive_noF
        k (pairs q ++ (front++ys)) t hpos hpre) hp.1
    · have hprefix : run (12*k*k+41*k+33)
          (init (List.replicate (3*k+2) true ++
            false :: (pairs q ++ (front++ys)))) =
        eStart (4*k) q (front++ys) := by
        rw [prefix_E]
        rfl
      have ht : t=(12*k*k+41*k+33)+(t-(12*k*k+41*k+33)) := by
        omega
      have hrest : t-(12*k*k+41*k+33) <
          2*(4*k)+4*q+N+15 := by omega
      rw [ht,run_add,hprefix] at hp
      exact (boundary_first_from_local_noF_turn
        (4*k) q N front out ys hTurn hTurnNoF)
        (t-(12*k*k+41*k+33)) hrest hp

/-- More general source compiler allowing marked interior F visits. -/
theorem full_E_from_noPhysical_turn_first (k q N : Nat)
    (front out ys : List Bool)
    (hTurn : ∀ L : List Bool,
      run N (⟨L,false,front++ys,0⟩ : Cfg) =
        ⟨L,true,out++ys,2⟩)
    (hTurnNoPhysical : ∀ L : List Bool,
      NoPhysical
        (⟨L,false,front++ys,0⟩ : Cfg) N) :
    let elapsed := 12*k*k+49*k+N+48+4*q
    let start := init (List.replicate (3*k+2) true ++
      false :: (pairs q ++ (front ++ ys)))
    run elapsed start =
      ⟨[],false,List.replicate (8*k+3) true ++
        outPacket q out ys,5⟩ ∧
    ∀ t, 0<t → t<elapsed →
      ¬ Physical (run t start) := by
  dsimp
  constructor
  · exact full_E_from_turn k q N front out ys hTurn
  · intro t hpos hlt hp
    by_cases hpre : t<12*k*k+41*k+33
    · exact (BB6.CryptidPrefixFirstReturn.prefixE_positive_noF
        k (pairs q ++ (front++ys)) t hpos hpre) hp.1
    · have hprefix : run (12*k*k+41*k+33)
          (init (List.replicate (3*k+2) true ++
            false :: (pairs q ++ (front++ys)))) =
        eStart (4*k) q (front++ys) := by
        rw [prefix_E]
        rfl
      have ht : t=(12*k*k+41*k+33)+(t-(12*k*k+41*k+33)) := by
        omega
      have hrest : t-(12*k*k+41*k+33) <
          2*(4*k)+4*q+N+15 := by omega
      rw [ht,run_add,hprefix] at hp
      exact (boundary_first_from_local_noPhysical_turn
        (4*k) q N front out ys hTurn hTurnNoPhysical)
        (t-(12*k*k+41*k+33)) hrest hp

#print axioms full_E_from_noPhysical_turn_first

#print axioms full_E_from_noF_turn_first
end BB6.Agent2EGenericFullFirst
