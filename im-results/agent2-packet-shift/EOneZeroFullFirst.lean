import Lean.Elab.Tactic.Omega
import EOneZero
import EOneZeroLocalFirst
import EAltBoundaryFirst
import PrefixENoFSource
import NoEarlierF

set_option maxHeartbeats 20000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace BB6.Agent2EOneZeroFullFirst
open CryptidBoundary
open BB6.Agent2EAltBoundaryFirst
open BB6.Agent2EGenericTurn
open BB6.CryptidFirstReturn
open BB6.CryptidPrefixFirstReturn
open BB6.Agent2EOneZero
open BB6.Agent2EOneZeroLocalFirst

private theorem appendNoPhysical (c d : Cfg) (a b : Nat)
    (hc : NoPhysical c a) (he : run a c = d)
    (hd : NoPhysical d b) : NoPhysical c (a+b) := by
  intro t ht
  by_cases hs : t<a
  · exact hc t hs
  · have heq : t=a+(t-a) := by omega
    rw [heq,run_add,he]
    exact hd (t-a) (by omega)

private theorem startFourNoPhysical (m r : Nat) (ys : List Bool) :
    NoPhysical (eOneStart m r ys) 4 := by
  intro t ht hp
  have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
  rcases hc with rfl | rfl | rfl | rfl
  all_goals simp [Physical,eOneStart,eStart,run,step,goL,goR,pairs] at hp

private theorem finishEightNoPhysical (m : Nat) (zs : List Bool) :
    NoPhysical
      (⟨oppairs 1 ++ (pairs (m+3) ++ [true,true]),true,zs,4⟩ : Cfg) 8 := by
  intro t ht hp
  have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 ∨ t=7 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Physical,run,step,goL,goR,pairs,oppairs] at hp

private theorem finishEight (m : Nat) (zs : List Bool) :
    run 8
      (⟨oppairs 1 ++ (pairs (m+3) ++ [true,true]),true,zs,4⟩ : Cfg) =
      sweepD m ([true,true,false,true,true,true,true,false] ++ zs) := by
  simp [run,step,goL,goR,pairs,oppairs,sweepD,List.append_assoc]

private theorem sweepDNoPhysical (m : Nat) (zs : List Bool) :
    NoPhysical (sweepD m zs) (2*m+3) := by
  intro t ht hp
  cases t with
  | zero => simpa [Physical,sweepD,run] using hp
  | succ t =>
      have hstep : step (sweepD m zs) = step (sweepB m zs) := by
        simp [sweepD,sweepB,step,goL,goR]
      have heq : (run (t+1) (sweepD m zs)).st =
          (run (t+1) (sweepB m zs)).st := by
        simp only [run]
        rw [hstep]
      rw [heq] at hp
      exact sweepB_firstF m zs (t+1) (by omega) hp.1

/-- A complete, original-source, all-natural, all-suffix *strict physical*
    first-return certificate for the one-pair E branch. -/
theorem e_one_boundary_first_physical (m r : Nat) (ys : List Bool) :
    NoPhysical (eOneStart m r ys) (2*m+31+4*r) := by
  let L : List Bool := oppairs 1 ++ (pairs (m+3) ++ [true,true])
  let zs : List Bool := List.replicate (2*r+6) true ++ ys
  let s1 : Cfg := ⟨L,false,
      [true,false,true,true,false] ++ (pairs r ++ (false::ys)),0⟩
  let s2 : Cfg := ⟨L,true,zs,4⟩
  let s3 : Cfg :=
      sweepD m ([true,true,false,true,true,true,true,false] ++ zs)
  have h0 : run 4 (eOneStart m r ys) = s1 := by
    dsimp [s1,L]
    simpa [eOneStart] using
      (eStart_scan m 0
        ([true,false,true,true,false] ++ (pairs r ++ (false::ys))))
  have h1 : run (4*r+16) s1 = s2 := by
    dsimp [s1,s2,L,zs]
    exact a_one_zero_turn r
      (oppairs 1 ++ (pairs (m+3) ++ [true,true])) ys
  have h2 : run 8 s2 = s3 := by
    dsimp [s2,s3,L,zs]
    exact finishEight m (List.replicate (2*r+6) true ++ ys)
  have hn0 : NoPhysical (eOneStart m r ys) 4 :=
    startFourNoPhysical m r ys
  have hn1 : NoPhysical s1 (4*r+16) := by
    dsimp [s1,L]
    exact a_one_zero_noPhysical r
      (oppairs 1 ++ (pairs (m+3) ++ [true,true])) ys
  have hn2 : NoPhysical s2 8 := by
    dsimp [s2,L,zs]
    exact finishEightNoPhysical m (List.replicate (2*r+6) true ++ ys)
  have hn3 : NoPhysical s3 (2*m+3) := by
    dsimp [s3]
    exact sweepDNoPhysical m
      ([true,true,false,true,true,true,true,false] ++ zs)
  have hjoin : NoPhysical (eOneStart m r ys)
      (4+((4*r+16)+(8+(2*m+3)))) :=
    appendNoPhysical (eOneStart m r ys) s1
      4 ((4*r+16)+(8+(2*m+3)))
      hn0 h0
      (appendNoPhysical s1 s2 (4*r+16) (8+(2*m+3))
        hn1 h1
        (appendNoPhysical s2 s3 8 (2*m+3) hn2 h2 hn3))
  have ht : 4+((4*r+16)+(8+(2*m+3)))=2*m+31+4*r := by omega
  simpa only [ht] using hjoin

theorem full_one_zero_first_physical (k r : Nat) (ys : List Bool) :
    let t := 12*k*k+49*k+64+4*r
    let xs := List.replicate (3*k+2) true ++
      false :: ([true,false,true,true,false] ++ (pairs r ++ (false::ys)))
    let out : Cfg := ⟨[],false,List.replicate (8*k+3) true ++
      ([true,true,false,true,true,true,true,false] ++
        (List.replicate (2*r+6) true ++ ys)),5⟩
    run t (init xs) = out ∧
      ∀ u, 0<u → u<t → ¬ Physical (run u (init xs)) := by
  dsimp
  constructor
  · exact full_one_zero k r ys
  · intro u hu ht hp
    let p : Nat := 12*k*k+41*k+33
    by_cases hpre : u<p
    · exact
        (prefixE_positive_noF k
          ([true,false,true,true,false] ++ (pairs r ++ (false::ys)))
          u hu hpre) hp.1
    · have heq : u=p+(u-p) := by omega
      rw [heq,run_add] at hp
      have hprefix : run p
          (init (List.replicate (3*k+2) true ++
            false :: ([true,false,true,true,false] ++
              (pairs r ++ (false::ys))))) =
          eOneStart (4*k) r ys := by
        dsimp [p,eOneStart]
        exact prefix_E k
          ([true,false,true,true,false] ++ (pairs r ++ (false::ys)))
      rw [hprefix] at hp
      exact (e_one_boundary_first_physical (4*k) r ys)
        (u-p) (by dsimp [p] at *; omega) hp

#print axioms e_one_boundary_first_physical
#print axioms full_one_zero_first_physical
end BB6.Agent2EOneZeroFullFirst
