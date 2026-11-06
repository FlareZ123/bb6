import Lean.Elab.Tactic.Omega
import EZeroPump
import EOneZeroLocalFirst
import EOneZero
import EAltBoundaryFirst
import PrefixENoFSource
import NoEarlierF

set_option maxHeartbeats 20000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace BB6.Agent2EZeroFirst
open CryptidBoundary
open BB6.Agent2EAltBoundaryFirst
open BB6.CryptidFirstReturn
open BB6.CryptidPrefixFirstReturn
open BB6.Agent2EZeroPump
open BB6.Agent32EZero

private theorem appendNoPhysical (c d : Cfg) (a b : Nat)
    (hc : NoPhysical c a) (he : run a c = d)
    (hd : NoPhysical d b) : NoPhysical c (a+b) := by
  intro t ht
  by_cases hs : t<a
  · exact hc t hs
  · have heq : t=a+(t-a) := by omega
    rw [heq,run_add,he]
    exact hd (t-a) (by omega)

/-- Every original-source 1100 exceptional E baseline segment is free
    of an earlier physical F/0 return, even though internal F visits occur. -/
private theorem eZero60NoPhysical (m : Nat) (ys : List Bool) :
    NoPhysical (eZero m ys) 60 := by
  intro t ht hp
  have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 ∨ t=7 ∨ t=8 ∨ t=9 ∨ t=10 ∨ t=11 ∨ t=12 ∨ t=13 ∨ t=14 ∨ t=15 ∨ t=16 ∨ t=17 ∨ t=18 ∨ t=19 ∨ t=20 ∨ t=21 ∨ t=22 ∨ t=23 ∨ t=24 ∨ t=25 ∨ t=26 ∨ t=27 ∨ t=28 ∨ t=29 ∨ t=30 ∨ t=31 ∨ t=32 ∨ t=33 ∨ t=34 ∨ t=35 ∨ t=36 ∨ t=37 ∨ t=38 ∨ t=39 ∨ t=40 ∨ t=41 ∨ t=42 ∨ t=43 ∨ t=44 ∨ t=45 ∨ t=46 ∨ t=47 ∨ t=48 ∨ t=49 ∨ t=50 ∨ t=51 ∨ t=52 ∨ t=53 ∨ t=54 ∨ t=55 ∨ t=56 ∨ t=57 ∨ t=58 ∨ t=59 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Physical,eZero,run,step,goL,goR,pairs] at hp

private theorem extended11NoPhysical (m r : Nat) (ys : List Bool) :
    NoPhysical (extended m r ys) 11 := by
  intro t ht hp
  have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 ∨ t=7 ∨ t=8 ∨ t=9 ∨ t=10 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Physical,extended,run,step,goL,goR,pairs] at hp

private def innerLeft (m : Nat) : List Bool :=
    pairs (m+3) ++ [true,true]

private def eMid (m r : Nat) (ys : List Bool) : Cfg :=
    ⟨[false,true,true,false,true]++innerLeft m,false,
      pairs r ++ (false::ys),0⟩

private theorem extended11 (m r : Nat) (ys : List Bool) :
    run 11 (extended m r ys) = eMid m r ys := by
  simp [extended,eMid,innerLeft,run,step,goL,goR,pairs,List.append_assoc]

private theorem midNoPhysical (m r : Nat) (ys : List Bool) :
    NoPhysical (eMid m r ys) (4*r+2) := by
  let L : List Bool := innerLeft m
  let a : Cfg := ⟨L,false,[true,false,true,true,false]++
      (pairs r ++ (false::ys)),0⟩
  have h9 : run 9 a = eMid m r ys := by
    dsimp [a,eMid,L,innerLeft]
    simp [run,step,goL,goR,pairs,List.append_assoc]
  have hno : NoPhysical a (4*r+16) := by
    dsimp [a]
    exact BB6.Agent2EOneZeroLocalFirst.a_one_zero_noPhysical r L ys
  intro t ht hp
  have heq : run (9+t) a = run t (eMid m r ys) := by
    rw [run_add,h9]
  apply hno (9+t) (by omega)
  rw [heq]
  exact hp

private theorem syncedNoPhysical (m r : Nat) (ys : List Bool) :
    NoPhysical (run 13 (eZero m (List.replicate (2*r) true ++ ys))) 47 := by
  intro t ht hp
  have htime : 13+t<60 := by omega
  have hrun : run t (run 13 (eZero m (List.replicate (2*r) true ++ ys))) =
      run (13+t) (eZero m (List.replicate (2*r) true ++ ys)) := by
    rw [run_add]
  rw [hrun] at hp
  exact (eZero60NoPhysical m (List.replicate (2*r) true ++ ys))
    (13+t) htime hp

/-- Strict physical first F/0 event across the new all-r E110(10)^r0
    boundary, including internal intermediate state F visits. -/
theorem e_zero_first_boundary (m r : Nat) (ys : List Bool) :
    NoPhysical (extended m r ys) (2*m+4*r+63) := by
  let middle : Cfg := eMid m r ys
  let synced : Cfg := run 13
    (eZero m (List.replicate (2*r) true ++ ys))
  let zs : List Bool :=
    packetZero ++ (List.replicate (2*r) true ++ ys)
  let last : Cfg := sweepB m zs
  have h1 : run 11 (extended m r ys) = middle :=
    extended11 m r ys
  have h2 : run (4*r+2) middle = synced := by
    have hh := compare13 m r ys
    rw [show 4*r+13 = 11+(4*r+2) by omega, run_add, h1] at hh
    exact hh
  have h3 : run 47 synced = last := by
    have hf := extended_front m r ys
    rw [show 4*r+60=(11+(4*r+2))+47 by omega,
        run_add,run_add,h1,h2] at hf
    exact hf
  have hn0 : NoPhysical (extended m r ys) 11 :=
    extended11NoPhysical m r ys
  have hn1 : NoPhysical middle (4*r+2) :=
    midNoPhysical m r ys
  have hn2 : NoPhysical synced 47 :=
    syncedNoPhysical m r ys
  have hn3 : NoPhysical last (2*m+3) := by
    dsimp [last]
    intro t ht hp
    exact sweepB_firstF m zs t ht hp.1
  have hjoined : NoPhysical (extended m r ys)
      (11+((4*r+2)+(47+(2*m+3)))) :=
    appendNoPhysical (extended m r ys) middle
      11 ((4*r+2)+(47+(2*m+3)))
      hn0 h1
      (appendNoPhysical middle synced (4*r+2) (47+(2*m+3))
        hn1 h2
        (appendNoPhysical synced last 47 (2*m+3) hn2 h3 hn3))
  have ht : 11+((4*r+2)+(47+(2*m+3))) = 2*m+4*r+63 := by omega
  simpa only [ht] using hjoined

theorem full_zero_first_physical (k r : Nat) (ys : List Bool) :
    let t := 12*k*k+49*k+96+4*r
    let xs := List.replicate (3*k+2) true ++
      false :: ([true,true,false] ++ (pairs r ++ (false::ys)))
    let out : Cfg := ⟨[],false,List.replicate (8*k+3) true ++
      (packetZero ++ (List.replicate (2*r) true ++ ys)),5⟩
    run t (init xs) = out ∧
      ∀ u, 0<u → u<t → ¬ Physical (run u (init xs)) := by
  dsimp
  constructor
  · exact full_exceptional_pump k r ys
  · intro u hu ht hp
    let p : Nat := 12*k*k+41*k+33
    by_cases hpre : u<p
    · exact
        (prefixE_positive_noF k
          ([true,true,false] ++ (pairs r ++ (false::ys)))
          u hu hpre) hp.1
    · have heq : u=p+(u-p) := by omega
      rw [heq,run_add] at hp
      have hprefix : run p
          (init (List.replicate (3*k+2) true ++
            false :: ([true,true,false] ++ (pairs r ++ (false::ys))))) =
          extended (4*k) r ys := by
        dsimp [p,extended]
        exact prefix_E k
          ([true,true,false] ++ (pairs r ++ (false::ys)))
      change Physical (run (u-p)
        (run p (init (List.replicate (3*k+2) true ++
          false :: ([true,true,false] ++
            (pairs r ++ (false::ys))))))) at hp
      rw [hprefix] at hp
      exact (e_zero_first_boundary (4*k) r ys)
        (u-p) (by dsimp [p] at *; omega) hp

#print axioms e_zero_first_boundary
#print axioms full_zero_first_physical
end BB6.Agent2EZeroFirst
