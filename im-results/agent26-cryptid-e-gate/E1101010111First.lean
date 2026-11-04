import Lean.Elab.Tactic.Omega
import E1101010111Pairs
import A1100First
import PrefixENoFSource
import NoEarlierF

namespace BB6.Agent26E1101010111First

open CryptidBoundary
open BB6.Agent26E1101010111
open BB6.CryptidPrefixFirstReturn
open BB6.CryptidFirstReturn

set_option maxHeartbeats 18000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

/-- Physical F/0 at blank left; stronger than merely visiting state F. -/
def NoPhysical (c : Cfg) (n : Nat) : Prop :=
  ∀ t, t < n → ¬ Physical (run t c)

private theorem noF_to_noPhysical (c : Cfg) (n : Nat)
    (h : NoF c n) : NoPhysical c n := by
  intro t ht hp
  exact h t ht hp.1

private theorem append_noPhysical (c d : Cfg) (a b : Nat)
    (hca : NoPhysical c a) (hcd : run a c = d)
    (hdb : NoPhysical d b) : NoPhysical c (a+b) := by
  intro t ht
  by_cases hsmall : t < a
  · exact hca t hsmall
  · have heq : t = a+(t-a) := by omega
    rw [heq, run_add, hcd]
    exact hdb (t-a) (by omega)

private theorem scanner_noF (n : Nat) (L ys : List Bool) :
    NoF (scanStart n L ys) (2*n) := by
  induction n generalizing L ys with
  | zero =>
      intro t ht
      omega
  | succ n ih =>
      have ht : 2*(n+1) = 2+2*n := by omega
      rw [ht]
      apply (show ∀ (c d : Cfg) (a b : Nat),
        NoF c a → run a c = d → NoF d b → NoF c (a+b) from
        (by
          intro c d a b h1 he h2 t hlt
          by_cases hsmall : t<a
          · exact h1 t hsmall
          · have heq : t=a+(t-a) := by omega
            rw [heq,run_add,he]
            exact h2 (t-a) (by omega)))
        (scanStart (n+1) L ys) (scanStart n ([false,true]++L) ys)
        2 (2*n)
      · intro t hlt
        have hc : t=0 ∨ t=1 := by omega
        rcases hc with rfl | rfl
        all_goals simp [scanStart,run,step,goL,goR,pairs]
      · exact scan_step n L ys
      · exact ih ([false,true]++L) ys

private theorem e_first2_noF (m q : Nat) (ys : List Bool) :
    NoF (eStart m q ys) 2 := by
  intro t ht
  have hc : t=0 ∨ t=1 := by omega
  rcases hc with rfl | rfl
  all_goals simp [eStart,run,step,goL,goR,pairs]

private theorem a_turn33_noF (L ys : List Bool) :
    NoF (⟨false::L,false,wordE ys,0⟩ : Cfg) 33 := by
  intro t ht
  have hc : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨ t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14 ∨ t = 15 ∨ t = 16 ∨ t = 17 ∨ t = 18 ∨ t = 19 ∨ t = 20 ∨ t = 21 ∨ t = 22 ∨ t = 23 ∨ t = 24 ∨ t = 25 ∨ t = 26 ∨ t = 27 ∨ t = 28 ∨ t = 29 ∨ t = 30 ∨ t = 31 ∨ t = 32 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [wordE,run,step,goL,goR]

private theorem cWalk_noF (n : Nat) (L ys : List Bool) :
    NoF (cWalk n L ys) (2*n) := by
  induction n generalizing ys with
  | zero =>
      intro t ht
      omega
  | succ n ih =>
      have ht : 2*(n+1)=2+2*n := by omega
      rw [ht]
      have hfirst : NoF (cWalk (n+1) L ys) 2 := by
        intro t hlt
        have hc : t=0 ∨ t=1 := by omega
        rcases hc with rfl | rfl
        all_goals simp [cWalk,oppairs,run,step,goL,goR]
      intro t hlt
      by_cases hsmall : t<2
      · exact hfirst t hsmall
      · have heq : t=2+(t-2) := by omega
        rw [heq,run_add,cWalk_step]
        exact ih (true::true::ys) (t-2) (by omega)

private theorem d_before_c_noF (m q : Nat) (ys : List Bool) :
    NoF
      (⟨true::(oppairs q++(pairs (m+2)++[true,true])),
        false,wordD ys,3⟩ : Cfg) 1 := by
  intro t ht
  have hz : t=0 := by omega
  subst t
  simp [run]

/-- The sole intermediate state-F encounter in the four C-base steps
    retains nonblank cells to the left for all m and all right suffixes. -/
private theorem cBase_noPhysical (m : Nat) (ys : List Bool) :
    NoPhysical
      (⟨pairs (m+2)++[true,true],true,ys,2⟩ : Cfg) 4 := by
  intro t ht hp
  have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
  rcases hc with rfl | rfl | rfl | rfl
  all_goals simp [Physical,run,step,goL,goR,pairs] at hp

/-- All q and arbitrary suffixes: no physical return in E's scanner,
    the 33-step A turn, the C walk, or the exceptional C-to-B join. -/
theorem e_front_firstPhysical (m q : Nat) (ys : List Bool) :
    NoPhysical (eStart m q ys) (4*q+42) := by
  let L := pairs (m+2)++[true,true]
  let s : Cfg := scanStart (q+1) L (wordE ys)
  let a : Cfg := ⟨oppairs (q+1)++L,false,wordE ys,0⟩
  let d : Cfg := ⟨true::(oppairs q++L),false,wordD ys,3⟩
  let c : Cfg := cWalk q L (true::wordD ys)
  let doneC : Cfg :=
      ⟨L,true,List.replicate (2*q) true++(true::wordD ys),2⟩
  have h1 : run 2 (eStart m q ys) = s := e_two m q ys
  have h2 : run (2*(q+1)) s = a := by
    dsimp [s,a]
    rw [scan_run]
  have h3 : run 33 a = d := by
    change run 33
      (⟨false::true::(oppairs q++L),false,wordE ys,0⟩ : Cfg) = d
    rw [a_turn]
    rfl
  have h4 : run 1 d = c := by
    dsimp [d,c,L]
    exact d_to_c m q ys
  have h5 : run (2*q) c = doneC := by
    dsimp [c,doneC]
    rw [cWalk_run]
  have h6 : run 4 doneC = sweepB m (bWord q ys) := by
    dsimp [doneC,L]
    rw [cBase]
    rfl
  have hnp1 : NoPhysical (eStart m q ys) 2 :=
    noF_to_noPhysical _ _ (e_first2_noF m q ys)
  have hnp2 : NoPhysical s (2*(q+1)) :=
    noF_to_noPhysical _ _ (scanner_noF (q+1) L (wordE ys))
  have hnp3 : NoPhysical a 33 := by
    apply noF_to_noPhysical
    dsimp [a]
    change NoF
      (⟨false::true::(oppairs q++L),false,wordE ys,0⟩ : Cfg) 33
    exact a_turn33_noF (true::(oppairs q++L)) ys
  have hnp4 : NoPhysical d 1 := by
    dsimp [d,L]
    exact noF_to_noPhysical _ _ (d_before_c_noF m q ys)
  have hnp5 : NoPhysical c (2*q) :=
    noF_to_noPhysical _ _ (cWalk_noF q L (true::wordD ys))
  have hnp6 : NoPhysical doneC 4 := by
    dsimp [doneC,L]
    exact cBase_noPhysical m
      (List.replicate (2*q) true++(true::wordD ys))
  have hall : NoPhysical (eStart m q ys)
      (2+(2*(q+1)+(33+(1+((2*q)+4))))) :=
    append_noPhysical (eStart m q ys) s 2
      (2*(q+1)+(33+(1+((2*q)+4)))) hnp1 h1
      (append_noPhysical s a (2*(q+1)) (33+(1+((2*q)+4)))
        hnp2 h2
        (append_noPhysical a d 33 (1+((2*q)+4))
          hnp3 h3
          (append_noPhysical d c 1 ((2*q)+4)
            hnp4 h4
            (append_noPhysical c doneC (2*q) 4 hnp5 h5 hnp6))))
  have ht : 2+(2*(q+1)+(33+(1+((2*q)+4))))=4*q+42 := by omega
  simpa only [ht] using hall

theorem e_firstPhysical (m q : Nat) (ys : List Bool) :
    NoPhysical (eStart m q ys) (2*m+4*q+45) := by
  have ht : 2*m+4*q+45=(4*q+42)+(2*m+3) := by omega
  rw [ht]
  exact append_noPhysical (eStart m q ys)
    (sweepB m (bWord q ys)) (4*q+42) (2*m+3)
    (e_front_firstPhysical m q ys) (e_to_b m q ys)
    (noF_to_noPhysical _ _
      (fun t hlt => sweepB_firstF m (bWord q ys) t hlt))

/-- Exact first physically blank-left F/0 return of the original E family. -/
theorem full_E_1101010111_first_return (k q : Nat) (ys : List Bool) :
    let duration := 12*k*k+49*k+80+4*q
    let initial := init (List.replicate (3*k+2) true ++
      false::(pairs q ++ wordE ys))
    run duration initial =
      ⟨[],false,List.replicate (8*k+5) true ++ bWord q ys,5⟩ ∧
    ∀ t, 0<t → t<duration → ¬ IsPhysicalReturn (run t initial) := by
  dsimp
  constructor
  · exact full_E_1101010111_pairs k q ys
  · intro t hpos hlt hphys
    by_cases hbefore : t<12*k*k+41*k+33
    · exact (prefixE_positive_noF k (pairs q++wordE ys)
        t hpos hbefore) hphys.1
    · have hprefix :
        run (12*k*k+41*k+33)
          (init (List.replicate (3*k+2) true ++
            false::(pairs q++wordE ys))) = eStart (4*k+1) q ys := by
        rw [prefix_E]
        rfl
      have htime : t=(12*k*k+41*k+33)+(t-(12*k*k+41*k+33)) := by omega
      have hrest : t-(12*k*k+41*k+33) <
          2*(4*k+1)+4*q+45 := by omega
      rw [htime,run_add,hprefix] at hphys
      apply (e_firstPhysical (4*k+1) q ys)
        (t-(12*k*k+41*k+33)) hrest
      exact ⟨hphys.1,by simp [hphys.2.2]⟩

#print axioms e_front_firstPhysical
#print axioms e_firstPhysical
#print axioms full_E_1101010111_first_return
end BB6.Agent26E1101010111First
