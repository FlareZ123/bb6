import Lean.Elab.Tactic.Omega
import EZeroMarkerP2Front

namespace BB6.Agent26EZTwo
open CryptidBoundary

set_option maxRecDepth 8192
set_option maxHeartbeats 10000000

/-- E boundary on (10)^(q+1) 110 (10)^r 0 with arbitrary right suffix. -/
def eZ (m q r : Nat) (ys : List Bool) : Cfg :=
  ⟨false::false::pairs (m+2) ++ [true,true],false,
    pairs (q+1) ++ ([true,true,false] ++ (pairs r ++ (false::ys))),4⟩

private theorem eZ_two (m q r : Nat) (ys : List Bool) :
    run 2 (eZ m q r ys) =
    scanStart (q+2) (pairs (m+2) ++ [true,true])
      ([true,true,false] ++ (pairs r ++ (false::ys))) := by
  simp [eZ,scanStart,run,step,goL,goR,pairs]

/-- General C terminal: the suffix after the zero is completely arbitrary. -/
private theorem cZ_finish4 (m t : Nat) (zs : List Bool) :
    run 4
      (⟨pairs (m+2) ++ [true,true],true,
        List.replicate t true ++ (false::zs),2⟩ : Cfg) =
      sweepB m (false::List.replicate (t+3) true ++ (false::zs)) := by
  simp [run,step,goL,goR,pairs,sweepB]
  have h : List.replicate (t+3) true =
      [true,true,true] ++ List.replicate t true := by
    calc
      _ = List.replicate (3+t) true := by rw [Nat.add_comm]
      _ = List.replicate 3 true ++ List.replicate t true :=
        (List.replicate_append_replicate).symm
      _ = _ := rfl
  rw [h]
  rfl

/-- Full exact source turn, q≥2 initial pairs and any number of final
    marker pairs: an unbounded symbolic E/A/C/B source transition. -/
theorem eZ_front_ge2 (m q r : Nat) (ys : List Bool) :
    run (4*(q+2)+22+4*r) (eZ m (q+1) r ys) =
      sweepB m (false::List.replicate (2*(q+2)+2) true ++
        (false::List.replicate (2*r+6) true ++ ys)) := by
  have ht : 4*(q+2)+22+4*r =
      (2+2*(q+3))+((16+4*r)+(2*(q+1)+4)) := by omega
  rw [ht,run_add (2+2*(q+3)) ((16+4*r)+(2*(q+1)+4)),
    run_add 2 (2*(q+3)),eZ_two,scan_run]
  change run ((16+4*r)+(2*(q+1)+4))
    (⟨oppairs (q+3) ++ (pairs (m+2) ++ [true,true]),false,
      [true,true,false] ++ (pairs r ++ (false::ys)),0⟩ : Cfg) = _
  rw [run_add (16+4*r) (2*(q+1)+4),a_front_Z]
  rw [run_add (2*(q+1)) 4,cWalk_run]
  let L : List Bool := pairs (m+2) ++ [true,true]
  let tail : List Bool := List.replicate (2*r+6) true ++ ys
  have hprefix : List.replicate (2*(q+1)) true ++ [true] =
      List.replicate (2*(q+1)+1) true := by
    calc
      _ = List.replicate (2*(q+1)) true ++ List.replicate 1 true := rfl
      _ = List.replicate (2*(q+1)+1) true :=
        List.replicate_append_replicate
  have hp : List.replicate (2*(q+1)) true ++ ([true,false] ++ tail) =
      List.replicate (2*(q+1)+1) true ++ (false::tail) := by
    calc
      _ = (List.replicate (2*(q+1)) true ++ [true]) ++
          (false::tail) := by simp [List.append_assoc]
      _ = _ :=
          congrArg (fun z : List Bool => z ++ (false::tail)) hprefix
  have hcfg :
      (⟨L,true,List.replicate (2*(q+1)) true ++
          ([true,false] ++ tail),2⟩ : Cfg) =
      (⟨L,true,List.replicate (2*(q+1)+1) true ++
          (false::tail),2⟩ : Cfg) :=
    congrArg (fun z : List Bool => (⟨L,true,z,2⟩ : Cfg)) hp
  have hcount : 2*(q+1)+1+3 = 2*(q+2)+2 := by omega
  have hend :
      sweepB m (false::List.replicate (2*(q+1)+1+3) true ++
        (false::tail)) =
      sweepB m (false::List.replicate (2*(q+2)+2) true ++
        (false::tail)) :=
    congrArg (fun z : Nat =>
      sweepB m (false::List.replicate z true ++ (false::tail))) hcount
  exact (congrArg (run 4) hcfg).trans
    ((cZ_finish4 m (2*(q+1)+1) tail).trans hend)

/-- Exact E source return for all q>=2 and arbitrary marker depth and suffix. -/
theorem eZ_run_ge2 (m q r : Nat) (ys : List Bool) :
    run (2*m+4*(q+2)+25+4*r) (eZ m (q+1) r ys) =
      ⟨[],false,List.replicate (2*m+3) true ++
        (false::List.replicate (2*(q+2)+2) true ++
         (false::List.replicate (2*r+6) true ++ ys)),5⟩ := by
  have ht : 2*m+4*(q+2)+25+4*r =
      (4*(q+2)+22+4*r)+(2*m+3) := by omega
  rw [ht,run_add,eZ_front_ge2,sweepB_run]

/-- Uniform ORIGINAL SIX-STATE F-to-F return for an E p2 section with
    at least two leading (10) pairs, retaining arbitrary physical
    continuation after the zero-ended tail. -/
theorem full_E_Z_p2_ge2 (k q r : Nat) (ys : List Bool) :
    run (12*k*k+49*k+60+4*(q+2)+4*r)
      (init (List.replicate (3*k+2) true ++
        false::(pairs (q+2) ++
          ([true,true,false] ++ (pairs r ++ (false::ys)))))) =
      ⟨[],false,List.replicate (8*k+5) true ++
        (false::List.replicate (2*(q+2)+2) true ++
          (false::List.replicate (2*r+6) true ++ ys)),5⟩ := by
  have ht : 12*k*k+49*k+60+4*(q+2)+4*r =
      (12*k*k+41*k+33)+(2*(4*k+1)+4*(q+2)+25+4*r) := by omega
  rw [ht,run_add,prefix_E]
  change run (2*(4*k+1)+4*(q+2)+25+4*r)
    (eZ (4*k+1) (q+1) r ys) = _
  rw [eZ_run_ge2]
  rw [show 2*(4*k+1)+3=8*k+5 by omega]

/-- The q=1 boundary is not covered by the q>=2 alternating prefix,
    but the short A-front turn closes it for every marker depth. -/
theorem eZ_base_front (m r : Nat) (ys : List Bool) :
    run (26+4*r) (eZ m 0 r ys) =
      sweepB m (false::List.replicate 4 true ++
        (false::List.replicate (2*r+6) true ++ ys)) := by
  have ht : 26+4*r = (2+2*2)+((16+4*r)+4) := by omega
  rw [ht,run_add (2+2*2) ((16+4*r)+4),
    run_add 2 (2*2),eZ_two,scan_run]
  change run ((16+4*r)+4)
    (⟨oppairs 2 ++ (pairs (m+2) ++ [true,true]),false,
      [true,true,false] ++ (pairs r ++ (false::ys)),0⟩ : Cfg) = _
  rw [run_add (16+4*r) 4,a_front_Z_short]
  have h := cZ_finish4 m 1 (List.replicate (2*r+6) true ++ ys)
  simpa [cWalk,oppairs] using h

/-- Full arbitrary-symbolic E p2 right grammar, all q>=1 and all
    marker depths; q=1 uses the special short-base A-front proof. -/
theorem eZ_front_all (m q r : Nat) (ys : List Bool) :
    run (4*(q+1)+22+4*r) (eZ m q r ys) =
      sweepB m (false::List.replicate (2*(q+1)+2) true ++
        (false::List.replicate (2*r+6) true ++ ys)) := by
  cases q with
  | zero => simpa using eZ_base_front m r ys
  | succ q => simpa using eZ_front_ge2 m q r ys

theorem eZ_run_all (m q r : Nat) (ys : List Bool) :
    run (2*m+4*(q+1)+25+4*r) (eZ m q r ys) =
      ⟨[],false,List.replicate (2*m+3) true ++
        (false::List.replicate (2*(q+1)+2) true ++
         (false::List.replicate (2*r+6) true ++ ys)),5⟩ := by
  have ht : 2*m+4*(q+1)+25+4*r =
      (4*(q+1)+22+4*r)+(2*m+3) := by omega
  rw [ht,run_add,eZ_front_all,sweepB_run]

/-- Arbitrary 10-pair count >=1, arbitrary zero-marker depth and
    arbitrary suffix, all on the authentic six-state D machine. -/
theorem full_E_Z_p2_all (k q r : Nat) (ys : List Bool) :
    run (12*k*k+49*k+64+4*q+4*r)
      (init (List.replicate (3*k+2) true ++
        false::(pairs (q+1) ++
          ([true,true,false] ++ (pairs r ++ (false::ys)))))) =
      ⟨[],false,List.replicate (8*k+5) true ++
        (false::List.replicate (2*(q+1)+2) true ++
          (false::List.replicate (2*r+6) true ++ ys)),5⟩ := by
  have ht : 12*k*k+49*k+64+4*q+4*r =
      (12*k*k+41*k+33)+(2*(4*k+1)+4*(q+1)+25+4*r) := by omega
  rw [ht,run_add,prefix_E]
  change run (2*(4*k+1)+4*(q+1)+25+4*r)
    (eZ (4*k+1) q r ys) = _
  rw [eZ_run_all]
  rw [show 2*(4*k+1)+3=8*k+5 by omega]

#print axioms eZ_base_front
#print axioms eZ_front_all
#print axioms full_E_Z_p2_all

#print axioms eZ_front_ge2
#print axioms eZ_run_ge2
#print axioms full_E_Z_p2_ge2
end BB6.Agent26EZTwo
