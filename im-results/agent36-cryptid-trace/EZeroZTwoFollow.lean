import Lean.Elab.Tactic.Omega
import EZeroZTwo
import CryptidTriplePairs

namespace BB6.Agent36EZeroZTwoFollow
open CryptidBoundary BB6.Agent36EZeroZTwo

set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

def tail7 : List Bool := [false,true,false,true,false,true,false]
def tail13 : List Bool := [false,true,false,true,false,true,false,true,false,true,false,true,false]

def postZ (k r : Nat) : Cfg :=
  ⟨[],false,List.replicate (8*k+3) true ++
    (BB6.Agent32EZero.packetZero ++ List.replicate (2*r) true),5⟩

private theorem b_shape (t r : Nat) :
    postZ (3*t+1) r =
      init (List.replicate (3*(8*t+3)) true ++
        false::(List.replicate 4 true ++ (tail7 ++ List.replicate (2*r) true))) := by
  have hn : List.replicate (8*(3*t+1)+3) true =
    true::true::List.replicate (3*(8*t+3)) true := by
    rw [show 8*(3*t+1)+3=2+3*(8*t+3) by omega,
      ←List.replicate_append_replicate]
    rfl
  simp [postZ, init, hn, BB6.Agent32EZero.packetZero, tail7, List.append_assoc]

/-- Every k=3t+1 E/110 zero marker follows a B return to an
    explicit almost-regular section at exact raw machine time. -/
theorem b_follow (t r : Nat) :
    run (12*(8*t+3)*(8*t+3)+49*(8*t+3)+40) (postZ (3*t+1) r) =
      ⟨[],false,List.replicate (64*t+37) true ++
        (tail7 ++ List.replicate (2*r) true),5⟩ := by
  rw [b_shape, full_B]
  change (⟨[], false,
    List.replicate (8*(8*t+3)+9) true ++
      (List.replicate 4 true ++ (tail7 ++ List.replicate (2*r) true)),5⟩ : Cfg) = _
  have hmerge : List.replicate (8*(8*t+3)+9) true ++
      (List.replicate 4 true ++ (tail7 ++ List.replicate (2*r) true)) =
    List.replicate (64*t+37) true ++ (tail7 ++ List.replicate (2*r) true) := by
    rw [←List.append_assoc, List.replicate_append_replicate]
    rw [show 8*(8*t+3)+9+4=64*t+37 by omega]
  exact congrArg (fun z : List Bool => (⟨[],false,z,5⟩ : Cfg)) hmerge

private theorem e_shape (t r : Nat) :
    postZ (3*t+2) r =
      init (List.replicate (3*(8*t+5)+2) true ++
        false::([true,true,true] ++
          (true::(tail7 ++ List.replicate (2*r) true)))) := by
  have hn : List.replicate (8*(3*t+2)+3) true =
    true::true::List.replicate (3*(8*t+5)+2) true := by
    rw [show 8*(3*t+2)+3=2+(3*(8*t+5)+2) by omega,
      ←List.replicate_append_replicate]
    rfl
  simp [postZ,init,hn,BB6.Agent32EZero.packetZero,tail7,List.append_assoc]

/-- Every k=3t+2 E/110 marker follows an E triple-prefix return. -/
theorem e_follow (t r : Nat) :
    run (12*(8*t+5)*(8*t+5)+49*(8*t+5)+58) (postZ (3*t+2) r) =
      ⟨[],false,List.replicate (64*t+49) true ++
        (tail13 ++ List.replicate (2*r) true),5⟩ := by
  rw [e_shape]
  have h := full_E_triple_pairs (8*t+5) 0
    (true::(tail7 ++ List.replicate (2*r) true))
  have hs : 8*(8*t+5)+9=64*t+49 := by omega
  simpa [pairs,tail7,tail13,oppairs,List.append_assoc,hs] using h

/-- Prepared F section with a concrete trailing zero at the E p2 marker. -/
def input (k r : Nat) : Cfg :=
  init (List.replicate (3*k+2) true ++
    false :: ([true,true,false] ++ (pairs r ++ [false])))

def firstTime (k r : Nat) : Nat := 12*k*k+49*k+96+4*r

def bTime (t : Nat) : Nat :=
  12*(8*t+3)*(8*t+3)+49*(8*t+3)+40

def eTime (t : Nat) : Nat :=
  12*(8*t+5)*(8*t+5)+49*(8*t+5)+58

/-- Two consecutive universally quantified original-machine returns.
    For k ≡ 1 mod 3, the next section is a regular word physically. -/
theorem b_two_return (t r : Nat) :
    run (firstTime (3*t+1) r + bTime t) (input (3*t+1) r) =
      ⟨[],false,List.replicate (64*t+37) true ++
        (tail7 ++ List.replicate (2*r) true),5⟩ := by
  have hfirst : run (firstTime (3*t+1) r) (input (3*t+1) r) =
      postZ (3*t+1) r := by
    simpa only [firstTime,input,postZ,List.append_nil,List.cons_append] using
      (full_E_zero_pairs_all (3*t+1) r [])
  rw [run_add, hfirst]
  exact b_follow t r

/-- Same two-return physical section theorem for k ≡ 2 mod 3. -/
theorem e_two_return (t r : Nat) :
    run (firstTime (3*t+2) r + eTime t) (input (3*t+2) r) =
      ⟨[],false,List.replicate (64*t+49) true ++
        (tail13 ++ List.replicate (2*r) true),5⟩ := by
  have hfirst : run (firstTime (3*t+2) r) (input (3*t+2) r) =
      postZ (3*t+2) r := by
    simpa only [firstTime,input,postZ,List.append_nil,List.cons_append] using
      (full_E_zero_pairs_all (3*t+2) r [])
  rw [run_add, hfirst]
  exact e_follow t r

#print axioms b_two_return
#print axioms e_two_return
#print axioms b_follow
#print axioms e_follow
end BB6.Agent36EZeroZTwoFollow
