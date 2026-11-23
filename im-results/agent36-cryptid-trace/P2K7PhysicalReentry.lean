import Lean.Elab.Tactic.Omega
import P2K7Source
import BoundaryPadding
import BoundaryBZero

/-!
  The k ≡ 25 (mod 27) exceptional Cryptid D E/p=2 cylinder is
  physically regularizing for *every* q.  Its three exact original-source
  return formulas are in Agent35K7; the only missing interface is the
  far-blank quotient for the q≡1 return and the canonical output coercions.
-/

namespace BB6.Agent36K7Physical

open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent35K7
open BB6.Agent35K7Shapes (code codeTail)
open BB6.Agent2BoundaryBZero
open BB6.BoundaryPadding

set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

private theorem zero_tail (n : Nat) :
    (⟨[],false,List.replicate n true ++
      [true,false,true,false,true,true,true],5⟩ : Cfg) =
      regularSection (n+1) 2 2 := by
  have hr : List.replicate (n+1) true =
      List.replicate n true ++ [true] := by
    calc
      List.replicate (n+1) true =
          List.replicate n true ++ List.replicate 1 true := by
            rw [List.replicate_append_replicate]
      _ = _ := by rfl
  simp [regularSection, oppairs, hr, List.append_assoc]

private theorem one_tail (n : Nat) :
    ObsEq
      (⟨[],false,List.replicate n true ++
        [false,true,false,true,false,true,false,true,false],5⟩ : Cfg)
      (regularSection n 4 0) := by
  have h := source_pad 0 0 1 (regularSection n 4 0)
  change ObsEq
    (regularSection n 4 0)
    (⟨[],false,
      (List.replicate n true ++
        (oppairs 4 ++ List.replicate 0 true)) ++ [false],5⟩ : Cfg) at h
  simpa [ObsEq,regularSection,run,oppairs,List.append_assoc] using
    (BB6.Padding.cfgEq_symm h)

private theorem two_tail (n : Nat) :
    (⟨[],false,List.replicate n true,5⟩ : Cfg) =
      regularSection n 0 0 := by
  simp [regularSection,oppairs]

private theorem close_zero_regular (t u : Nat) :
    ∃ T a q b, ObsEq
      (run T
        (packet (3*firstK t+4) (3*u) 2
          (false::List.replicate 6 true)))
      (regularSection a q b) := by
  let ka := aK t
  let ws := code u
  let n := 2*((4*ka+3)+CryptidA.wordInc ws)+5
  let finalTime := (12*ka*ka+41*ka+32) +
    (CryptidA.wordCost (4*ka+3) ws +
      (2*((4*ka+3)+CryptidA.wordInc ws)+6))
  refine ⟨beforeATime t (3*u)+finalTime,n+1,2,2,?_⟩
  have h :
      run (beforeATime t (3*u)+finalTime)
        (packet (3*firstK t+4) (3*u) 2
          (false::List.replicate 6 true)) =
      (⟨[],false,List.replicate n true ++
        [true,false,true,false,true,true,true],5⟩ : Cfg) := by
    simpa only [ka,ws,n,finalTime] using
      (BB6.Agent35K7.close_zero t u)
  rw [h,zero_tail]
  exact BB6.Padding.cfgEq_refl _

private theorem close_one_regular (t u : Nat) :
    ∃ T a q b, ObsEq
      (run T
        (packet (3*firstK t+4) (3*u+1) 2
          (false::List.replicate 6 true)))
      (regularSection a q b) := by
  let ka := aK t
  let ws := code u
  let m := 4*ka+3+CryptidA.wordInc ws
  let n := 2*m+5
  let finalTime := (12*ka*ka+41*ka+32) +
    (CryptidA.wordCost (4*ka+3) ws + (2*m+36))
  refine ⟨beforeATime t (3*u+1)+finalTime,n,4,0,?_⟩
  have h :
      run (beforeATime t (3*u+1)+finalTime)
        (packet (3*firstK t+4) (3*u+1) 2
          (false::List.replicate 6 true)) =
      (⟨[],false,List.replicate n true ++
        [false,true,false,true,false,true,false,true,false],5⟩ : Cfg) := by
    simpa only [ka,ws,m,n,finalTime] using
      (BB6.Agent35K7.close_one t u)
  rw [h]
  exact one_tail n

private theorem close_two_regular (t u : Nat) :
    ∃ T a q b, ObsEq
      (run T
        (packet (3*firstK t+4) (3*u+2) 2
          (false::List.replicate 6 true)))
      (regularSection a q b) := by
  let ka := aK t
  let ws := codeTail u
  let n := 2*((4*ka+3)+CryptidA.wordInc ws)+5
  let finalTime := (12*ka*ka+41*ka+32) +
    (CryptidA.wordCost (4*ka+3) ws +
      (2*((4*ka+3)+CryptidA.wordInc ws)+6))
  refine ⟨beforeATime t (3*u+2)+finalTime,n,0,0,?_⟩
  have h :
      run (beforeATime t (3*u+2)+finalTime)
        (packet (3*firstK t+4) (3*u+2) 2
          (false::List.replicate 6 true)) =
      (⟨[],false,List.replicate n true,5⟩ : Cfg) := by
    simpa only [ka,ws,n,finalTime] using
      (BB6.Agent35K7.close_two t u)
  rw [h,two_tail]
  exact BB6.Padding.cfgEq_refl _

/-- Full q-uniform, source-connected physically regular return for the
    hitherto non-integrated k=27t+25 E/p=2 reset branch. -/
theorem all_k25_regular (t q : Nat) :
    ∃ T a q' b, ObsEq
      (run T
        (packet (3*firstK t+4) q 2
          (false::List.replicate 6 true)))
      (regularSection a q' b) := by
  have hmod : q%3=0 ∨ q%3=1 ∨ q%3=2 := by omega
  rcases hmod with h0 | h1 | h2
  · have hq : q=3*(q/3) := by omega
    rw [hq]
    exact close_zero_regular t (q/3)
  · have hq : q=3*(q/3)+1 := by omega
    rw [hq]
    exact close_one_regular t (q/3)
  · have hq : q=3*(q/3)+2 := by omega
    rw [hq]
    exact close_two_regular t (q/3)

/-- Direct authentic-blank integration interface: an ObsEq rootTime into
    the k=27t+25 cylinder may be composed into a genuine regular source
    section, without claiming that any such rootTime currently exists. -/
theorem chain_k25_regular (c : Cfg) (t q rootTime : Nat)
    (h : ObsEq
      (run rootTime c)
      (packet (3*firstK t+4) q 2
        (false::List.replicate 6 true))) :
    ∃ T a q' b, ObsEq (run T c) (regularSection a q' b) := by
  obtain ⟨tail,a,q',b,htail⟩ := all_k25_regular t q
  exact ⟨rootTime+tail,a,q',b,
    source_chain rootTime tail c
      (packet (3*firstK t+4) q 2
        (false::List.replicate 6 true))
      (regularSection a q' b) h htail⟩

#print axioms all_k25_regular
#print axioms chain_k25_regular
end BB6.Agent36K7Physical
