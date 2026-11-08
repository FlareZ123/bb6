import Lean.Elab.Tactic.Omega
import P2MarkerA
import PacketNormalizeSource
import BoundaryPadding
import BoundaryBZero
import PacketP2ResetSource
import CryptidPairs

namespace BB6.Agent2MarkerTwo
open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent31PacketRank BB6.Agent2PacketNormalizeSource
open BB6.BoundaryPadding BB6.Padding
open BB6.Agent2BoundaryBZero

set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

/-- The suffix after an E-zero exit on the exceptional 01010111 marker. -/
def markerTwo : List Bool := [false,true,false,true,true,true]
def markerThree : List Bool := BB6.Agent2PacketP2Reset.marker
def finalCode (q r : Nat) : List Bool :=
  BB6.Agent35MarkerA.code q r ++ [false,false,true]

private theorem oppairs_add (q r : Nat) :
    oppairs (q+r) = oppairs q ++ oppairs r := by
  induction q with
  | zero => simp [oppairs]
  | succ q ih => simp [Nat.succ_add,oppairs,ih]

private theorem oppairs_false (q : Nat) :
    oppairs q ++ [false] = false :: pairs q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simpa [oppairs,pairs,List.append_assoc] using
      congrArg (fun xs : List Bool => false :: true :: xs) ih

/-- A p=1 mod3 marker-two packet is a fully coded A source with implicit
    blank after the final 111 token. -/
private theorem a_shape (ka q r : Nat) :
    packet (3*ka+3) q (3*r+1) markerTwo =
      init (List.replicate (3*ka+1) true ++
        false :: CryptidA.wordCode (finalCode q r)) := by
  have hn : List.replicate (3*ka+3) true =
      true :: true :: List.replicate (3*ka+1) true := by
    rw [show 3*ka+3=2+(3*ka+1) by omega,
      ←List.replicate_append_replicate]
    rfl
  have hw : pairs q ++
      (List.replicate (3*r+1) true ++ markerTwo) =
      CryptidA.wordCode (finalCode q r) := by
    rw [finalCode,BB6.Agent35MarkerA.code_append,
        BB6.Agent35MarkerA.code_word]
    have hp : List.replicate (3*r+1) true =
        List.replicate (3*r) true ++ [true] := by
      rw [show 3*r+1=3*r+1 by omega,
          ←List.replicate_append_replicate]
      rfl
    rw [hp]
    simp [markerTwo,CryptidA.wordCode,List.append_assoc]
  have hs : oppairs q ++
      (false :: (List.replicate (3*r+1) true ++ markerTwo)) =
      false :: CryptidA.wordCode (finalCode q r) := by
    calc
      _ = (oppairs q ++ [false]) ++
        (List.replicate (3*r+1) true ++ markerTwo) := by
          simp [List.append_assoc]
      _ = _ := by rw [oppairs_false,hw]; rfl
  simp only [packet,word,init,List.cons_append]
  rw [hn,hs]
  rfl

def aCost (ka q r : Nat) : Nat :=
  (12*ka*ka+41*ka+32) +
    (CryptidA.wordCost (4*ka+3) (finalCode q r) +
     (2*((4*ka+3)+CryptidA.wordInc (finalCode q r))+6))

def aUnary (ka q r : Nat) : Nat :=
  2*((4*ka+3)+CryptidA.wordInc (finalCode q r))+5

/-- Every A terminal with p≡1 mod3 returns to physical pure unary. -/
theorem a_one (ka q r : Nat) :
    run (aCost ka q r)
      (packet (3*ka+3) q (3*r+1) markerTwo) =
      (⟨[],false,List.replicate (aUnary ka q r) true,5⟩ : Cfg) := by
  rw [a_shape]
  exact BB6.Agent32Code.full_A_code_implicit_nil ka (finalCode q r)

theorem b_zero (kb p : Nat) :
    run (12*kb*kb+49*kb+40) (packet (3*kb+2) 0 p markerTwo) =
      regularSection (8*kb+9+p) 2 2 := by
  rw [BB6.Agent2PacketP2Reset.b_zero_any]
  simp [regularSection,markerTwo,oppairs,List.append_assoc]

theorem e_one (a q : Nat) :
    packet a q 1 markerTwo = regularSection a (q+3) 2 := by
  rw [show q+3=q+3 by rfl]
  simp only [packet,word,regularSection,List.replicate_one,
    List.singleton_append]
  rw [oppairs_add]
  simp [markerTwo,oppairs,List.append_assoc]

theorem terminal_one (d : Packet)
    (ha : d.a ≥ 4) (hp : d.p % 3 = 1)
    (hc : d.a % 3 = 0 ∨
      (d.a % 3 = 2 ∧ d.q = 0) ∨
      (d.a % 3 = 1 ∧ (d.p = 0 ∨ d.p = 1))) :
    ∃ T a r b,
      ObsEq (run T (packet d.a d.q d.p markerTwo))
        (regularSection a r b) := by
  rcases hc with hA | hB | hE
  · let ka := (d.a-3)/3
    let rr := d.p/3
    have ha' : d.a=3*ka+3 := by dsimp [ka]; omega
    have hp' : d.p=3*rr+1 := by dsimp [rr]; omega
    refine ⟨aCost ka d.q rr,aUnary ka d.q rr,0,0,?_⟩
    rw [ha',hp',a_one]
    change ObsEq
      (⟨[],false,List.replicate (aUnary ka d.q rr) true,5⟩ : Cfg)
      (⟨[],false,List.replicate (aUnary ka d.q rr) true ++
        (oppairs 0 ++ List.replicate 0 true),5⟩ : Cfg)
    simpa [oppairs] using
      (cfgEq_refl (⟨[],false,List.replicate (aUnary ka d.q rr) true,5⟩ : Cfg))
  · obtain ⟨hB,hq⟩ := hB
    let kb := (d.a-2)/3
    have ha' : d.a=3*kb+2 := by dsimp [kb]; omega
    refine ⟨12*kb*kb+49*kb+40,8*kb+9+d.p,2,2,?_⟩
    rw [ha',hq,b_zero]
    exact cfgEq_refl _
  · obtain ⟨hE,hsmall⟩ := hE
    have hp1 : d.p=1 := by omega
    refine ⟨0,d.a,d.q+3,2,?_⟩
    change ObsEq (packet d.a d.q d.p markerTwo)
      (regularSection d.a (d.q+3) 2)
    rw [hp1,e_one]
    exact cfgEq_refl _

/-- Universal all-depth source reentry for the new marker and p≡1 mod3. -/
theorem all_one_regular (c : Packet) (ha : c.a ≥ 4)
    (hp : c.p % 3 = 1) :
    ∃ T a r b,
      ObsEq (run T (packet c.a c.q c.p markerTwo))
        (regularSection a r b) := by
  let d : Packet := (normalizeWithCount c).2
  obtain ⟨T,hraw⟩ := normalized_original_source c ha markerTwo
  have hb : d.a % 3 = 0 ∨
      (d.a % 3 = 2 ∧ d.q=0) ∨
      (d.a % 3 = 1 ∧ (d.p=0 ∨ d.p=1)) :=
    BB6.Agent2PacketSafe.normalize_safe_exit c ha (by omega)
  have hamin : d.a ≥ 4 :=
    BB6.Agent2PacketSafe.normalize_amin c ha
  have hpmod : d.p % 3=1 :=
    (BB6.Agent2PacketSafe.normalize_pmod c).trans hp
  obtain ⟨n,a,r,b,hboundary⟩ :=
    terminal_one d hamin hpmod hb
  refine ⟨T+n,a,r,b,?_⟩
  change run T (packet c.a c.q c.p markerTwo) =
    packet d.a d.q d.p markerTwo at hraw
  rw [run_add,hraw]
  exact hboundary

private theorem marker_three_shape :
    markerThree = false :: [true,false,true,false,true,true,true] := by
  rfl

/-- Exact original six-state E,p0 input with the original marker. -/
private theorem e_zero_input (k q : Nat) :
    packet (3*k+4) q 0 markerThree =
      init (List.replicate (3*k+2) true ++
        false :: (pairs q ++
          (false :: [true,false,true,false,true,true,true]))) := by
  have hn : List.replicate (3*k+4) true =
      true::true::List.replicate (3*k+2) true := by
    rw [show 3*k+4=2+(3*k+2) by omega,
      ←List.replicate_append_replicate]
    rfl
  have hw : oppairs q ++ (false :: markerThree) =
      false :: (pairs q ++
        (false :: [true,false,true,false,true,true,true])) := by
    rw [marker_three_shape]
    calc
      _ = (oppairs q ++ [false]) ++
        (false :: [true,false,true,false,true,true,true]) := by
          simp [List.append_assoc]
      _ = _ := by rw [oppairs_false]; rfl
  simp only [packet,word,init,List.replicate_zero,
    List.nil_append,List.cons_append]
  rw [hn,hw]
  rfl

/-- Unrestricted q,k exact E-zero reset to the shorter 010111 marker. -/
theorem e_zero_reset (k q : Nat) :
    run (12*k*k+49*k+50+4*q)
      (packet (3*k+4) q 0 markerThree) =
      packet (8*k+5) 0 (2*q+7) markerTwo := by
  rw [e_zero_input]
  rw [full_E_pairs]
  have hr : List.replicate (2*q+7) true =
      List.replicate (2*q+6) true ++ [true] := by
    rw [show 2*q+7=(2*q+6)+1 by omega,
      ←List.replicate_append_replicate]
    rfl
  simp [packet,word,markerTwo,oppairs,hr,List.append_assoc]

/-- For ALL k and q divisible by three, the original E-zero exceptional
    marker returns to canonical L in finite primitive original-machine time. -/
theorem all_e_zero_q0_regular (k u : Nat) :
    ∃ T a r b,
      ObsEq
        (run T
          (packet (3*k+4) (3*u) 0 markerThree))
        (regularSection a r b) := by
  let c : Packet := ⟨8*k+5,0,2*(3*u)+7⟩
  have ha : c.a ≥ 4 := by dsimp [c]; omega
  have hp : c.p % 3=1 := by dsimp [c]; omega
  obtain ⟨T,a,r,b,h⟩ := all_one_regular c ha hp
  refine ⟨12*k*k+49*k+50+4*(3*u)+T,a,r,b,?_⟩
  rw [run_add,e_zero_reset]
  exact h

#print axioms a_one
#print axioms b_zero
#print axioms e_one
#print axioms all_one_regular
#print axioms e_zero_reset
#print axioms all_e_zero_q0_regular
end BB6.Agent2MarkerTwo
