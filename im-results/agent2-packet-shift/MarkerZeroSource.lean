import Lean.Elab.Tactic.Omega
import P2MarkerA
import PacketNormalizeSource
import BoundaryPadding
import BoundaryBZero
import PacketP2ResetSource
import CryptidPairs
import EAltMarkerAll

namespace BB6.Agent2MarkerZero
open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent31PacketRank BB6.Agent2PacketNormalizeSource
open BB6.BoundaryPadding BB6.Padding
open BB6.Agent2BoundaryBZero

set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

/-- A regular finite-tail family. The actual tape is blank beyond this list. -/
def marker (m : Nat) : List Bool := oppairs m ++ [false]
def code (q r m : Nat) : List Bool :=
  BB6.Agent35MarkerA.code q r ++ List.replicate (m+1) false

private theorem oppairs_add (q r : Nat) :
    oppairs (q+r) = oppairs q ++ oppairs r := by
  induction q with
  | zero => simp [oppairs]
  | succ q ih => simp [Nat.succ_add,oppairs,ih]

theorem oppairs_false (q : Nat) :
    oppairs q ++ [false] = false :: pairs q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simpa [oppairs,pairs,List.append_assoc] using
      congrArg (fun xs : List Bool => false :: true :: xs) ih

/-- 1(01)^m0 is the valid A code (10)^(m+1) for every m. -/
theorem one_marker (m : Nat) :
    true :: marker m = pairs (m+1) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change true :: false :: (true :: marker m) =
      true :: false :: pairs (m+1)
    exact congrArg (fun x : List Bool => true :: false :: x) ih

private theorem code_word (q r m : Nat) :
    CryptidA.wordCode (code q r m) =
      pairs q ++ (List.replicate (3*r) true ++
        pairs (m+1)) := by
  unfold code
  rw [BB6.Agent35MarkerA.code_append,
    BB6.Agent35MarkerA.code_word]
  rw [BB6.Agent35MarkerA.pair_code]
  simp [List.append_assoc]

private theorem a_tail (q r m : Nat) :
    pairs q ++ (List.replicate (3*r+1) true ++ marker m) =
      CryptidA.wordCode (code q r m) := by
  have hp : List.replicate (3*r+1) true =
      List.replicate (3*r) true ++ [true] := by
    rw [show 3*r+1=(3*r)+1 by omega,
      ←List.replicate_append_replicate]
    rfl
  calc
    _ = pairs q ++ (List.replicate (3*r) true ++
          (true :: marker m)) := by
            rw [hp]
            simp [List.append_assoc]
    _ = pairs q ++ (List.replicate (3*r) true ++
          pairs (m+1)) := by rw [one_marker]
    _ = _ := (code_word q r m).symm

private theorem a_shape (ka q r m : Nat) :
    packet (3*ka+3) q (3*r+1) (marker m) =
      init (List.replicate (3*ka+1) true ++
        false :: CryptidA.wordCode (code q r m)) := by
  have hn : List.replicate (3*ka+3) true =
      true :: true :: List.replicate (3*ka+1) true := by
    rw [show 3*ka+3=2+(3*ka+1) by omega,
      ←List.replicate_append_replicate]
    rfl
  have hw : pairs q ++
      (List.replicate (3*r+1) true ++ marker m) =
      CryptidA.wordCode (code q r m) := a_tail q r m
  have hs : oppairs q ++
      (false :: (List.replicate (3*r+1) true ++ marker m)) =
      false :: CryptidA.wordCode (code q r m) := by
    calc
      _ = (oppairs q ++ [false]) ++
        (List.replicate (3*r+1) true ++ marker m) := by
          simp [List.append_assoc]
      _ = _ := by
        rw [oppairs_false]
        exact congrArg (List.cons false) hw
  simp only [packet,word,init,List.cons_append]
  rw [hn,hs]
  rfl

def aCost (ka q r m : Nat) : Nat :=
  (12*ka*ka+41*ka+32) +
    (CryptidA.wordCost (4*ka+3) (code q r m) +
     (2*((4*ka+3)+CryptidA.wordInc (code q r m))+6))
def aUnary (ka q r m : Nat) : Nat :=
  2*((4*ka+3)+CryptidA.wordInc (code q r m))+5

theorem a_one (ka q r m : Nat) :
    run (aCost ka q r m)
      (packet (3*ka+3) q (3*r+1) (marker m)) =
      (⟨[],false,List.replicate (aUnary ka q r m) true,5⟩ : Cfg) := by
  rw [a_shape]
  exact BB6.Agent32Code.full_A_code_implicit_nil ka (code q r m)

private theorem regularPad (a m : Nat) :
    ObsEq
      (⟨[],false,List.replicate a true ++
        (oppairs m ++ [false]),5⟩ : Cfg)
      (regularSection a m 0) := by
  have h := BB6.BoundaryPadding.source_pad 0 0 1
    (regularSection a m 0)
  change CfgEq
    (represent
      (⟨[],false,List.replicate a true ++
        (oppairs m ++ [false]),5⟩ : Cfg))
    (represent (regularSection a m 0))
  simpa [regularSection,CryptidBoundary.run,List.append_assoc] using
    (cfgEq_symm h)

theorem b_zero (kb p m : Nat) :
    ObsEq
      (run (12*kb*kb+49*kb+40)
        (packet (3*kb+2) 0 p (marker m)))
      (regularSection (8*kb+9+p) m 0) := by
  rw [BB6.Agent2PacketP2Reset.b_zero_any]
  change ObsEq
    (⟨[],false,List.replicate (8*kb+9+p) true ++
      (oppairs m ++ [false]),5⟩ : Cfg)
    (regularSection (8*kb+9+p) m 0)
  exact regularPad _ _

private theorem e_one_exact (a q m : Nat) :
    packet a q 1 (marker m) =
      (⟨[],false,List.replicate a true ++
        (oppairs (q+m+1) ++ [false]),5⟩ : Cfg) := by
  have hop : oppairs (q+m+1) =
      oppairs q ++ ([false,true] ++ oppairs m) := by
    rw [show q+m+1=q+(m+1) by omega,oppairs_add]
    rfl
  simp only [packet,word,List.replicate_one,
    List.singleton_append,hop]
  simp [marker,List.append_assoc]

theorem e_one (a q m : Nat) :
    ObsEq (packet a q 1 (marker m))
      (regularSection a (q+m+1) 0) := by
  rw [e_one_exact]
  exact regularPad _ _

theorem terminal_one (d : Packet) (m : Nat)
    (ha : d.a ≥ 4) (hp : d.p % 3 = 1)
    (hc : d.a % 3 = 0 ∨
      (d.a % 3 = 2 ∧ d.q = 0) ∨
      (d.a % 3 = 1 ∧ (d.p = 0 ∨ d.p = 1))) :
    ∃ T a r b,
      ObsEq (run T (packet d.a d.q d.p (marker m)))
        (regularSection a r b) := by
  rcases hc with hA | hB | hE
  · let ka := (d.a-3)/3
    let rr := d.p/3
    have ha' : d.a=3*ka+3 := by dsimp [ka]; omega
    have hp' : d.p=3*rr+1 := by dsimp [rr]; omega
    refine ⟨aCost ka d.q rr m,aUnary ka d.q rr m,0,0,?_⟩
    rw [ha',hp',a_one]
    change CfgEq
      (BB6.BoundaryPadding.represent
        (⟨[],false,List.replicate (aUnary ka d.q rr m) true,5⟩ : Cfg))
      (BB6.BoundaryPadding.represent
        (regularSection (aUnary ka d.q rr m) 0 0))
    simpa [regularSection,oppairs] using
      (cfgEq_refl (BB6.BoundaryPadding.represent
        (⟨[],false,List.replicate (aUnary ka d.q rr m) true,5⟩ : Cfg)))
  · obtain ⟨hB,hq⟩ := hB
    let kb := (d.a-2)/3
    have ha' : d.a=3*kb+2 := by dsimp [kb]; omega
    refine ⟨12*kb*kb+49*kb+40,8*kb+9+d.p,m,0,?_⟩
    rw [ha',hq]
    exact b_zero kb d.p m
  · obtain ⟨hE,hsmall⟩ := hE
    have hp1 : d.p=1 := by omega
    refine ⟨0,d.a,d.q+m+1,0,?_⟩
    rw [hp1]
    exact e_one d.a d.q m

/-- Unbounded marker depth, unary prefix and packet rank: all p=1 mod3
    packets return to canonical regular L through the ORIGINAL six-state
    primitive-step source machine and the well-founded packet normalizer. -/
theorem all_p1_regular (m : Nat) (c : Packet) (ha : c.a ≥ 4)
    (hp : c.p % 3 = 1) :
    ∃ T a r b,
      ObsEq (run T (packet c.a c.q c.p (marker m)))
        (regularSection a r b) := by
  let d : Packet := (normalizeWithCount c).2
  obtain ⟨T,hraw⟩ := normalized_original_source c ha (marker m)
  have hb : d.a % 3 = 0 ∨
      (d.a % 3 = 2 ∧ d.q=0) ∨
      (d.a % 3 = 1 ∧ (d.p=0 ∨ d.p=1)) :=
    BB6.Agent2PacketSafe.normalize_safe_exit c ha (by omega)
  have hamin : d.a ≥ 4 :=
    BB6.Agent2PacketSafe.normalize_amin c ha
  have hpmod : d.p % 3=1 :=
    (BB6.Agent2PacketSafe.normalize_pmod c).trans hp
  obtain ⟨n,a,r,b,hboundary⟩ :=
    terminal_one d m hamin hpmod hb
  refine ⟨T+n,a,r,b,?_⟩
  change run T (packet c.a c.q c.p (marker m)) =
    packet d.a d.q d.p (marker m) at hraw
  rw [run_add,hraw]
  exact hboundary

#print axioms one_marker
#print axioms a_one
#print axioms b_zero
#print axioms e_one
#print axioms all_p1_regular
end BB6.Agent2MarkerZero
