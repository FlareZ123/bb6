import Lean.Elab.Tactic.Omega
import Y3SafeNormalizer
import MarkerTowerSource

/-!
  An original-source recursive Y_m=(01)^m11 terminal grammar.

  New A/p=0 source rule for every positive depth Y_(m+1) and arbitrary
  k,q,r,m; this and the existing E/p0 marker drop close deeper
  exceptional paths without a finite-depth cutoff.
-/
namespace BB6.Agent36YSafe

open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent31PacketRank BB6.Agent2PacketNormalizeSource
open BB6.Agent2MarkerTower (marker)
open BB6.Agent2BoundaryBZero
open BB6.BoundaryPadding

set_option maxHeartbeats 12000000
set_option maxRecDepth 8192

private theorem oppairs_false (q : Nat) :
    oppairs q ++ [false] = false :: pairs q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simpa [oppairs,pairs,List.append_assoc] using
      congrArg (fun xs : List Bool => [false,true] ++ xs) ih

private theorem oppairs_snoc (q : Nat) :
    oppairs q ++ [false,true] = oppairs (q+1) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simpa [oppairs,List.append_assoc] using
      congrArg (fun xs : List Bool => [false,true] ++ xs) ih

private theorem a_zero_shape (ka q r m : Nat) :
    packet (3*ka+3) q (3*r) (marker (m+1)) =
      init (List.replicate (3*ka+1) true ++
        false :: (CryptidA.wordCode (BB6.Agent35MarkerA.code q r) ++
          (false :: true :: marker m))) := by
  have hn : List.replicate (3*ka+3) true =
      true :: true :: List.replicate (3*ka+1) true := by
    rw [show 3*ka+3=2+(3*ka+1) by omega,
      ←List.replicate_append_replicate]
    rfl
  have hw : oppairs q ++
      (false :: (List.replicate (3*r) true ++ marker (m+1))) =
      false :: (CryptidA.wordCode (BB6.Agent35MarkerA.code q r) ++
        (false :: true :: marker m)) := by
    calc
      _ = (oppairs q ++ [false]) ++
        (List.replicate (3*r) true ++ marker (m+1)) := by
          simp [List.append_assoc]
      _ = false :: (pairs q ++
        (List.replicate (3*r) true ++ marker (m+1))) := by
          rw [oppairs_false]
          rfl
      _ = false :: (CryptidA.wordCode (BB6.Agent35MarkerA.code q r) ++
        (false :: true :: marker m)) := by
          rw [BB6.Agent35MarkerA.code_word]
          rfl
  simp only [packet,word,init,List.cons_append]
  rw [hn,hw]
  rfl

def aZeroCost (ka q r : Nat) : Nat :=
  BB6.Agent35MarkerA.aTime0 ka q r
def aZeroN (ka q r : Nat) : Nat :=
  2*((4*ka+3)+CryptidA.wordInc (BB6.Agent35MarkerA.code q r))+5

/-- Source-exact A/p0 for arbitrary positive marker depth Y_(m+1). -/
theorem a_zero_original (ka q r m : Nat) :
    run (aZeroCost ka q r)
      (packet (3*ka+3) q (3*r) (marker (m+1))) =
      (⟨[],false,List.replicate (aZeroN ka q r) true ++
        (true :: marker m),5⟩ : Cfg) := by
  rw [a_zero_shape]
  exact BB6.Agent35.full_A_code ka
    (BB6.Agent35MarkerA.code q r) (true :: marker m)

/-- Every A-index, p=0 modulo 3 packet with marker depth >=1
    returns to canonical regular L with arbitrary marker index. -/
theorem a_zero_regular (ka q r m : Nat) :
    ∃ T a Q b,
      ObsEq
        (run T (packet (3*ka+3) q (3*r) (marker (m+1))))
        (regularSection a Q b) := by
  refine ⟨aZeroCost ka q r,aZeroN ka q r+1,m,2,?_⟩
  rw [a_zero_original]
  have hr : List.replicate (aZeroN ka q r+1) true =
      List.replicate (aZeroN ka q r) true ++ [true] := by
    rw [show aZeroN ka q r+1 = aZeroN ka q r + 1 by omega,
        ←List.replicate_append_replicate]
    rfl
  have heq :
      (⟨[],false,
        List.replicate (aZeroN ka q r) true ++ (true :: marker m),5⟩ : Cfg) =
      regularSection (aZeroN ka q r+1) m 2 := by
    simp [regularSection,marker,hr,List.append_assoc]
  rw [heq]
  exact BB6.Padding.cfgEq_refl _

/-- At depth zero the E/p0 packet is regular without moving. -/
theorem e_zero_y0 (a q : Nat) :
    packet a q 0 (marker 0) = regularSection a (q+1) 1 := by
  have hs := oppairs_snoc q
  simp only [packet,word,marker,regularSection,List.replicate_zero,
    List.nil_append]
  rw [←hs]
  simp [oppairs,List.append_assoc]

/-- A source-sound finite terminal classifier for any marker depth. -/
def terminalYSafe (m : Nat) (d : Packet) : Prop :=
  d.p % 3 = 1 ∨
  (m > 0 ∧ d.a % 3 = 0 ∧ d.p % 3 = 0) ∨
  (d.a % 3 = 2 ∧ d.q = 0)

theorem terminalYSafe_source (m : Nat) (d : Packet)
    (ha : d.a ≥ 4) (hs : terminalYSafe m d) :
    ∃ T a q b,
      ObsEq (run T (packet d.a d.q d.p (marker m)))
        (regularSection a q b) := by
  rcases hs with hp1 | hA | hB
  · exact BB6.Agent2MarkerTower.all_p1_regular m d ha hp1
  · obtain ⟨hm,ha0,hp0⟩ := hA
    cases m with
    | zero => omega
    | succ m =>
      let ka : Nat := (d.a-3)/3
      let rr : Nat := d.p/3
      have hka : d.a=3*ka+3 := by dsimp [ka]; omega
      have hrr : d.p=3*rr := by dsimp [rr]; omega
      rw [hka,hrr]
      exact a_zero_regular ka d.q rr m
  · obtain ⟨ha2,hq0⟩ := hB
    let kb : Nat := (d.a-2)/3
    have hkb : d.a=3*kb+2 := by dsimp [kb]; omega
    refine ⟨12*kb*kb+49*kb+40,8*kb+9+d.p,m,2,?_⟩
    rw [hkb,hq0,BB6.Agent2MarkerTower.b_zero]
    exact BB6.Padding.cfgEq_refl _

/-- Structural recursion decreases Y marker depth at every exceptional
    E/p0, and uses the proved rank-reducing source B/E normalizer inside
    each level. Rejected input is unresolved, not proven nonreturning. -/
def safeY : Nat → Packet → Prop
  | 0,c =>
      let d := (normalizeWithCount c).2
      terminalYSafe 0 d ∨ (d.a % 3 = 1 ∧ d.p = 0)
  | m+1,c =>
      let d := (normalizeWithCount c).2
      terminalYSafe (m+1) d ∨
        (d.a % 3 = 1 ∧ d.p = 0 ∧
          safeY m ⟨8*((d.a-4)/3)+5,0,2*d.q+7⟩)

theorem safeY_source (m : Nat) (c : Packet) (ha : c.a ≥ 4)
    (hs : safeY m c) :
    ∃ T a q b, ObsEq (run T
      (packet c.a c.q c.p (marker m)))
      (regularSection a q b) := by
  induction m generalizing c with
  | zero =>
    let d : Packet := (normalizeWithCount c).2
    change terminalYSafe 0 d ∨ (d.a % 3 = 1 ∧ d.p = 0) at hs
    have hd : d.a ≥ 4 := BB6.Agent2PacketSafe.normalize_amin c ha
    obtain ⟨Tp,hpath⟩ :=
      normalized_original_source c ha (marker 0)
    change run Tp (packet c.a c.q c.p (marker 0)) =
      packet d.a d.q d.p (marker 0) at hpath
    rcases hs with hgood | ⟨hE,hzero⟩
    · obtain ⟨Te,a,q,b,hregular⟩ :=
        terminalYSafe_source 0 d hd hgood
      refine ⟨Tp+Te,a,q,b,?_⟩
      rw [run_add,hpath]
      exact hregular
    · refine ⟨Tp,d.a,d.q+1,1,?_⟩
      rw [hpath,hzero,e_zero_y0]
      exact BB6.Padding.cfgEq_refl _
  | succ m ih =>
    let d : Packet := (normalizeWithCount c).2
    change terminalYSafe (m+1) d ∨
      (d.a % 3 = 1 ∧ d.p = 0 ∧
        safeY m ⟨8*((d.a-4)/3)+5,0,2*d.q+7⟩) at hs
    have hd : d.a ≥ 4 := BB6.Agent2PacketSafe.normalize_amin c ha
    obtain ⟨Tp,hpath⟩ :=
      normalized_original_source c ha (marker (m+1))
    change run Tp (packet c.a c.q c.p (marker (m+1))) =
      packet d.a d.q d.p (marker (m+1)) at hpath
    rcases hs with hgood | ⟨hE,hzero,hrec⟩
    · obtain ⟨Te,a,q,b,hregular⟩ :=
        terminalYSafe_source (m+1) d hd hgood
      refine ⟨Tp+Te,a,q,b,?_⟩
      rw [run_add,hpath]
      exact hregular
    · let ke : Nat := (d.a-4)/3
      let next : Packet := ⟨8*ke+5,0,2*d.q+7⟩
      have hshape : d.a=3*ke+4 := by dsimp [ke]; omega
      have hnext : safeY m next := by
        simpa only [next,ke] using hrec
      have hnmin : next.a ≥ 4 := by change 8*ke+5≥4; omega
      obtain ⟨Te,a,q,b,hregular⟩ := ih next hnmin hnext
      refine ⟨Tp+((12*ke*ke+49*ke+50+4*d.q)+Te),a,q,b,?_⟩
      rw [run_add,hpath,hshape,hzero]
      rw [run_add,BB6.Agent2MarkerTower.e_zero_drop]
      simpa only [next] using hregular

/-- Universal q/k/depth conditional E/p0 exit, including q%3=1/2
    cases when the descendant normalizer accepts. -/
theorem e_zero_safeY (k q m : Nat)
    (hs : safeY m ⟨8*k+5,0,2*q+7⟩) :
    ∃ T a Q b,
      ObsEq
        (run T (packet (3*k+4) q 0 (marker (m+1))))
        (regularSection a Q b) := by
  obtain ⟨T,a,Q,b,h⟩ :=
    safeY_source m ⟨8*k+5,0,2*q+7⟩
      (by change 8*k+5≥4; omega) hs
  refine ⟨12*k*k+49*k+50+4*q+T,a,Q,b,?_⟩
  rw [run_add,BB6.Agent2MarkerTower.e_zero_drop]
  exact h

#print axioms a_zero_original
#print axioms a_zero_regular
#print axioms e_zero_y0
#print axioms terminalYSafe_source
#print axioms safeY_source
#print axioms e_zero_safeY
end BB6.Agent36YSafe
