import Lean.Elab.Tactic.Omega
import P2MarkerA
import PacketNormalizeSource
import BoundaryPadding
import BoundaryBZero
import PacketP2ResetSource

namespace BB6.Agent35MarkerOne
open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent31PacketRank BB6.Agent2PacketNormalizeSource
open BB6.BoundaryPadding BB6.Padding
open BB6.Agent2BoundaryBZero
open BB6.Agent2PacketP2Reset
set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

def marker : List Bool := BB6.Agent2PacketP2Reset.marker

private theorem oppairs_add (q r : Nat) :
    oppairs (q+r) = oppairs q ++ oppairs r := by
  induction q with
  | zero => simp [oppairs]
  | succ q ih =>
    simp [Nat.succ_add,oppairs,ih]

/-- Any marker packet with p=1 is already a regular L section. -/
theorem e_one_regular (a q : Nat) :
    packet a q 1 marker = regularSection a (q+4) 2 := by
  simp only [packet,word,regularSection]
  rw [oppairs_add]
  simp [marker,BB6.Agent2PacketP2Reset.marker,
    BB6.Agent35K4Shapes.marker,oppairs,List.append_assoc]

/-- B with no remaining (01) pairs immediately turns the marker into L(a,3,2). -/
theorem b_zero_regular (k p : Nat) :
    run (12*k*k+49*k+40) (packet (3*k+2) 0 p marker) =
    regularSection (8*k+9+p) 3 2 := by
  rw [show marker = BB6.Agent2PacketP2Reset.marker by rfl]
  rw [b_zero_any]
  simp [regularSection,BB6.Agent2PacketP2Reset.marker,
    BB6.Agent35K4Shapes.marker,oppairs]

private theorem p0_shape (n : Nat) :
    (⟨[],false,List.replicate n true ++
      [true,false,true,false,true,true,true],5⟩ : Cfg) =
    regularSection (n+1) 2 2 := by
  simp only [regularSection]
  have hn : List.replicate (n+1) true =
      List.replicate n true ++ [true] := by
    rw [←List.replicate_append_replicate]
    rfl
  rw [hn]
  simp [oppairs,List.append_assoc]

private theorem p2_shape (n : Nat) :
    ObsEq
      (⟨[],false,List.replicate n true ++
        [false,true,false,true,false,true,false,true,false],5⟩ : Cfg)
      (regularSection n 4 0) := by
  change TapeEq ([] : List Bool) [] ∧ false=false ∧
    TapeEq (List.replicate n true ++
        [false,true,false,true,false,true,false,true,false])
      (List.replicate n true ++ (oppairs 4 ++ List.replicate 0 true)) ∧ 5=5
  refine ⟨tapeEq_refl _,rfl,?_,rfl⟩
  have hl :
      List.replicate n true ++
         [false,true,false,true,false,true,false,true,false] =
        (List.replicate n true ++ oppairs 4) ++ List.replicate 1 false := by
    simp [oppairs,List.append_assoc]
  rw [hl]
  simpa only [List.replicate_zero,List.append_nil]
    using tapeEq_symm (tapeEq_pad (List.replicate n true ++ oppairs 4) 1)

/-- All q,p at every A-index marker return to canonical regular physical tape. -/
theorem a_marker_regular (ka q p : Nat) :
    ∃ T a r b,
      ObsEq (run T (packet (3*ka+3) q p marker))
        (regularSection a r b) := by
  obtain ⟨T,n,h0 | h1 | h2⟩ :=
    BB6.Agent35MarkerA.all_A_marker_returns ka q p
  · refine ⟨T,n+1,2,2,?_⟩
    change ObsEq (run T (packet (3*ka+3) q p BB6.Agent35K4Shapes.marker)) (regularSection (n+1) 2 2)
    rw [h0,p0_shape]
    exact cfgEq_refl _
  · refine ⟨T,n,0,0,?_⟩
    change ObsEq (run T (packet (3*ka+3) q p BB6.Agent35K4Shapes.marker)) (regularSection n 0 0)
    rw [h1]
    change CfgEq (BB6.BoundaryPadding.represent
        (⟨[],false,List.replicate n true,5⟩ : Cfg))
      (BB6.BoundaryPadding.represent (regularSection n 0 0))
    simpa [regularSection,oppairs] using
      (cfgEq_refl (BB6.BoundaryPadding.represent
        (⟨[],false,List.replicate n true,5⟩ : Cfg)))
  · refine ⟨T,n,4,0,?_⟩
    change ObsEq (run T (packet (3*ka+3) q p BB6.Agent35K4Shapes.marker)) (regularSection n 4 0)
    rw [h2]
    exact p2_shape n

/-- Terminal packet of invariant p≡1 mod3: A, exhausted B, or already regular E. -/
theorem one_terminal_regular (d : Packet)
    (ha : d.a ≥ 4) (hp : d.p % 3 = 1)
    (hc : d.a % 3 = 0 ∨
      (d.a % 3 = 2 ∧ d.q = 0) ∨
      (d.a % 3 = 1 ∧ (d.p = 0 ∨ d.p = 1))) :
    ∃ T a r b,
      ObsEq (run T (packet d.a d.q d.p marker))
        (regularSection a r b) := by
  rcases hc with hA | hB | hE
  · let ka : Nat := (d.a-3)/3
    have ha' : d.a = 3*ka+3 := by dsimp [ka]; omega
    simpa only [ha'] using a_marker_regular ka d.q d.p
  · obtain ⟨hB,hq⟩ := hB
    let kb : Nat := (d.a-2)/3
    have ha' : d.a = 3*kb+2 := by dsimp [kb]; omega
    refine ⟨12*kb*kb+49*kb+40,8*kb+9+d.p,3,2,?_⟩
    rw [ha',hq,b_zero_regular]
    exact cfgEq_refl _
  · obtain ⟨hE,hsmall⟩ := hE
    have hp1 : d.p=1 := by omega
    refine ⟨0,d.a,d.q+4,2,?_⟩
    change ObsEq (packet d.a d.q d.p marker)
      (regularSection d.a (d.q+4) 2)
    rw [hp1,e_one_regular]
    exact cfgEq_refl _

/-- Universal source-connected L reentry for all marked packets with p≡1 mod3. -/
theorem all_marker_one_regular (c : Packet) (ha : c.a ≥ 4)
    (hp : c.p % 3 = 1) :
    ∃ T a r b,
      ObsEq (run T (packet c.a c.q c.p marker))
        (regularSection a r b) := by
  let d : Packet := (normalizeWithCount c).2
  obtain ⟨T,hraw⟩ :=
    normalized_original_source c ha marker
  have hb : d.a % 3 = 0 ∨
      (d.a % 3 = 2 ∧ d.q=0) ∨
      (d.a % 3 = 1 ∧ (d.p=0 ∨ d.p=1)) :=
    BB6.Agent2PacketSafe.normalize_safe_exit c ha (by omega)
  have hamin : d.a ≥ 4 := BB6.Agent2PacketSafe.normalize_amin c ha
  have hpmod : d.p % 3=1 :=
    (BB6.Agent2PacketSafe.normalize_pmod c).trans hp
  obtain ⟨n,a,r,b,hboundary⟩ :=
    one_terminal_regular d hamin hpmod hb
  refine ⟨T+n,a,r,b,?_⟩
  change run T (packet c.a c.q c.p marker) =
    packet d.a d.q d.p marker at hraw
  rw [run_add,hraw]
  exact hboundary

/-- All source E,p=2 reset inputs with q≡2 mod3 reach regular L, for ANY k. -/
theorem all_e_two_q2_regular (k u : Nat) :
    ∃ T a r b,
      ObsEq (run T
        (packet (3*k+4) (3*u+2) 2 (false :: List.replicate 6 true)))
        (regularSection a r b) := by
  let c : Packet := ⟨8*k+5,0,2*(3*u+2)+6⟩
  have ha : c.a ≥ 4 := by dsimp [c]; omega
  have hp : c.p % 3=1 := by dsimp [c]; omega
  obtain ⟨T,a,r,b,h⟩ := all_marker_one_regular c ha hp
  refine ⟨eTwoTime k (3*u+2)+T,a,r,b,?_⟩
  rw [run_add,e_two_reset]
  exact h

#print axioms a_marker_regular
#print axioms all_marker_one_regular
#print axioms all_e_two_q2_regular
end BB6.Agent35MarkerOne
