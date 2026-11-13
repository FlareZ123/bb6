import Lean.Elab.Tactic.Omega
import EERootBEA

namespace BB6.Agent37EERootBEAFloor

open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent37EChain
open BB6.Agent37EChainBExit
open BB6.Agent37EChainBEExit
open BB6.Agent2PacketP2Reset
open BB6.Agent2E7SecondSafe
open BB6.Agent2BoundaryBZero

set_option maxHeartbeats 16000000
set_option maxRecDepth 32768

private def fixedTail : List Bool := false :: List.replicate 6 true

private theorem markerEq :
    BB6.Agent2PacketP2Reset.marker = BB6.Agent35K4Shapes.marker := by
  decide

/-- Every A-marker completion has unary parameter at least 8*ka+11. -/
private theorem all_A_marker_returns_floor (ka q p : Nat) :
    ∃ (T n : Nat),
      8*ka+11 ≤ n ∧
      (run T (packet (3*ka+3) q p BB6.Agent35K4Shapes.marker) =
           (⟨[],false,List.replicate n true ++
             [true,false,true,false,true,true,true],5⟩ : Cfg) ∨
       run T (packet (3*ka+3) q p BB6.Agent35K4Shapes.marker) =
           (⟨[],false,List.replicate n true,5⟩ : Cfg) ∨
       run T (packet (3*ka+3) q p BB6.Agent35K4Shapes.marker) =
           (⟨[],false,List.replicate n true ++
             [false,true,false,true,false,true,false,true,false],5⟩ : Cfg)) := by
  let r := p / 3
  have hcases : p=3*r ∨ p=3*r+1 ∨ p=3*r+2 := by
    have hm := Nat.mod_add_div p 3
    dsimp [r]
    omega
  rcases hcases with h0 | h1 | h2
  · refine ⟨BB6.Agent35MarkerA.aTime0 ka q r,
      2*((4*ka+3)+CryptidA.wordInc (BB6.Agent35MarkerA.code q r))+5,
      ?_, Or.inl ?_⟩
    · have hi : 0 ≤ CryptidA.wordInc (BB6.Agent35MarkerA.code q r) :=
        Nat.zero_le _
      omega
    · rw [h0]
      exact BB6.Agent35MarkerA.close_zero ka q r
  · refine ⟨BB6.Agent35MarkerA.aTime1 ka q r,
      2*((4*ka+3)+CryptidA.wordInc (BB6.Agent35MarkerA.tailCode q r))+5,
      ?_, Or.inr (Or.inl ?_)⟩
    · have hi : 0 ≤ CryptidA.wordInc (BB6.Agent35MarkerA.tailCode q r) :=
        Nat.zero_le _
      omega
    · rw [h1]
      exact BB6.Agent35MarkerA.close_one ka q r
  · refine ⟨BB6.Agent35MarkerA.aTime2 ka q r,
      2*((4*ka+3)+CryptidA.wordInc (BB6.Agent35MarkerA.code q r))+5,
      ?_, Or.inr (Or.inr ?_)⟩
    · have hi : 0 ≤ CryptidA.wordInc (BB6.Agent35MarkerA.code q r) :=
        Nat.zero_le _
      omega
    · rw [h2]
      exact BB6.Agent35MarkerA.close_two ka q r

/-- A regular endpoint retaining a lower bound on its unary parameter. -/
def regularEndpointFloor (c : Cfg) (floor : Nat) : Prop :=
  ∃ (T n : Nat),
    floor ≤ n ∧
    (run T c = (⟨[],false,List.replicate n true ++
        [true,false,true,false,true,true,true],5⟩ : Cfg) ∨
     run T c = (⟨[],false,List.replicate n true,5⟩ : Cfg) ∨
     run T c = (⟨[],false,List.replicate n true ++
        [false,true,false,true,false,true,false,true,false],5⟩ : Cfg))

private theorem prepend_floor (c d : Cfg) (floor t : Nat)
    (h : run t c = d)
    (hend : regularEndpointFloor d floor) :
    regularEndpointFloor c floor := by
  obtain ⟨tailTime,n,hn,htail⟩ := hend
  unfold regularEndpointFloor
  refine ⟨t+tailTime,n,hn,?_⟩
  rw [run_add,h]
  exact htail

/-- The three physical-section conversions preserve the certified floor. -/
theorem regularEndpointFloor_reentry (floor : Nat) (c : Cfg)
    (h : regularEndpointFloor c floor) :
    ∃ (T a q b : Nat),
      BB6.BoundaryPadding.ObsEq (run T c)
        (BB6.Agent2BoundaryBZero.regularSection a q b) ∧
      floor ≤ a := by
  have hrep_all : ∀ n : Nat, List.replicate (n+1) true =
      List.replicate n true ++ [true] := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      calc
        List.replicate (Nat.succ n + 1) true =
            true :: List.replicate (n+1) true := by rfl
        _ = true :: (List.replicate n true ++ [true]) := by rw [ih]
        _ = (true :: List.replicate n true) ++ [true] := by rfl
        _ = List.replicate (Nat.succ n) true ++ [true] := by rfl
  rcases h with ⟨T,n,hn,hcases⟩
  have hrep := hrep_all n
  rcases hcases with h0 | h1 | h2
  · refine ⟨T,n+1,2,2,?_⟩
    constructor
    · rw [h0]
      change BB6.Padding.CfgEq
        (BB6.BoundaryPadding.represent
          (⟨[],false,List.replicate n true ++
            [true,false,true,false,true,true,true],5⟩ : Cfg))
        (BB6.BoundaryPadding.represent
          (BB6.Agent2BoundaryBZero.regularSection (n+1) 2 2))
      have heq :
          BB6.BoundaryPadding.represent
            (⟨[],false,List.replicate n true ++
              [true,false,true,false,true,true,true],5⟩ : Cfg) =
          BB6.BoundaryPadding.represent
            (BB6.Agent2BoundaryBZero.regularSection (n+1) 2 2) := by
        simp [BB6.BoundaryPadding.represent,
          BB6.Agent2BoundaryBZero.regularSection,
          hrep, CryptidBoundary.oppairs,
          List.append_assoc]
      rw [heq]
      exact BB6.Padding.cfgEq_refl _
    · omega
  · refine ⟨T,n,0,0,?_⟩
    constructor
    · rw [h1]
      change BB6.Padding.CfgEq
        (BB6.BoundaryPadding.represent
          (⟨[],false,List.replicate n true,5⟩ : Cfg))
        (BB6.BoundaryPadding.represent
          (BB6.Agent2BoundaryBZero.regularSection n 0 0))
      have heq :
          BB6.BoundaryPadding.represent
            (⟨[],false,List.replicate n true,5⟩ : Cfg) =
          BB6.BoundaryPadding.represent
            (BB6.Agent2BoundaryBZero.regularSection n 0 0) := by
        simp [BB6.BoundaryPadding.represent,
          BB6.Agent2BoundaryBZero.regularSection,
          CryptidBoundary.oppairs]
      rw [heq]
      exact BB6.Padding.cfgEq_refl _
    · omega
  · refine ⟨T,n,4,0,?_⟩
    constructor
    · rw [h2]
      change BB6.Padding.CfgEq
        (BB6.BoundaryPadding.represent
          (⟨[],false,List.replicate n true ++
            [false,true,false,true,false,true,false,true,false],5⟩ : Cfg))
        (BB6.BoundaryPadding.represent
          (BB6.Agent2BoundaryBZero.regularSection n 4 0))
      apply BB6.Padding.cfgEq_symm
      simp only [BB6.BoundaryPadding.represent,
        BB6.Agent2BoundaryBZero.regularSection,
        List.replicate_zero]
      have hword : CryptidBoundary.oppairs 4 =
          [false,true,false,true,false,true,false,true] := by decide
      rw [hword]
      refine ⟨BB6.Padding.tapeEq_refl _, rfl, ?_, rfl⟩
      simpa [List.append_assoc] using
        (BB6.Padding.tapeEq_pad
          (List.replicate n true ++
            [false,true,false,true,false,true,false,true]) 1)
    · omega

/-- The B-E-A corridor carries the final A-marker unary floor backwards. -/
theorem chain_B_E_A_floor (floor d h t q p : Nat)
    (hh : 1 ≤ h) (hd : 1 ≤ d)
    (ha : 1+4*8^d*h=27*t+20)
    (hfloor : floor ≤ 8*(64*t+50)+11) :
    regularEndpointFloor
      (packet (1+4*3^d*h) q (3*d+(3+p))
        BB6.Agent35K4Shapes.marker) floor := by
  let kb : Nat := 9*t+6
  let ke : Nat := 24*t+18
  let ka : Nat := 64*t+50
  have hb : 1+4*8^d*h=3*kb+2 := by
    calc
      1+4*8^d*h = 27*t+20 := ha
      _ = 3*kb+2 := by dsimp [kb]; omega
  have he : 8*kb+10=3*ke+4 := by
    dsimp [kb,ke]
    omega
  have hA : 8*ke+9=3*ka+3 := by
    dsimp [ke,ka]
    omega
  have hq : (q+2*d-1)+1=q+2*d := by omega
  have hq2 : (q+2*d-1)+2=q+2*d+1 := by omega
  have hfirst :
      run (BB6.Agent37EChain.chainTime d h q)
        (packet (1+4*3^d*h) q (3*d+(3+p))
          BB6.Agent35K4Shapes.marker) =
      packet (3*kb+2) (q+2*d) (3+p)
        BB6.Agent35K4Shapes.marker := by
    rw [BB6.Agent37EChain.chain_return d h q (3+p)
      BB6.Agent35K4Shapes.marker hh, hb]
  have hBE0 :=
    BB6.Agent37EChainBEExit.b_then_e kb ke (q+2*d-1) p
      BB6.Agent35K4Shapes.marker he
  have hBE :
      run (BB6.Agent37EChainBExit.bTime kb +
          BB6.Agent37EChain.eTime ke (q+2*d-1))
        (packet (3*kb+2) (q+2*d) (3+p)
          BB6.Agent35K4Shapes.marker) =
      packet (8*ke+9) (q+2*d+1) p
        BB6.Agent35K4Shapes.marker := by
    simpa only [hq,hq2] using hBE0
  obtain ⟨ta,n,hn,htail⟩ :=
    all_A_marker_returns_floor ka (q+2*d+1) p
  have hbound : floor ≤ n := by
    have hka : ka=64*t+50 := rfl
    omega
  have hfinal :
      regularEndpointFloor
        (packet (8*ke+9) (q+2*d+1) p
          BB6.Agent35K4Shapes.marker) floor := by
    rw [hA]
    unfold regularEndpointFloor
    exact ⟨ta,n,hbound,htail⟩
  have hmid :
      regularEndpointFloor
        (packet (3*kb+2) (q+2*d) (3+p)
          BB6.Agent35K4Shapes.marker) floor :=
    prepend_floor _ _ floor
      (BB6.Agent37EChainBExit.bTime kb +
        BB6.Agent37EChain.eTime ke (q+2*d-1)) hBE hfinal
  exact prepend_floor _ _ floor
    (BB6.Agent37EChain.chainTime d h q) hfirst hmid

/-- Physical regularSection endpoint with the same unary lower bound. -/
theorem chain_B_E_A_reentry_floor (floor d h t q p : Nat)
    (hh : 1 ≤ h) (hd : 1 ≤ d)
    (ha : 1+4*8^d*h=27*t+20)
    (hfloor : floor ≤ 8*(64*t+50)+11) :
    ∃ (T a q' b : Nat),
      BB6.BoundaryPadding.ObsEq
        (run T
          (packet (1+4*3^d*h) q (3*d+(3+p))
            BB6.Agent35K4Shapes.marker))
        (BB6.Agent2BoundaryBZero.regularSection a q' b) ∧
      floor ≤ a := by
  exact regularEndpointFloor_reentry floor _
    (chain_B_E_A_floor floor d h t q p hh hd ha hfloor)

private theorem q4_marker_prefix (m : Nat) :
    ∃ (T4 h t : Nat),
      1 ≤ h ∧
      1+4*8^1*h=27*t+20 ∧
      BB6.BoundaryPadding.ObsEq
        (run T4 (BB6.Agent2E7SecondSafe.sourceStart (2187*m+1647) 4))
        (BB6.Agent31PacketSource.packet (1+4*3^1*h) 0 (3*1+(3+4))
          BB6.Agent35K4Shapes.marker) := by
  let z : Nat := 81*m+61
  let u : Nat := 2187*m+1647
  let k0 : Nat := 1728*z+53
  let k1 : Nat := 4608*z+144
  let k2 : Nat := 12288*z+386
  let k3 : Nat := 32768*z+1031
  let h : Nat := 1769472*m+1333253
  let t : Nat := 2097152*m+1580151
  have hpos : 1 ≤ h := by
    dsimp [h]
    omega
  have hu : u=27*z := by
    dsimp [u,z]
    simp only [Nat.mul_add]
    omega
  have hA0 : 192*u+161=3*k0+2 := by
    dsimp [u,z,k0]
    simp only [Nat.mul_add]
    omega
  have hB1 : 8*k0+10=3*k1+2 := by
    clear hu hA0
    dsimp [k0,k1]
    simp only [Nat.mul_add]
    omega
  have hB2 : 8*k1+10=3*k2+4 := by
    clear hu hA0 hB1
    dsimp [k1,k2]
    simp only [Nat.mul_add]
    omega
  have hE : 8*k2+9=3*k3+4 := by
    clear hu hA0 hB1 hB2
    dsimp [k2,k3]
    simp only [Nat.mul_add]
    omega
  have hReset : 8*k3+5=1+4*3^1*h := by
    clear hu hA0 hB1 hB2 hE
    dsimp [k3,h,z]
    simp only [Nat.mul_add]
    omega
  have hBEA : 1+4*8^1*h=27*t+20 := by
    clear hu hA0 hB1 hB2 hE hReset
    dsimp [h,t]
    simp only [Nat.mul_add]
    omega
  have houter : 8*(24*u+19)+9=192*u+161 := by
    clear hu hA0 hB1 hB2 hE hReset hBEA
    simp only [Nat.mul_add]
    omega
  have hEE0 :=
    BB6.Agent2E7SecondSafe.exceptional_EE_packet u 4 (by decide)
  have hEE :
      BB6.BoundaryPadding.ObsEq
        (run (BB6.Agent2E7SecondSafe.eTime u 4 +
          BB6.Agent2E7SecondSafe.middleTime u)
          (BB6.Agent2E7SecondSafe.sourceStart u 4))
        (BB6.Agent31PacketSource.packet (3*k0+2) 2 5 fixedTail) := by
    have hshape :
        BB6.BoundaryPadding.ObsEq
          (run (BB6.Agent2E7SecondSafe.eTime u 4 +
            BB6.Agent2E7SecondSafe.middleTime u)
            (BB6.Agent2E7SecondSafe.sourceStart u 4))
          (BB6.Agent31PacketSource.packet (192*u+161) 2 5 fixedTail) := by
      simpa [BB6.Agent2E7SecondSafe.sourceStart,
        BB6.Agent2E7SecondSafe.secondOutput,
        fixedTail, houter, BB6.Agent31PacketSource.packet,
        BB6.Agent31PacketSource.word, CryptidBoundary.packetThree,
        BB6.Agent2E7SecondSafe.suffix2, CryptidBoundary.oppairs] using hEE0
    simpa [hA0] using hshape
  have hb1eq :
      run (BB6.Agent37EChainBExit.bTime k0)
        (BB6.Agent31PacketSource.packet (3*k0+2) 2 5 fixedTail) =
      BB6.Agent31PacketSource.packet (3*k1+2) 1 5 fixedTail := by
    have hb := BB6.Agent31PacketSource.b_packet k0 1 5 fixedTail
    simpa [BB6.Agent37EChainBExit.bTime, hB1] using hb
  have hb1 :
      BB6.BoundaryPadding.ObsEq
        (run (BB6.Agent37EChainBExit.bTime k0)
          (BB6.Agent31PacketSource.packet (3*k0+2) 2 5 fixedTail))
        (BB6.Agent31PacketSource.packet (3*k1+2) 1 5 fixedTail) := by
    rw [hb1eq]
    exact BB6.Padding.cfgEq_refl _
  have hb2eq :
      run (BB6.Agent37EChainBExit.bTime k1)
        (BB6.Agent31PacketSource.packet (3*k1+2) 1 5 fixedTail) =
      BB6.Agent31PacketSource.packet (3*k2+4) 0 5 fixedTail := by
    have hb := BB6.Agent31PacketSource.b_packet k1 0 5 fixedTail
    simpa [BB6.Agent37EChainBExit.bTime, hB2] using hb
  have hb2 :
      BB6.BoundaryPadding.ObsEq
        (run (BB6.Agent37EChainBExit.bTime k1)
          (BB6.Agent31PacketSource.packet (3*k1+2) 1 5 fixedTail))
        (BB6.Agent31PacketSource.packet (3*k2+4) 0 5 fixedTail) := by
    rw [hb2eq]
    exact BB6.Padding.cfgEq_refl _
  have heq :
      run (BB6.Agent37EChain.eTime k2 0)
        (BB6.Agent31PacketSource.packet (3*k2+4) 0 5 fixedTail) =
      BB6.Agent31PacketSource.packet (3*k3+4) 2 2 fixedTail := by
    have he := BB6.Agent31PacketSource.e_packet k2 0 2 fixedTail
    simpa [BB6.Agent37EChain.eTime, hE] using he
  have he :
      BB6.BoundaryPadding.ObsEq
        (run (BB6.Agent37EChain.eTime k2 0)
          (BB6.Agent31PacketSource.packet (3*k2+4) 0 5 fixedTail))
        (BB6.Agent31PacketSource.packet (3*k3+4) 2 2 fixedTail) := by
    rw [heq]
    exact BB6.Padding.cfgEq_refl _
  have hresetEq :
      run (BB6.Agent2PacketP2Reset.eTwoTime k3 2)
        (BB6.Agent31PacketSource.packet (3*k3+4) 2 2 fixedTail) =
      BB6.Agent31PacketSource.packet (1+4*3^1*h) 0 (3*1+(3+4))
        BB6.Agent35K4Shapes.marker := by
    have hr := BB6.Agent2PacketP2Reset.e_two_reset k3 2
    simpa [BB6.Agent2PacketP2Reset.eTwoTime, hReset, markerEq,
      fixedTail] using hr
  have hreset :
      BB6.BoundaryPadding.ObsEq
        (run (BB6.Agent2PacketP2Reset.eTwoTime k3 2)
          (BB6.Agent31PacketSource.packet (3*k3+4) 2 2 fixedTail))
        (BB6.Agent31PacketSource.packet (1+4*3^1*h) 0 (3*1+(3+4))
          BB6.Agent35K4Shapes.marker) := by
    rw [hresetEq]
    exact BB6.Padding.cfgEq_refl _
  let T0 : Nat :=
    BB6.Agent2E7SecondSafe.eTime u 4 +
      BB6.Agent2E7SecondSafe.middleTime u
  let T1 : Nat := T0 + BB6.Agent37EChainBExit.bTime k0
  let T2 : Nat := T1 + BB6.Agent37EChainBExit.bTime k1
  let T3 : Nat := T2 + BB6.Agent37EChain.eTime k2 0
  let T4 : Nat := T3 + BB6.Agent2PacketP2Reset.eTwoTime k3 2
  have h1 :
      BB6.BoundaryPadding.ObsEq
        (run T1 (BB6.Agent2E7SecondSafe.sourceStart u 4))
        (BB6.Agent31PacketSource.packet (3*k1+2) 1 5 fixedTail) :=
    BB6.BoundaryPadding.source_chain T0
      (BB6.Agent37EChainBExit.bTime k0)
      (BB6.Agent2E7SecondSafe.sourceStart u 4)
      (BB6.Agent31PacketSource.packet (3*k0+2) 2 5 fixedTail)
      (BB6.Agent31PacketSource.packet (3*k1+2) 1 5 fixedTail) hEE hb1
  have h2 :
      BB6.BoundaryPadding.ObsEq
        (run T2 (BB6.Agent2E7SecondSafe.sourceStart u 4))
        (BB6.Agent31PacketSource.packet (3*k2+4) 0 5 fixedTail) :=
    BB6.BoundaryPadding.source_chain T1
      (BB6.Agent37EChainBExit.bTime k1)
      (BB6.Agent2E7SecondSafe.sourceStart u 4)
      (BB6.Agent31PacketSource.packet (3*k1+2) 1 5 fixedTail)
      (BB6.Agent31PacketSource.packet (3*k2+4) 0 5 fixedTail) h1 hb2
  have h3 :
      BB6.BoundaryPadding.ObsEq
        (run T3 (BB6.Agent2E7SecondSafe.sourceStart u 4))
        (BB6.Agent31PacketSource.packet (3*k3+4) 2 2 fixedTail) :=
    BB6.BoundaryPadding.source_chain T2
      (BB6.Agent37EChain.eTime k2 0)
      (BB6.Agent2E7SecondSafe.sourceStart u 4)
      (BB6.Agent31PacketSource.packet (3*k2+4) 0 5 fixedTail)
      (BB6.Agent31PacketSource.packet (3*k3+4) 2 2 fixedTail) h2 he
  have h4 :
      BB6.BoundaryPadding.ObsEq
        (run T4 (BB6.Agent2E7SecondSafe.sourceStart u 4))
        (BB6.Agent31PacketSource.packet (1+4*3^1*h) 0 (3*1+(3+4))
          BB6.Agent35K4Shapes.marker) :=
    BB6.BoundaryPadding.source_chain T3
      (BB6.Agent2PacketP2Reset.eTwoTime k3 2)
      (BB6.Agent2E7SecondSafe.sourceStart u 4)
      (BB6.Agent31PacketSource.packet (3*k3+4) 2 2 fixedTail)
      (BB6.Agent31PacketSource.packet (1+4*3^1*h) 0 (3*1+(3+4))
        BB6.Agent35K4Shapes.marker) h3 hreset
  exact ⟨T4,h,t,hpos,hBEA,h4⟩

/-- For every m, the q=4 E/E source cylinder returns to regular L with
    unary coordinate at least 411. This is a source-level endpoint bound,
    not a claim that the authentic blank-root orbit reaches the cylinder. -/
theorem q4_exceptional_EE_BEA_section_ge (m : Nat) :
    ∃ (T a q b : Nat),
      BB6.BoundaryPadding.ObsEq
        (run T (BB6.Agent2E7SecondSafe.sourceStart (2187*m+1647) 4))
        (BB6.Agent2BoundaryBZero.regularSection a q b) ∧
      411 ≤ a := by
  obtain ⟨T4,h,t,hpos,hBEA,h4⟩ := q4_marker_prefix m
  have hfloor : 411 ≤ 8*(64*t+50)+11 := by omega
  obtain ⟨Ttail,a,q',b,htail,ha⟩ :=
    chain_B_E_A_reentry_floor
      411 1 h t 0 4 hpos (by decide) hBEA hfloor
  exact ⟨T4+Ttail,a,q',b,
    ⟨BB6.BoundaryPadding.source_chain T4 Ttail
      (BB6.Agent2E7SecondSafe.sourceStart (2187*m+1647) 4)
      (BB6.Agent31PacketSource.packet (1+4*3^1*h) 0 (3*1+(3+4))
        BB6.Agent35K4Shapes.marker)
      (BB6.Agent2BoundaryBZero.regularSection a q' b)
      h4 htail, ha⟩⟩

#print axioms all_A_marker_returns_floor
#print axioms regularEndpointFloor_reentry
#print axioms chain_B_E_A_reentry_floor
#print axioms q4_exceptional_EE_BEA_section_ge

end BB6.Agent37EERootBEAFloor
