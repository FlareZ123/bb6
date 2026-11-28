import Lean.Elab.Tactic.Omega
import EChainDoubleBReentry
import PacketP2ResetSource
import PacketEZeroAnyTail

set_option maxHeartbeats 40000000
set_option maxRecDepth 16384

namespace BB6.Agent37EChain169Split

private theorem regularSection_sourceSection
    (a q b : Nat) (ha : 2 ≤ a) :
    BB6.Agent2BoundaryBZero.regularSection a q b =
      DRegularSource.sourceSection ⟨a,q,b⟩ := by
  simp only [BB6.Agent2BoundaryBZero.regularSection,
    DRegularSource.sourceSection, CryptidBoundary.init]
  have hrepAdd (m n : Nat) :
      List.replicate (m+n) true =
        List.replicate m true ++ List.replicate n true := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show Nat.succ m+n=(m+n)+1 by omega]
      rw [List.replicate_succ,ih]
      rw [← List.cons_append,← List.replicate_succ]
  have hrep : List.replicate a true =
      [true,true] ++ List.replicate (a-2) true := by
    rw [show a=2+(a-2) by omega,hrepAdd]
    simp
  rw [hrep]
  simp [List.append_assoc]

open CryptidBoundary BB6.Agent31PacketSource
open BB6.Padding BB6.BoundaryPadding
open BB6.Agent37EChain BB6.Agent37EChainBExit
open BB6.Agent2PacketP2Reset BB6.Agent35K4Shapes
open BB6.Agent37EChainDoubleBReentry


def eTime (k q : Nat) : Nat := 12*k*k+49*k+58+6*q

private theorem reset_one_E (k h Q : Nat) (hh : 1 ≤ h)
    (hk : 2*k+1=3*h) :
    run (BB6.Agent2PacketP2Reset.eTwoTime k Q +
      BB6.Agent37EChain.chainTime 1 h 0)
      (packet (3*k+4) Q 2 (false :: List.replicate 6 true)) =
      packet (1+32*h) 2 (2*Q+3) BB6.Agent35K4Shapes.marker := by
  have hprefix : 8*k+5=1+4*3*h := by
    calc
      8*k+5=4*(2*k+1)+1 := by omega
      _=4*(3*h)+1 := by rw [hk]
      _=1+4*3*h := by omega
  have hm : BB6.Agent2PacketP2Reset.marker =
      BB6.Agent35K4Shapes.marker := by decide
  have hreset :
      run (BB6.Agent2PacketP2Reset.eTwoTime k Q)
        (packet (3*k+4) Q 2 (false :: List.replicate 6 true)) =
      packet (1+4*3*h) 0 (2*Q+6)
        BB6.Agent35K4Shapes.marker := by
    rw [BB6.Agent2PacketP2Reset.e_two_reset,hprefix,hm]
  have hchain :
      run (BB6.Agent37EChain.chainTime 1 h 0)
        (packet (1+4*3*h) 0 (3+(2*Q+3))
          BB6.Agent35K4Shapes.marker) =
      packet (1+32*h) 2 (2*Q+3)
        BB6.Agent35K4Shapes.marker := by
    simpa [BB6.Agent37EChain.chainTime] using
      (BB6.Agent37EChain.chain_return 1 h 0 (2*Q+3)
        BB6.Agent35K4Shapes.marker hh)
  rw [run_add,hreset]
  simpa using hchain

private theorem finish_A_to_source (c0 : Cfg) (ka q p : Nat)
    (hprefix : ∃ T, run T c0 =
      packet (3*ka+3) q p BB6.Agent35K4Shapes.marker) :
    ∃ (T a q' b : Nat),
      ObsEq (run T c0) (DRegularSource.sourceSection ⟨a,q',b⟩) ∧
      DRegular.Canon ⟨a,q',b⟩ := by
  obtain ⟨Tp,hp⟩ := hprefix
  obtain ⟨ta,n,hA,hn⟩ :=
    BB6.Agent37EChainDoubleBReentry.all_A_marker_returns_floor ka q p
  let floor := 2*(4*ka+3)+5
  have hf : BB6.Agent37EChainDoubleBReentry.regularEndpointFloor c0 floor := by
    refine ⟨Tp+ta,n,?_,hn⟩
    rw [run_add,hp]
    exact hA
  exact BB6.Agent37EChainDoubleBReentry.regularEndpointFloor_sourceSection
    c0 floor (by dsimp [floor]; omega) hf

/-- Exact source-prefix time for the middle ternary child of the previously
    uncovered k ≡ 169 (mod 243) P2-reset class. -/
def time729_412 (s Q : Nat) : Nat :=
  (eTwoTime (729*s+412) Q + chainTime 1 (486*s+275) 0) +
    (bTime (5184*s+2933) +
      (bTime (13824*s+7824) +
        (eTime (36864*s+20866) 0 +
          bTime (98304*s+55645))))

/-- The class k=729*s+412 is forced through
    reset → E → B → B → E → B and lands on the universal A-marker family. -/
theorem prefix729_412 (s Q : Nat) :
    run (time729_412 s Q)
      (packet (3*(729*s+412)+4) Q 2
        (false :: List.replicate 6 true)) =
      packet (3*(262144*s+148389)+3) 1 (2*Q)
        BB6.Agent35K4Shapes.marker := by
  have hreset :=
    reset_one_E (729*s+412) (486*s+275) Q
      (by omega) (by omega)
  have h1 :
      1+32*(486*s+275) = 3*(5184*s+2933)+2 := by
    omega
  have h2 :
      8*(5184*s+2933)+10 = 3*(13824*s+7824)+2 := by
    omega
  have h3 :
      8*(13824*s+7824)+10 = 3*(36864*s+20866)+4 := by
    omega
  have h4 :
      8*(36864*s+20866)+9 = 3*(98304*s+55645)+2 := by
    omega
  have h5 :
      8*(98304*s+55645)+10 = 3*(262144*s+148389)+3 := by
    omega
  have hb1 :
      run (bTime (5184*s+2933))
        (packet (3*(5184*s+2933)+2) 2 (2*Q+3)
          BB6.Agent35K4Shapes.marker) =
      packet (8*(5184*s+2933)+10) 1 (2*Q+3)
        BB6.Agent35K4Shapes.marker :=
    BB6.Agent31PacketSource.b_packet
      (5184*s+2933) 1 (2*Q+3) BB6.Agent35K4Shapes.marker
  have hb2 :
      run (bTime (13824*s+7824))
        (packet (3*(13824*s+7824)+2) 1 (2*Q+3)
          BB6.Agent35K4Shapes.marker) =
      packet (8*(13824*s+7824)+10) 0 (2*Q+3)
        BB6.Agent35K4Shapes.marker :=
    BB6.Agent31PacketSource.b_packet
      (13824*s+7824) 0 (2*Q+3) BB6.Agent35K4Shapes.marker
  have he :
      run (eTime (36864*s+20866) 0)
        (packet (3*(36864*s+20866)+4) 0 (2*Q+3)
          BB6.Agent35K4Shapes.marker) =
      packet (8*(36864*s+20866)+9) 2 (2*Q)
        BB6.Agent35K4Shapes.marker :=
    BB6.Agent31PacketSource.e_packet
      (36864*s+20866) 0 (2*Q) BB6.Agent35K4Shapes.marker
  have hb3 :
      run (bTime (98304*s+55645))
        (packet (3*(98304*s+55645)+2) 2 (2*Q)
          BB6.Agent35K4Shapes.marker) =
      packet (8*(98304*s+55645)+10) 1 (2*Q)
        BB6.Agent35K4Shapes.marker :=
    BB6.Agent31PacketSource.b_packet
      (98304*s+55645) 1 (2*Q) BB6.Agent35K4Shapes.marker
  unfold time729_412
  rw [run_add,hreset,run_add,h1,run_add,hb1,h2,
    run_add,hb2,h3,run_add,he,h4,hb3,h5]

/-- A new infinite source-connected regular reentry cylinder inside the
    external 107-call terminal route: every k=729*s+412 P2 reset packet,
    for arbitrary Q, returns to a canonical DRegular source section.
    This is a prepared-packet theorem; it does not assert blank-root reachability. -/
theorem reset729_412_source_reentry (s Q : Nat) :
    ∃ (T a q b : Nat),
      ObsEq
        (run T (packet (3*(729*s+412)+4) Q 2
          (false :: List.replicate 6 true)))
        (DRegularSource.sourceSection ⟨a,q,b⟩) ∧
      DRegular.Canon ⟨a,q,b⟩ := by
  apply finish_A_to_source
    (packet (3*(729*s+412)+4) Q 2
      (false :: List.replicate 6 true))
    (262144*s+148389) 1 (2*Q)
  exact ⟨time729_412 s Q, prefix729_412 s Q⟩


/-- Common forced prefix for the whole previously uncovered
    k=243*t+169 residue class.  It stops exactly before the next ternary
    branch, at q=1 and p=2Q. -/
def time243_169 (t Q : Nat) : Nat :=
  (eTwoTime (243*t+169) Q + chainTime 1 (162*t+113) 0) +
    (bTime (1728*t+1205) +
      (bTime (4608*t+3216) +
        (eTime (12288*t+8578) 0 +
          bTime (32768*t+22877))))

theorem prefix243_169 (t Q : Nat) :
    run (time243_169 t Q)
      (packet (3*(243*t+169)+4) Q 2
        (false :: List.replicate 6 true)) =
      packet (262144*t+183026) 1 (2*Q)
        BB6.Agent35K4Shapes.marker := by
  have hreset :=
    reset_one_E (243*t+169) (162*t+113) Q
      (by omega) (by omega)
  have h1 :
      1+32*(162*t+113) = 3*(1728*t+1205)+2 := by omega
  have h2 :
      8*(1728*t+1205)+10 = 3*(4608*t+3216)+2 := by omega
  have h3 :
      8*(4608*t+3216)+10 = 3*(12288*t+8578)+4 := by omega
  have h4 :
      8*(12288*t+8578)+9 = 3*(32768*t+22877)+2 := by omega
  have h5 :
      8*(32768*t+22877)+10 = 262144*t+183026 := by omega
  have hb1 :
      run (bTime (1728*t+1205))
        (packet (3*(1728*t+1205)+2) 2 (2*Q+3)
          BB6.Agent35K4Shapes.marker) =
      packet (8*(1728*t+1205)+10) 1 (2*Q+3)
        BB6.Agent35K4Shapes.marker :=
    BB6.Agent31PacketSource.b_packet
      (1728*t+1205) 1 (2*Q+3) BB6.Agent35K4Shapes.marker
  have hb2 :
      run (bTime (4608*t+3216))
        (packet (3*(4608*t+3216)+2) 1 (2*Q+3)
          BB6.Agent35K4Shapes.marker) =
      packet (8*(4608*t+3216)+10) 0 (2*Q+3)
        BB6.Agent35K4Shapes.marker :=
    BB6.Agent31PacketSource.b_packet
      (4608*t+3216) 0 (2*Q+3) BB6.Agent35K4Shapes.marker
  have he :
      run (eTime (12288*t+8578) 0)
        (packet (3*(12288*t+8578)+4) 0 (2*Q+3)
          BB6.Agent35K4Shapes.marker) =
      packet (8*(12288*t+8578)+9) 2 (2*Q)
        BB6.Agent35K4Shapes.marker :=
    BB6.Agent31PacketSource.e_packet
      (12288*t+8578) 0 (2*Q) BB6.Agent35K4Shapes.marker
  have hb3 :
      run (bTime (32768*t+22877))
        (packet (3*(32768*t+22877)+2) 2 (2*Q)
          BB6.Agent35K4Shapes.marker) =
      packet (8*(32768*t+22877)+10) 1 (2*Q)
        BB6.Agent35K4Shapes.marker :=
    BB6.Agent31PacketSource.b_packet
      (32768*t+22877) 1 (2*Q) BB6.Agent35K4Shapes.marker
  unfold time243_169
  rw [run_add,hreset,run_add,h1,run_add,hb1,h2,
    run_add,hb2,h3,run_add,he,h4,hb3,h5]

/-- The t ≡ 3 (mod 9) child of k=243*t+169 reaches A after one
    additional B packet and therefore reenters the canonical language. -/
theorem reset2187_898_source_reentry (v Q : Nat) :
    ∃ (T a q b : Nat),
      ObsEq
        (run T (packet (3*(2187*v+898)+4) Q 2
          (false :: List.replicate 6 true)))
        (DRegularSource.sourceSection ⟨a,q,b⟩) ∧
      DRegular.Canon ⟨a,q,b⟩ := by
  apply finish_A_to_source
    (packet (3*(2187*v+898)+4) Q 2
      (false :: List.replicate 6 true))
    (2097152*v+861741) 0 (2*Q)
  refine ⟨time243_169 (9*v+3) Q + bTime (786432*v+323152), ?_⟩
  rw [run_add]
  have hp := prefix243_169 (9*v+3) Q
  have hin :
      262144*(9*v+3)+183026 =
        3*(786432*v+323152)+2 := by omega
  rw [hp,hin]
  have hb :=
    BB6.Agent31PacketSource.b_packet
      (786432*v+323152) 0 (2*Q) BB6.Agent35K4Shapes.marker
  have hout :
      8*(786432*v+323152)+10 =
        3*(2097152*v+861741)+3 := by omega
  rw [hb,hout]

/-- The t ≡ 6 (mod 9) child reaches a q=0 B packet after one additional
    B edge, so the arbitrary-tail B-zero theorem closes it for every Q. -/
theorem reset2187_1627_source_reentry (v Q : Nat) :
    ∃ (T a q b : Nat),
      ObsEq
        (run T (packet (3*(2187*v+1627)+4) Q 2
          (false :: List.replicate 6 true)))
        (DRegularSource.sourceSection ⟨a,q,b⟩) ∧
      DRegular.Canon ⟨a,q,b⟩ := by
  let k6 := 2097152*v+1560792
  let t0 := time243_169 (9*v+6) Q
  let t1 := bTime (786432*v+585296)
  let t2 := 12*k6*k6+49*k6+40
  let aOut := 8*k6+9+2*Q
  refine ⟨t0+t1+t2,aOut,3,2,?_,?_⟩
  have hp := prefix243_169 (9*v+6) Q
  have hin :
      262144*(9*v+6)+183026 =
        3*(786432*v+585296)+2 := by omega
  have hb1 :
      run t1
        (packet (3*(786432*v+585296)+2) 1 (2*Q)
          BB6.Agent35K4Shapes.marker) =
      packet (3*k6+2) 0 (2*Q) BB6.Agent35K4Shapes.marker := by
    dsimp [t1,k6]
    have hb :=
      BB6.Agent31PacketSource.b_packet
        (786432*v+585296) 0 (2*Q) BB6.Agent35K4Shapes.marker
    have hout :
        8*(786432*v+585296)+10 =
          3*(2097152*v+1560792)+2 := by omega
    rw [hb,hout]
  have hb0 :
      run t2 (packet (3*k6+2) 0 (2*Q)
        BB6.Agent35K4Shapes.marker) =
      BB6.Agent2BoundaryBZero.regularSection aOut 3 2 := by
    dsimp [t2,aOut,k6]
    simpa [BB6.Agent2BoundaryBZero.regularSection,
      BB6.Agent35K4Shapes.marker, oppairs] using
      (BB6.Agent2PacketP2Reset.b_zero_any
        (2097152*v+1560792) (2*Q) BB6.Agent35K4Shapes.marker)
  have hreg :
      BB6.Agent2BoundaryBZero.regularSection aOut 3 2 =
        DRegularSource.sourceSection ⟨aOut,3,2⟩ := by
    apply regularSection_sourceSection
    dsimp [aOut,k6]
    omega
  change ObsEq
    (run (t0+t1+t2)
      (packet (3*(2187*v+1627)+4) Q 2
        (false :: List.replicate 6 true)))
    (DRegularSource.sourceSection ⟨aOut,3,2⟩)
  have hraw :
      run (t0+t1+t2)
        (packet (3*(2187*v+1627)+4) Q 2
          (false :: List.replicate 6 true)) =
      BB6.Agent2BoundaryBZero.regularSection aOut 3 2 := by
    rw [run_add]
    rw [run_add]
    dsimp [t0]
    have hk :
        2187*v+1627 = 243*(9*v+6)+169 := by omega
    rw [hk,hp,hin,hb1,hb0]
  rw [hraw,hreg]
  exact BB6.Padding.cfgEq_refl _
  constructor
  · dsimp [aOut,k6]
    omega
  · exact Or.inl (by decide)


/-- The first child of the t ≡ 2 (mod 3) residual closes for Q≥2:
    one additional E packet reaches the universal A-marker family. -/
theorem reset2187_655_source_reentry (v Q : Nat) (hQ : 2 ≤ Q) :
    ∃ (T a q b : Nat),
      ObsEq
        (run T (packet (3*(2187*v+655)+4) Q 2
          (false :: List.replicate 6 true)))
        (DRegularSource.sourceSection ⟨a,q,b⟩) ∧
      DRegular.Canon ⟨a,q,b⟩ := by
  apply finish_A_to_source
    (packet (3*(2187*v+655)+4) Q 2
      (false :: List.replicate 6 true))
    (2097152*v+628722) 3 (2*Q-3)
  refine ⟨time243_169 (9*v+2) Q +
      eTime (786432*v+235770) 1, ?_⟩
  rw [run_add]
  have hp := prefix243_169 (9*v+2) Q
  have hin :
      262144*(9*v+2)+183026 =
        3*(786432*v+235770)+4 := by omega
  rw [hp,hin]
  have he :
      run (eTime (786432*v+235770) 1)
        (packet (3*(786432*v+235770)+4) 1 (2*Q)
          BB6.Agent35K4Shapes.marker) =
      packet (8*(786432*v+235770)+9) 3 (2*Q-3)
        BB6.Agent35K4Shapes.marker := by
    have hP : 2*Q-3+3 = 2*Q := by omega
    simpa [hP] using
      (BB6.Agent31PacketSource.e_packet
        (786432*v+235770) 1 (2*Q-3)
        BB6.Agent35K4Shapes.marker)
  have hout :
      8*(786432*v+235770)+9 =
        3*(2097152*v+628722)+3 := by omega
  rw [he,hout]


def externalU6 : List Bool :=
  [false,true,false,true,true,true]

/-- Source composition through the actual external-cylinder call-24 boundary.
    The exact external replay has t ≡ 5 (mod 9) and Q=0 in the
    k=243*t+169 P2 class.  After the common reset/E/B/B/E/B prefix this is
    an E-zero packet; the arbitrary-tail theorem consumes the leading 01
    of the marker and reaches P(0,9;010111). -/
theorem external169_call24_prefix (v : Nat) :
    let kE := 786432*v+497914
    let T := time243_169 (9*v+5) 0 +
      (12*kE*kE+49*kE+54)
    run T
      (packet (3*(2187*v+1384)+4) 0 2
        (false :: List.replicate 6 true)) =
      packet (6291456*v+3983317) 0 9 externalU6 := by
  dsimp only
  rw [run_add]
  have hp := prefix243_169 (9*v+5) 0
  have hk0 :
      2187*v+1384 = 243*(9*v+5)+169 := by omega
  rw [hk0,hp]
  have hin :
      262144*(9*v+5)+183026 =
        3*(786432*v+497914)+4 := by omega
  rw [hin]
  have hmarker :
      BB6.Agent35K4Shapes.marker =
        false :: true :: externalU6 := by decide
  rw [hmarker]
  have he :=
    BB6.Agent37PacketBoundary.e_zero_drop_any
      (786432*v+497914) 1 externalU6
  have hout :
      8*(786432*v+497914)+5 =
        6291456*v+3983317 := by omega
  simpa [hout] using he


def externalU4 : List Bool :=
  [false,true,true,true]

def externalCall24To32Time (r : Nat) : Nat :=
  eTime (4586471424*r+3681829531) 0 +
  (bTime (12230590464*r+9818212085) +
  (bTime (32614907904*r+26181898896) +
  (eTime (86973087744*r+69818397058) 0 +
  (bTime (231928233984*r+186182392157) +
  (bTime (618475290624*r+496486379088) +
  (eTime (1649267441664*r+1323963677570) 0 +
    (12*(4398046511104*r+3530569806855)*
        (4398046511104*r+3530569806855) +
      49*(4398046511104*r+3530569806855) + 58)))))))

/-- The next seven forced packet edges of the authentic terminal cylinder,
    from call 24 through the call-32 E-zero reset. -/
theorem external_call24_to32 (r : Nat) :
    run (externalCall24To32Time r)
      (packet (13759414272*r+11045488597) 0 9 externalU6) =
    packet (35184372088832*r+28244558454845) 0 11 externalU4 := by
  let k25 := 4586471424*r+3681829531
  let k26 := 12230590464*r+9818212085
  let k27 := 32614907904*r+26181898896
  let k28 := 86973087744*r+69818397058
  let k29 := 231928233984*r+186182392157
  let k30 := 618475290624*r+496486379088
  let k31 := 1649267441664*r+1323963677570
  let k32 := 4398046511104*r+3530569806855
  have ha25 :
      13759414272*r+11045488597 = 3*k25+4 := by
    dsimp [k25]; omega
  have ha26 :
      8*k25+9 = 3*k26+2 := by
    dsimp [k25,k26]; omega
  have ha27 :
      8*k26+10 = 3*k27+2 := by
    dsimp [k26,k27]; omega
  have ha28 :
      8*k27+10 = 3*k28+4 := by
    dsimp [k27,k28]; omega
  have ha29 :
      8*k28+9 = 3*k29+2 := by
    dsimp [k28,k29]; omega
  have ha30 :
      8*k29+10 = 3*k30+2 := by
    dsimp [k29,k30]; omega
  have ha31 :
      8*k30+10 = 3*k31+4 := by
    dsimp [k30,k31]; omega
  have ha32 :
      8*k31+9 = 3*k32+4 := by
    dsimp [k31,k32]; omega
  have hout :
      8*k32+5 = 35184372088832*r+28244558454845 := by
    dsimp [k32]; omega
  have he25 :
      run (eTime k25 0)
        (packet (3*k25+4) 0 9 externalU6) =
      packet (8*k25+9) 2 6 externalU6 := by
    simpa using
      (BB6.Agent31PacketSource.e_packet k25 0 6 externalU6)
  have hb26 :
      run (bTime k26)
        (packet (3*k26+2) 2 6 externalU6) =
      packet (8*k26+10) 1 6 externalU6 :=
    BB6.Agent31PacketSource.b_packet k26 1 6 externalU6
  have hb27 :
      run (bTime k27)
        (packet (3*k27+2) 1 6 externalU6) =
      packet (8*k27+10) 0 6 externalU6 :=
    BB6.Agent31PacketSource.b_packet k27 0 6 externalU6
  have he28 :
      run (eTime k28 0)
        (packet (3*k28+4) 0 6 externalU6) =
      packet (8*k28+9) 2 3 externalU6 := by
    simpa using
      (BB6.Agent31PacketSource.e_packet k28 0 3 externalU6)
  have hb29 :
      run (bTime k29)
        (packet (3*k29+2) 2 3 externalU6) =
      packet (8*k29+10) 1 3 externalU6 :=
    BB6.Agent31PacketSource.b_packet k29 1 3 externalU6
  have hb30 :
      run (bTime k30)
        (packet (3*k30+2) 1 3 externalU6) =
      packet (8*k30+10) 0 3 externalU6 :=
    BB6.Agent31PacketSource.b_packet k30 0 3 externalU6
  have he31 :
      run (eTime k31 0)
        (packet (3*k31+4) 0 3 externalU6) =
      packet (8*k31+9) 2 0 externalU6 := by
    simpa using
      (BB6.Agent31PacketSource.e_packet k31 0 0 externalU6)
  have htail : externalU6 = false :: true :: externalU4 := by decide
  have he32 :
      run (12*k32*k32+49*k32+58)
        (packet (3*k32+4) 2 0 externalU6) =
      packet (8*k32+5) 0 11 externalU4 := by
    rw [htail]
    simpa using
      (BB6.Agent37PacketBoundary.e_zero_drop_any k32 2 externalU4)
  unfold externalCall24To32Time
  rw [run_add,ha25,he25,ha26,
    run_add,hb26,ha27,
    run_add,hb27,ha28,
    run_add,he28,ha29,
    run_add,hb29,ha30,
    run_add,hb30,ha31,
    run_add,he31,ha32,he32,hout]

/-- Internal original-source composition of the actual external terminal
    cylinder through its second E-zero reset (call 32).  The 3^14-spaced
    P2 class is exactly the seven-trit refinement selected by the pinned
    external replay. -/
theorem external169_call32_prefix (r : Nat) :
    ∃ T,
      run T
        (packet (3*(4782969*r+3839569)+4) 0 2
          (false :: List.replicate 6 true)) =
      packet (35184372088832*r+28244558454845) 0 11 externalU4 := by
  let v := 2187*r+1755
  let t0 := time243_169 (9*v+5) 0 +
    (12*(786432*v+497914)*(786432*v+497914) +
      49*(786432*v+497914)+54)
  let t1 := externalCall24To32Time r
  refine ⟨t0+t1,?_⟩
  rw [run_add]
  have h0 := external169_call24_prefix v
  have hk :
      2187*v+1384 = 4782969*r+3839569 := by
    dsimp [v]; omega
  have ha :
      6291456*v+3983317 =
        13759414272*r+11045488597 := by
    dsimp [v]; omega
  dsimp [t0]
  rw [hk] at h0
  rw [ha] at h0
  rw [h0]
  exact external_call24_to32 r

#print axioms prefix729_412
#print axioms reset729_412_source_reentry
#print axioms prefix243_169
#print axioms reset2187_898_source_reentry
#print axioms reset2187_1627_source_reentry
#print axioms reset2187_655_source_reentry
#print axioms external169_call24_prefix
#print axioms external_call24_to32
#print axioms external169_call32_prefix

end BB6.Agent37EChain169Split
