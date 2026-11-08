import Lean.Elab.Tactic.Omega
import MarkerZeroSource
import MarkerZeroAZero
import CryptidPairs

namespace BB6.Agent36EZeroZ
open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent2MarkerZero
open BB6.Agent2BoundaryBZero
open BB6.BoundaryPadding

set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

/-- The first 01 in a nonempty zero-ended marker is absorbed as one
    additional 1 after the exact original E/p=0 return. -/
private theorem input_shape (k q m : Nat) :
    packet (3*k+4) q 0 (marker (m+1)) =
      init (List.replicate (3*k+2) true ++
        false :: (pairs q ++ (false :: (true :: marker m)))) := by
  have hn : List.replicate (3*k+4) true =
      true :: true :: List.replicate (3*k+2) true := by
    rw [show 3*k+4=2+(3*k+2) by omega,
      ← List.replicate_append_replicate]
    rfl
  have hw :
      oppairs q ++ (false :: marker (m+1)) =
        false :: (pairs q ++ (false :: (true :: marker m))) := by
    calc
      _ = (oppairs q ++ [false]) ++ marker (m+1) := by
        simp [List.append_assoc]
      _ = (false :: pairs q) ++ marker (m+1) := by
        rw [oppairs_false]
      _ = _ := by
        simp [marker,oppairs,List.append_assoc]
  simp only [packet,word,init,List.replicate_zero,
    List.nil_append,List.cons_append]
  rw [hn,hw]
  rfl

private theorem output_shape (k q m : Nat) :
    (⟨[],false,List.replicate (8*k+5) true ++
      (false :: (List.replicate (2*q+6) true ++
        (true :: marker m))),5⟩ : Cfg) =
      packet (8*k+5) 0 (2*q+7) (marker m) := by
  have hp : List.replicate (2*q+7) true =
      List.replicate (2*q+6) true ++ [true] := by
    rw [show 2*q+7=(2*q+6)+1 by omega,
      ← List.replicate_append_replicate]
    rfl
  simp [packet,word,oppairs,hp,List.append_assoc]

/-- All-parameter, exact original-machine step transformation:
    M(3k+4,q,0;Z_(m+1)) -> M(8k+5,0,2q+7;Z_m).
    This is a Z-marker analogue of the earlier Y-marker E-zero drop. -/
theorem e_zero_drop_Z (k q m : Nat) :
    run (12*k*k+49*k+50+4*q)
      (packet (3*k+4) q 0 (marker (m+1))) =
    packet (8*k+5) 0 (2*q+7) (marker m) := by
  rw [input_shape]
  exact (full_E_pairs k q (true :: marker m)).trans
    (output_shape k q m)

/-- Entire infinite p=0 terminal cylinder q divisible by three and
    positive zero-marker depth reenters the regular L section through
    an original-source physical-tape certificate. No blank-root entry
    is asserted. -/
theorem e_zero_q0_Z_regular (k u m : Nat) :
    ∃ T a r b,
      ObsEq
        (run T (packet (3*k+4) (3*u) 0 (marker (m+1))))
        (regularSection a r b) := by
  let c : BB6.Agent31PacketRank.Packet :=
    ⟨8*k+5,0,2*(3*u)+7⟩
  obtain ⟨T,a,r,b,h⟩ :=
    all_p1_regular m c (by dsimp [c]; omega)
      (by dsimp [c]; omega)
  refine ⟨(12*k*k+49*k+50+4*(3*u))+T,a,r,b,?_⟩
  rw [run_add,e_zero_drop_Z]
  exact h


/-- When k is 0 modulo 3, the E-zero Z drop lands directly in the
    q=0 B sector, which returns to the regular section for every q. -/
theorem e_zero_k0_Z_regular (t q m : Nat) :
    ∃ T a r b,
      ObsEq
        (run T (packet (3*(3*t)+4) q 0 (marker (m+1))))
        (regularSection a r b) := by
  let kb : Nat := 8*t+1
  have ha : 8*(3*t)+5 = 3*kb+2 := by dsimp [kb]; omega
  have he := e_zero_drop_Z (3*t) q m
  rw [ha] at he
  refine ⟨(12*(3*t)*(3*t)+49*(3*t)+50+4*q)+
    (12*kb*kb+49*kb+40),8*kb+9+(2*q+7),m,0,?_⟩
  rw [run_add,he]
  exact b_zero kb (2*q+7) m

/-- For k≡2 and q≡1 (mod 3), the E-zero Z drop lands at an A
    terminal whose run parameter is a multiple of three. The existing
    all-marker-depth A/p=0 theorem then proves physical regular reentry. -/
theorem e_zero_k2_q1_Z_regular (t u m : Nat) :
    ∃ T a r b,
      ObsEq
        (run T
          (packet (3*(3*t+2)+4) (3*u+1) 0 (marker (m+1))))
        (regularSection a r b) := by
  let ka : Nat := 8*t+6
  have ha : 8*(3*t+2)+5 = 3*ka+3 := by dsimp [ka]; omega
  have hp : 2*(3*u+1)+7 = 3*(2*u+3) := by omega
  obtain ⟨Ta,a,r,b,hA⟩ :=
    BB6.Agent2MarkerZeroAZero.aZeroRegular ka 0 (2*u+3) m
  have hE := e_zero_drop_Z (3*t+2) (3*u+1) m
  rw [ha,hp] at hE
  refine ⟨(12*(3*t+2)*(3*t+2)+49*(3*t+2)+50+4*(3*u+1))+Ta,
    a,r,b,?_⟩
  rw [run_add,hE]
  exact hA


/-- A second genuinely unbounded Z-marker E-zero cylinder. Here the first
    E-zero drop is followed by one guarded original E packet edge; its
    endpoint is exactly the all-depth A/p=0 zero-marker terminal. -/
theorem e_zero_k1mod9_q1_Z_regular (t u m : Nat) :
    ∃ T a r b,
      ObsEq
        (run T
          (packet (3*(9*t+1)+4) (3*u+1) 0 (marker (m+1))))
        (regularSection a r b) := by
  let ke : Nat := 24*t+3
  let ka : Nat := 64*t+10
  have hEshape : 8*(9*t+1)+5 = 3*ke+4 := by dsimp [ke]; omega
  have hAshape : 8*ke+9 = 3*ka+3 := by dsimp [ke,ka]; omega
  have hp : 2*(3*u+1)+7 = 3*(2*u+2)+3 := by omega
  have h0 := e_zero_drop_Z (9*t+1) (3*u+1) m
  rw [hEshape,hp] at h0
  have h1 := e_packet ke 0 (3*(2*u+2)) (marker m)
  rw [hAshape] at h1
  obtain ⟨Ta,a,r,b,hA⟩ :=
    BB6.Agent2MarkerZeroAZero.aZeroRegular ka 2 (2*u+2) m
  refine ⟨(12*(9*t+1)*(9*t+1)+49*(9*t+1)+50+4*(3*u+1))+
    ((12*ke*ke+49*ke+58)+Ta),a,r,b,?_⟩
  rw [run_add,h0,run_add,h1]
  exact hA


/-- The terminal marker Z_0 is a genuinely blank zero after the suffix.
    For any E-zero packet and any scanner parameter q the source E-pair
    return is already physically equivalent to regular L. -/
theorem e_zero_Z0_regular (k q : Nat) :
    ObsEq
      (run (12*k*k+49*k+50+4*q)
        (packet (3*k+4) q 0 (marker 0)))
      (regularSection (8*k+5) 1 (2*q+5)) := by
  have hn : List.replicate (3*k+4) true =
    true :: true :: List.replicate (3*k+2) true := by
      rw [show 3*k+4=2+(3*k+2) by omega,
        ← List.replicate_append_replicate]
      rfl
  have hi : packet (3*k+4) q 0 (marker 0) =
      init (List.replicate (3*k+2) true ++
        false :: (pairs q ++ [false,false])) := by
    simp only [packet,word,marker,oppairs,List.replicate_zero,
      List.nil_append,init,List.cons_append,hn]
    rw [show oppairs q ++ [false] = false :: pairs q from oppairs_false q]
    simp [List.append_assoc]
  rw [hi,full_E_pairs]
  let reg : Cfg := regularSection (8*k+5) 1 (2*q+5)
  have hout :
      (⟨[],false,List.replicate (8*k+5) true ++
        (false :: (List.replicate (2*q+6) true ++ [false])),5⟩ : Cfg) =
      (⟨reg.l,reg.h,reg.r++[false],reg.st⟩ : Cfg) := by
    dsimp [reg,regularSection,oppairs]
    simp [List.append_assoc,List.replicate_succ]
  rw [hout]
  change ObsEq
    (⟨reg.l,reg.h,reg.r++[false],reg.st⟩ : Cfg) reg
  simpa [reg,run] using
    (BB6.Padding.cfgEq_symm
      (BB6.BoundaryPadding.source_pad 0 0 1 reg))

#print axioms e_zero_drop_Z
#print axioms e_zero_q0_Z_regular
#print axioms e_zero_k0_Z_regular
#print axioms e_zero_k2_q1_Z_regular
#print axioms e_zero_k1mod9_q1_Z_regular
#print axioms e_zero_Z0_regular

end BB6.Agent36EZeroZ
