import S0DrainQ4Postlude
import PositiveZFirstCyclePrefix
import Lean.Elab.Tactic.Omega

/-!
# Corrected P2 S0 postlude followed by the next type-A q4 prefix

This source draft composes Agent 44's corrected 0100/100 S0 drain and
q4/S0 postlude with Agent 48's generic first-cycle prefix. The postlude
returns the type-A window 00110000 at head 1; its right stream is exactly

  0^3 ++ 1^(H) ++ 0^2 ++ 1^(3*2^a) ++ 0^4,

where a=n-1 and H=m+2+3*n. Thus the next first-cycle prefix applies with
parameters (H, 2^a).

This is an intermediate theorem, not yet locally compiled, not connected
to the authentic q4Tail-to-S0 identity, and not a BB(6) halt proof.
-/

namespace BB6Coverage.Agent48P2NextQ4Tail

open BB6Coverage
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent42Q4S0Drain
open BB6Coverage.Agent48Q4S0Macros
open BB6Coverage.Agent44P2Postlude
open BB6Coverage.Agent48PositiveZFirstCycle
open BB6Coverage.Agent48PositiveZFirstCyclePrefix
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent48Champion

set_option maxHeartbeats 4000000

private theorem sideBit_d1pow_true_local (n i : Nat) (hi : i < 3*n) :
    sideBit (d1pow n) i = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
      cases i with
      | zero => simp [d1pow,d1,sideBit]
      | succ i =>
          cases i with
          | zero => simp [d1pow,d1,sideBit]
          | succ i =>
              cases i with
              | zero => simp [d1pow,d1,sideBit]
              | succ i =>
                  have hi' : i < 3*n := by omega
                  simpa [d1pow,d1,sideBit] using ih i hi'

private theorem sideBit_ge_length_local (xs : List Bool) (i : Nat)
    (hi : xs.length ≤ i) : sideBit xs i = false := by
  induction xs generalizing i with
  | nil => simp [sideBit]
  | cons b xs ih =>
      cases i with
      | zero => simp at hi
      | succ i =>
          simp only [sideBit]
          apply ih
          simp at hi
          omega

private theorem s0RightFacing_after_six_local (b i : Nat) (hi : 6 ≤ i) :
    sideBit (s0RightFacing b) i =
      sideBit (d1pow (b+1)) (i-6) := by
  unfold s0RightFacing
  rw [Agent6Q4Prefix.sideBit_append_right
    [false,true,true,true,false,false] (d1pow (b+1)) i (by simp; omega)]
  simp

private theorem s0RightFacing_firstThree_local (b i : Nat)
    (hi : i=1 ∨ i=2 ∨ i=3) :
    sideBit (s0RightFacing b) i = true := by
  rcases hi with h|h|h <;> subst i <;>
    simp [s0RightFacing,sideBit]

private theorem s0RightFacing_sep4_local (b : Nat) :
    sideBit (s0RightFacing b) 4 = false := by
  simp [s0RightFacing,sideBit]

private theorem s0RightFacing_sep5_local (b : Nat) :
    sideBit (s0RightFacing b) 5 = false := by
  simp [s0RightFacing,sideBit]

/-- At every position x>=5, the corrected P2 postlude has a simple
right-facing profile: it is the new unary run through H+1, followed by
the unchanged right stream of the drained S0 configuration. -/
private theorem p2PostludeFrame_right_cell
    (m n : Nat) (tail : List Bool) (hn : 2≤n)
    (x : Int) (hx : 5≤x) :
    (p2PostludeFrame m n tail).tape x =
      if x ≤ (m+2+3*n:Int)+1 then true
      else sideBit (s0RightFacing (2^(n-1)-1))
        (Int.toNat (x-(m+2+3*n:Int)-1)) := by
  let a : Nat := n-1
  let H : Int := (m+2+3*n)
  let K : Nat := 3*a+(m+2)
  let ell : List Bool := p2ResidualLeft m tail
  let T : Int → Bool := (s0Config ell a 0 (2^a-1) H).tape
  let U : Int → Bool := s0LeftSweep K T H
  have hcenter : H-(K:Int)=3 := by
    dsimp [H,K,a]
    omega
  have hk : 0<K := by
    dsimp [K,a]
    omega
  have hframe :
      (p2PostludeFrame m n tail).tape x = U x := by
    change (q4FrameAt U 3 q4S0Final4Inside q4S0Final4End).tape x = U x
    rw [q4FrameAt_tape]
    have hnot : q4S0Final4Inside (x-3)=false := by
      simp [q4S0Final4Inside]
      omega
    simp [hnot]
  have hsweep := s0LeftSweep_shift K T H hk x
  have hprofile : U x = if x≤H+1 then true else T x := by
    rw [hsweep,hcenter]
    have hneq : x≠4 := by omega
    simp [hneq,hx]
  have hbase :
      (p2PostludeFrame m n tail).tape x =
        if x≤H+1 then true else T x := by
    rw [hframe,hprofile]
  by_cases hmid : x≤H+1
  · simpa [H,hmid] using hbase
  · have hnonneg : 0≤x-H-1 := by omega
    have hidx : (Int.toNat (x-H-1):Int)=x-H-1 :=
      Int.toNat_of_nonneg hnonneg
    have hcell := s0Config_right_cell ell a 0 (2^a-1) H
      (Int.toNat (x-H-1))
    have hcoord : H+1+(Int.toNat (x-H-1):Int)=x := by omega
    rw [hcoord] at hcell
    rw [hidx] at hcell
    simpa [H,hmid,T,a] using hbase.trans hcell

/-- The postlude's right stream satisfies the full generic first-cycle
prefix contract with m'=H and n'=2^(n-1). -/
private theorem p2PostludeFrame_firstCycleGuards
    (m n : Nat) (tail : List Bool) (hn : 2≤n)
    (ht0 : sideBit tail 0 = true)
    (ht1 : sideBit tail 1 = false)
    (ht2 : sideBit tail 2 = false) :
    let P := p2PostludeFrame m n tail
    linearRightOnes P.tape 5 (m+2+3*n) ∧
    P.tape (5+(m+2+3*n:Int)) = false ∧
    P.tape (5+(m+2+3*n:Int)+1) = false ∧
    d1BlocksOn P.tape (7+(m+2+3*n:Int)) (2^(n-1)) ∧
    (∀ i : Nat, i≤4 →
      P.tape (7+(m+2+3*n:Int)+3*(2^(n-1):Int)+(i:Int)) = false) := by
  let P := p2PostludeFrame m n tail
  let H : Nat := m+2+3*n
  let a : Nat := n-1
  let nNext : Nat := 2^a
  have hfirst : linearRightOnes P.tape 5 H := by
    intro i hi
    let x : Int := 5+(i:Int)
    have hx : 5≤x := by dsimp [x]; omega
    have hval := p2PostludeFrame_right_cell m n tail hn x hx
    by_cases hmid : x≤(H:Int)+1
    · simpa [P,H,x,hmid] using hval
    · have hcases : i=H-3 ∨ i=H-2 ∨ i=H-1 := by omega
      rcases hcases with h0|h1|h2
      · subst i
        have hidx : Int.toNat (x-(H:Int)-1)=1 := by
          dsimp [x]
          omega
        have hval' : P.tape x =
            sideBit (s0RightFacing (2^a-1)) 1 := by
          simpa [P,H,a,x,hmid,hidx] using hval
        have htrue := s0RightFacing_firstThree_local
          (2^a-1) 1 (by omega)
        simpa [x] using hval'.trans htrue
      · subst i
        have hidx : Int.toNat (x-(H:Int)-1)=2 := by
          dsimp [x]
          omega
        have hval' : P.tape x =
            sideBit (s0RightFacing (2^a-1)) 2 := by
          simpa [P,H,a,x,hmid,hidx] using hval
        have htrue := s0RightFacing_firstThree_local
          (2^a-1) 2 (by omega)
        simpa [x] using hval'.trans htrue
      · subst i
        have hidx : Int.toNat (x-(H:Int)-1)=3 := by
          dsimp [x]
          omega
        have hval' : P.tape x =
            sideBit (s0RightFacing (2^a-1)) 3 := by
          simpa [P,H,a,x,hmid,hidx] using hval
        have htrue := s0RightFacing_firstThree_local
          (2^a-1) 3 (by omega)
        simpa [x] using hval'.trans htrue

  have hsep0 : P.tape (5+(H:Int)) = false := by
    have hval := p2PostludeFrame_right_cell m n tail hn
      (5+(H:Int)) (by omega)
    have hmid : ¬ (5+(H:Int)≤(H:Int)+1) := by omega
    have hidx : Int.toNat (5+(H:Int)-(H:Int)-1)=4 := by omega
    have hval' : P.tape (5+(H:Int)) =
        sideBit (s0RightFacing (2^a-1)) 4 := by
      simpa [P,H,a,hmid,hidx] using hval
    exact hval'.trans (s0RightFacing_sep4_local (2^a-1))

  have hsep1 : P.tape (5+(H:Int)+1) = false := by
    have hval := p2PostludeFrame_right_cell m n tail hn
      (5+(H:Int)+1) (by omega)
    have hmid : ¬ (5+(H:Int)+1≤(H:Int)+1) := by omega
    have hidx : Int.toNat (5+(H:Int)+1-(H:Int)-1)=5 := by omega
    have hval' : P.tape (5+(H:Int)+1) =
        sideBit (s0RightFacing (2^a-1)) 5 := by
      simpa [P,H,a,hmid,hidx] using hval
    exact hval'.trans (s0RightFacing_sep5_local (2^a-1))

  have hblocks : d1BlocksOn P.tape (7+(H:Int)) nNext := by
    intro i hi
    refine ⟨?_,?_,?_⟩
    · let x : Int := (H:Int)+7+3*(i:Int)
      have hx : 5≤x := by dsimp [x]; omega
      have hmid : ¬ x≤(H:Int)+1 := by dsimp [x]; omega
      have hidx : Int.toNat (x-(H:Int)-1)=6+3*i := by
        dsimp [x]
        omega
      have hval := p2PostludeFrame_right_cell m n tail hn x hx
      have hval' : P.tape x =
          sideBit (s0RightFacing (2^a-1)) (6+3*i) := by
        simpa [P,H,a,x,hmid,hidx] using hval
      have htail := s0RightFacing_after_six_local
        (2^a-1) (6+3*i) (by omega)
      have hbit := sideBit_d1pow_true_local (2^a) (3*i) (by omega)
      simpa [x] using hval'.trans (htail.trans hbit)
    · let x : Int := (H:Int)+7+3*(i:Int)+1
      have hx : 5≤x := by dsimp [x]; omega
      have hmid : ¬ x≤(H:Int)+1 := by dsimp [x]; omega
      have hidx : Int.toNat (x-(H:Int)-1)=6+3*i+1 := by
        dsimp [x]
        omega
      have hval := p2PostludeFrame_right_cell m n tail hn x hx
      have hval' : P.tape x =
          sideBit (s0RightFacing (2^a-1)) (6+3*i+1) := by
        simpa [P,H,a,x,hmid,hidx] using hval
      have htail := s0RightFacing_after_six_local
        (2^a-1) (6+3*i+1) (by omega)
      have hbit := sideBit_d1pow_true_local (2^a) (3*i+1) (by omega)
      simpa [x] using hval'.trans (htail.trans hbit)
    · let x : Int := (H:Int)+7+3*(i:Int)+2
      have hx : 5≤x := by dsimp [x]; omega
      have hmid : ¬ x≤(H:Int)+1 := by dsimp [x]; omega
      have hidx : Int.toNat (x-(H:Int)-1)=6+3*i+2 := by
        dsimp [x]
        omega
      have hval := p2PostludeFrame_right_cell m n tail hn x hx
      have hval' : P.tape x =
          sideBit (s0RightFacing (2^a-1)) (6+3*i+2) := by
        simpa [P,H,a,x,hmid,hidx] using hval
      have htail := s0RightFacing_after_six_local
        (2^a-1) (6+3*i+2) (by omega)
      have hbit := sideBit_d1pow_true_local (2^a) (3*i+2) (by omega)
      simpa [x] using hval'.trans (htail.trans hbit)

  have hzeros : ∀ i : Nat, i≤4 →
      P.tape (7+(H:Int)+3*(nNext:Int)+(i:Int)) = false := by
    intro i hi
    let x : Int := (H:Int)+7+3*(nNext:Int)+(i:Int)
    have hx : 5≤x := by dsimp [x]; omega
    have hmid : ¬ x≤(H:Int)+1 := by dsimp [x]; omega
    have hidx : Int.toNat (x-(H:Int)-1)=6+3*nNext+i := by
      dsimp [x]
      omega
    have hval := p2PostludeFrame_right_cell m n tail hn x hx
    have hval' : P.tape x =
        sideBit (s0RightFacing (2^a-1)) (6+3*nNext+i) := by
      simpa [P,H,a,nNext,x,hmid,hidx] using hval
    have htail := s0RightFacing_after_six_local
      (2^a-1) (6+3*nNext+i) (by omega)
    have hblank : sideBit (d1pow (2^a)) (3*nNext+i) = false := by
      apply sideBit_ge_length_local
      rw [d1pow_length]
      omega
    have hfinal := hval'.trans (htail.trans hblank)
    simpa [x] using hfinal

  have hH : H=m+2+3*n := by rfl
  refine ⟨?_,hsep0,hsep1,hblocks,hzeros⟩
  simpa [P,H,hH] using hfirst

/-- A corrected P2 S0 input, after its all-ones drain and q4/S0
postlude, supplies the complete type-A checkpoint and right-stream
hypotheses for another generic first-cycle prefix. -/
theorem p2S0_to_next_q4Tail
    (m n : Nat) (tail : List Bool) (hn : 2≤n)
    (ht0 : sideBit tail 0 = true)
    (ht1 : sideBit tail 1 = false)
    (ht2 : sideBit tail 2 = false) :
    let a : Nat := n-1
    let H : Nat := m+2+3*n
    let nNext : Nat := 2^a
    let P := p2PostludeFrame m n tail
    let T1 := (frameAt P.tape 1
      firstCyclePrefix22Inside firstCyclePrefix22End).tape
    let h1 : Int := 1+4+(H:Int)
    let T2 := afterFirstCycleTwoZero T1 h1
    let h2 : Int := h1+2
    let T3 : Int → Bool := d0Sweep nNext T2 h2
    let g : Int := h2+3*(nNext:Int)
    run tm2
      ((6*4^a+42*2^a-12*a-48) + (3*H-5) +
        (22+H+2+3*nNext+29))
      (s0Config (p2ResidualLeft m tail) a (2^a-1) 0 (H:Int)) =
    some (frameAt T3 g q4TailInside q4TailEnd) := by
  let a : Nat := n-1
  let H : Nat := m+2+3*n
  let nNext : Nat := 2^a
  let P := p2PostludeFrame m n tail
  let T1 := (frameAt P.tape 1
    firstCyclePrefix22Inside firstCyclePrefix22End).tape
  let h1 : Int := 1+4+(H:Int)
  let T2 := afterFirstCycleTwoZero T1 h1
  let h2 : Int := h1+2
  let T3 : Int → Bool := d0Sweep nNext T2 h2
  let g : Int := h2+3*(nNext:Int)

  have hpost :
      run tm2
        ((6*4^a+42*2^a-12*a-48)+(3*H-5))
        (s0Config (p2ResidualLeft m tail) a (2^a-1) 0 (H:Int)) =
      some P := by
    simpa [a,H,P] using
      p2S0Drain_q4Postlude m n tail (by omega)

  have hwindow := p2PostludeFrame_typeAWindow m n tail
    (by omega) ht0 ht1 ht2
  have hinput22 :
      P.tape (1-4) = false ∧
      P.tape (1-3) = false ∧
      P.tape (1-2) = true ∧
      P.tape (1-1) = true ∧
      P.tape 1 = false ∧
      P.tape (1+1) = false ∧
      P.tape (1+2) = false ∧
      P.tape (1+3) = false := by
    simpa [P] using hwindow

  have hguards := p2PostludeFrame_firstCycleGuards m n tail hn ht0 ht1 ht2
  have hfirst : linearRightOnes P.tape 5 H := by
    simpa [P,H] using hguards.1
  have hsep0 : P.tape (1+4+(H:Int)) = false := by
    simpa [H] using hguards.2.1
  have hsep1 : P.tape (1+4+(H:Int)+1) = false := by
    simpa [H,Int.add_assoc] using hguards.2.2.1
  have hblocks : d1BlocksOn P.tape (1+4+(H:Int)+2) nNext := by
    simpa [H,nNext] using hguards.2.2.2.1
  have hzeros : ∀ i : Nat, i≤4 →
      P.tape (1+4+(H:Int)+2+3*(nNext:Int)+(i:Int)) = false := by
    simpa [H,nNext,Int.add_assoc] using hguards.2.2.2.2

  have ha : 1≤a := by dsimp [a]; omega
  have hnNext : 2≤nNext := by
    dsimp [nNext,a]
    have hp := Nat.pow_le_pow_right (by decide : 0<2) ha
    simpa using hp

  have hprefix := firstCyclePrefix_from_checkpoint
    H nNext P.tape 1 hinput22 hfirst hsep0 hsep1 hblocks hzeros hnNext
  have hprefix' :
      run tm2 (22+H+2+3*nNext+29) ⟨4,1,P.tape⟩ =
        some (frameAt T3 g q4TailInside q4TailEnd) := by
    simpa [P,T1,h1,T2,h2,T3,g] using hprefix

  calc
    run tm2
        (((6*4^a+42*2^a-12*a-48)+(3*H-5)) +
          (22+H+2+3*nNext+29))
        (s0Config (p2ResidualLeft m tail) a (2^a-1) 0 (H:Int))
      = (run tm2
          ((6*4^a+42*2^a-12*a-48)+(3*H-5))
          (s0Config (p2ResidualLeft m tail) a (2^a-1) 0 (H:Int))).bind
          (fun c => run tm2 (22+H+2+3*nNext+29) c) := by
            rw [run_append]
    _ = run tm2 (22+H+2+3*nNext+29) ⟨4,1,P.tape⟩ := by
          rw [hpost]
          rfl
    _ = some (frameAt T3 g q4TailInside q4TailEnd) := hprefix'

/-- Closed arithmetic cost for the corrected S0-postlude plus next
type-A first-cycle prefix. -/
theorem p2S0_to_next_q4Tail_cost (m n : Nat) (hn : 2≤n) :
    (6*4^(n-1)+42*2^(n-1)-12*(n-1)-48) +
      (3*(m+2+3*n)-5) +
      (22+(m+2+3*n)+2+3*(2^(n-1))+29) =
    6*4^(n-1)+45*2^(n-1)+4*m+20 := by
  omega

#print axioms p2PostludeFrame_right_cell
#print axioms p2PostludeFrame_firstCycleGuards
#print axioms p2S0_to_next_q4Tail
#print axioms p2S0_to_next_q4Tail_cost

end BB6Coverage.Agent48P2NextQ4Tail
