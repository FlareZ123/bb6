import P2RootS0FrameIdentity
import GeneralQ4TailArithmetic
import Lean.Elab.Tactic.Omega

/-!
# General-A q4Tail residual as a canonical S1 dispatcher input

This extends the A=2 adapter-config equality to every A>=2. It is a
source-level draft; the full repository import closure has not been compiled.
-/

namespace BB6Coverage.Agent44GeneralQ4TailReparam

open BB6Coverage
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent44P2Postlude
open BB6Coverage.Agent38RootQ4TailS0
open BB6Coverage.Agent42FirstQ4P1Arithmetic
open BB6Coverage.Agent44GeneralQ4TailArithmetic

/-- The canonical S1-side residual obtained from an arbitrary-A q4Tail. -/
def generalEll (L A K : Nat) : List Bool :=
  d1pow K ++ markerWord 0 ++ d0 ++
    binDec (A+L+2) (firstQ4P1M L A-3) ++ lh

private theorem general_d1pow_replicate (k : Nat) :
    d1pow k = List.replicate (3*k) true := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp [d1pow,d1,Nat.mul_succ,List.replicate_add,ih]

/-- Drop the four sentinel ones and the first two bits of the P1 value. -/
theorem generalTail0_drop6 (L A : Nat) (hA : 2≤A) :
    (List.replicate 4 true ++
      binDec (A+L+1) (firstQ4P1Value L A) ++ lh).drop 6 =
      [true] ++ d0pow (A-2) ++ d1 ++ d0pow (L+1) ++ lh := by
  rw [firstQ4P1Value_binDec_shape L A (by omega)]
  have hblock : d0pow (A-1) = d0 ++ d0pow (A-2) := by
    rw [show A-1=(A-2)+1 by omega]
    rfl
  rw [hblock]
  simp [List.drop,List.replicate,d0,d1,List.append_assoc]

private theorem generalFixedPrefix (tail : List Bool) :
    [false,true,false,false] ++
      ([true,false,false,true,true,true] ++ ([true] ++ tail)) =
    markerWord 0 ++ d0 ++ d0 ++ d1 ++ tail := by
  simp [markerWord,d0,d1,List.append_assoc]

/-- The P2 residual at arbitrary outer width A is a canonical S1 suffix. -/
theorem generalEll_eq_p2Residual (L A z : Nat) (hA : 2≤A) :
    p2ResidualLeft (3*2^z+3*z+7)
      (q4TailS0Tail (A+L+1) (firstQ4P1Value L A)) =
    generalEll L A (2^z+z+3) := by
  let K : Nat := 2^z+z+3
  have hlen : (3*2^z+3*z+7)+2 = 3*K := by
    dsimp [K]
    omega
  have hrep :
      List.replicate ((3*2^z+3*z+7)+2) true = d1pow K := by
    rw [hlen]
    exact (general_d1pow_replicate K).symm
  unfold p2ResidualLeft q4TailS0Tail generalEll
  rw [hrep]
  rw [generalTail0_drop6 L A hA]
  rw [generalFixedPrefix
    (d0pow (A-2) ++ d1 ++ d0pow (L+1) ++ lh)]
  rw [q4TerminalIndex_binDec_shape L A hA]
  simp [List.append_assoc,K]

private theorem general_binDec_max (k : Nat) :
    binDec k (2^k-1) = d0pow k := by
  induction k with
  | zero =>
      simp [binDec,binaryCounterFuel,d0pow]
  | succ k ih =>
      have hp : 0 < 2^k := Nat.pow_pos (by decide)
      have hbound : 2^k-1 < 2^k := by omega
      have hpow : 2^(k+1) = 2^k*2 := by rw [Nat.pow_succ]
      have hnum : 2^(k+1)-1 = 2*(2^k-1)+1 := by omega
      rw [hnum,binDec_odd k (2^k-1) hbound]
      simp [d0pow,d0,ih]

private theorem general_binDec_lowCarry (K n : Nat)
    (hK : 0<K) (hn : 0<n) :
    binDec (K+n-1) (2^(n-1)-1) =
      d0pow (n-1) ++ d1pow K := by
  have hwidth : K+n-1 = (K-1)+1+(n-1) := by omega
  have hvalue : 2^(n-1)-1 = ((2*0+1)*2^(n-1))-1 := by omega
  calc
    binDec (K+n-1) (2^(n-1)-1)
        = binDec ((K-1)+1+(n-1)) (((2*0+1)*2^(n-1))-1) := by
            rw [hwidth,hvalue]
    _ = d0pow (n-1) ++ d1 ++ binDec (K-1) 0 :=
          binDec_sub_one_carryPrefix (K-1) 0 (n-1) (by
            have hpos : 0 < 2^(K-1) := Nat.pow_pos (by decide)
            omega)
    _ = d0pow (n-1) ++ d1pow K := by
          rw [binDec_zero]
          have hK' : (K-1)+1=K := by omega
          calc
            d0pow (n-1) ++ d1 ++ d1pow (K-1)
                = d0pow (n-1) ++ d1pow ((K-1)+1) := by
                    simp [d1pow]
            _ = d0pow (n-1) ++ d1pow K := by rw [hK']

/-- Full left-facing tape equality for the arbitrary-A S1 reparameterization. -/
theorem generalFullLeftFacing_eq (L A K n : Nat)
    (hA : 2≤A) (hK : 0<K) (hn : 0<n) :
    binDec (n-1) (2^(n-1)-1) ++ generalEll L A K =
      binDec (K+n-1) (2^(n-1)-1) ++
        markerWord 0 ++ d0 ++
          binDec (A+L+2) (firstQ4P1M L A-3) ++ lh := by
  calc
    binDec (n-1) (2^(n-1)-1) ++ generalEll L A K
        = d0pow (n-1) ++ d1pow K ++ markerWord 0 ++ d0 ++
            binDec (A+L+2) (firstQ4P1M L A-3) ++ lh := by
              simp [generalEll,general_binDec_max,List.append_assoc]
    _ = binDec (K+n-1) (2^(n-1)-1) ++
          markerWord 0 ++ d0 ++
            binDec (A+L+2) (firstQ4P1M L A-3) ++ lh := by
              rw [general_binDec_lowCarry K n hK hn]

/-- The S0 adapter configuration is extensionally the S1 dispatcher input. -/
theorem generalAdapterConfig_eq (L A K n : Nat) (H : Int)
    (hA : 2≤A) (hK : 0<K) (hn : 0<n) :
    s0Config (generalEll L A K) (n-1) (2^(n-1)-1) 0 H =
      s1Config (A+L+2) (firstQ4P1M L A-3) 0 (K+n-1)
        (2^(n-1)-1) 0 H := by
  change
    ({ state := (3 : Fin 6), head := H,
       tape := s0Tape (generalEll L A K) (n-1) (2^(n-1)-1) 0 H } : Config)
      =
    ({ state := (3 : Fin 6), head := H,
       tape := s0Tape
         (markerWord 0 ++ d0 ++
           binDec (A+L+2) (firstQ4P1M L A-3) ++ lh)
         (K+n-1) (2^(n-1)-1) 0 H } : Config)
  have htape :
      s0Tape (generalEll L A K) (n-1) (2^(n-1)-1) 0 H =
      s0Tape
        (markerWord 0 ++ d0 ++
          binDec (A+L+2) (firstQ4P1M L A-3) ++ lh)
        (K+n-1) (2^(n-1)-1) 0 H := by
    funext x
    by_cases hx : x≤H
    · simp [s0Tape,s0LeftFacing,hx,
        generalFullLeftFacing_eq L A K n hA hK hn]
    · simp [s0Tape,s0RightFacing,hx]
  exact congrArg
    (fun t : Int → Bool =>
      ({ state := (3 : Fin 6), head := H, tape := t } : Config))
    htape

#print axioms generalEll_eq_p2Residual
#print axioms generalAdapterConfig_eq

end BB6Coverage.Agent44GeneralQ4TailReparam
