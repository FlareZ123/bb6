import M2EvenResidueZeroSource
import LBinDecHRunLeftFacing
import Q4RightEndpoint
import S1CountedDrain
import Lean.Elab.Tactic.Omega

/-!
# Source-level all-q m=2, n=8*k residue-zero reset

The proof composes the source left sweep, the exact 44-step setup,
the arbitrary-context LBinDec H-run, the 14-step postlude, the E scan,
the generic q4 suffix, and the already-counted all-ones drain.

The variable carry is handled by the source factorization
k=(2*q+1)*2^t.  No finite-tape simulation or blank-tail assumption is
used in the transition theorem.
-/

namespace BB6Coverage.Agent24M2EvenCounted

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8Rst1Prime
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent8M2EvenResidueZero
open BB6Coverage.Agent24M2EvenSource
open BB6Coverage.Agent24M2EvenFrames
open BB6Coverage.Agent24LBinDecHRun
open BB6Coverage.Agent24ChampionTime
open BB6Coverage.Agent24Q4Endpoint
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent48CountedInc0
open BB6ChampionArithmetic

set_option maxHeartbeats 3000000

private theorem sideBit_append (xs ys : List Bool) :
    ∀ i, sideBit (xs ++ ys) i =
      if i < xs.length then sideBit xs i else sideBit ys (i-xs.length) := by
  intro i
  induction xs generalizing i with
  | nil => simp [sideBit]
  | cons x xs ih =>
      cases i with
      | zero => simp [sideBit]
      | succ i => simp [sideBit,ih]

private theorem sideBit_append_right (xs ys : List Bool) (i : Nat)
    (hi : xs.length ≤ i) :
    sideBit (xs ++ ys) i = sideBit ys (i-xs.length) := by
  rw [sideBit_append]
  simp [Nat.not_lt_of_ge hi]

private theorem sideBit_d1pow_true (n i : Nat) (hi : i < 3*n) :
    sideBit (d1pow n) i = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
      by_cases hsmall : i < 3
      · have hcases : i=0 ∨ i=1 ∨ i=2 := by omega
        rcases hcases with h|h|h <;> subst i <;>
          simp [d1pow,d1,sideBit]
      · have htail : i-3 < 3*n := by omega
        rw [d1pow,sideBit_append]
        simp [hsmall,d1,sideBit]
        exact ih (i-3) htail

private theorem sideBit_false_of_length (xs : List Bool) :
    ∀ i, xs.length ≤ i → sideBit xs i = false := by
  induction xs with
  | nil =>
      intro i hi
      simp [sideBit]
  | cons x xs ih =>
      intro i hi
      cases i with
      | zero => simp at hi
      | succ i =>
          simp [sideBit]
          apply ih
          simpa using hi

private theorem d0pow_add_right (a b : Nat) :
    d0pow (a+b) = d0pow b ++ d0pow a := by
  induction b with
  | zero => simp [d0pow]
  | succ b ih =>
      rw [Nat.add_succ]
      simp [d0pow,ih,List.append_assoc]


private theorem frameAt_tape_outside8
    (T : Int → Bool) (h : Int) (inside : Int → Bool)
    (c : FConfig) (x : Int)
    (hout : inside (x-h)=false) :
    (frameAt T h inside c).tape x = T x := by
  simpa [hout] using
    BB6Coverage.Agent8Rst1Prime.frameAt_tape T h inside c x

/-- The source word after exposing the three low d1 blocks and the
quotient's exact odd-part carry prefix. -/
private theorem m2ZeroSourceLeft
    (L k a q t ell : Nat)
    (hkBound : k < 2^(L-3))
    (hfactor : k=(2*q+1)*2^t)
    (hlen : L=ell+4+t)
    (hq : q<2^ell) :
    s1LeftFacing L (8*k) 2 a 0 =
      d1pow a ++ markerWord 2 ++ d0 ++ d1pow 3 ++
        d1pow t ++ d0 ++ binDec ell q ++ lh := by
  have hmul := binDec_mulpow2 (L-3) k 3 hkBound
  have hlen3 : L-3+3=L := by omega
  have hnum : k*2^3=8*k := by omega
  have hbin8 : binDec L (8*k) =
      d1pow 3 ++ binDec (L-3) k := by
    simpa [hlen3,hnum] using hmul
  have hlenK : L-3=ell+1+t := by omega
  have hcarry := binDec_carryPrefix ell q t hq
  have hbinK : binDec (L-3) k =
      d1pow t ++ d0 ++ binDec ell q := by
    calc
      binDec (L-3) k =
          binDec (ell+1+t) ((2*q+1)*2^t) := by
            rw [hlenK,hfactor]
      _ = d1pow t ++ d0 ++ binDec ell q := hcarry
  simp [s1LeftFacing,binDec_zero,hbin8,hbinK,List.append_assoc]

/-- The target counter is the same odd quotient with three additional
low-order carry blocks. -/
private theorem m2ZeroTargetBinDec
    (L k q t ell : Nat)
    (hfactor : k=(2*q+1)*2^t)
    (hlen : L=ell+4+t)
    (hq : q<2^ell) :
    binDec L (8*k-1) =
      d0pow (t+3) ++ d1 ++ binDec ell q := by
  have hpow : 2^(t+3)=8*2^t := by
    rw [Nat.pow_add]
    omega
  have hnum : 8*k=(2*q+1)*2^(t+3) := by
    calc
      8*k = 8*((2*q+1)*2^t) := by rw [hfactor]
      _ = (2*q+1)*(8*2^t) := by ac_rfl
      _ = (2*q+1)*2^(t+3) := by rw [← hpow]
  have hlen' : L=ell+1+(t+3) := by omega
  have hcarry := binDec_sub_one_carryPrefix ell q (t+3) hq
  simpa [hlen',hnum] using hcarry

/-- Exact source-side q4 left stream after the fixed setup, universal
H-run, fixed postlude, and E scan. -/
private def m2ZeroQ4LeftFacing
    (a t : Nat) (tail : List Bool) : List Bool :=
  [true] ++ d1pow a ++
    (markerWord 1 ++ d0pow (4+t) ++ d1 ++ tail)

/-- The all-q marker-2 residue-zero reset-prefix theorem. -/
theorem m2Even_residue0_q4_reset_prefix_source
    (L k a b : Nat) (h : Int)
    (hL : 4≤L) (hk : 0<k)
    (hbound : 8*k<2^L) (ha : 0<a) :
    run tm2 (resetPrefixCost 2 (8*k) a b)
      (s1Config L (8*k) 2 a 0 b h) =
      some (s1Config L (8*k-1) 1 (a+b+2) (2^b-1) 0
        (h+5+3*b)) := by
  have hpowL : 2^L=8*2^(L-3) := by
    calc
      2^L = 2^((L-3)+3) := by congr 1 <;> omega
      _ = 2^(L-3)*2^3 := by rw [Nat.pow_add]
      _ = 8*2^(L-3) := by omega
  have hkBound : k<2^(L-3) := by
    rw [hpowL] at hbound
    omega
  obtain ⟨q,t,ell,hfactor,hlenFactor,hq⟩ :=
    exists_odd_factor_bounded (L-3) k hk hkBound
  have hlen : L=ell+4+t := by omega

  let T : Int → Bool := (s1Config L (8*k) 2 a 0 b h).tape
  let N : Nat := 3*a+2
  let hN : Int := h-(N:Int)
  let hH : Int := hN-14
  let T1 : Int → Bool := sweptLeft N T h
  let Tsetup : Int → Bool :=
    (frameAt T1 hN m2ZeroSetupInside m2ZeroSetupEnd).tape
  let tail : List Bool := binDec ell q ++ lh
  let Rsrc : List Bool := d1pow t ++ d0 ++ tail
  let Thrun : Int → Bool := lbinDecHRunTape t Tsetup hH
  let Tpost : Int → Bool :=
    (frameAt Thrun (hN-12) m2ZeroPostludeInside m2ZeroPostludeEnd).tape
  let M : List Bool :=
    markerWord 1 ++ d0pow (4+t) ++ d1 ++ tail
  let W : List Bool := [true] ++ M
  let Q : List Bool := m2ZeroQ4LeftFacing a t tail

  have hsourceLeft := m2ZeroSourceLeft L k a q t ell
    hkBound hfactor hlen hq
  let srcPrefix : List Bool :=
    d1pow a ++ markerWord 2 ++ d0 ++ d1pow 3
  have hsrcSplit :
      s1LeftFacing L (8*k) 2 a 0 = srcPrefix ++ Rsrc := by
    rw [hsourceLeft]
    simp [srcPrefix,Rsrc,tail,List.append_assoc]
  have hsrcPrefixLen : srcPrefix.length=3*a+16 := by
    simp [srcPrefix,d1pow_length,markerWord,d0,d1]

  have hleftT1 :
      ∀ i : Nat, T1 (hH-(i:Int)) = sideBit Rsrc i := by
    intro i
    have hcoord : hH-(i:Int)=h-((3*a+16+i):Int) := by
      dsimp [hH,hN,N]
      omega
    have hpres :
        T1 (hH-(i:Int)) = T (hH-(i:Int)) := by
      dsimp [T1]
      apply BB6Coverage.Agent6Q4Prefix.sweptLeft_preserves_left
      dsimp [hH,hN,N]
      omega
    have hcell :
        T (h-((3*a+16+i):Int)) =
          sideBit (s1LeftFacing L (8*k) 2 a 0) (3*a+16+i) := by
      simpa [T] using
        s1Config_left_cell L (8*k) 2 a 0 b h (3*a+16+i)
    calc
      T1 (hH-(i:Int)) = T (hH-(i:Int)) := hpres
      _ = T (h-((3*a+16+i):Int)) := by rw [hcoord]
      _ = sideBit (s1LeftFacing L (8*k) 2 a 0) (3*a+16+i) := hcell
      _ = sideBit Rsrc i := by
        rw [hsrcSplit]
        have hs := sideBit_append_right srcPrefix Rsrc
          (3*a+16+i) (by rw [hsrcPrefixLen]; omega)
        simpa [hsrcPrefixLen] using hs

  have honN : leftOnes T h N := by
    simpa [N,T] using s1M2InitialLeftOnes L k a b h
  have honT1 : leftOnes T1 hH (3*t) := by
    intro i hi
    rw [hleftT1 i]
    have hbit : sideBit Rsrc i=true := by
      change sideBit (d1pow t ++ d0 ++ tail) i = true
      rw [List.append_assoc,sideBit_append]
      simpa [d1pow_length,hi] using sideBit_d1pow_true t i hi
    exact hbit
  have h0T1 : T1 (hH-(3*t:Int))=false := by
    calc
      T1 (hH-(3*t:Int)) = sideBit Rsrc (3*t) := hleftT1 (3*t)
      _ = false := by
        change sideBit (d1pow t ++ d0 ++ tail) _ = _
        rw [List.append_assoc, sideBit_append_right _ _ _ (by simp [d1pow_length] <;> omega)]
        simp [d1pow_length,d0,sideBit] <;> omega
  have hm1T1 : T1 (hH-(3*t:Int)-1)=false := by
    have hcoord : hH-(3*t:Int)-1 = hH-((3*t+1):Int) := by omega
    rw [hcoord]
    calc
      T1 (hH-((3*t+1):Int)) = sideBit Rsrc (3*t+1) := hleftT1 (3*t+1)
      _ = false := by
        change sideBit (d1pow t ++ d0 ++ tail) _ = _
        rw [List.append_assoc, sideBit_append_right _ _ _ (by simp [d1pow_length] <;> omega)]
        simp [d1pow_length,d0,sideBit] <;> omega
  have hthirdT1 : T1 (hH-(3*t:Int)-2)=true := by
    have hcoord : hH-(3*t:Int)-2 = hH-((3*t+2):Int) := by omega
    rw [hcoord]
    calc
      T1 (hH-((3*t+2):Int)) = sideBit Rsrc (3*t+2) := hleftT1 (3*t+2)
      _ = true := by
        change sideBit (d1pow t ++ d0 ++ tail) _ = _
        rw [List.append_assoc, sideBit_append_right _ _ _ (by simp [d1pow_length] <;> omega)]
        simp [d1pow_length,d0,sideBit] <;> omega
  have hrSource : T (h+1)=false := by
    simpa [T] using s1M2RightZero L k a b h
  have hrT1 : T1 (hN+1)=false := by
    have hs := sweptLeft_boundary_right_zero N T h hrSource
    simpa [T1,hN,N] using hs
  have hmatch :=
    m2ZeroSetup_match_after_initial_sweep L k a b h
      (by omega) hkBound
  have hmid :=
    m2ZeroSetup_HRun_Postlude t T1 hN hmatch
      honT1 h0T1 hm1T1 hrT1

  have hsetupLeft :
      ∀ i : Nat, Tsetup (hH-(i:Int)) = sideBit Rsrc i := by
    intro i
    have hout : m2ZeroSetupInside ((hH-(i:Int))-hN)=false := by
      simp [m2ZeroSetupInside,hH]
      omega
    have hf := frameAt_tape_outside8 T1 hN
      m2ZeroSetupInside m2ZeroSetupEnd (hH-(i:Int)) hout
    calc
      Tsetup (hH-(i:Int)) = T1 (hH-(i:Int)) := by
        simpa [Tsetup] using hf
      _ = sideBit Rsrc i := hleftT1 i
  have hrSetup : Tsetup (hH+1)=false := by
    have hcoord : hH+1=hN-13 := by dsimp [hH]; omega
    rw [hcoord]
    have hw := m2ZeroSetupAt_window T1 hN (-13) (by decide)
    change (frameAt T1 hN m2ZeroSetupInside m2ZeroSetupEnd).tape (hN-13) = false
    rw [show hN-13 = hN+(-13) by omega, hw]
    decide
  have honSetup : leftOnes Tsetup hH (3*t) := by
    intro i hi
    rw [hsetupLeft i]
    have hbit : sideBit Rsrc i=true := by
      change sideBit (d1pow t ++ d0 ++ tail) i = true
      rw [List.append_assoc,sideBit_append]
      simpa [d1pow_length,hi] using sideBit_d1pow_true t i hi
    exact hbit
  have hleftHrun :=
    lbinDecHRunTape_leftFacing_of_input t Tsetup hH tail
      hrSetup (by
        intro i
        simpa [Rsrc,List.append_assoc] using hsetupLeft i)
  have hrightPlus1 :=
    lbinDecHRunTape_rightPlus1 t Tsetup hH honSetup

  have hfirst := m2ZeroInitialSweep L k a b h (by omega) hkBound
  have hfirst' :
      run tm2 (9*a+6) (s1Config L (8*k) 2 a 0 b h) =
        some ⟨3,hN,T1⟩ := by
    simpa [T,N,hN,T1] using hfirst
  have hbase :
      run tm2 ((9*a+6)+(44+(12*t+4)+14))
        (s1Config L (8*k) 2 a 0 b h) =
        some (frameAt Thrun (hN-12)
          m2ZeroPostludeInside m2ZeroPostludeEnd) := by
    rw [run_append,hfirst']
    simp only [Option.bind_some]
    simpa [Tsetup,Thrun,hH] using hmid
  have hbase' :
      run tm2 ((9*a+6)+(44+(12*t+4)+14))
        (s1Config L (8*k) 2 a 0 b h) =
        some ⟨4,hN+2,Tpost⟩ := by
    rw [hbase]
    congr 1
    apply BB6Coverage.Agent8Rst1Prime.config_ext
    · simp [m2ZeroPostludeEnd]
    · simp [m2ZeroPostludeEnd]; omega
    · rfl

  have hpostRight (x : Int) (hx : hN+2≤x) :
      Tpost x = T1 x := by
    have houtPost :
        m2ZeroPostludeInside (x-(hN-12))=false := by
      simp [m2ZeroPostludeInside]
      omega
    have hp := frameAt_tape_outside8 Thrun (hN-12)
      m2ZeroPostludeInside m2ZeroPostludeEnd x houtPost
    have hh := lbinDecHRunTape_preserves_right t Tsetup hH x (by omega)
    have houtSetup : m2ZeroSetupInside (x-hN)=false := by
      simp [m2ZeroSetupInside]
      omega
    have hs := frameAt_tape_outside8 T1 hN
      m2ZeroSetupInside m2ZeroSetupEnd x houtSetup
    calc
      Tpost x = Thrun x := by simpa [Tpost] using hp
      _ = Tsetup x := hh
      _ = T1 x := by simpa [Tsetup] using hs

  have hlinear : linearRightOnes Tpost (hN+2) (3*a) := by
    intro i hi
    have hblock := sweptLeft_shifted_block N T h honN i (by omega)
    have hcoord : hN+2+(i:Int) =
        h-(N:Int)+2+(i:Int) := by rfl
    calc
      Tpost (hN+2+(i:Int)) =
          T1 (hN+2+(i:Int)) :=
        hpostRight (hN+2+(i:Int)) (by omega)
      _ = true := by
        simpa [T1,hcoord,N] using hblock

  have hscan := E_scan Tpost (hN+2) (3*a) hlinear
  have hscanHead : hN+2+(3*a:Int)=h := by
    dsimp [hN,N]
    omega
  have hpre :
      run tm2 (((9*a+6)+(44+(12*t+4)+14))+3*a)
        (s1Config L (8*k) 2 a 0 b h) =
        some ⟨4,h,Tpost⟩ := by
    rw [run_append,hbase']
    simp only [Option.bind_some]
    simpa [hscanHead] using hscan

  have hd0split : d0pow (4+t)=d0pow 4 ++ d0pow t := by
    have hcomm : 4+t=t+4 := by omega
    rw [hcomm]
    exact d0pow_add_right t 4
  let P : List Bool := [true] ++ markerWord 1 ++ d0pow 4
  let Rout : List Bool := d0pow t ++ d1 ++ tail
  have hWsplit : W=P++Rout := by
    dsimp [W,M,P,Rout]
    rw [hd0split]
    simp [List.append_assoc]
  have hPlen : P.length=16 := by
    simp [P,markerWord,d0pow_length,d0]

  have hpostLeft :
      ∀ i : Nat, Tpost (hN+2-(i:Int))=sideBit W i := by
    intro i
    by_cases hi0 : i=0
    · subst i
      have hp := hpostRight (hN+2) (by omega)
      have hb := sweptLeft_shifted_block N T h honN 0 (by omega)
      have hcoord : hN+2 =
          h-(N:Int)+2 := by rfl
      rw [show hN+2-((0:Nat):Int)=hN+2 by omega]
      calc
        Tpost (hN+2) = T1 (hN+2) := hp
        _ = true := by simpa [T1,hcoord,N] using hb
        _ = sideBit W 0 := by simp [W,sideBit]
    · by_cases hi15 : i=15
      · subst i
        have xcoord : hN+2-(15:Int)=hH+1 := by dsimp [hH]; omega
        have hout :
            m2ZeroPostludeInside
              ((hN+2-(15:Int))-(hN-12))=false := by
          simp [m2ZeroPostludeInside]
          omega
        have hp := frameAt_tape_outside8 Thrun (hN-12)
          m2ZeroPostludeInside m2ZeroPostludeEnd
          (hN+2-(15:Int)) hout
        calc
          Tpost (hN+2-(15:Int)) = Thrun (hN+2-(15:Int)) := by
            simpa [Tpost] using hp
          _ = true := by rw [xcoord]; exact hrightPlus1
          _ = sideBit W 15 := by
            rw [hWsplit,sideBit_append]
            simp [P,hPlen,markerWord,d0pow,d0,sideBit]
      · by_cases hi16 : 16≤i
        · have xcoord :
            hN+2-(i:Int)=hH-((i-16:Nat):Int) := by
              dsimp [hH]
              omega
          have hout :
              m2ZeroPostludeInside
                ((hN+2-(i:Int))-(hN-12))=false := by
            simp [m2ZeroPostludeInside]
            omega
          have hp := frameAt_tape_outside8 Thrun (hN-12)
            m2ZeroPostludeInside m2ZeroPostludeEnd
            (hN+2-(i:Int)) hout
          have hside : sideBit W i=sideBit Rout (i-16) := by
            rw [hWsplit]
            exact sideBit_append_right P Rout i (by rw [hPlen]; omega)
          calc
            Tpost (hN+2-(i:Int)) = Thrun (hN+2-(i:Int)) := by
              simpa [Tpost] using hp
            _ = sideBit Rout (i-16) := by
              rw [xcoord]
              simpa [Rout,List.append_assoc] using hleftHrun (i-16)
            _ = sideBit W i := hside.symm
        · have hi1 : 1≤i := by omega
          have hi14 : i≤14 := by omega
          have hlocal :
              Tpost (hN+2-(i:Int))=sideBit W i := by
            let x : Int := 14-(i:Int)
            have hx : m2ZeroPostludeInside x=true := by
              simp [x,m2ZeroPostludeInside]
              omega
            have hw := m2ZeroPostludeAt_window Thrun (hN-12) x hx
            have hcoord : hN+2-(i:Int)=hN-12+x := by
              dsimp [x]
              omega
            have hside :
                sideBit W i =
                  decide (x∈m2ZeroPostludeEnd.marked) := by
              rw [hWsplit,sideBit_append]
              have hc : i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 := by omega
              rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [P,markerWord,d0pow,d0,sideBit,x,m2ZeroPostludeEnd]
            change (frameAt Thrun (hN-12)
              m2ZeroPostludeInside m2ZeroPostludeEnd).tape
              (hN+2-(i:Int)) = sideBit W i
            rw [hcoord]
            exact hw.trans hside.symm
          exact hlocal

  have hqLeft :
      ∀ i : Nat, Tpost (h-(i:Int))=sideBit Q i := by
    intro i
    by_cases hi : i≤3*a
    · let j : Nat := 3*a-i
      have hj : j<N := by dsimp [j,N]; omega
      have hcoord : h-(i:Int)=hN+2+(j:Int) := by
        dsimp [hN,N,j]
        omega
      have hp := hpostRight (hN+2+(j:Int)) (by omega)
      have hb := sweptLeft_shifted_block N T h honN j hj
      have hbit : sideBit Q i=true := by
        by_cases hzero : i=0
        · subst i
          simp [Q,m2ZeroQ4LeftFacing,sideBit]
        · have hi' : i-1<3*a := by omega
          have hone := sideBit_d1pow_true a (i-1) hi'
          have htail :
              sideBit (d1pow a ++ M) (i-1)=true := by
            rw [sideBit_append]
            simp [d1pow_length,hi',hone]
          have hq :
              sideBit Q i=sideBit (d1pow a ++ M) (i-1) := by
            change sideBit ([true] ++ (d1pow a ++ M)) i = _
            rw [sideBit_append]
            simp [hzero]
          rw [hq]
          exact htail
      calc
        Tpost (h-(i:Int)) = Tpost (hN+2+(j:Int)) := by rw [hcoord]
        _ = T1 (hN+2+(j:Int)) := hp
        _ = true := by simpa [T1,hN,N] using hb
        _ = sideBit Q i := hbit.symm
    · let j : Nat := i-3*a
      have hj : 1≤j := by dsimp [j]; omega
      have hcoord : h-(i:Int)=hN+2-(j:Int) := by
        dsimp [hN,N,j]
        omega
      have hside : sideBit Q i=sideBit W j := by
        have hlenX : ([true]++d1pow a).length=3*a+1 := by
          simp [d1pow_length]
        have hqside0 := sideBit_append_right ([true]++d1pow a) M i
          (by rw [hlenX]; omega)
        have hwside0 := sideBit_append_right [true] M j (by omega)
        have hqside :
            sideBit Q i=sideBit M (i-(3*a+1)) := by
          change sideBit (([true]++d1pow a)++M) i = _
          simpa [hlenX,d1pow_length] using hqside0
        have hwside :
            sideBit W j=sideBit M (j-1) := by
          change sideBit ([true]++M) j = _
          simpa using hwside0
        have hindex : i-(3*a+1)=j-1 := by dsimp [j]; omega
        rw [hqside,hwside,hindex]
      calc
        Tpost (h-(i:Int)) = Tpost (hN+2-(j:Int)) := by rw [hcoord]
        _ = sideBit W j := hpostLeft j
        _ = sideBit Q i := hside.symm

  have hpostOriginalRight (x : Int) (hx : h+2≤x) :
      Tpost x=T x := by
    calc
      Tpost x = T1 x := hpostRight x (by dsimp [hN,N]; omega)
      _ = T x := by
        dsimp [T1]
        apply BB6Coverage.Agent6Q4Prefix.sweptLeft_preserves_right
        omega

  have hfirstFive : ∀ i : Nat, i<5 → Tpost (h+(i:Int))=true := by
    intro i hi
    by_cases hsmall : i<2
    · let j : Nat := 3*a+i
      have hj : j<N := by dsimp [j,N]; omega
      have hcoord : h+(i:Int)=hN+2+(j:Int) := by
        dsimp [hN,N,j]
        omega
      have hp := hpostRight (h+(i:Int)) (by dsimp [hN,N]; omega)
      have hb := sweptLeft_shifted_block N T h honN j hj
      calc
        Tpost (h+(i:Int)) = T1 (h+(i:Int)) := hp
        _ = true := by simpa [T1,hN,N,j,hcoord] using hb
    · have hi2 : 2≤i := by omega
      have hcoord : h+(i:Int)=h+1+((i-1:Nat):Int) := by omega
      have hp := hpostOriginalRight (h+(i:Int)) (by omega)
      have hcell := s1Config_right_cell L (8*k) 2 a 0 b h (i-1)
      have hbit :
          sideBit (s1PhysicalRight b) (i-1)=true := by
        have hc : i=2 ∨ i=3 ∨ i=4 := by omega
        rcases hc with rfl|rfl|rfl <;> simp [s1PhysicalRight_source,sideBit]
      calc
        Tpost (h+(i:Int)) = T (h+(i:Int)) := hp
        _ = sideBit (s1PhysicalRight b) (i-1) := by
          simpa [T,hcoord] using hcell
        _ = true := hbit
  have hzero5 : Tpost (h+5)=false := by
    have hp := hpostOriginalRight (h+5) (by omega)
    have hcell := s1Config_right_cell L (8*k) 2 a 0 b h 4
    have hcell' : T (h+5)=sideBit (s1PhysicalRight b) 4 := by
      rw [show h+5 = h+1+((4:Nat):Int) by omega]
      exact hcell
    have hbit : sideBit (s1PhysicalRight b) 4=false := by
      simp [s1PhysicalRight_source,sideBit]
    exact hp.trans (hcell'.trans hbit)
  have hzero6 : Tpost (h+6)=false := by
    have hp := hpostOriginalRight (h+6) (by omega)
    have hcell := s1Config_right_cell L (8*k) 2 a 0 b h 5
    have hcell' : T (h+6)=sideBit (s1PhysicalRight b) 5 := by
      rw [show h+6 = h+1+((5:Nat):Int) by omega]
      exact hcell
    have hbit : sideBit (s1PhysicalRight b) 5=false := by
      simp [s1PhysicalRight_source,sideBit]
    exact hp.trans (hcell'.trans hbit)
  have hones : ∀ i : Nat, i<3*(b+1) →
      Tpost (h+7+(i:Int))=true := by
    intro i hi
    have hp := hpostOriginalRight (h+7+(i:Int)) (by omega)
    have hcoord : h+7+(i:Int)=h+1+((6+i):Int) := by omega
    have hcell := s1Config_right_cell L (8*k) 2 a 0 b h (6+i)
    have hbit :
        sideBit (s1PhysicalRight b) (6+i)=true := by
      rw [s1PhysicalRight_source]
      have hbase :
          sideBit ([false,true,true,true,false,false] ++
            d1pow (b+1)) (6+i) =
            sideBit (d1pow (b+1)) i := by
        have hs := sideBit_append_right
          [false,true,true,true,false,false] (d1pow (b+1))
          (6+i) (by simp <;> omega)
        simpa using hs
      rw [hbase]
      exact sideBit_d1pow_true (b+1) i hi
    calc
      Tpost (h+7+(i:Int)) = T (h+7+(i:Int)) := hp
      _ = sideBit (s1PhysicalRight b) (6+i) := by
        simpa [T,hcoord] using hcell
      _ = true := hbit
  have htail :
      ∀ i : Nat, 9+3*b≤i → Tpost (h+1+(i:Int))=false := by
    intro i hi
    have hp := hpostOriginalRight (h+1+(i:Int)) (by omega)
    have hcell := s1Config_right_cell L (8*k) 2 a 0 b h i
    have hlen :
        ([false,true,true,true,false,false]++
          d1pow (b+1)).length=9+3*b := by
      simp [d1pow_length] <;> omega
    have hbit :
        sideBit (s1PhysicalRight b) i=false := by
      rw [s1PhysicalRight_source]
      exact sideBit_false_of_length
        ([false,true,true,true,false,false]++d1pow (b+1))
        i (by rw [hlen]; exact hi)
    calc
      Tpost (h+1+(i:Int)) = T (h+1+(i:Int)) := hp
      _ = sideBit (s1PhysicalRight b) i := by
        simpa [T] using hcell
      _ = false := hbit

  have hblank : ∀ i : Nat, i≤4 →
      Tpost (h+10+(3*b:Int)+(i:Int))=false := by
    intro i hi
    have hcoord :
        h+10+(3*b:Int)+(i:Int)=h+1+((9+3*b+i:Nat):Int) := by omega
    rw [hcoord]
    apply htail
    omega
  have hshape : q4RightShape Tpost h b :=
    ⟨hfirstFive,hzero5,hzero6,hones,hblank⟩

  have happend :
      s1LeftFacing L (8*k-1) 1 (a+b+2) (2^b-1) =
        d0pow b ++ d1pow 2 ++ Q.drop 1 := by
    have hpow := binDec_pow2_sub_one a b
    have hbinSub := m2ZeroTargetBinDec L k q t ell hfactor hlen hq
    have hd1 := d1pow_add_right a 2
    have hd0 : d0++d0pow (t+3)=d0pow (t+4) := by
      have heq : t+4=(t+3)+1 := by omega
      rw [heq]
      rfl
    have hd0comm : d0++d0pow (t+3)=d0pow (4+t) := by
      calc
        d0++d0pow (t+3)=d0pow (t+4) := hd0
        _ = d0pow (4+t) := by congr 1 <;> omega
    unfold s1LeftFacing
    rw [hpow,hbinSub,hd1]
    simp [Q,m2ZeroQ4LeftFacing,M,tail,hd0comm,
      List.drop,List.append_assoc]
    rw [← List.append_assoc,hd0comm]

  have hfactor8 : 8*k=(2*q+1)*2^(t+3) := by
    have hpow : 2^(t+3)=8*2^t := by
      rw [Nat.pow_add]
      omega
    calc
      8*k = 8*((2*q+1)*2^t) := by rw [hfactor]
      _ = (2*q+1)*(8*2^t) := by ac_rfl
      _ = (2*q+1)*2^(t+3) := by rw [← hpow]
  have hv : BB6ChampionArithmetic.v2 (8*k)=t+3 :=
    v2_of_odd_factorization (8*k) q (t+3) hfactor8
  have hcost :
      resetPrefixCost 2 (8*k) a b =
        (((9*a+6)+(44+(12*t+4)+14)+3*a)+(39+3*b)) := by
    simp [resetPrefixCost,hv]
    omega

  have hq4 :=
    q4_suffix_run_to_s1Config Tpost h b L (8*k-1) 1
      (a+b+2) (2^b-1) Q hshape htail hqLeft happend
  have hprefix :
      run tm2 (resetPrefixCost 2 (8*k) a b)
        (s1Config L (8*k) 2 a 0 b h) =
        some (s1Config L (8*k-1) 1 (a+b+2) (2^b-1) 0
          (h+5+3*b)) := by
    rw [hcost,run_append,hpre]
    simp only [Option.bind_some]
    exact hq4
  exact hprefix

/-- Complete original-TM2 counted increment for every positive k in
the marker-2, n=8*k source family. -/
theorem m2Even_residue0_counted_increment_source
    (L k a b : Nat) (h : Int)
    (hL : 4≤L) (hk : 0<k)
    (hbound : 8*k<2^L) (ha : 0<a) :
    run tm2 (proposedIncrementCost 2 (8*k) a b)
      (s1Config L (8*k) 2 a 0 b h) =
      some (s1Config L (8*k-1) 1 (a+b+2) 0 (2^b-1)
        (h+5+3*b)) := by
  have hp := m2Even_residue0_q4_reset_prefix_source
    L k a b h hL hk hbound ha
  have hboundDrain := resetDrainBound a b 2 ha
  have hrun := s1Config_reset_prefix_then_counted_drain
    L (8*k-1) 1 (a+b+2) b (h+5+3*b)
    (s1Config L (8*k) 2 a 0 b h)
    (resetPrefixCost 2 (8*k) a b)
    hp (by simpa [resetDelta] using hboundDrain)
  simpa [proposedIncrementCost_decomp] using hrun

#print axioms m2Even_residue0_q4_reset_prefix_source
#print axioms m2Even_residue0_counted_increment_source

end BB6Coverage.Agent24M2EvenCounted
