import Lean.Elab.Tactic.Omega
import BlankThirtySecondRejoin
import EAllDouble
import CryptidThree
import ACodeFirstReturn
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent37ThirtyThirdRejoin

open CryptidBoundary BB6.BoundaryPadding BB6.Padding
open BB6.Agent2ThirtySecondRejoin

/-- The exact DRegular state after the 9,276-step segment from seed33. -/
def terminal9276 : DRegular.L :=
  (BB6.DRegularFast.fastRun 9276 seed33).getD ⟨9,0,0⟩

def t33 : Nat := (terminal9276.a - 7) / 9
def u33 : Nat := t33 / 3
def k33 : Nat := 3*t33+1
def s33 : Nat := 8*t33+3
def r33 : Nat := 64*u33+10

def seed34 : DRegular.L := ⟨512*u33+129,0,0⟩

def y33 : List Bool :=
  List.replicate 7 true ++ [false] ++ List.replicate 6 true

def ws33 : List Bool := [false,false,true,true,false,true,true]

/-- The residue replay is now checked against the exact 3-adic fast evaluator,
    not merely against a separately implemented BigInt simulator. -/
theorem terminal9276_certificate :
    DRegular.run 9276 seed33 = some terminal9276 ∧
      terminal9276.a % 59049 = 49579 ∧
      terminal9276.q = 5 ∧
      terminal9276.b = 1 := by
  rw [BB6.DRegularFast.fastRun_correct 9276 seed33 seed33_canon]
  decide

/-- The residue 49,579 modulo 59,049 forces a=9*t+7 and t=0 mod 27. -/
theorem terminal9276_shape :
    terminal9276 = ⟨9*t33+7,5,1⟩ ∧ t33 % 27 = 0 := by
  have hrun := terminal9276_certificate.1
  have hfast : BB6.DRegularFast.fastRun 9276 seed33 =
      some ⟨9*t33+7,5,1⟩ := by
    rw [← BB6.DRegularFast.fastRun_correct 9276 seed33 seed33_canon]
    exact hrun
  have hterm : terminal9276 = ⟨9*t33+7,5,1⟩ := by
    simp [terminal9276,hfast]
  have hmod59049 := terminal9276_certificate.2.1
  have hmod9 : terminal9276.a % 9 = 7 := by
    calc
      terminal9276.a % 9 =
          (terminal9276.a % 59049) % 9 := by
            symm
            exact Nat.mod_mod_of_dvd terminal9276.a (by norm_num : 9 ∣ 59049)
      _ = 49579 % 9 := by rw [hmod59049]
      _ = 7 := by norm_num
  have hmod243 : terminal9276.a % 243 = 7 := by
    calc
      terminal9276.a % 243 =
          (terminal9276.a % 59049) % 243 := by
            symm
            exact Nat.mod_mod_of_dvd terminal9276.a (by norm_num : 243 ∣ 59049)
      _ = 49579 % 243 := by rw [hmod59049]
      _ = 7 := by norm_num
  have hsub9 : (terminal9276.a-7) % 9 = 0 := by omega
  have hdiv9 := Nat.mod_add_div (terminal9276.a-7) 9
  rw [hsub9] at hdiv9
  have hEq : terminal9276.a = 9*t33+7 := by
    dsimp [t33]
    omega
  have hsub243 : (terminal9276.a-7) % 243 = 0 := by omega
  have hmodMul : (9*t33) % (9*27) = 0 := by
    simpa [hEq] using hsub243
  have hdiv243 : 9*27 ∣ 9*t33 :=
    Nat.dvd_of_mod_eq_zero hmodMul
  have hdiv27 : 27 ∣ t33 :=
    Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdiv243
  have hmod27 : t33 % 27 = 0 :=
    Nat.mod_eq_zero_of_dvd hdiv27
  exact ⟨hterm,hmod27⟩

/-- The first undefined regular successor is immediately after transition 9,276. -/
theorem terminal9276_first_stop :
    DRegular.run 9276 seed33 = some terminal9276 ∧
      DRegular.next terminal9276 = none := by
  refine ⟨terminal9276_certificate.1, ?_⟩
  rw [terminal9276_shape.1]
  have hm : (9*t33+7) % 3 = 1 := by omega
  simp [DRegular.next,hm]

theorem t33_eq_three_u33 : t33 = 3*u33 := by
  have hmod27 := terminal9276_shape.2
  have hdiv27 : 27 ∣ t33 := Nat.dvd_of_mod_eq_zero hmod27
  have hdiv3 : 3 ∣ t33 := dvd_trans (by norm_num) hdiv27
  have hmod3 : t33 % 3 = 0 := Nat.mod_eq_zero_of_dvd hdiv3
  have h := Nat.mod_add_div t33 3
  rw [hmod3] at h
  dsimp [u33]
  omega

theorem seed34_canon : DRegular.Canon seed34 := by
  constructor
  · dsimp [seed34]
    omega
  · right
    rfl

/-- The q=5,b=1 source section is exactly the EAllDouble(q=4) input. -/
theorem terminal9276_eAll_input :
    DRegularSource.sourceSection terminal9276 =
      CryptidBoundary.init
        (List.replicate (3*k33+2) true ++
          false :: (CryptidBoundary.pairs 4 ++ [true,true])) := by
  rw [terminal9276_shape.1]
  have htail :
      CryptidBoundary.oppairs 5 ++ [true] =
        false :: (CryptidBoundary.pairs 4 ++ [true,true]) := by
    decide
  simp only [DRegularSource.sourceSection, List.replicate_one,
    List.append_assoc]
  rw [htail]
  congr 1
  dsimp [k33]
  omega

def eAllTime33 : Nat := BB6.Agent32EAll.duration k33 4
def eThreeTime33 : Nat := 12*s33*s33+49*s33+58

def eThreeInput33 : CryptidBoundary.Cfg :=
  CryptidBoundary.init
    (List.replicate (3*s33+2) true ++
      false :: ([true,true,true] ++ y33))

def eThreeOutput33 : CryptidBoundary.Cfg :=
  ⟨[],false,
    List.replicate (8*s33+9) true ++
      (CryptidBoundary.packetThree ++ y33),5⟩

/-- The EAllDouble output is exactly the physical input of E-three. -/
theorem eAll_output_eThree_input :
    BB6.Agent32EAll.output k33 4 [] = eThreeInput33 := by
  change
    (⟨[],false,
      List.replicate (8*k33+5) true ++
        (false :: List.replicate 10 true ++
          (false :: List.replicate 6 true)),5⟩ : CryptidBoundary.Cfg) =
    ⟨[],false,
      true :: true ::
        (List.replicate (3*s33+2) true ++
          false :: ([true,true,true] ++ y33)),5⟩
  have hlen : 8*k33+5 = 3*s33+4 := by
    dsimp [k33,s33]
    omega
  have hrep :
      List.replicate (8*k33+5) true =
        true :: true :: List.replicate (3*s33+2) true := by
    rw [hlen, show 3*s33+4 = 2+(3*s33+2) by omega,
      ← List.replicate_append_replicate]
    rfl
  have htail :
      false :: (List.replicate 10 true ++
        (false :: List.replicate 6 true)) =
      false :: ([true,true,true] ++ y33) := by
    simp [y33,List.append_assoc]
  rw [hrep,htail]

theorem eAll_source_return33 :
    ObsEq
      (CryptidBoundary.run eAllTime33
        (DRegularSource.sourceSection terminal9276))
      (BB6.Agent32EAll.output k33 4 []) := by
  rw [terminal9276_eAll_input]
  simpa [eAllTime33] using
    (BB6.Agent32EAll.all_e_double_implicit_blank k33 4)

theorem eThree_after_eAll33 :
    CryptidBoundary.run eThreeTime33
      (BB6.Agent32EAll.output k33 4 []) = eThreeOutput33 := by
  rw [eAll_output_eThree_input]
  simpa [eThreeTime33,eThreeOutput33] using
    (CryptidBoundary.full_E_three s33 y33)

theorem eThree_source_return33 :
    ObsEq
      (CryptidBoundary.run eThreeTime33
        (BB6.Agent32EAll.output k33 4 []))
      eThreeOutput33 := by
  rw [eThree_after_eAll33]
  exact BB6.Padding.cfgEq_refl _

def xs33 : List Bool :=
  List.replicate (3*r33+1) true ++
    false :: CryptidA.wordCode ws33

def aStart33 : CryptidBoundary.Cfg :=
  BB6.CryptidACodeFirstReturn.mixedStart r33 ws33 []

def aEnd33 : CryptidBoundary.Cfg :=
  BB6.CryptidACodeFirstReturn.mixedEnd r33 ws33 []

def aCodeTime33 : Nat :=
  (12*r33*r33+41*r33+32) +
    (CryptidA.wordCost (4*r33+3) ws33 +
      (2*((4*r33+3)+CryptidA.wordInc ws33)+6))

/-- The E-three tail is precisely the seven-symbol mixed A-code. -/
theorem eThreeOutput33_eq_init_xs :
    eThreeOutput33 = CryptidBoundary.init xs33 := by
  have hprefix : 8*s33+9 = 3*r33+3 := by
    have ht := t33_eq_three_u33
    dsimp [s33,r33]
    omega
  have htail :
      CryptidBoundary.packetThree ++ y33 =
        false :: CryptidA.wordCode ws33 := by
    decide
  change
    (⟨[],false,
      List.replicate (8*s33+9) true ++
        (CryptidBoundary.packetThree ++ y33),5⟩ : CryptidBoundary.Cfg) =
    ⟨[],false,true :: true :: xs33,5⟩
  rw [htail]
  have hrep :
      List.replicate (8*s33+9) true =
        true :: true :: List.replicate (3*r33+1) true := by
    rw [hprefix, show 3*r33+3 = 2+(3*r33+1) by omega,
      ← List.replicate_append_replicate]
    rfl
  rw [hrep]
  simp [xs33,List.append_assoc]

theorem aStart33_eq_init_padded :
    aStart33 = CryptidBoundary.init (xs33 ++ [false]) := by
  simp [aStart33,BB6.CryptidACodeFirstReturn.mixedStart,
    xs33,ws33,List.append_assoc]

theorem eThree_to_AStart33 :
    ObsEq eThreeOutput33 aStart33 := by
  have hpad0 := BB6.BoundaryPadding.source_init_pad 0 1 xs33
  have hpad : ObsEq
      (CryptidBoundary.init xs33)
      (CryptidBoundary.init (xs33 ++ [false])) := by
    simpa [CryptidBoundary.run,List.replicate_one] using hpad0
  rw [eThreeOutput33_eq_init_xs,aStart33_eq_init_padded]
  exact hpad

theorem aCode_return33 :
    CryptidBoundary.run aCodeTime33 aStart33 = aEnd33 := by
  simpa [aCodeTime33,aStart33,aEnd33,
    BB6.CryptidACodeFirstReturn.mixedStart,
    BB6.CryptidACodeFirstReturn.mixedEnd] using
    (BB6.CryptidACodeFirstReturn.full_A_mixed_code_first_return
      r33 ws33 []).1

theorem eThree_aCode_return33 :
    ObsEq
      (CryptidBoundary.run aCodeTime33 eThreeOutput33)
      aEnd33 := by
  have h := BB6.BoundaryPadding.source_congr
    aCodeTime33 eThree_to_AStart33
  rw [aCode_return33] at h
  simpa [aStart33,aEnd33] using h

theorem aEnd33_eq_seed34_source :
    aEnd33 = DRegularSource.sourceSection seed34 := by
  have hinc : CryptidA.wordInc ws33 = 19 := by decide
  have hlen :
      2*((4*r33+3)+CryptidA.wordInc ws33)+5 =
        512*u33+129 := by
    rw [hinc]
    dsimp [r33]
    omega
  have hrep :
      true :: true :: List.replicate (512*u33+127) true =
        List.replicate (512*u33+129) true := by
    rw [show 512*u33+129 = 2+(512*u33+127) by omega,
      ← List.replicate_append_replicate]
    rfl
  simp [aEnd33,BB6.CryptidACodeFirstReturn.mixedEnd,
    DRegularSource.sourceSection,seed34,
    CryptidBoundary.init,CryptidBoundary.oppairs,
    hlen,hrep]

def sourceReturn33Time : Nat :=
  eAllTime33+eThreeTime33+aCodeTime33

theorem source_return33 :
    ObsEq
      (CryptidBoundary.run sourceReturn33Time
        (DRegularSource.sourceSection terminal9276))
      (DRegularSource.sourceSection seed34) := by
  have hE := BB6.BoundaryPadding.source_chain
    eAllTime33 eThreeTime33
    (DRegularSource.sourceSection terminal9276)
    (BB6.Agent32EAll.output k33 4 [])
    eThreeOutput33
    eAll_source_return33 eThree_source_return33
  have hA := eThree_aCode_return33
  have hEA := BB6.BoundaryPadding.source_chain
    (eAllTime33+eThreeTime33) aCodeTime33
    (DRegularSource.sourceSection terminal9276)
    eThreeOutput33 aEnd33 hE hA
  rw [aEnd33_eq_seed34_source] at hEA
  simpa [sourceReturn33Time] using hEA

def exception33Time (T22 Tnorm24 Tnorm27 : Nat) : Nat :=
  BB6.Agent2ThirtySecondRejoin.reentry32Time T22 Tnorm24 Tnorm27 +
    DRegular.accumulated 9276 seed33

def reentry33Time (T22 Tnorm24 Tnorm27 : Nat) : Nat :=
  exception33Time T22 Tnorm24 Tnorm27 + sourceReturn33Time

/-- The 9,276-step q=5 E/E/A exception is now a source-exact continuation
    from the conditional blank-root seed33. -/
theorem blank_thirty_third_exception_from
    (T22 Tnorm24 Tnorm27 : Nat)
    (h32 : ObsEq
      (CryptidBoundary.run
        (BB6.Agent2ThirtySecondRejoin.reentry32Time
          T22 Tnorm24 Tnorm27) CryptidBoundary.blank)
      (DRegularSource.sourceSection seed33)) :
    ObsEq
      (CryptidBoundary.run (exception33Time T22 Tnorm24 Tnorm27)
        CryptidBoundary.blank)
      (DRegularSource.sourceSection terminal9276) := by
  apply BB6.Agent25RootChain.extend_regular
    CryptidBoundary.blank
    (BB6.Agent2ThirtySecondRejoin.reentry32Time T22 Tnorm24 Tnorm27)
    9276 seed33 terminal9276
  · exact seed33_canon
  · exact terminal9276_certificate.1
  · exact h32

theorem blank_thirty_third_exception :
    ∃ T22 Tnorm24 Tnorm27,
      ObsEq
        (CryptidBoundary.run (exception33Time T22 Tnorm24 Tnorm27)
          CryptidBoundary.blank)
        (DRegularSource.sourceSection terminal9276) := by
  obtain ⟨T22,Tnorm24,Tnorm27,h32⟩ :=
    BB6.Agent2ThirtySecondRejoin.blank_thirty_second_reentry
  exact ⟨T22,Tnorm24,Tnorm27,
    blank_thirty_third_exception_from T22 Tnorm24 Tnorm27 h32⟩

/-- The authentic blank-root path now has a third new prepared-section
    continuation, ending at seed34=L(512*u33+129,0,0). -/
theorem blank_thirty_third_reentry :
    ∃ T22 Tnorm24 Tnorm27,
      ObsEq
        (CryptidBoundary.run (reentry33Time T22 Tnorm24 Tnorm27)
          CryptidBoundary.blank)
        (DRegularSource.sourceSection seed34) := by
  obtain ⟨T22,Tnorm24,Tnorm27,h33⟩ :=
    blank_thirty_third_exception
  exact ⟨T22,Tnorm24,Tnorm27,
    BB6.BoundaryPadding.source_chain
      (exception33Time T22 Tnorm24 Tnorm27) sourceReturn33Time
      CryptidBoundary.blank
      (DRegularSource.sourceSection terminal9276)
      (DRegularSource.sourceSection seed34)
      h33 source_return33⟩

#print axioms terminal9276_certificate
#print axioms terminal9276_first_stop
#print axioms blank_thirty_third_exception
#print axioms source_return33
#print axioms blank_thirty_third_reentry

end BB6.Agent37ThirtyThirdRejoin
