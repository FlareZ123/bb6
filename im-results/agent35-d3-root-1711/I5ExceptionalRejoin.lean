import I5Root1711
import EDouble
import DRegularBSource
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 180000
set_option maxHeartbeats 0

namespace BB6.Agent35I5Exceptional

open CryptidBoundary
open BB6.BoundaryPadding
open BB6.Padding
open BB6.Agent19.Physical
open BB6.Portfolio

/-- The concrete 729-digit quotient parameter at the modeled seed5 E exit. -/
def t5 : Nat := (DRegular.terminal5.a - 4) / 9

theorem terminal5_shape :
    DRegular.terminal5 = (⟨9*t5+4,5,1⟩ : DRegular.L) := by
  have hq0 : DRegular.terminal5.q = 5 := by decide
  have hb0 : DRegular.terminal5.b = 1 := by decide
  have ha0 : DRegular.terminal5.a % 9 = 4 := by decide
  cases h : DRegular.terminal5 with
  | mk a q b =>
    have hA : DRegular.terminal5.a = a := congrArg DRegular.L.a h
    have hQ : DRegular.terminal5.q = q := congrArg DRegular.L.q h
    have hB : DRegular.terminal5.b = b := congrArg DRegular.L.b h
    have ha : a % 9 = 4 := by simpa [hA] using ha0
    have hq : q = 5 := hQ.symm.trans hq0
    have hb : b = 1 := hB.symm.trans hb0
    simp only [DRegular.L.mk.injEq]
    constructor
    · have hval : a = 9*((a-4)/9)+4 := by omega
      simpa [t5,hA] using hval
    · exact ⟨hq,hb⟩

theorem t5_mod3 : t5 % 3 = 2 := by
  decide

def eCost (t : Nat) : Nat :=
  12*(3*t)*(3*t) + 49*(3*t) + 64 + 4*3
def bCost (t : Nat) : Nat :=
  12*(8*t+1)*(8*t+1) + 49*(8*t+1) + 40
def bThirdIndex (t : Nat) : Nat := (64*t+25)/3
def bThirdCost (t : Nat) : Nat :=
  12*(bThirdIndex t)*(bThirdIndex t) + 49*(bThirdIndex t) + 40

def eMiddle (t : Nat) : CryptidBoundary.Cfg :=
  ⟨[],false,List.replicate (24*t+5) true ++
    (false :: List.replicate 10 true ++
      (false :: List.replicate 6 true)),5⟩

def bMiddle (t : Nat) : CryptidBoundary.Cfg :=
  DRegularSource.sourceSection ⟨64*t+27,1,5⟩

def pureReentry (t : Nat) : DRegular.L :=
  ⟨(512*t+245)/3,0,0⟩

/-- Original-source E-double step from the actual q=5,b=1 terminal section.
    Two explicit far-right blanks are added only through source_init_pad. -/
theorem e_double_source (t : Nat) :
    BB6.BoundaryPadding.ObsEq
      (CryptidBoundary.run (eCost t)
        (DRegularSource.sourceSection ⟨9*t+4,5,1⟩))
      (eMiddle t) := by
  let xs : List Bool :=
    List.replicate (9*t+2) true ++
      (CryptidBoundary.oppairs 5 ++ [true])
  have hstart :
      DRegularSource.sourceSection ⟨9*t+4,5,1⟩ =
        CryptidBoundary.init xs := by
    have hlen : 9*t+4-2 = 9*t+2 := by omega
    simp [DRegularSource.sourceSection, xs, hlen]
  have hpad :=
    BB6.BoundaryPadding.source_init_pad (eCost t) 2 xs
  have hinput :
      CryptidBoundary.init (xs ++ List.replicate 2 false) =
      CryptidBoundary.init
        (List.replicate (3*(3*t)+2) true ++
          false :: (CryptidBoundary.pairs 4 ++ [true,true,false,false])) := by
    have hlen : 3*(3*t)+2 = 9*t+2 := by omega
    simp [xs, hlen, CryptidBoundary.oppairs,
      CryptidBoundary.pairs, List.append_assoc]
  have hcost :
      eCost t = 12*(3*t)*(3*t)+49*(3*t)+64+4*3 := rfl
  have hraw :
      CryptidBoundary.run (eCost t)
        (CryptidBoundary.init (xs ++ List.replicate 2 false)) =
      eMiddle t := by
    rw [hinput, hcost]
    have hprefix : 8*(3*t)+5 = 24*t+5 := by omega
    simpa [eMiddle,hprefix] using (BB6.Agent35.full_E_double (3*t) 3 [])
  rw [hraw] at hpad
  rw [hstart]
  exact hpad

/-- The B source macro restores the E-double packet to a canonical
    (q=1,b=5) section. -/
theorem b_source (t : Nat) :
    CryptidBoundary.run (bCost t) (eMiddle t) = bMiddle t := by
  let K : Nat := 8*t+1
  let ys : List Bool :=
    List.replicate 10 true ++
      (false :: List.replicate 6 true)
  have hlen : 3*K+2 = 24*t+5 := by
    dsimp [K]
    omega
  have hfront :
      List.replicate (24*t+5) true =
        true :: true :: List.replicate (3*K) true := by
    rw [show 24*t+5 = 3*K+2 by omega,
      List.replicate_succ, List.replicate_succ]
  have hinput :
      eMiddle t =
        CryptidBoundary.init
          (List.replicate (3*K) true ++ false :: ys) := by
    simp [eMiddle, CryptidBoundary.init, K, ys, hlen, hfront,
      List.append_assoc]
  have hcost : bCost t = 12*K*K+49*K+40 := rfl
  have hrep :
      List.replicate (8*K+9) true ++ List.replicate 10 true =
        List.replicate (64*t+27) true := by
    rw [List.replicate_append_replicate]
    congr 1
    dsimp [K]
    omega
  have hfront :
      List.replicate (64*t+27) true =
        true :: true :: List.replicate (64*t+25) true := by
    rw [show 64*t+27 = (64*t+25)+1+1 by omega,
      List.replicate_succ, List.replicate_succ]
  have htarget :
      (⟨[],false,List.replicate (8*K+9) true ++ ys,5⟩ :
        CryptidBoundary.Cfg) = bMiddle t := by
    simp [bMiddle, DRegularSource.sourceSection,
      CryptidBoundary.init, CryptidBoundary.oppairs,
      ys, hrep, hfront, List.append_assoc]
  calc
    CryptidBoundary.run (bCost t) (eMiddle t) =
        CryptidBoundary.run (12*K*K+49*K+40)
          (CryptidBoundary.init
            (List.replicate (3*K) true ++ false :: ys)) := by
              rw [hinput, hcost]
    _ = ⟨[],false,List.replicate (8*K+9) true ++ ys,5⟩ :=
      CryptidBoundary.full_B K ys
    _ = bMiddle t := htarget

/-- The following B return, with t ≡ 2 (mod 3), removes the six-one packet
    and re-enters the canonical pure-unary regular language. -/
theorem b_reentry_source (t : Nat) (ht : t % 3 = 2) :
    CryptidBoundary.run (bThirdCost t) (bMiddle t) =
      DRegularSource.sourceSection (pureReentry t) := by
  let k : Nat := bThirdIndex t
  have hmod : (64*t+25) % 3 = 0 := by omega
  have hdiv : 3*k = 64*t+25 := by
    dsimp [k,bThirdIndex]
    omega
  have hnum : 3*(8*k+15) = 512*t+245 := by
    calc
      3*(8*k+15) = 8*(3*k)+45 := by omega
      _ = 8*(64*t+25)+45 := by rw [hdiv]
      _ = 512*t+245 := by omega
  have hstart : 64*t+27 = 3*k+2 := by omega
  have htarget : 8*k+15 = (512*t+245)/3 := by
    rw [← hnum]
    simp
  have hs :
      DRegularSource.sourceSection ⟨64*t+27,1,5⟩ =
      DRegularSource.sourceSection ⟨3*k+2,1,5⟩ := by
    rw [hstart]
  have htgt :
      DRegularSource.sourceSection ⟨8*k+15,0,0⟩ =
      DRegularSource.sourceSection (pureReentry t) := by
    simp [pureReentry, htarget]
  change CryptidBoundary.run (bThirdCost t)
    (DRegularSource.sourceSection ⟨64*t+27,1,5⟩) =
      DRegularSource.sourceSection (pureReentry t)
  rw [hs, htgt]
  simpa [bThirdCost,k,bThirdIndex] using
    (BB6.Agent31RegularB.b_one k 5)

/-- Three exact exceptional source returns: E-double, B restoration, B
    re-entry. This is a source theorem, not merely the arithmetic DExceptional
    transport interface. -/
theorem e_b_b_source (t : Nat) (ht : t % 3 = 2) :
    BB6.BoundaryPadding.ObsEq
      (CryptidBoundary.run (eCost t + bCost t + bThirdCost t)
        (DRegularSource.sourceSection ⟨9*t+4,5,1⟩))
      (DRegularSource.sourceSection (pureReentry t)) := by
  have hEB :
      BB6.BoundaryPadding.ObsEq
        (CryptidBoundary.run (eCost t + bCost t)
          (DRegularSource.sourceSection ⟨9*t+4,5,1⟩))
        (bMiddle t) :=
    BB6.BoundaryPadding.source_chain
      (eCost t) (bCost t)
      (DRegularSource.sourceSection ⟨9*t+4,5,1⟩)
      (eMiddle t) (bMiddle t)
      (e_double_source t)
      (by
        rw [b_source]
        exact BB6.Padding.cfgEq_refl _)
  have hB :
      BB6.BoundaryPadding.ObsEq
        (CryptidBoundary.run (bThirdCost t) (bMiddle t))
        (DRegularSource.sourceSection (pureReentry t)) := by
    rw [b_reentry_source t ht]
    exact BB6.Padding.cfgEq_refl _
  simpa [Nat.add_assoc] using
    (BB6.BoundaryPadding.source_chain
      (eCost t + bCost t) (bThirdCost t)
      (DRegularSource.sourceSection ⟨9*t+4,5,1⟩)
      (bMiddle t) (DRegularSource.sourceSection (pureReentry t))
      hEB hB)

/-- The authentic D3 blank root now reaches a new pure-unary F/0 section
    after the 1711 regular returns and three source-certified exceptions. -/
theorem i5_three_exception_rejoin :
    BB6.BoundaryPadding.ObsEq
      (CryptidBoundary.run
        (DRegular.accumulated 1711 DRegular.seed5 +
          eCost t5 + bCost t5 + bThirdCost t5)
        (sourceUnary 5))
      (DRegularSource.sourceSection (pureReentry t5)) := by
  have htail :
      BB6.BoundaryPadding.ObsEq
        (CryptidBoundary.run (eCost t5 + bCost t5 + bThirdCost t5)
          (DRegularSource.sourceSection DRegular.terminal5))
        (DRegularSource.sourceSection (pureReentry t5)) := by
    simpa [terminal5_shape] using (e_b_b_source t5 t5_mod3)
  exact BB6.BoundaryPadding.source_chain
    (DRegular.accumulated 1711 DRegular.seed5)
    (eCost t5 + bCost t5 + bThirdCost t5)
    (sourceUnary 5)
    (DRegularSource.sourceSection DRegular.terminal5)
    (DRegularSource.sourceSection (pureReentry t5))
    BB6.Agent35I5Root.i5_checkpoint htail

def tailCost : Nat := eCost t5 + bCost t5 + bThirdCost t5
def sourceElapsed : Nat := DRegular.accumulated 1711 DRegular.seed5 + tailCost
def horizon : Nat := 15 + sourceElapsed

private theorem obs_state {c d : CryptidBoundary.Cfg}
    (h : BB6.BoundaryPadding.ObsEq c d) : c.st = d.st := by
  change BB6.Padding.CfgEq
    (BB6.BoundaryPadding.represent c)
    (BB6.BoundaryPadding.represent d) at h
  exact h.2.2.2

/-- The pure-unary re-entry section and one more transition are both live. -/
theorem reentry_next_live :
    (CryptidBoundary.run (sourceElapsed+1) (sourceUnary 5)).st ≠ 6 := by
  have hObs := BB6.BoundaryPadding.source_congr 1 i5_three_exception_rejoin
  have hstate := obs_state hObs
  have hrun :
      CryptidBoundary.run (sourceElapsed+1) (sourceUnary 5) =
        CryptidBoundary.run 1
          (CryptidBoundary.run sourceElapsed (sourceUnary 5)) := by
    exact CryptidBoundary.run_add _ _ _
  rw [hrun]
  intro hbad
  have hright :
      (CryptidBoundary.run 1
        (DRegularSource.sourceSection (pureReentry t5))).st ≠ 6 := by
    simp [CryptidBoundary.run, CryptidBoundary.step,
      DRegularSource.sourceSection, CryptidBoundary.init, goL]
  exact hright (hstate.symm.trans hbad)

private theorem frozen_step (c : CryptidBoundary.Cfg) (h : c.st = 6) :
    CryptidBoundary.step c = c := by
  cases c with
  | mk l bit r st =>
    change st = 6 at h
    subst st
    cases bit <;> rfl

private theorem frozen_run (c : CryptidBoundary.Cfg) (n : Nat)
    (h : c.st = 6) : CryptidBoundary.run n c = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change CryptidBoundary.run n (CryptidBoundary.step c) = c
    rw [frozen_step c h]
    exact ih

private theorem no_frozen_before_live_endpoint
    (c : CryptidBoundary.Cfg) (N n : Nat) (hn : n ≤ N)
    (hlive : (CryptidBoundary.run N c).st ≠ 6) :
    (CryptidBoundary.run n c).st ≠ 6 := by
  intro hst
  have ht : n + (N-n) = N := by omega
  have hrun :
      CryptidBoundary.run N c =
        CryptidBoundary.run (N-n) (CryptidBoundary.run n c) := by
    calc
      _ = CryptidBoundary.run (n+(N-n)) c :=
        congrArg (fun m => CryptidBoundary.run m c) ht.symm
      _ = _ := CryptidBoundary.run_add _ _ _
  have hfinal : (CryptidBoundary.run N c).st = 6 := by
    rw [hrun, frozen_run (CryptidBoundary.run n c) (N-n) hst]
    exact hst
  exact hlive hfinal

theorem no_frozen_through_reentry (n : Nat)
    (hn : n ≤ sourceElapsed+1) :
    (CryptidBoundary.run n (sourceUnary 5)).st ≠ 6 :=
  no_frozen_before_live_endpoint (sourceUnary 5)
    (sourceElapsed+1) n hn reentry_next_live

/-- The literal parsed D3 blank-root machine cannot halt before the
    source-certified E/B/B re-entry to pure unary. -/
theorem parsed_D3_no_halt_through_reentry (n : Nat)
    (hn : n ≤ horizon) :
    ¬ BB6.Portfolio.haltsAt
      (BB6.Portfolio.parseRLE BB6.Portfolio.rleD3)
      (0 : BB6.Portfolio.State) n := by
  by_cases hlt : n < 15
  · intro hh
    have hh' : BB6.Portfolio.haltsAt BB6.Portfolio.D3
        (0 : BB6.Portfolio.State) n := by
      simpa only [BB6.Portfolio.parsed_D3_eq] using hh
    have hd0 := (BB6.Portfolio.D3_exact_halt_time n).mp hh'
    have hp := BB6.Portfolio.no_halt_before_prefix
      BB6.Portfolio.D0 (BB6.Portfolio.blank (1 : BB6.Portfolio.State))
      (BB6.Portfolio.F0Pure 5 (-3)) 15 n
      BB6.Portfolio.blank_root_B_to_I5 hd0
    omega
  · have hge : 15 ≤ n := by omega
    let k := n-15
    have hk : k ≤ sourceElapsed := by
      dsimp [k, horizon, sourceElapsed, tailCost] at *
      omega
    have htime : 15+k=n := by omega
    intro hh
    have hh' : BB6.Portfolio.haltsAt
        (BB6.Portfolio.parseRLE BB6.Portfolio.rleD3)
        (0 : BB6.Portfolio.State) (15+k) := by
      simpa [htime] using hh
    have hfrozen :=
      (BB6.Agent19.Physical.parsed_D3_exact_source_time k).mp hh'
    exact no_frozen_through_reentry (k+1) (by omega) hfrozen.2

theorem horizon_ge_10pow1458 : 10^1458 ≤ horizon := by
  have hOld := BB6.Agent35I5Root.horizon_ge_10pow1458
  have hMono : BB6.Agent35I5Root.horizon ≤ horizon := by
    dsimp [BB6.Agent35I5Root.horizon, horizon, sourceElapsed, tailCost]
    omega
  exact Nat.le_trans hOld hMono

#print axioms terminal5_shape
#print axioms t5_mod3
#print axioms e_double_source
#print axioms b_source
#print axioms b_reentry_source
#print axioms e_b_b_source
#print axioms i5_three_exception_rejoin
#print axioms parsed_D3_no_halt_through_reentry
#print axioms horizon_ge_10pow1458

end BB6.Agent35I5Exceptional
