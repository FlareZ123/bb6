import Raw56E1RCMixed
import Raw56RC0LAAll
import Raw56RC0LBAll
import Raw56RC0LEAll
import Raw56RC0LFAll
import Raw56RC0RAAll
import Raw56RC0RBAll
import Raw56RC0RDAll
import Raw56RC0REAll
import Raw56RC0RFAll
import Raw56RC1LAAll
import Raw56RC1LBAll
import Raw56RC1LCAll
import Raw56RC1LEAll
import Raw56RC1LFAll
import Raw56RC1RAAll
import Raw56RC1RBAll
import Raw56RCRDAll
import Raw56RC1REAll
import Raw56RC1RFAll

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent1Raw56E1RC
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial
open BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent31FourHoleRoster


theorem eq0LA : BB6.Agent1Raw56.RC0LA.p = c0LA := sameTable_sound (by decide)
theorem eq0LB : BB6.Agent1Raw56.RC0LB.p = c0LB := sameTable_sound (by decide)
theorem eq0LE : BB6.Agent1Raw56.RC0LE.p = c0LE := sameTable_sound (by decide)
theorem eq0LF : BB6.Agent1Raw56.RC0LF.p = c0LF := sameTable_sound (by decide)
theorem eq0RA : BB6.Agent1Raw56.RC0RA.p = c0RA := sameTable_sound (by decide)
theorem eq0RB : BB6.Agent1Raw56.RC0RB.p = c0RB := sameTable_sound (by decide)
theorem eq0RD : BB6.Agent1Raw56.RC0RD.p = c0RD := sameTable_sound (by decide)
theorem eq0RE : BB6.Agent1Raw56.RC0RE.p = c0RE := sameTable_sound (by decide)
theorem eq0RF : BB6.Agent1Raw56.RC0RF.p = c0RF := sameTable_sound (by decide)
theorem eq1LA : BB6.Agent1Raw56.RC1LA.p = c1LA := sameTable_sound (by decide)
theorem eq1LB : BB6.Agent1Raw56.RC1LB.p = c1LB := sameTable_sound (by decide)
theorem eq1LC : BB6.Agent1Raw56.RC1LC.p = c1LC := sameTable_sound (by decide)
theorem eq1LE : BB6.Agent1Raw56.RC1LE.p = c1LE := sameTable_sound (by decide)
theorem eq1LF : BB6.Agent1Raw56.RC1LF.p = c1LF := sameTable_sound (by decide)
theorem eq1RA : BB6.Agent1Raw56.RC1RA.p = c1RA := sameTable_sound (by decide)
theorem eq1RB : BB6.Agent1Raw56.RC1RB.p = c1RB := sameTable_sound (by decide)
theorem eq1RD : BB6.Agent1Raw56.RCRD.p = c1RD := sameTable_sound (by decide)
theorem eq1RE : BB6.Agent1Raw56.RC1RE.p = c1RE := sameTable_sound (by decide)
theorem eq1RF : BB6.Agent1Raw56.RC1RF.p = c1RF := sameTable_sound (by decide)

theorem branchCovers : BranchCovers where
  h0LA m hm := BB6.Agent1Raw56.RC0LA.all_quotient m (eq0LA.symm ▸ hm)
  h0LB m hm := BB6.Agent1Raw56.RC0LB.all_quotient m (eq0LB.symm ▸ hm)
  h0LE m hm := BB6.Agent1Raw56.RC0LE.all_quotient m (eq0LE.symm ▸ hm)
  h0LF m hm := BB6.Agent1Raw56.RC0LF.all_quotient m (eq0LF.symm ▸ hm)
  h0RA m hm := BB6.Agent1Raw56.RC0RA.all_quotient m (eq0RA.symm ▸ hm)
  h0RB m hm := BB6.Agent1Raw56.RC0RB.all_quotient m (eq0RB.symm ▸ hm)
  h0RD m hm := BB6.Agent1Raw56.RC0RD.all_quotient m (eq0RD.symm ▸ hm)
  h0RE m hm := BB6.Agent1Raw56.RC0RE.all_quotient m (eq0RE.symm ▸ hm)
  h0RF m hm := BB6.Agent1Raw56.RC0RF.all_quotient m (eq0RF.symm ▸ hm)
  h1LA m hm := BB6.Agent1Raw56.RC1LA.all_quotient m (eq1LA.symm ▸ hm)
  h1LB m hm := BB6.Agent1Raw56.RC1LB.all_quotient m (eq1LB.symm ▸ hm)
  h1LC m hm := BB6.Agent1Raw56.RC1LC.all_quotient m (eq1LC.symm ▸ hm)
  h1LE m hm := BB6.Agent1Raw56.RC1LE.all_quotient m (eq1LE.symm ▸ hm)
  h1LF m hm := BB6.Agent1Raw56.RC1LF.all_quotient m (eq1LF.symm ▸ hm)
  h1RA m hm := BB6.Agent1Raw56.RC1RA.all_quotient m (eq1RA.symm ▸ hm)
  h1RB m hm := BB6.Agent1Raw56.RC1RB.all_quotient m (eq1RB.symm ▸ hm)
  h1RD m hm := BB6.Agent1Raw56.RCRD.all_quotient m (eq1RD.symm ▸ hm)
  h1RE m hm := BB6.Agent1Raw56.RC1RE.all_quotient m (eq1RE.symm ▸ hm)
  h1RF m hm := BB6.Agent1Raw56.RC1RF.all_quotient m (eq1RF.symm ▸ hm)

theorem all_quotient : ∀ m, TNFQuotientCompatible p m → WeightedBound 10000 m :=
  all_quotient_from_branches branchCovers

theorem all : ∀ m, compatible p m → WeightedBound 10000 m :=
  all_from_branches branchCovers

#print axioms all_quotient
#print axioms all
end BB6.Agent1Raw56E1RC

namespace BB6.Agent1Raw56Root
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial
open BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent31FourHoleRoster

theorem sound18RC_closed :
    ∀ m, TNFQuotientCompatible parent m →
      WeightedBound 10000 m ∨ ∃ e ∈ remaining18RC, TNFQuotientCompatible e.2 m :=
  sound18RC BB6.Agent1Raw56E1RC.all_quotient

#print axioms sound18RC_closed
end BB6.Agent1Raw56Root
