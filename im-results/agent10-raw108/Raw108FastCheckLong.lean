import Raw108FastCheck
import Raw108LongAudit

namespace BB6.Agent10Raw108FastCheck
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6Coverage.Agent10ZipAudit

theorem longCheck_eq (B : Nat) (p : PartialMachine) (t : Audit) :
    fastCheck BB6.Agent10Raw108Long.longRead B p t = BB6.Agent10Raw108FastAudit.zipCheck B p t :=
  (fastCheck_eq _ BB6.Agent10Raw108Long.longRead_eq B p t).trans
    (BB6.Agent10Raw108FastAudit.check_eq B p t).symm

theorem longQuery_eq (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) :
    fastQuery BB6.Agent10Raw108Long.longRead B p n s = BB6.Agent10Raw108FastAudit.zipQueryOK B p n s :=
  (fastQuery_eq _ BB6.Agent10Raw108Long.longRead_eq B p n s).trans
    (BB6.Agent10Raw108FastAudit.query_eq B p n s).symm

#print axioms longCheck_eq
#print axioms longQuery_eq
end BB6.Agent10Raw108FastCheck
