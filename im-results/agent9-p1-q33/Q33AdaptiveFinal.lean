import Q33Adaptive
import GenericCritical41K

namespace BB6.Agent9Q33AdaptiveFinal
open BB6.Agent9Adaptive

/-- All-time original P1 blank-root critical gateway exclusion for every
    exponent n = 530 + 2^44*r, r natural. -/
theorem blank_no_critical_530_plus_2pow44 (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(33+P*r)+2)-2*(16*(33+P*r)+2)-10) := by
  exact BB6.Agent9Generic41K.critical_unreachable_of_shadow41K
    (33+P*r) (by omega) (decode r nodes0) (decode r nodes1)
    (root0 r) (root1 r)
    (closed0 r) (closed1 r)
    (fun m z h => (bounds0 r m z h).1)
    (fun m z h => (bounds1 r m z h).1)
    (fun m z h => (bounds0 r m z h).2)
    (fun m z h => (bounds1 r m z h).2)

#print axioms blank_no_critical_530_plus_2pow44
end BB6.Agent9Q33AdaptiveFinal
