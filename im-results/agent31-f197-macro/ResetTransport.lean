import Macro

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace F197

/-- Consume one P=AAT block when the shortened right word begins 0·u.
    The old u is incremented to s and a new u is prepended. -/
theorem reset_P_consume_us (l r : Tape) :
    run 36
      (other B
        (pre [true, false, true, false, true, true, false, false] l)
        (pre [false, true, true, true, true, false, false, false] r)) =
    some
      (other B l
        (pre [false, true, true, true, true, false, false, false,
              true, true, true, true, true, false, false, false] r)) := rfl

/-- First P-consumption from terminal reset right e. -/
theorem reset_P_consume_e (l : Tape) :
    run 36
      (other B
        (pre [true, false, true, false, true, true, false, false] l)
        (pre [false, true] blank)) =
    some
      (other B l
        (pre [false, true, true, true, true, false, false, false,
              true, true] blank)) := rfl

/-- One decoder step: J on the left and x·s on the right transfer one P
    behind J while deleting the s. -/
theorem reset_decoder_s (l r : Tape) :
    run 32
      (other B
        (pre [true, false, false] l)
        (pre [false, true, false, true, true, true, true, true,
              false, false, false] r)) =
    some
      (other B
        (pre [true, false, false, true, false, true, false, true, true,
              false, false] l)
        (pre [false, true, false] r)) := rfl

/-- Terminal decoder step x·d -> e, replacing leading J by P. -/
theorem reset_decoder_d (l : Tape) :
    run 27
      (other B
        (pre [true, false, false] l)
        (pre [false, true, false, true, true] blank)) =
    some
      (other B
        (pre [true, false, true, false, true, true, false, false] l)
        (pre [false, true] blank)) := rfl

#print axioms reset_P_consume_us
#print axioms reset_P_consume_e
#print axioms reset_decoder_s
#print axioms reset_decoder_d

end F197
