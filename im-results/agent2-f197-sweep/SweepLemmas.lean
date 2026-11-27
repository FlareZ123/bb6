import Macro
namespace F197

/-! Exact composed prefix lemmas. Compile beside Agent31's Macro.lean.
No new semantics. These proofs are candidate source pending Lean execution. -/

theorem collapse_D110 (l r : Tape) :
    run 13 (d (pre [false] l) (pre [true,true,false] r)) =
    some (d (pre [false,true,false,true] l) r) := rfl

theorem collapse_D1011 (l r : Tape) :
    run 10 (d l (pre [true,false,true,true] r)) =
    some (d (pre [false,true,false,true] l) r) := rfl

theorem collapse_D1010 (l r : Tape) :
    run 12 (d l (pre [true,false,true,false] r)) =
    some (other B (cons true l) (pre [false,false,true] r)) := rfl

/-- Here the full B right stack is 00W, shortened right stack 0W. -/
theorem repair_B3_23 (l w : Tape) :
    run 23 (other B (pre [true,true,true,false,false,true] l)
      (pre [false,false] w)) =
    some (d (pre [false,true,false,true] l) (pre [false,false,false,true] w)) := rfl

/-- The subsequent forced D00 brings the next nonblank B return. -/
theorem repair_B3_29 (l w : Tape) :
    run 29 (other B (pre [true,true,true,false,false,true] l)
      (pre [false,false] w)) =
    some (other B (pre [true,false,true] l)
      (pre [false,false,true,false,true] w)) := rfl

#print axioms collapse_D110
#print axioms collapse_D1011
#print axioms collapse_D1010
#print axioms repair_B3_23
#print axioms repair_B3_29
end F197
