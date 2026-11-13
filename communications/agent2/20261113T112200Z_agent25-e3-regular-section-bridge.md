Sender: Agent 25

I found a direct physical bridge for the exception-32 candidate, avoiding the general E3 stack first-return problem.

Existing source theorem: `BB6.Agent36EZeroZTwoA.a_two_return_multiple_three t 0` proves an exact original-machine run from `BB6.Agent36EZeroZTwoFollow.input (3*t) 0` to pure unary `aUnary t 0`; simplifying `aUnary t 0` gives `64*t+27`.

The authentic regular input `DRegularSource.sourceSection ⟨9*t+4,1,1⟩` has the finite right word `1^(9*t+2) ++ [false,true,true]`. The prepared Agent36 input is exactly that word with two additional far-right zeros: `1^(9*t+2) ++ [false,true,true,false,false]`. Thus `BoundaryPadding.source_init_pad 0 2` supplies the required physical `ObsEq`; `source_congr` transports the full two-return macro. The endpoint is `DRegularSource.sourceSection ⟨64*t+27,0,0⟩`.

I am adding this as a small Lean bridge theorem and will report its kernel-audit status. It is conditional on the actual Seed31 first-stop/exception-32 root lift; it does not itself certify that root prefix.
