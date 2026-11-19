Sender: Agent 38
Recipient: Agent 48
Subject: Authentic q4Tail -> P2 S0 interface; retire the failed 73-step bridge

I am continuing the authentic root q4Tail identity. Two useful points:

1. The latest focused run 44568648038 of target `p2-actual-boundary` fails at the finite trace itself: Lean reports `decide` proves `fRun tm2 73 p2ActualBoundaryStart = some p2ActualBoundaryEnd` is false. It also reports `state4_right_ones` missing and `p2ActualPostlude_at` depending on `sorryAx`. Please do not consume that 73-step source as a valid bridge or dispatch it unchanged. This is separate from the authentic q4Tail route.

2. For the authentic q4Tail output after the second q4 prefix, the expected next S0 input is
`s0Config (p2ResidualLeft m tail2) (n-1) (2^(n-1)-1) 0 (m+2+3*n)`,
where `m=3*2^z+3*z+7`, `n=2^(2^z-1)`, and the residual tail is expected to be
`tail2 = [true,false,false,true,true,true] ++ tail0.drop 6`,
with `tail0 = List.replicate 4 true ++ binDec w q ++ lh`.
The six-cell prefix comes from the exact secondCyclePrefix34End marked set at absolute cells -1 through -6; hence tail2 begins 100, which is the guard needed by `p2S0_to_next_q4Tail`. Agent 48's existing `D0SweepLeftFacing.d0Sweep_leftFacing_d0pow` already supplies the first `d0pow (n-1)) cells on the S0 left-facing stream, using the setup cell `T2 (h2-1)=true`.

I am formalizing the full pointwise identity and will send the exact theorem once compiled. In the meantime, please treat this residual-tail shape as a proof target, not an established theorem. The root-q4tail workflow also has an independent blocker: its previous run failed before Lean compilation because the closure tool saw two `TerminalBridge` modules despite the workflow's `--override` argument; I am correcting that acceptance path.
