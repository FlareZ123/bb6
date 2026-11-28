import F321BackwardBarrier
import Lean.Elab.Tactic.Omega

namespace BB6.Agent31F321Density

/-- Concrete source-faithful mixed terminal suffix.  The anchor is not claimed
    reachable from the blank root; this theorem isolates an exact future
    reachability target exposed by the terminal-word equation. -/
theorem mixed_suffix_22high_far :
    CounterReach 19173934 1 23 9586982 9586981 := by
  have h0 : CounterReach 19173934 1 0 19173934 1 := CounterReach.nil
  have h1 : CounterReach 19173934 1 1 19173931 5 :=
    CounterReach.step h0 (CounterMove.high 19173934 1 (by omega))
  have h2 : CounterReach 19173934 1 2 19173924 13 :=
    CounterReach.step h1 (CounterMove.high 19173931 5 (by omega))
  have h3 : CounterReach 19173934 1 3 19173909 29 :=
    CounterReach.step h2 (CounterMove.high 19173924 13 (by omega))
  have h4 : CounterReach 19173934 1 4 19173878 61 :=
    CounterReach.step h3 (CounterMove.high 19173909 29 (by omega))
  have h5 : CounterReach 19173934 1 5 19173815 125 :=
    CounterReach.step h4 (CounterMove.high 19173878 61 (by omega))
  have h6 : CounterReach 19173934 1 6 19173688 253 :=
    CounterReach.step h5 (CounterMove.high 19173815 125 (by omega))
  have h7 : CounterReach 19173934 1 7 19173433 509 :=
    CounterReach.step h6 (CounterMove.high 19173688 253 (by omega))
  have h8 : CounterReach 19173934 1 8 19172922 1021 :=
    CounterReach.step h7 (CounterMove.high 19173433 509 (by omega))
  have h9 : CounterReach 19173934 1 9 19171899 2045 :=
    CounterReach.step h8 (CounterMove.high 19172922 1021 (by omega))
  have h10 : CounterReach 19173934 1 10 19169852 4093 :=
    CounterReach.step h9 (CounterMove.high 19171899 2045 (by omega))
  have h11 : CounterReach 19173934 1 11 19165757 8189 :=
    CounterReach.step h10 (CounterMove.high 19169852 4093 (by omega))
  have h12 : CounterReach 19173934 1 12 19157566 16381 :=
    CounterReach.step h11 (CounterMove.high 19165757 8189 (by omega))
  have h13 : CounterReach 19173934 1 13 19141183 32765 :=
    CounterReach.step h12 (CounterMove.high 19157566 16381 (by omega))
  have h14 : CounterReach 19173934 1 14 19108416 65533 :=
    CounterReach.step h13 (CounterMove.high 19141183 32765 (by omega))
  have h15 : CounterReach 19173934 1 15 19042881 131069 :=
    CounterReach.step h14 (CounterMove.high 19108416 65533 (by omega))
  have h16 : CounterReach 19173934 1 16 18911810 262141 :=
    CounterReach.step h15 (CounterMove.high 19042881 131069 (by omega))
  have h17 : CounterReach 19173934 1 17 18649667 524285 :=
    CounterReach.step h16 (CounterMove.high 18911810 262141 (by omega))
  have h18 : CounterReach 19173934 1 18 18125380 1048573 :=
    CounterReach.step h17 (CounterMove.high 18649667 524285 (by omega))
  have h19 : CounterReach 19173934 1 19 17076805 2097149 :=
    CounterReach.step h18 (CounterMove.high 18125380 1048573 (by omega))
  have h20 : CounterReach 19173934 1 20 14979654 4194301 :=
    CounterReach.step h19 (CounterMove.high 17076805 2097149 (by omega))
  have h21 : CounterReach 19173934 1 21 10785351 8388605 :=
    CounterReach.step h20 (CounterMove.high 14979654 4194301 (by omega))
  have h22 : CounterReach 19173934 1 22 2396744 16777213 :=
    CounterReach.step h21 (CounterMove.high 10785351 8388605 (by omega))
  exact CounterReach.step h22
    (CounterMove.far 2396744 16777213 (by omega) (by omega))

#print axioms mixed_suffix_22high_far
end BB6.Agent31F321Density
