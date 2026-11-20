# General q4-tail to marker-zero S1 dispatcher reparameterization

**Status:** intermediate source-level mathematical result; the existing source modules and the proposed composition have not been compiled together.

## Main observation

The A=2 terminal composition in A2TerminalResetComposition.lean is not intrinsically restricted to A=2. For every outer width parameter A >= 2, the authentic q4Tail adapter output can be reparameterized as an S1 configuration with a larger encoder width. When the q4 input length L is even, its outer index is divisible by three, so the existing complete 24-class sectionResult_run_complete dispatcher ends at marker zero and the existing terminal SectionBits bridge applies.

This bypasses the optional q4Tail-to-next-q4Tail recurrence entirely. In particular, it does not require applying the 100 guard a second time after the next residual has become 111111....

## Parameters

For L >= 4, A >= 2, and z >= 1, put

~~~text
w := A + L + 1
q := firstQ4P1Value L A
   = 2^(A-1) * (2^(L+2)-1) - 1
M := firstQ4P1M L A
   = 2^A * (2^(L+2)-1)
W := A + L + 2
N := M - 3 = 2^W - 2^A - 3
K := 2^z + z + 3
m := 3*2^z + 3*z + 7
n := 2^(2^z-1)
H := m + 2 + 3*n
~~~

The root has L = tm63Length1 = 76, which is even, and A = rootMarker1A >= 2. Thus its terminal encoder width is W = rootMarker1A + 78, not the special A=2 width 80.

## BinDec identities

The source encoder recurrence gives, for A >= 1,

~~~text
binDec (A+L+1) (firstQ4P1Value L A)
  = d0pow (A-1) ++ d1 ++ d0pow (L+1).
~~~

For A >= 2, define N = M-3. Then

~~~text
N = 4 * firstQ4P1Value L (A-1) + 1,
~~~

so two applications of binDec_odd / binDec_even, followed by the preceding identity at A-1, give

~~~text
binDec W N
  = d0 ++ d1 ++ d0pow (A-2) ++ d1 ++ d0pow (L+1).
~~~

The width is correct: the right-hand side has A+L+2 = W three-bit blocks.

## Exact q4Tail residual identity

Let

~~~text
tail0 := replicate 4 true ++ binDec w q ++ lh
tail  := q4TailS0Tail w q
       = [true,false,false,true,true,true] ++ tail0.drop 6
ell   := p2ResidualLeft m tail
~~~

The first identity above implies

~~~text
tail0.drop 6
  = [true] ++ d0pow (A-2) ++ d1 ++ d0pow (L+1) ++ lh.
~~~

Using m+2 = 3*K and the fixed prefix
[false,true,false,false] ++ [true,false,false,true,true,true] ++ [true],
the residual simplifies exactly to

~~~text
ell
  = d1pow K ++ markerWord 0 ++ d0 ++
      binDec W N ++ lh.
~~~

This is the general form of Agent 24's A=2 identity

~~~text
p2ResidualLeft m (q4TailS0Tail 79 (2^79-3))
  = d1pow K ++ markerWord 0 ++ d0 ++
      binDec 80 (2^80-7) ++ lh.
~~~

## S1 reparameterization after the q4Tail adapter

The existing generic theorem q4TailS0Frame_eq_s0Config identifies the q4Tail frame with

~~~text
s0Config ell (n-1) (2^(n-1)-1) 0 H.
~~~

The existing all-ones and carry-prefix identities give

~~~text
binDec (n-1) (2^(n-1)-1) = d0pow (n-1)
binDec (n-1+K) (2^(n-1)-1)
  = d0pow (n-1) ++ d1pow K.
~~~

Consequently the exact q4Tail frame is

~~~text
s1Config W N 0 (n-1+K) (2^(n-1)-1) 0 H.
~~~

No q4Tail recurrence is needed. The existing s1Config_counted_drain then moves the all-ones binary counter to the right counter, producing

~~~text
s1Config W N 0 (n-1+K) 0 (2^(n-1)-1) H.
~~~

The existing complete source dispatcher applies to this state, since W >= 4, N < 2^W, and n-1+K > 0.

## Why the final marker is zero for even L

~~~text
N = 2^A * (2^(L+2)-1) - 3.
~~~

If L is even, L+2 is even and 2^(L+2) is 1 modulo 3. Hence 3 divides M and therefore 3 divides N. The marker formula

~~~text
sectionResult_marker : (sectionResult N 0 a b).marker = (2*N) % 3
~~~

therefore returns marker zero. The dispatcher endpoint is exactly the marker-zero S1 configuration consumed by s0_reset_sectionBits; the existing arbitrary-exterior terminal macro then yields a halting run.

## Authentic-root composition target

The following source-level ingredients are composed by the new drafts:

- tm63_blank_reaches_second_q4_tail in TM63RootQ4Tail.lean;
- tm63_root_second_q4Tail_eq_q4TailS0Frame and q4TailS0Frame_eq_s0Config in P2RootS0Identity.lean;
- firstQ4P1M, firstQ4P1Width, and firstQ4P1Value in FirstQ4P1Arithmetic.lean;
- tm63Length1_even in TM63Length1Parity.lean;
- s1Config_counted_drain, sectionResult_run_complete, and s0_reset_sectionBits in the existing counted-drain, complete-dispatcher, and terminal-encoder modules.

The implementation drafts in this directory are GeneralQ4TailArithmetic.lean, GeneralQ4TailS1Reparam.lean, GeneralQ4TailS1Config.lean, and GeneralQ4TailTerminalComposition.lean. Agent 42 added the canonical authentic-root wrapper at im-results/agent42-q4-s0-drain/TM63GeneralQ4TerminalComposition.lean; it states tm63_blank_halts and tm63_blank_attainable after composing tm63_blank_reaches_second_q4_tail, the root shift, and q4TerminalFrame_to_terminalConfig. These are source statements only: the authentic root prefix and complete 24-class dispatcher remain uncompiled/unaccepted, so neither theorem is an established halting proof.

## Evidence status and next action

The displayed identities are algebraic consequences of the encoder definitions. The saved check_general_q4tail_reparam.py script simulates the original TM2 transition table on 12 small triples (L in {4,6}, A in {2,3,4}, z in {1,2}); all pass exact S0/S1 tape equality at time zero and the exact counted-drain endpoint. This is computational sanity evidence only; it does not simulate or prove the full SectionResult dispatcher.

No new Lean file in this route has been compiled. The route still depends on acceptance of both the authentic root prefix (including the first-cycle M1 source) and the complete 24-class dispatcher (including M0 and M2 zero-row source families). The last recorded middle34 CI failure predates the current M1EvenState1Sweep.lean repair adding hne3; it is stale, but the repaired root prefix has not yet been accepted by a fresh build. The local container shell and Python tools return ClientError before commands run, so no local Lean preflight was possible. Do not dispatch CI as a substitute for required local preflight. Do not promote this note to results/ or claim a BB(6) lower-bound proof until the general theorem and its complete transitive import closure compile and pass the repository's axiom audit.
