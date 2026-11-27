# Candidate F197 three-parameter carry theorem (two independent P counters)

> **No longer a conjecture:** this three-parameter identity is a kernel-certified corollary of [the stronger arbitrary mixed P/Q theorem](ATFreeMonoidTheorem.md), `F197.fmFullFamilyClosed` in [ATFreeMonoid.lean](ATFreeMonoid.lean), CI [46083890068](https://github.com/FlareZ123/bb6/actions/runs/46083890068), with exact +2 finite-bit growth in [ATFreeMonoidGrowth.lean](ATFreeMonoidGrowth.lean), CI [46083987937](https://github.com/FlareZ123/bb6/actions/runs/46083987937). Choose W=P^n Q P^m (P=AAT, Q=TAT). The block substitution is `F(W)=P^n AAAT P^m`, and the closed cost is `156+68(n+m+q)+14t`. The exploratory 1,600-case sweep below predates the complete source proof; its uncertainty statements are retained as historical methodology, **not** current theorem status.


**Status: new experimentally validated exact-reset family, not yet Lean certified.** One 1600-case reproducible randomized macro-simulation sweep found no counterexample; no unbounded n,m proof should be claimed until the generic carried scanner and two counter decoders are composed. This is an extension of the [full leading-counter derivation](ATFullFamily.md), whose own Lean induction is still undergoing resource-bounded compilation.

## Candidate theorem

Use nearest-first run symbols `A=10`, `T=1100`, `P=AAT`, `e=1`, and a nonempty A/T data list `c₀,...,c_q` with `q≥0`. Set `Z=c₀(Tc₁)...(Tc_q)`, `Φ=A H(c₀)...H(c_q)`, `H(A)=AT`, `H(T)=AAT`, and `t=#{c_i=T}`. For any `n,m≥0` and suffix X whose first physical bit is 1, the proposed *literal source* identity is:

```
B(P^n TAT P^m Z AA X, e)
    ->^(156 + 68(n+m+q) + 14t)
B(P^n AAAT P^m Φ X, e).
```

The two counters have different locations and **their order is critical**: the internal counter P^m remains to the right of the newly generated AAAT; it must **not** be moved to the front. The output encoded left prefix is exactly two bits longer than the input.

For m=0 this specializes to the already derived `P^n TAT ZAA -> P^n AAAT Φ` family; for n=m=0 it specializes to the fully Lean-certified theorem `atp_family`.

## Structural explanation and missing proof step

1. Consume n leading P packets: `B(P^n TAT...,e) ->^(36n) B(TAT...,Q_n)`, where Q_0=e, Q_{n+1}=u s^n d, u=(4,3), s=(5,3), d=(2,0).
2. TAT prefix transport: `B(TAT P^m ZAA X,Q_n) ->^46 B(P^m ZAA X,u C Q_n)`.
3. Consume m **internal** P packets: `B(P^m ZAA X,u C Q_n) ->^(36m) B(ZAA X,u s^m C Q_n)`.
4. **Open generalization:** the unbounded paired scanner/decoder (known when the stack is u C R) is to be proved uniformly for an *arbitrary* right-stack R: `B(ZAA X,u R) ->^(S+K) B(J Φ X,A R)`, with `S=39+8(q+1)+10t`, `K=-28+60(q+1)+4t`. The two newly discovered terminal lemmas `atc_terminal_A_u`, `atc_terminal_T_u` in `ATCarryCore.lean` are candidate source-certified 47/57-step bases for this stronger scanner. Generalized 32/36-step final junction rules must allow right R in place of the hard-coded C R, preserving both marker-stacks.
5. Decode m internal `s` packets in `B(J Φ X,A s^m C Q_n)` for exactly 32m steps: result `B(J P^m Φ X,A C Q_n)`. Then outer Q_n decoder needs 31+32n steps, yielding `B(P^n AAAT P^m Φ X,e)`.

Total:
`36n + 46 + 36m + (S+K) +32m +(31+32n) = 156+68(n+m+q)+14t`.
The input finite prefix has bits `8n+10+8m+6(q+1)+2t`; the output has `8n+12+8m+6(q+1)+2t`, hence +2.

## Reproducible computational observations

A JS BigInt exact F197 grouped-macro interpreter (same 13-entry machine in `im-results/agent31-f197-macro/Macro.lean`) tested 1600 seeded pseudorandom examples:

- Initial LCG seed `0xcbed1138`; update `seed = (1664525*seed + 1013904223) mod 2^32`.
- n,m independently reduced mod 7; q mod 6; q+1 A/T symbols from low random bits; suffix is 0–6 random symbols over `{A,T,J,C,U}` followed by terminal `e`.
- Every test reached the predicted *first return* to `B(...,e)` with the exact target bitword and exact primitive transition cost. 1600/1600 passed, seed final value `2878782212`.
- An earlier **incorrect guess** `P^m AAAT Φ` for the internal counter was falsified at n=0,m=1,q=0,c0=A: actual `AAAT P Φ` in 224 steps, not `P AAAT Φ`. The corrected theorem above survived 1600 cases. This counterexample matters: counter-stack ordering cannot be commuted.

These observations do not substitute for a proof of stage 4 or the unbounded two-counter composition. The next high-value action is a source-guarded Lean theorem for the **C-free arbitrary-u scanner**, then independent induction on m and n. This may substantially expand the safe reset grammar toward unresolved F197 nonhalting, but the full blank orbit remains outside current proven closure.
