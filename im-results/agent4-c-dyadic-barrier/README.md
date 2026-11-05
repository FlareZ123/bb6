# Machine C: dyadic immediate-halting saturation

**Agent 4, 2026-11-05. Intermediate theorem; BB(6) and Machine C remain undecided.**

The source-connected Machine C section map `BB6.Agent46.secNext` has a previously proved complete stopping equation in `im-results/agent1-c-unified-gateway/UnifiedGateway.lean`. For any odd first counter `a=2u+1` and any naturals `e,w`, the new Lean theorem `BB6CDyadicBarrier.every_odd_dyadic_class_has_immediate_halt` constructs a right counter `K` such that

```lean
K % (2^e) = w % (2^e) ∧
BB6.Agent46.secNext (2*u+1,K) = none
```

In particular, for **every** power-of-two modulus, there is a synthetic source input `(5,K)` in the same two-counter residue class as the authentic blank section seed `(5,1)` that halts **immediately**. This is a theorem about artificial inputs; it does not assert that the real blank orbit reaches them.

## Construction

Let `G(0)=0`, `G(e+1)=4G(e)+1`, `C=u+w+4`, `m=C*G(e)+(C+e+1)*4^e`, and `K=4^(m+1)*(u+2)-(u+3m+4)`. The proof establishes

```text
3*G(e)+1 = 4^e
3*m+C = (4*C+3e+3)*4^e
K+u+3*m+4 = 4^(m+1)*(u+2)
```

together with `m≥C+e+1`, `K≥w`, and `2^e ∣ K-w`. The last equation is the imported, pre-existing exact Machine C source stopping criterion for odd first counters.

## Implications and provenance

A pure dyadic two-counter residue abstraction cannot refute Machine C halting: its initial abstract state already admits an immediately stopping synthetic representative. Root-conditioned modular exclusions remain useful, and abstractions carrying other information can escape this limitation.

Lean source: [CDyadicImmediateHalts.lean](CDyadicImmediateHalts.lean). Its proof compiled locally in Lean 4.36.0-rc2 against a temporary declaration-only interface for the previously source-checked `source_section_halts_iff_one_equation`; **source-native CI remains separately required**. The interface was not committed, and this dossier does not claim a new blank-origin halt or a novel BB(6) bound. Keep intermediate pending independent mathematical novelty and source audit.


## Extension: mod 3 does not remove the blank-cylinder obstruction

The supplementary [CDyadicMod6.lean](CDyadicMod6.lean) proves for **all** `e:Nat` the stronger statement
```lean
∃ K : Nat, K % (3*(2^e)) = 1 % (3*(2^e)) ∧
  BB6.Agent46.secNext (5,K) = none
```
using the previous `2^e` construction, the existing *source-verified* `source_positive_stopping_right_mod3` theorem (`K%3=1` for any positive-left source stop), and elementary coprimality `Nat.Coprime 3 (2^e)`. Thus adjoining a *single factor of three* to an arbitrarily fine dyadic residue quotient still cannot decide actual blank-root nonhalting by classifying its initial cylinder. The claim is specifically for `3*2^e`; higher powers of 3 or arbitrary moduli are **not** covered by this theorem. The real blank origin is not asserted to halt.

Both modules have been checked locally against precisely matching, pre-existing theorem signatures, without `sorryAx`. A manual source CI run of both modules and the complete unchanged C source import chain is queued as [41970586436](https://github.com/FlareZ123/bb6/actions/runs/41970586436); an earlier run checking only the first module is [41970212167](https://github.com/FlareZ123/bb6/actions/runs/41970212167). Update this dossier if source CI succeeds or finds a mismatch.
