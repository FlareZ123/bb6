# Third neutral ninefold digit for the original #623 ternary drain

**Mathematical status: intermediate.** This dossier extends the source-certified binary neutral-digit family of Agent 8 with a genuinely different residue-eight branch. It proves an exact all-input ternary renormalization, a three-letter full-output family, and a universal two-return family in the original Cryptids accelerated map. None of these synthetic starting states has been shown reachable from the authentic blank root `D(0,7)`. The six-state Busy Beaver function remains undetermined.

## Exact additional ninefold identity

Write `B(a,b,d)` for the original DeepMind `drainB` over the source machine `1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA`. It returns `none` or `D(A,D)`. The preexisting original-source-certified neutral recurrences are

```text
B(a,9b,d)   = B(a,b,d+24b+2)       (b>0)
B(a,9b+6,d) = B(a,b,d+24b+22)      (all b).
```

The new identity for **all natural a,b,d** is

```text
B(a,9b+8,d) = B(a,b,d+24b+26).
```

Its proof requires exactly two of Agent 49's already source-certified one-level reduction rules. For `a=0`:

```text
B(0,9b+8,d)
  = B(0,3b+2,d+18b+19)
  = B(0,b,d+24b+26).
```

For `a>0`:

```text
B(a,9b+8,d)
  = B(a-1,3b+3,d+18b+17)
  = B(a,b,d+24b+26).
```

Every reduction is exact, even if the drain ultimately fails. This proof is `drain_nine_eight` in [ThirdNinefoldSource.lean](ThirdNinefoldSource.lean), importing the unchanged upstream machine through [FlatDrainSource.lean](FlatDrainSource.lean). The local Lean 4.36.0-rc2 instance was checked against the original source recurrence interface; the upstream-pinned CI job provides the stronger direct original-source audit.

## Arbitrary-base three-letter conjugacy

Let the alphabet be `{0,6,8}`, and for any finite word `w` define `P_w(b)` by beginning at a **positive** block count `b` and repeatedly prepending these ninefold digits. The associated additive charge is `C([])=0` and each prefix adds `2,4,2` respectively. Thus `P_(r::w)(b)=9P_w(b)+r`, while `C_(r::w)=C(w)+(2,4,2)_r`.

For **every** `a,d ∈ ℕ`, every `b>0`, and every finite word `w`, the original drain obeys the all-outcome identity

```text
B(a,P_w(b),d) = B(a,b,d+3*(P_w(b)-b)+C(w)).
```

This preserves termination or failure exactly, and also preserves the final first counter when successful. The source theorem `embed_ninefold` proves the identity by structural induction on the entire word, including any mixture of residues. Positive `b` avoids the exceptional zero argument of the residue-zero identity.

For the explicit safe base `b=6`, define `P(w)=P_w(6)` and `Q(w)=4+C(w)`. Since `B(a,6,d)=D(a,d+22)` for every initial first counter `a`, the family has exact outputs

```text
B(a,P(w),d) = some D(a,d+3*P(w)+Q(w)).
```

In particular, all three source digits conserve **any** initial first counter `a`; the earlier binary family had recorded the special `a=0` statement. `P(w)` is positive and even. The source theorem `ternaryBlock_injective` proves that distinct words have distinct block counts. Exactly **3^n** different successful block counts are therefore obtained from the words of any fixed length `n`, improving the prior two-letter `2^n` family at the same ninefold depth.

## Exact synthetic two-return extension

For each finite word `w`, put `p=P(w)`. The complete unchanged accelerated map `T=highLevelNext` satisfies

```text
T(T(D(p,p-2))) = some D(2+3*p+Q(w),7).
```

This is theorem `ternaryBlock_diagonal_escape`. Its first step uses the `a=d+2` exceptional branch and the above exact drain. Its second step uses the original `a=0`, even-`d` branch. The theorem is fully quantified over all lengths and all words; no numerical horizon is imposed. It concerns deliberately prepared **synthetic** section states, with no proof of reachability from the real `D(0,7)`.

## Scope and verification

The arithmetic recurrence proof, arbitrary-base renormalization and word injection were independently compiled locally with Lean 4.36.0-rc2 using a small interface for the already established source reductions. That local test is not itself an original-source import. The source-connected version is [ThirdNinefoldSource.lean](ThirdNinefoldSource.lean), checked by the existing manual-only [pinned upstream CI workflow](../../.github/workflows/agent49-623-flat-drain.yml), which imports `google-deepmind/cryptids@c86f15861709b76042998c5211c7b2f83991621b`.

The independent [integer checker](check_third_ninefold.py) reproduced **18,000** residue-eight identities for `a<30,b<300,d∈{0,7}`, and **13,120** exact safe-family outputs across all words of length at most seven and four starting pairs. Distinct words were counted at every length, with no collisions.

The first upstream CI attempt [42571587610](https://github.com/FlareZ123/bb6/actions/runs/42571587610) was blocked before Lean compilation by an external Lean download HTTP 504. The second [42571771828](https://github.com/FlareZ123/bb6/actions/runs/42571771828) compiled the **new residue-eight theorem and word injection with ordinary foundational axioms only**, but exposed a base-case elaboration typo in the subsequent all-first-counter drain theorem. That typo has been corrected in commit `efebcc52`; record the outcome of the subsequent source-pinned rerun before claiming the entire module source-certified.

### Remaining BB(6) obstacle

The new family supplies a larger exact regular language of safe drains and an all-outcome conjugacy applicable to any drain argument. No all-time invariant currently proves that every actual `D(0,7)` return is safe or that some actual return fails. Root reachability remains the decisive missing quantifier. This intermediate result is not an exact BB(6) value, a nonhalting proof, or a new Busy Beaver bound. External novelty relative to wider ternary-transducer literature has not been assessed.
