# S4 head dynamics: a global attractor and a stationary-triple dichotomy

**Agent 5, 6 November 2026. Intermediate original-source mathematical research.** The exact three-drain map below is connected to the six-state, two-symbol S4 machine `1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF` through the existing [original-source reduction](../agent5-s4-octet/README.md). These new theorems classify several *synthetic input* families. They do not decide the authentic blank-tape machine or the six-state Busy Beaver value, and no external novelty review has occurred. The authentic reduced blank seed is `[301,650,645,322,163,160]`.

## The exact source map

Let `W([])=0`, `W(a::S)=a+1+2W(S)`. The source's all-depth odd-drain `G(c,·)` is defined in [S4Octet.lean](../agent5-s4-octet/S4Octet.lean) and [S4PowerGate.lean](../agent5-s4-length/S4PowerGate.lean). Its exact stopping condition for positive `c` is `G(c,T)=none ↔ W(T)+c=2^k` for some natural `k`. Define

```text
P(T) = G(509,T) >>= G(290) >>= G(219).
prun(0,T)=some T;
prun(n+1,T)=prun(n,T) >>= P.
```

For a successful `P` return, its first digit depends exclusively on the previous first digit by `f(a)=h(219,h(290,h(509,a)))`, where `h(c,a)=⌊(a+c)/2⌋+2` if `a+c` is even, and `h(c,a)=⌊(a+c)/2⌋` otherwise. The original-source theorem `S4ToggleHead.P_head` already validates this relationship.

## 1. Infinite uniform drifting cylinder

[S4DriftRay.lean](S4DriftRay.lean) establishes for **every** `x,n : Nat` and every finite suffix `S`:

```text
P ([284,1646,1026,x] ++ S)
  = some ([284,1646,1026,x+1024] ++ S),

prun n ([284,1646,1026,x] ++ S)
  = some ([284,1646,1026,x+1024*n] ++ S).
```

Thus the entire cylinder continues forever, preserves the arbitrary suffix, and increases its fourth digit by exactly 1024 every return. The full state is nonperiodic, even though its three-digit prefix is stationary. This theorem holds without a finite simulation cutoff. Original-source [manual CI 42287516418](https://github.com/FlareZ123/bb6/actions/runs/42287516418) **SUCCESS**, checked-in revision `1cffc9fc95cc16cf93bfde8c4cce28878cf713cc`, compiled the source after importing the unchanged pinned Cryptids acceleration.

## 2. Exact classification of all stationary three-digit prefixes

[S4FixedTriple.lean](S4FixedTriple.lean) defines a total finite-prefix projection `C(c,·)` of the odd-drain and `D=C(219)∘C(290)∘C(509)`. The theorem `P_causal` directly proves, against the exact source `G` and `P`, that every successful source return beginning with an arbitrary finite prefix `xs` also begins with `D(xs)`.

The new quantified fixed-point classification is:

```text
D([a,b,c]) = [a,b,c]
  ↔ a=284 and b=1646 and (c=1021 or c=1026).
```

The theorem `actual_stationary_three` carries this conclusion to **every source `P) return that preserves its first three digits**. The proof solves the head fixed-point equation, the two possible second-digit fixed equations, then eliminates one second-digit branch and classifies the third; all symbolic cases are resolved by Lean integer arithmetic. Original-source [manual CI 42289302941](https://github.com/FlareZ123/bb6/actions/runs/42289302941) **SUCCESS**, revision `428ca9c16456b6e60c4fb2213a401a5f7c20baa2`, verified the complete adapter and this module with standard axioms only.

The second stationary triple has a different possible fate. [S4DriftBad.lean](S4DriftBad.lean) proves `P([284,1646,1021,1])=none` by direct evaluation. More generally, for all `x,S`, if `x+1023+2W(S)` is an exact binary power, then `P([284,1646,1021,x]++S)=none`. This follows from the exact identity

```text
W([284,1646,1021,x]++S)+509 = 8*(x+1023+2W(S)).
```

The theorem is locally Lean-checked against a definition-matching source interface, with the already source-certified `G_none_iff_power` imported as a temporary *local test axiom*. The combined original-source audit is **pending**; its new standalone file is included in the manually dispatched workflow.

## 3. Global five-head absorbing band

[S4HeadAttractor.lean](S4HeadAttractor.lean) proves a strict natural-number Lyapunov descent for the total head map. Define

```text
δ(a)=(280-a)+(a-284)    (natural-number truncated subtraction).
```

Outside the band `{280,281,282,283,284}`, each application of `f` strictly decreases `δ`; inside, it stays zero. Consequently, **every natural-number head** enters that five-element band within `δ(a)` total head returns. Its exact internal dynamics are

```text
280→281→283→282→280,       284→284.
```

The attached `prun_head` and `rooted_survivor_head_band` theorems connect this total map to successful arbitrary-tail returns of the actual `P` map. This is **conditional on surviving until the stated horizon**; earlier halting remains possible. The local arithmetic and induction compiled with Lean 4.36.0-rc2. The local source-matched stand-in for `S4ToggleHead.P_head` was a temporary test axiom; the original-source CI for this new combined file is **pending**.

## Reproduction, provenance, and what remains

All three new Lean modules import existing repository S4 definitions; the original-source manual job [agent7-s4-original.yml](../../.github/workflows/agent7-s4-original.yml) builds pinned unchanged Cryptids `c86f15861709b76042998c5211c7b2f83991621b` and the complete S4 source bridge before checking new modules. The committed proof sources contain no `sorry` or new axiom declarations. Locally checked proof audits show only standard axioms in the source-independent portions; the pending complete job is the decisive original-import provenance test for the new head-attractor and bad-gate files.

The authentic S4 reduced seed enters the separately source-proved `280..283` four-head cycle after the transient. It cannot subsequently enter either stationary triple, both of which require first digit 284. This gives an exact obstruction to treating these synthetic families as a blank-root decision. The practical next target is a history-sensitive whole-tail invariant or a genuine reached stopping gate within the real four-head cycle. The already verified [all-depth prefix projection](../agent5-s4-prefix-causal/README.md) provides a reusable finite-dimensional interface; the [inverse-collision dossier](../agent5-s4-inverse-collision/README.md) warns that synthetic stopping completions persist at arbitrary depth.

**Publication boundary:** these are internally new exact dynamical lemmas and real synthetic nonhalting/halting families. Neither an all-time result about the genuine blank S4 orbit nor a global BB(6) bound follows.
