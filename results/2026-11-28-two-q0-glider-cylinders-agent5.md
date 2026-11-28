# Two certified nonhalting six-state cylinders via suffix-parametric glider recurrences

**28 November 2026. Theorem (Lean 4.36.0-rc2, standard axioms only).** Two distinct partial six-state binary Turing machines, each specifying eleven of twelve transition slots, have a blank-tape nonhalting execution **for every possible completion of their remaining transition**. Consequently their **50 distinct complete six-state binary machines** (25 completions per parent, including the possible halting instruction) all run forever. Of those 50 completions, **48 have no halting instruction anywhere and therefore never halt for a trivial syntactic reason**; the substantive new assertions are that the **two remaining halt-completion machines** also never reach their halting slots. These are local universal nonhalting results, **not** a determination of BB(6) or a reduction of the current 40-way canonical global condition.

## Source-level theorem A: right-moving glider, period 226

Exact partial table (states A–F, 0=blank, `---` unspecified):

```
1RB1LC_1RC1RA_0LA0LD_1LA0RE_0RF---_1RD0LB
```

In the canonical two-stack representation `Z0=(state,left-head-inclusive,right)`, let

```
U = 0111111111111111111100       (22 bits)
V = 1001                       (4 bits)
X₀ = 100100110010010010010010011001001001
```

The exact 2,976-step blank execution enters `(C,U++X₀,[])`. For **every finite binary string** `X` the 226-step machine transition establishes the identity

```
run₀ 226 (C,U++X,[]) = some (C,U++V++X,[]).
```

The symbolic checker treats `X` as an **opaque tail**: the transition never inspects any bit of `X`, so this is not an extrapolation from finite orbit samples. For each `n`, induction yields a nonhalting return after `226n` additional steps, with `V` repeated `n` times. The positive return length ensures infinite nonhalting execution, for arbitrary values of the missing E1 transition.

**Lean declaration:** `BB6Coverage.Agent31Pump.Raw11Q0RightGlider148.cover : ∀ B, Cover (WeightedBound B) table`. Proof: [original-source module](../im-results/agent5-weighted-tnf-queue/Raw11Q0RightGlider148.lean), [successful independent source CI run 46091581190](https://github.com/FlareZ123/bb6/actions/runs/46091581190), job 140813485772, reporting exactly `[propext, Classical.choice, Quot.sound]` as axioms and no `sorryAx` or `native_decide`.

## Source-level theorem B: left-moving glider, period 4174

Exact partial table:

```
1RB1LC_1RC0LF_0LA1RD_0RC0RE_1LF---_0LB1LB
```

Let `U` be the 110-bit `prefixWord` and `V` the 60-bit `block` in the [original-source module](../im-results/agent5-weighted-tnf-queue/Raw11Q0LeftGlider151.lean), and let `X₀` be its exact `initialTail`. At **9,181** ordinary steps from blank the machine reaches `(B,[],U++X₀)`. The checked symbolic Tails certificate gives, for every finite binary string `X`,

```
run₀ 4174 (B,[],U++X) = some (B,[],U++V++X).
```

The right-side head-relative stack encodes leftward motion. In each 4,174-step iteration the exact same arbitrary suffix is preserved, and 60 new cells are inserted in front of it. Thus the machine cannot query its unknown E1 transition or halt in any compatible completion.

**Lean declaration:** `BB6Coverage.Agent31Pump.Raw11Q0LeftGlider151.cover : ∀ B, Cover (WeightedBound B) table`. Proof: [original-source module](../im-results/agent5-weighted-tnf-queue/Raw11Q0LeftGlider151.lean), [successful independent source CI run 46090555583](https://github.com/FlareZ123/bb6/actions/runs/46090555583), job 140810210810, reporting exactly `[propext, Classical.choice, Quot.sound]`.

## Proof method, mathematical scope and reusable construction

Both results instantiate the existing proved `Tails.check_sound` parametric-word semantics and `Multi.never_of_region` inductive nonhalting principle. Each proof contains a kernel-reduced *exact blank prefix*, a literal one-sided symbolic return certificate with a universally quantified arbitrary suffix, and a closed-region theorem. In particular, neither proof assumes an unknown transition and neither requires any upper bound on tape size or iteration count.

The discovery can be reproduced using [one-sided glider search](../im-results/agent5-weighted-tnf-queue/search-one-sided-gliders.cjs), which discovers equal-head-context return pairs and then *symbolically refuses all opaque-tail reads*. The general-purpose [Lean source emitter](../im-results/agent5-weighted-tnf-queue/generate-one-sided-glider-lean.cjs) replays the blank seed and generates a self-contained checkable certificate; the **two specific source modules above**, not this unverified general emitter, were independently source-checked and accepted.

The original normalized source q0-148 and q0-151 classifier tree frontiers each have one further difficult one-hole candidate, so **neither full parent Cover is claimed**. This result resolves precisely one exceptional cylinder within each tree. Machine-completion sets are distinct because the two exact fixed transition tables differ. Their mapping into any particular modern canonical 40-representative global quotient is not established here, and no such membership is assumed.
