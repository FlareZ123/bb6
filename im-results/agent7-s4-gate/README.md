# S4 original-source stack halting gate and four-phase dynamics

Agent 7, R004; started 2026-11-03. **Intermediate mathematical research.**
Target original blank-start root:
`1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF`, DeepMind **#660**.

**No new BB(6) machine decision or global bound.** Existing DeepMind source
already identified this holdout as a power-of-two bottom-exposure S4
stack system and discussed a single-pass drainage law. This dossier sharpens
that law into a precise all-stack binary-word gate, verifies a necessary
direction against the actual source in Lean, and records conditional
four-phase dynamics. Do not claim novelty beyond prior art until separately
reviewed.

## Authoritative source and proof

Pinned original:
[Cryptids c86f158 S4 source](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/Accelerations/M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.lean).

The original source proves `IsHalt target ↔ CollatzHalts highLevelNext highLevelStart`
under the literal RLE six-state machine, where `highLevelStart = C(3,[0])`.
Its `stepEpoch(a,L,R)` is a total, well-founded recursion and returns
`none` precisely when that accelerated epoch halts.

[Source-level theorem `halt_requires_binary_divisibility`](S4GateOriginal.lean)
was checked on the unchanged source with pinned Lean 4.35.0-rc4 in
[run 41561244271 (SUCCESS)](https://github.com/FlareZ123/bb6/actions/runs/41561244271).
The original source module compiled. The proof has no `sorry`, and Lean
printed only `[propext, Quot.sound]` for the final theorem.
Run was built at commit `0d0d4b45c986529f242ba8a87574d064d7b5fef3` for the relevant file.
The independent verification script is
[`gate_audit.py`](gate_audit.py).

## An exact arithmetic formula for *one* S4 halting step

Let `L=[b0,b1,...,b_{N-1}]` and define the little-endian weighted sum

```
w([])       = 0
w(b :: L)   = b + 2*w(L)
```

For every right stack `R`, and for every odd current digit `a=2q+1`,
the exact source recurrence yields

```
stepEpoch(2q+1, L, R) = none
   iff  exists m>=0:
        q + w(L) + 2^N = 2^(N+m), where N=len(L).
```

The only even-digit halting state is `a=0,L=[]`.
Thus the right stack is *irrelevant to the binary halting predicate*.
The main closed formula is supported by the following independent
mathematical argument and brute-force exact arithmetic checks; see
[`S4GateExact.lean`](S4GateExact.lean) for the attempted
original-source kernel proof. **Treat the full equivalence as a paper
derivation until its own CI passes**.

### Proof of the closed formula (for all finite stacks)

For an empty left stack and odd current digit `a=2q+1`, source `stepEpoch`
halts immediately when `q=0`, returns immediately if `q>=2` is even,
and otherwise recurses on the smaller odd current digit `q`.
By strong induction on `q`, the empty-left failure condition is exactly

```
q+1 = 2^m for some m>=0.
```

For `L=b::L'`, with odd `a=2q+1`, the source first consumes digit
`b` and recurses at current digit `a'=b+q+1` with remaining left
stack `L'`, regardless of `R`. If `q+b` is odd then `a'` is even
and at least 2, so that epoch necessarily returns successfully. In
that case `q+w(b::L')+2^(|L'|+1)` is odd and cannot equal a power of
2 with exponent at least one. If `q+b` is even, put
`q'=(q+b)/2`. Then `a'=2q'+1`; the induction hypothesis on `L'`
gives the desired equivalence after multiplying both sides of the
equation by 2, since
`w(b::L')=b+2w(L')`. This exhausts every branch.

Consequently a source-level *necessary* gate is

```
2^N divides q+w(L).
```

That direction is the certified theorem. The **additional** necessary
and sufficient condition is that `(q+w(L))/2^N+1` is a power of 2.

## A four-phase normalized return section

The source logic implies that any successful odd-source high-level epoch
starting at `a=2q+1` returns with first digit exactly `q`, while an
even-source epoch returns with first digit `a/2+2`. Reason: the first
odd branch appends `q` as the last right digit, and subsequent branches
modify/prepend only the *head* of that right list. The final `transferHL`
makes its last right digit the next first digit.

Hence the genuine blank-origin section must follow the first-digit
cycle `3→1→0→2→3` as long as it survives, independently of the
unbounded left stack. More precisely, once the three-phase stack is
normalized to `C(3,5::7::S)`, any defined step has the shape

```
C(3, 5::7::S) → C(1, 3::5::S')
C(1, 3::5::S') → C(0, 4::7::S')
C(0, 4::7::S') → C(2, 4::7::S')
C(2, 4::7::S') → C(3, 5::7::S').
```

The first arrow may be `none`, and only its stack-tail
transformation remains hard. The other three exact equalities are
submitted as [`S4Control.lean`](S4Control.lean) for source-level
kernel checking. The first arrow's output prefix follows from the
right-stack suffix preserved by the initial 3,5,7 odd drains; this
additional all-time normalization theorem is still to be formalized.
The first normalized genuine section occurs after eight successful
high-level steps, `C(3,[5,7,2])` (exact evaluator check).

For the normalized surviving `3`-phase stack `L`, write `N=|L|`.
A halting step requires

```
1 + w(L) + 2^N = 2^(N+m).
```

For the normalized `1`-phase state
`C(1,3::5::S')`, the epoch is always safe: it becomes the
explicit `C(0,4::7::S')` above. Consequently a *true*
blank-origin failure can only happen at the normalized `3` phase.
This is a substantial simplification of the mathematical search
space, though the single exceptional tail-word gate is still infinite.

## Independent computational checks and limitations

The independent simulator reproduces `bumpHead`, `transferHL`,
and both branches of `stepEpoch` from the exact source equations;
it does not call the weighted gate to decide the source branch.

- Exhaustive `a=0..16`, left digit values `0..7`, left stack
  lengths `0..4`: **79,577 distinct (a,L)**, each with three
  right stacks (`[0]`, `[]`, `[2,7]`), totalling **238,731**
  predicate evaluations. Every source-style result matched
  the closed power-of-two criterion.
- Exact blank-origin high-level prefix has a strict control cycle
  `3→1→0→2→3` for 20,000 consecutive macro steps, no halting,
  all encountered left stacks nonempty; the largest left stack length
  was 17. Longer finite runs remain experiments only.
- A *synthetic* normalized counterexample
  `C(3,[5,7,1])` **does halt** by the closed gate. The prefixes
  5,7 and first-coordinate cycle therefore do **not** prove
  nonhalting; distinguishing the true orbit's dynamic stack tails is
  indispensable.

Research direction: encode the surviving `3`-phase return map on
the variable tail `S` and prove an invariant avoiding every exact
binary power gate (or find a reachable witness). Do not broaden
a finite simulation or finite congruence screen into a halting decision.
