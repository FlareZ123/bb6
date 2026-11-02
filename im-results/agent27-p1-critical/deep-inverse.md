# Agent 27: unbounded actual two-step inverse depth in a P1 critical family

**Status:** Universal, kernel-checked **structural obstruction** for the genuine Agent 1 accelerated map `T`. Intermediate mathematical result, **not** a P1 halting/nonhalting proof, BB(6) bound, nor evidence of blank-tape reachability. External publication novelty has not been evaluated.

## A universal genuine-transition inverse identity

For every `b,d : Nat` with `b%4=0`, original unmodified P1 accelerated map `BB6.Agent1.T` satisfies **both**:

```text
T (b, d+b+10)     = (b+3, d+b+8)
T (b+3, d+b+8)   = (2b+12, d)
```

Lean proves `BB6.Agent27.upper_two_step` directly by evaluation of the actual recursive `BB6.Agent1.G`. For any `r`, define `U_r(0)=4r` and `U_r(h+1)=2 U_r(h)+12`. Lean proves `U_r(h)%4=0` and `U_r(h)+12=4·2^h·(r+3)`. The inductive `TwoStepPath h b d` relation has a base constructor at depth zero and a successor constructor that **stores both exact T-transition equations**. Its `arbitrary_upper_depth` theorem constructs a depth-h path terminating at `(U_r(h),d)` for every `h,r,d`, with precisely `2h` actual accelerated transitions along the chain.

## Specialization to P1 critical halting precursors

For any natural `k`, put

```text
n = 2^(k+3)-2
g = 2^(k+3)-(k+5)
r = 7·2^g-4
h = k+2
```

The universal identity, proved symbolically by `critical_upper_root`, is

```text
U_r(h) = 14·2^n − 2n − 16.
```

Thus the proved theorem `BB6.Agent27.critical_has_deep_inverse (k)` is precisely

```lean
TwoStepPath (k+2)
  (14*2^(2^(k+3)-2)-2*(2^(k+3)-2)-16) 3
```

with a definitionally equal `criticalIndex k` in the source. This is the actual odd-sector `(B,3)` necessary precursor of P1's sparse halting-critical targets.

**Interpretation:** For any proposed fixed inverse depth D, taking k≥D produces a critical index `n=2^(k+3)-2` with a genuine chain of length at least D. Each intermediary even-left hub has left coordinate divisible by four and its right counter remains odd. Hence the chain is compatible with the already-proved parity filter `reachable_even_mod4`; the positive-even-right power-shape invariant does not directly reject any of its intermediate even-left hubs. The fact that a synthetic chain exists does **not** prove it is reachable from the actual blank entry; it shows why a globally fixed-depth inverse-tree exhaustion is insufficient without a stronger invariant or a way to reject admissible branches.

## Exact source, verification, limitations

- [Successful original-source GitHub Actions 41407649678](https://github.com/FlareZ123/bb6/actions/runs/41407649678), completed 2026-11-02 07:39:42 UTC. The manual workflow [`agent27-p1-deep-inverse-verify.yml`](../../.github/workflows/agent27-p1-deep-inverse-verify.yml) compiles the **unmodified source** `im-results/agent1-p1-map/PosEvenForm.lean` and then checks the full theorem file. No replacement, stub, mock, new axiom, admitted proof, or unsafe `native_decide`.
- Exact 149-line source: [`UpperDeep.lean.xz.b64`](./UpperDeep.lean.xz.b64). Decompressed SHA-256 `b8045299f45dd1144726d921642c400056c65610c17650829bbbf6373dc7ae44`; CI asserts this exact digest before compilation.
- Original-source axiom audit: `critical_has_deep_inverse`, `upper_two_step`, and `arbitrary_upper_depth` each depend only on `[propext, Quot.sound]`, with **no `sorryAx`**.
- Logical strength: exact finite-depth *synthetic preimages* for an infinite parameter family, without any claim about the authentic blank-entry orbit. This finding is compatible with the three separately proven infinite all-time **unreachability** families `158,190,206(mod256)`, and does not invalidate their complete finite symbolic proofs for each fixed congruence class.

This is actionable evidence for developing forward reachable-set invariants or parameter-uniform inverse branch ranking rather than trying to close every P1 target using a universal fixed backward search depth.
