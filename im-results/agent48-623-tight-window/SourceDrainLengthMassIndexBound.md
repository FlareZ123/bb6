# Source-drain length is bounded by the mass index

Status: mathematical proof sketch from the current `sourceDrainStep_spec` and `sourceDrainSummary` definitions; not yet added to Lean or compiler-checked in this invocation.

## Proposed source theorem

Let `sourceDrainLength` be Agent1's recursive summary length. The following bound should be provable directly from `sourceDrainStep_spec`:

**If** `2*b < 3^n`, **then** `sourceDrainLength b ≤ n`.

This is stronger for the current purpose than the available depth-only estimate on the signed drop. It supplies the missing `L ≤ ell` premise for `correction_buffer_by_depth`.

## Induction proof

Use strong induction on `b`. The case `b=0` is immediate. For `b=b₀+1`, let `t=sourceDrainStep b₀`, and write `v=t.1`, `q=t.2.1`, `eps=t.2.2`. The existing `sourceDrainStep_spec` gives

`b₀ = ternaryOnes(v) + 3^v*(3*q+2*eps)`, with `eps≤1`.

Since `2*ternaryOnes(v)+1=3^v`, this yields the exact factorization

`2*b-1 = 3^v*(6*q+4*eps+1)`.

The existing summary recursion gives

`sourceDrainLength(b) = v+1+sourceDrainLength(q)`.

Now assume `2*b<3^n`. The factor is at least one, so `3^v≤2*b-1<3^n`, hence `v<n`. Cancelling `3^v` in the factorization gives

`6*q+4*eps+1 < 3^(n-v) = 3*3^(n-v-1)`.

In particular `2*q<3^(n-v-1)`. Also `q<b` by the existing `sourceDrainStep_q_lt`. Apply the induction hypothesis to `q` at exponent `n-v-1`:

`sourceDrainLength(q)≤n-v-1`.

Substitute in the summary recursion to obtain `sourceDrainLength(b)≤n`.

The only arithmetic details in a Lean implementation are the cancellation of a positive `3^v`, strict monotonicity of `3^v`, and rewriting `3^(m+1)=3*3^m`; `omega` should discharge the remaining linear inequalities.

## Application to the four #623 rays

Let `S=a+d`, `q=min(a,d)`, and let `ell` be the mass index defined by `(3^ell-1)/2 ≥ S+3`, equivalently `2*S+7≤3^ell`. Every ray drain input is one of `q+3`, `q+2`, `q-1`, or `q+1`, so `b≤q+3`. Since `2*q≤S`,

`2*b ≤ 2*q+6 ≤ S+6 < 2*S+7 ≤ 3^ell`.

Thus the proposed theorem gives `sourceDrainLength(b)≤ell` for every ray drain (with the ray's existing nonnegativity/budget hypotheses for `q-1`).

Agent1's `sourceDrainStats_bounds` already gives `E≤R≤L`. Consequently the new length bound yields `E≤R≤L≤ell`. Together with `drainB_digit_cocycle` identifying `D=L-2E`, this discharges every hypothesis of `SignedCoordinateNormalForm.correction_buffer_by_depth` and establishes the sharper correction envelope `|C|≤34*ell+122`, `|F|≤24*ell+84` from the source drain itself.

It also gives `|D|=|L-2E|≤L≤ell` and `R≤ell`. Since `corrB` is of the form `±3D±2R+c` with `|c|≤19`, the source threshold bound `|T|≤5*ell+22` follows directly (indeed `5*ell+19` suffices). Thus the sharper `B_corr=34*ell+122` and the sign-branch comparison can be source-closed without relying on the separate depth-only estimate `D∈[-ell,ell+1]`.

## Integration target

Add the theorem immediately after `sourceDrainStats_bounds` in `DrainDigitSourceBridge.lean`, then prove a ray wrapper using `b≤q+3` and the mass-index lower bound. After a successful exact-import Lean compile, the `correction_buffer_by_depth` path can replace the conservative `correction_buffer_from_depth` path for these four rays.

Until that theorem is compiled, retain `B_S=max(34*ell+140,36*ell+88)` as the safe source-supported envelope. This note is not a claim that the proposed Lean theorem has compiled.

— Agent 48