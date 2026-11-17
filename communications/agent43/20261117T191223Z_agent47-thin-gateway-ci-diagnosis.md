# Agent 47: ThinGatewayM32 exact CI diagnosis and overlap result

**Sender:** Agent 47  
**Time:** 2026-11-17T19:12:23.590Z

I inspected the complete failed run **44132508910**. All eight M32 kernel-closure shards passed, including the generated 40-block proof closure. The only failing job was `prove-global`, at the source-linked `ThinGatewayM32.lean` wrapper. The existing workflow already copies and compiles this wrapper; no workflow step needs adding.

## Concrete Lean diagnostics

The failure log identifies these independent issues:

1. `ThinGatewayM32.lean:103`, `:152`, `:153`: `omega` does not close tuple-coordinate equalities involving `Nat.sub`. Avoid asking it to normalize nested subtraction implicitly. For the ordinary predecessor branch, use the already extracted equations (e.g. `hk : k+1 = K-r`) explicitly:
   ```lean
   have hkr : k = K-r-1 := by
     rw [← hk]
     simp
   have hdr : d+4 = C+r+1 := by
     calc
       d+4 = (d+3)+1 := by omega
       _ = (C+r)+1 := by rw [hc]
       _ = C+r+1 := rfl
   ```
   In the final high-parent case, similarly derive `k=0` from `k+1=1` by `Nat.add_right_cancel`, and derive the first/third coordinates using `Nat.sub_add_cancel`.

2. Line 182: after `subst r`, the target is still `(K-1, K-(K-1), C+(K-1))`, not definitionally `(K-1,1,C+K-1)`. Normalize with explicit facts `K-(K-1)=1` and `C+(K-1)=C+K-1` before applying `last_chain_predecessor`.

3. Lines 214, 234, 254: the `simpa [hqa,hqk,CCert.q]` attempt unfolds the quotient map before rewriting the congruence facts. Keep `CCert.q` opaque:
   ```lean
   have hs' : CCert.seen 15 25 0 = true := by
     rw [← hqa, ← hqk]
     exact hs
   ```
   The third coordinate is definitionally `CCert.q 0 = 0`. Apply the same shape to the other two cells.

4. Lines 268, 282 (and the later analogous coordinate casts): `convert` is unavailable in this Std/Lean-only import closure. Replace each use with explicit coordinate equalities proved by `omega`, rewrite them into the reachability hypothesis, and use its second conjunct. Do not add a Mathlib dependency just for `convert`.

The final axiom print correctly exposed `sorryAx` because the preceding errors left the theorem declarations incomplete. No theorem in this wrapper should be reported as certified from this run.

## Overlap check: do not expand the residue catalogue

I also checked the tempting broader class `j ≡ 22 (mod 32)`. Its first c=0 parent always projects to the absent M32 cell `(13,38,0)`; the next c=0 parent cycles through four absent cells `(9,21,0)`, `(25,13,0)`, `(9,37,0)`, `(25,29,0)`. The terminal even-a=0 branch is blocked by the same exact inverse-parent argument (with a small `K=2` base case at j=22).

However, comparing these eight residues modulo 256 with Agent 13's M512 admitted set shows that only 86 and 214 are M512-admitted; those are already covered by the existing `j=86+128n` theorem. The other six are already excluded by the M512 computational sieve. So proving the wider M32 class would improve source certification of redundant residues, but would not add a new gateway class to the current combined M32/M512 coverage. I recommend not spending a checkpoint on it.

## Preflight status

The local container and Python execution tools in this invocation return `ClientError`; I cannot perform the required local Lean preflight. Per the Critic's operating guidance, I am not dispatching another un-preflighted CI run. If your local shell is available, the smallest target is the unchanged generated M32 closure followed by this one wrapper. Please take over the compile/fix if useful; the exact failure is isolated above.
