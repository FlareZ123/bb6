# Exact macro dynamics of the DR corridor family

**Status: REQUIRES RE-EVALUATION; the previous blanket withdrawal was based on a wrong branch reading.** The pinned `mode_DR_n_n_closed` tokenizes only right-head 0; positive right heads take the ordinary branch. The restored source-transcribed simulator again reaches `Corr(3,3)` at macro 24. This does not automatically validate every formula below: treat the family identities as candidates until the full regression is rerun. See [ModeDRBranchAudit.md](./ModeDRBranchAudit.md).

## Definitions

Let `0^r` denote `r` zero tokens, let `10` denote the two-token list `[1,0]`, and define

`Corr(r,c) := DR(L = 0^r ++ [1], R = [1,c])`, for `r ≥ 1`, `c ≥ 0`.

Define the terminal family

`F(r) := EL(L = [0,0,0,0], R = [1,0,0,0] ++ ( [1,0] repeated r+2 times ) ++ [3])`.

Let `S` be one outer successor, including the token normalizers when a DL/DR token branch is reached.

## Macro theorem

The following four exact identities hold:

1. **Decrement-by-three corridor** (`c ≥ 3`):

   `S^(2r+14)(Corr(r,c)) = Corr(r+4,c-3)`.

2. **Zero reset** (`c = 0`):

   `S^(3r+32)(Corr(r,0)) = Corr(3,2r+7)`.

3. **Two-token drift** (`c = 2`, `r ≥ 8`):

   `S^(2r+30)(Corr(r,2)) = CR(L=0^(r-8) ++ [1], R=[33])`.

4. **One-token exit** (`c = 1`):

   `S^(3r+20)(Corr(r,1)) = F(r)`.

The c=2 formula is now stated only for `r ≥ 8`; the previous exponent-independent reset to `Corr(3,4)` is withdrawn. The proof sketches reduce the remaining claims to explicit outer transition clauses and `List.replicate`-style zero-pop loops. The corrected regression harness has been edited, but a post-correction Node/CI run is not yet available.

## Proof sketches

### Shared transfer corridor

For arbitrary finite tails `U,T` and `r ≥ 0`, the `DR` branch gives

`S^(r+1)(DR(L=0^r ++ [1] ++ U, R=[1] ++ T)) = CR(L=[0] ++ U, R=0^(r+2) ++ T)`.

Each of the first `r` steps sees left head `0` and right head `1`, drops one left zero, and prefixes `1,0` to the right tail. The final step sees heads `1,1` and produces the stated `CR` state. The `Corr(r,c)` family is the case `U=[]`, `T=[c]`.

### Case `c ≥ 3`

The shared corridor first gives `CR([0],0^(r+2) ++ [c])`. From there:

- 8 fixed steps reach `EL([0,1],0^(r+3) ++ [c])`;
- `r+3` EL zero-pop steps reach `EL(0^(r+4) ++ [1],[c])`;
- one EL step subtracts 1 from `c`, and one DL step (valid since `c-1 ≥ 2`) emits `DR(0^(r+4)1,[1,c-3])`.

The post-corridor length is `r+13`; adding the initial `r+1` transfer steps gives `2r+14`.

### Case `c = 0`

The shared corridor gives `CR([0],0^(r+3))`. From this state:

- 8 fixed steps reach `EL([0,1],0^(r+4))`;
- `r+4` EL zero-pop steps reach `EL(0^(r+5)1,[])`;
- one empty-R EL step gives `CR(0^(r+5)1,[0])`;
- `r+5` CR zero-pop steps give `CR([1],[2r+10])`;
- the next CR step gives `EL([0],[0,2r+13])`;
- 12 fixed steps give `DR(0^3 1,[1,2r+7]) = Corr(3,2r+7)`.

The post-corridor length is `2r+31`; adding `r+1` gives `3r+32`.

### Case `c = 2`

The shared corridor gives `CR([0],0^(r+2) ++ [2])`. Eight fixed steps and `r+3` EL zero-pop steps reach `EL(0^(r+4)1,[2])`; one EL step reaches `DL(0^(r+4)1,[1])`. The next step invokes `closeTokDR` on `0^(r+4)1`.

The source-exact token identities, for any right context `q`, are:

`closeTokDR(q, 0^n) = CR(L=0^(n+1) ++ [1], R=bump(q))`

and

`closeTokDR(q, 0^n ++ [1]) = CR(L=0^(n+4) ++ [1], R=bump(q))`.

The extra zeros come from applying `tok_EL_1` once for every leading 1 in the accumulator. In the c=2 corridor, the closure input is `0^(r+4) ++ [1]`, so it returns `CR(L=0^(r+8) ++ [1], R=[1])`. For `r ≥ 8`, the next 16 steps are all CR zero-pop steps, giving `CR(L=0^(r-8) ++ [1], R=[33])`. The total length remains `(r+1)+8+(r+3)+1+1+16 = 2r+30`.

### Case `c = 1`

The shared corridor gives `CR([0],0^(r+2) ++ [1])`. Eight fixed steps and `r+3` EL zero-pop steps reach `EL(0^(r+4)1,[1])`; the next three steps give `CR([0,1,0^(r+3)1],[0])`.

One CR step gives `CR([1,0^(r+3)1],[2])`. The CR zero-gap transfer identity is

`S(CR([1] ++ 0^g ++ [1] ++ U, R)) = CR([1] ++ 0^(g-1) ++ [1] ++ U, [0,0] ++ bump(R))`.

After `g` steps this becomes `CR([1,1] ++ U, [0,0] ++ ( [1,0] repeated g-1 times ) ++ bump(R))`. Apply it with `g=r+3`, `U=[]`, `R=[2]`; then one final CR step gives exactly `F(r)`. The total length is `3r+20`.

## Root-trace instance

The million-step replay contains the following exact corridor-family chain (macro indices are zero-based):

| Macro index | State | Macro successor |
|---:|---|---|
| 24 | `Corr(3,3)` | `Corr(7,0)` at 44 |
| 44 | `Corr(7,0)` | `Corr(3,21)` at 97 |
| 97 | `Corr(3,21)` | `Corr(7,18)` at 117 |
| 405 | `Corr(31,0)` | `Corr(3,69)` at 530 |
| 3014 | `Corr(95,0)` | `Corr(3,197)` at 3331 |
| 21271 | `Corr(263,2)` | `CR(L=0^255 ++ [1],R=[33])` at 21827 |
| 21827 | `CR(L=0^255 ++ [1],R=[33])` | `EL(L=[0],R=[0,546])` at 22083 |

The long middle runs are exactly repeated applications of case 1. For example, `Corr(3,69)` iterates case 1 until `Corr(95,0)`, then case 2 resets to `Corr(3,197)`. Likewise `Corr(3,197)` iterates case 1 until `Corr(263,2)`. The corrected c=2 token closure then produces a long CR zero sweep, not `Corr(3,4)`; the root reaches `EL([0],[0,546])` at macro 22,083.

## What remains

- Prove the corrected countdown/reset chain and the 76-step root-reachable growth macro documented in [RootCountdownGrowth.md](RootCountdownGrowth.md); compress the 50,000-step entry and formalize the tail-parametric block insertion.
- The `c=1` exit and the subsequent `F/G/H` identities remain valid as standalone projected macros, but the corrected blank-root trace no longer reaches them through the old c=2 reset.
- Prove the exact `ListBlank` head-boundary/control-state correspondence for the candidate DRegular relation; the right-side image `0 1^(c+1) 0 11` is still unmatched.
- Formalize the corrected token identities and the corridor macros against the actual source stack successor in Lean; no checked Lean theorem is claimed.
- Do not infer nonhalting from a finite macro prefix or halting from the external cylinder. Root-to-cylinder reachability remains open.

## Reproducible regression result

The earlier Actions runs (89, 97, 105, and 106 checks) predate the token-normalizer correction and are withdrawn as evidence for the c=2/root-chain claims. The corrected harness now tests both `closeTokDR(q,0^n)` and `closeTokDR(q,0^n1)`, the two corrected CR-token branches, the c=2 drift for `r ≥ 8`, and the corrected root continuation. Manual V8 checks passed for `n=0,...,32`, c=2 parameters `r=8,9,10,263`, and the 556+256-step root continuation. The checked-in harness has not yet been executed under Node/CI after editing; these are computational checks, not a Lean-checked theorem.

## Closed form for repeated decrement phases

Iterating case 1 `k` times from `Corr(3,c)` gives, whenever `c ≥ 3k`,

`S^(4k^2+16k)(Corr(3,c)) = Corr(3+4k,c-3k)`.

The elapsed time is the sum of the individual macro lengths `2(3+4j)+14 = 20+8j` for `j=0,...,k-1`, namely `4k^2+16k`. This turns each long decrement run into a quadratic-time-indexed family of exact states.

The observed root trace decomposes into these three sweeps:

- From `Corr(3,21)` at macro 97, take `k=0,...,7`; the endpoint is `Corr(31,0)` at macro 405, then the zero reset reaches `Corr(3,69)` at macro 530.
- From `Corr(3,69)` at macro 530, take `k=0,...,23`; the endpoint is `Corr(95,0)` at macro 3014, then the zero reset reaches `Corr(3,197)` at macro 3331.
- From `Corr(3,197)` at macro 3331, take `k=0,...,65`; the endpoint is `Corr(263,2)` at macro 21271. The corrected c=2 macro reaches `CR(L=0^255 ++ [1],R=[33])` at 21827 and then `EL(L=[0],R=[0,546])` at 22083.

The earlier `Corr(3,4) -> Corr(7,1) -> F(7) -> G(7) -> H(7)` chain remains a collection of standalone projected identities, but it is not on the corrected blank-root trajectory. This is a compact exact description of the corrected corridor-family prefix; it does not imply an all-time orbit result.

## One further exact continuation from F(r)

Define

`G(r) := DR(L=0^2 ++ ( [1,0] repeated r+2 times ) ++ 0^2 ++ [1] ++ 0^3, R=[1,0])`.

Then

`S^(3r+13)(F(r)) = G(r)`.

Proof: the initial `1,0,0,0` prefix of `F(r)` takes 5 steps and reaches `EL(L=0^4 1 0^3, R=(10)^(r+2)3)`. Each remaining `(1,0)` pair takes 3 steps: EL decrements the leading 1, DL consumes the resulting zero and maps `L` to `0 :: bump(L)`, then EL consumes the original second zero. The net left-list map is `U(L)=0^2 ++ bump(L)`. Inductively, `U^k(0^4 1 0^3)=0^2(10)^k0^2 1 0^3`. After `r+2` pairs, the remaining right list is `[3]`; two final EL/DL steps produce `G(r)`. The total is `5+3(r+2)+2=3r+13`.

These are exact standalone identities. The corrected blank-root trace does not reach `F(7)`, `G(7)`, or `H(7)` via the withdrawn c=2 reset, so they are not root-reachability claims.

The harness was extended and passed Actions run `44979005652` on commit `ba92d315165e341787be8fbc36bb8b69f1625d50`, reporting `{ ok: true, checks: 97 }`.


## G(r) to H(r)

Define

`H(r) := CR(L=[0] ++ ( [1,0] repeated r+1 times ) ++ [0,0,1,0,0,0], R=[2,0,0,0,0])`.

Then `S^4(G(r)) = H(r)`. The first two DR steps remove the two leading zeros of `G(r)` while extending the right prefix; the next DR step sees heads `1,1` and produces `CR(L=00(10)^(r+1)001000, R=0^5)`; one CR zero-pop step gives `H(r)`.

The former root-prefix claim to `G(7) and `H(7)` is withdrawn. These remain standalone identities only; the corrected root state at macro 21,926 is in the CR zero-sweep family, not `H(7)`.

The earlier regression run for `G(r) -> H(r)` predates the source-normalizer correction. The local identity is retained as a standalone projected transition, but it is not a current root-prefix claim.


The 24-step seed-to-`Corr(3,3)` prefix is unchanged by the correction. The old 106-check run included the invalid c=2 reset and H(7) reachability, so it is not evidence for the corrected full prefix. The corrected root continuation is now checked manually in V8 through macro 22,083; a post-correction Node/CI run is pending.


Process note: the temporary one-off Node workflow used for the 106-check regression was removed after the passing run, in line with the repository-wide direction to avoid proliferating standalone workflows. The self-contained JS harness remains available for local reproduction with Node 20.


Editorial precision: the 106-check Actions run predates the subsequent pure notation rename `E(r,c)` -> `Corr(r,c)` and the label clarification that `DR([0,0],[1])` is the accelerated stack seed at raw TM time 7. The transition logic and test cases were not changed by those edits; no post-rename CI run is claimed.

## Physical tape image in the pair-stack encoding

The #85 source defines `cfg_DR_n_n L R` with physical tape `encLeft(R) D> encRight(L)`, while `evalStackCfg DR_n_n L R` swaps the arguments (as recorded in [`DeepMindStackReduction.md`](../agent32-cryptid-padding/DeepMindStackReduction.md)). For pair lists with second coordinate 0, `encLeft` concatenates `1^(a+1)0` in list order and `encRight` concatenates the same blocks in reverse list order.

Consequently, the outer state `Corr(r,c)=DR(L=0^r1,R=[1,c])` has the exact pair-stack tape image

`(10)^r 110 D> 0 1^(c+1) 0 11`,

up to the source's blank-extension equivalence. This is a concrete encoding of the corridor family in the #85-oriented stack system. It is **not** yet an identification with the @-d `A(n,r)` section or a proof of reachability to the halting cylinder; the full A-step2/stack-system bridge remains open (see [`ASectionStackEncoding.md`](../agent32-cryptid-padding/ASectionStackEncoding.md)).
## Explicit fixed subpaths for the reset cases

The two fixed tails used above can be checked directly from the outer clauses. Write `EL(L;R)` etc. with the left list before the semicolon and right list after it, and `ε` for the empty list.

### The 12-step tail in the `c=0` reset

Starting from `EL([0];[0,2r+13])`, the exact 12-step chain is:

```text
EL(0 ; 0,2r+13)
→ EL(0,0 ; 2r+13)
→ DL(0,0 ; 2r+12)
→ DR(0,0 ; 1,2r+10)
→ DR(0 ; 1,0,2r+10)
→ DR(ε ; 1,0,0,2r+10)
→ EL(0 ; 1,0,0,2r+10)
→ DL(0 ; 0,0,0,2r+10)
→ EL(0,1 ; 0,0,2r+10)
→ EL(0,0,1 ; 0,2r+10)
→ EL(0,0,0,1 ; 2r+10)
→ DL(0,0,0,1 ; 2r+9)
→ DR(0,0,0,1 ; 1,2r+7)
```

The endpoint is `Corr(3,2r+7)`.

### The corrected 16-step tail in the `c=2` corridor

After the corrected token closure, the state is `CR(L=0^(r+8) ++ [1],R=[1])`. For `r ≥ 8`, all of the next 16 transitions are CR zero-pop steps:

```text
CR(0^(r+8)1 ; 1)
→ CR(0^(r+7)1 ; 3)
→ CR(0^(r+6)1 ; 5)
→ ...
→ CR(0^(r-8)1 ; 33)
```

For the root value `r=263, this gives `CR(L=0^255 ++ [1],R=[33])` at macro 21,827. A further 256 successors reach `EL(L=[0],R=[0,546])` at macro 22,083. The previous 16-step tail through `Corr(3,4)` is invalid because it used the uncorrected `tok_EL_1` normalization.
| 21926 | `CR(L=0^156 ++ [1],R=[231])` | `EL(L=[0],R=[0,546])` at 22083 |
## Candidate relation to the DRegular source section (not yet a state correspondence)

The exact left-stack tape identity also has a potentially useful relation to the repository's DRegular source language. For `q=r≥1`, the source definition gives `sourceSection(2,r,0)=11(01)^r`. Reversing this word gives `(10)^r11`, while

`encLeft(0^r1) = (10)^r110 = reverse(sourceSection(2,r,0)) ++ [0]`.

So the left tape of `Corr(r,c)` is the reversed canonical DRegular section `(a,q,b)=(2,r,0)` with one additional boundary blank at the head. This is an exact string identity from the two encodings. It is only a **candidate bridge**: the exact `ListBlank` head-boundary equivalence, control-state correspondence, and the right-suffix image `encRight([1,c])=0 1^(c+1) 0 11` have not been matched to the DRegular state. Do not treat `Corr(r,c)` as a DRegular state without proving those conditions.

The H(7) tail-parametric growth loop is discussed in [HPhaseGrowth.md](HPhaseGrowth.md). The currently root-connected candidate 76-step growth family is described in [RootCountdownGrowth.md](RootCountdownGrowth.md). Neither identity is yet Lean-proved or lifted to an original-TM nonhalting theorem.
