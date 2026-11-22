# Exact macro dynamics of the DR corridor family

**Status:** exact identities for the outer stack successor defined in `fast_root_stack_sim.js`; the root trace instantiates them. This is a macro reduction, not yet an all-time proof for the blank-root orbit.

## Definitions

Let `0^r` denote `r` zero tokens, let `10` denote the two-token list `[1,0]`, and define

`E(r,c) := DR(L = 0^r ++ [1], R = [1,c])`, for `r ≥ 1`, `c ≥ 0`.

Define the terminal family

`F(r) := EL(L = [0,0,0,0], R = [1,0,0,0] ++ ( [1,0] repeated r+2 times ) ++ [3])`.

Let `S` be one outer successor, including the token normalizers when a DL/DR token branch is reached.

## Macro theorem

The following four exact identities hold:

1. **Decrement-by-three corridor** (`c ≥ 3`):

   `S^(2r+14)(E(r,c)) = E(r+4,c-3)`.

2. **Zero reset** (`c = 0`):

   `S^(3r+32)(E(r,0)) = E(3,2r+7)`.

3. **Two-token reset** (`c = 2`):

   `S^(2r+30)(E(r,2)) = E(3,4)`.

4. **One-token exit** (`c = 1`):

   `S^(3r+20)(E(r,1)) = F(r)`.

These formulas have been checked by an independent array-based implementation for `r=1,...,8`; the proof sketches below reduce each to the explicit outer transition clauses and `List.replicate`-style zero-pop loops.

## Proof sketches

### Shared transfer corridor

For arbitrary finite tails `U,T` and `r ≥ 0`, the `DR` branch gives

`S^(r+1)(DR(L=0^r ++ [1] ++ U, R=[1] ++ T)) = CR(L=[0] ++ U, R=0^(r+2) ++ T)`.

Each of the first `r` steps sees left head `0` and right head `1`, drops one left zero, and prefixes `1,0` to the right tail. The final step sees heads `1,1` and produces the stated `CR` state. The `E(r,c)` family is the case `U=[]`, `T=[c]`.

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
- 12 fixed steps give `DR(0^3 1,[1,2r+7]) = E(3,2r+7)`.

The post-corridor length is `2r+31`; adding `r+1` gives `3r+32`.

### Case `c = 2`

The shared corridor gives `CR([0],0^(r+2) ++ [2])`. Eight fixed steps and `r+3` EL zero-pop steps reach `EL(0^(r+4)1,[2])`; one EL step reaches `DL(0^(r+4)1,[1])`. The next step invokes `closeTokDR` on `0^(r+4)1`.

The token identity is independent of the exponent:

`closeTokDR(0^n ++ [1]) = CR(L=[0,0,0,1], R=[1])`.

Indeed, `bounceDR` turns the left accumulator into `1^(n+1)0` and the right word into `[0,0,1]`; `normalizeEL` drops the leading ones and consumes the final zero. From `CR([0,0,0,1],[1])`, 16 fixed steps reach `E(3,4)`. The total length is `(r+1)+8+(r+3)+1+1+16 = 2r+30`.

### Case `c = 1`

The shared corridor gives `CR([0],0^(r+2) ++ [1])`. Eight fixed steps and `r+3` EL zero-pop steps reach `EL(0^(r+4)1,[1])`; the next three steps give `CR([0,1,0^(r+3)1],[0])`.

One CR step gives `CR([1,0^(r+3)1],[2])`. The CR zero-gap transfer identity is

`S(CR([1] ++ 0^g ++ [1] ++ U, R)) = CR([1] ++ 0^(g-1) ++ [1] ++ U, [0,0] ++ bump(R))`.

After `g` steps this becomes `CR([1,1] ++ U, [0,0] ++ ( [1,0] repeated g-1 times ) ++ bump(R))`. Apply it with `g=r+3`, `U=[]`, `R=[2]`; then one final CR step gives exactly `F(r)`. The total length is `3r+20`.

## Root-trace instance

The million-step replay contains the following exact corridor-family chain (macro indices are zero-based):

| Macro index | State | Macro successor |
|---:|---|---|
| 24 | `E(3,3)` | `E(7,0)` at 44 |
| 44 | `E(7,0)` | `E(3,21)` at 97 |
| 97 | `E(3,21)` | `E(7,18)` at 117 |
| 405 | `E(31,0)` | `E(3,69)` at 530 |
| 3014 | `E(95,0)` | `E(3,197)` at 3331 |
| 21271 | `E(263,2)` | `E(3,4)` at 21827 |
| 21827 | `E(3,4)` | `E(7,1)` at 21847 |
| 21847 | `E(7,1)` | `F(7)` at 21888 |

The long middle runs are exactly repeated applications of case 1. For example, `E(3,69)` iterates case 1 until `E(95,0)`, then case 2 resets to `E(3,197)`. Likewise `E(3,197)` iterates case 1 until `E(263,2)`, then case 3 resets to `E(3,4)`.

## What remains

- Analyze the `F(r)` family and its successors. The macro theorem reaches `F(7)` at macro 21888 but does not close the subsequent orbit.
- Formalize the four identities against a Lean definition of the outer stack successor; the current checks are executable finite tests plus transition-case derivations, not a checked Lean theorem.
- Do not infer an infinite root orbit from this finite macro prefix. The result is a reusable exact compression of a substantial portion of the root trajectory.