# Complete second E-exception return classification in the D-start six-state machine

**Status:** source-family mathematical derivation, a conditional all-parameter two-return transducer for **synthetic** blank-left F/0 inputs. It awaits one consolidated original-source Lean import audit and a genuine blank-origin applicability theorem. It does not resolve the D holdout or BB(6).

## Setup

Machine `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`; `I_n(y)` is an F/0 section with blank left tape and right physical tape `1^ny0^∞`; `P_r=(01)^r`. Consider **every** E-exception input

```text
X(k,q) = I_(3k+4)(P_q 1), k>=0, q>=1.
```

Existing Agent37 first-return formulas (also implied by Agent31 E-zero and Agent35 E-double exact raw rules) show:

- q=1: after `T1=12k²+49k+96` raw transitions, `I_(8k+3)(0 1^4 0 (10)^3)` (trailing physical zeros implicit).
- q>=2: after `T1=12k²+49k+56+4q`, `I_(8k+5)(0 1^(2q) 0 1^6)`.

These first outputs are outside the canonical `L(a,r,b)=I_a(P_r1^b)` grammar. Now take one *additional* source-derived physical F/0 return. In the following table, `u=floor(2q/3)`; `k=3t+r`.

| k residue | q condition | **Second output physical F/0 section** | L class |
|---|---|---|---|
| 0 | q=1 | `I_(64t+27)` | pure unary |
| 0 | q>=2 | `I_(64t+17+2q)(0 1^6)` | `L(64t+17+2q,1,5)` |
| 1 | q=1 | `I_(64t+37)(P_3)` | `L(64t+37,3,0)` |
| 1 | q=2 | `I_(64t+33)(P_4 1^5)` | `L(64t+33,4,5)` |
| 1 | q>=3 | `I_(64t+33)(P_2 0 1^(2q-3) 0 1^6)` | **outside L** |
| 2 | q=1 | `I_(64t+49)(P_6)` | `L(64t+49,6,0)` |
| 2 | q>=2 and 2q mod3=0 | `I_(64t+65+8u)` | pure unary |
| 2 | q>=2 and 2q mod3=1 | `I_(64t+77+8u)` | pure unary |
| 2 | q>=2 and 2q mod3=2 | `I_(64t+59+8u)(P_3 1^2)` | `L(64t+59+8u,3,2)` |

Consequently **the only two-checkpoint non-L branch for these synthetic E-exception inputs is `k≡1(mod3), q>=3`**. This is not a reachability theorem for the true blank start. For all other residues, the named second *checkpoint* lies back in L, although the source identities alone do not exclude unobserved earlier F/0 returns.

## Symbolic explanation by the source-certified rules

Write `K` for the branch index of the *intermediate* state. When q>=2, the first result has unary length `8k+5`:

- If `k=3t`, `8k+5=3(8t+1)+2`; original Agent31 `full_B` consumes the initial zero. The following run of `2q` ones merges with the unary prefix, leaving `0 1^6`. Second return time is `12K²+49K+40` with `K=8t+1`.
- If `k=3t+1`, `8k+5=3(8t+3)+4`; original Agent32 `full_E_triple_pairs` with zero right pairs consumes the leading `0 111`, leaving `1^(2q-3) 0 1^6`. Second return time is `12K²+49K+58` with `K=8t+3`. For q>=3 the internal `110` obstruction excludes every regular L suffix; `EscapeLanguage.lean` kernel-proves the exclusion for all parameters. For q=2 the suffix canonically simplifies to `P_4 1^5`.
- If `k=3t+2`, `8k+5=3(8t+6)+3` is an A section. Parse the run `1^(2q)` as `(111)^u` followed by `s=2q mod3` ones. For s=0, original Agent35 `full_A_code` closes at the following zero and merges the six terminal ones. For s=1, consume the remaining `10` and two further `111` tokens using `full_A_code` with certified implicit blank closure. For s=2, original Agent31 `full_A_code_110111_first_return` consumes the `110111` packet and leaves `01010 111=P_3 1^2`.

For q=1 the first output is `0 1111 0 101010`. The intermediate unary residues are A for k=3t, B for k=3t+1 and E for k=3t+2, respectively:

- A consumes one triple token and four pair tokens before its implicit blank close, with total token increment `4+4=8`, yielding the stated pure unary output.
- B consumes the initial zero; the remaining `1^4` joins the unary prefix and the tail canonicalizes to `P_3`.
- E consumes `0 111` via the Agent32 triple-pairs theorem; the remainder canonicalizes to `P_6`.

All these source-family rules have prior individual Lean proof records in `im-results/agent31-cryptid-boundary`, `im-results/agent32-cryptid-third`, `im-results/agent35-cryptid-code`, and `im-results/agent31-cryptid-boundary/A110111CodeFirst.lean`. The physical `0^∞` tail-equivalence requires the existing Agent32 `BoundaryPadding.source_congr`, especially for implicit versus explicitly appended zeros. **The nine-way composition has not yet been verified as one Lean theorem.**

## Exact primitive-step count of second return

For q=1: let `K=8t` (k residue 0), `8t+3` (residue 1), or `8t+5` (residue 2), respectively. The second costs are `12K²+73K+127`, `12K²+49K+40`, and `12K²+49K+58`.

For q>=2: residue 0 has `K=8t+1` and cost `12K²+49K+40`; residue 1 has `K=8t+3` and cost `12K²+49K+58`.

For q>=2, residue 2: set `K=8t+6`, `m=4K+3`, `u=floor(2q/3)`, `P=12K²+41K+32`, `C=u(6m+41)+12u(u-1)`. The second costs are:

- s=0: `P+C+2(m+4u)+6`.
- s=1: `P+C+2+[6(m+4u+1)+41]+[6(m+4u+5)+41]+2(m+4u+9)+6`.
- s=2: `P+C+2(m+4u)+24`.

These follow by adding exact per-token source costs `10→2` and `111→6m+41` (with m increment 1 or 4, respectively), then the source-certified A-section closing cost. The cost formulas also form an independent falsification target for any transcription error.

## Independent literal-TM verification

`check_all_E_second.py` uses a separate physical sparse-tape simulator, with exact 11 live transition entries. It checks **all 144 cases `0<=k<=11, 1<=q<=12`**, and independently verifies both primitive-step counts, complete canonical physical right tapes, physical blank-left head conditions, and the expected L-membership classification. All 144 pass; exactly 40 cases end outside L.

The all-parameter derivation is based on exact source theorems; the 144 cases are finite corroboration only. Neither implies BB(6)'s exact value or resolves this machine's original-blank halting behaviour.
