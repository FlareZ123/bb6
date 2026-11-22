# H-phase 76-step tail-parametric growth macro

**Status: WITHDRAWN as a source-stack identity.** The old successor omitted the pinned source's DR right-head-one token branch. The 76-step C1 replay invokes that branch and misses the claimed endpoint. The 157-step H(7)-to-C1 entry remains unverified: a corrected replay reaches an unresolved token-normalizer case at outer step 11. The root reachability chain to H(7) is invalid. Preserve the sections below as historical projected-simulator output only. See [DRHeadOneCycle.md](../agent48-cryptid-root-cycle/DRHeadOneCycle.md).

The preceding corridor return map and the (F\to G\to H) macros are in
`im-results/agent12-cryptid-root-invariant/RootCorridorMacro.md`.

## 1. Historical H(7)-to-C1 entry (unverified)

Use Agent 12's definition
[
H(r)=\mathrm{CR}(0(10)^{r+1}001000,;20000).
]
Here the digit strings abbreviate lists of natural numbers, and all pair-stack second coordinates in the projected simulator are zero.

For (r=7), an exact run of 157 outer successors gives

[
H(7)\xrightarrow{157}
C_1:=\mathrm{CR}([1,0],P\mathbin{++}B\mathbin{++}U),
]
where
[
egin{aligned}
P&=[0,0,1,0,19],\\
B&=[0,0,0,2,0,0,0,2,0,0,0,16],\\
U&=[0,0,0,12,0,0,0,12,0,0,0,12,0,0,0,2,0,0,0,0].
end{aligned}
]

The exact interpreter check is
`run(H(7),157) == state("CR",[1,0],[...P,...B,...U])`.
The resulting right list has length 37.

The root's outer-successor index at this seed is
[
24+73+433+2801+18496+61+34+4+157=22083.
]
The summands are, respectively, the root prefix to (D(3,3)), the four
mod-3 corridor returns to (D(3,4)), the (q=1) escape to (F(7)),
the (F\to G) and (G\to H) macros, and the 157-step (H(7)) prefix.
These are outer-successor counts, not raw Turing-machine steps.

## 2. Historical 76-step identity (falsified under the source branch)

For every finite suffix (T), the projected successor system satisfies

[
\boxed{
\mathrm{CR}([1,0],P\mathbin{++}B\mathbin{++}T)
\xrightarrow{76}
\mathrm{CR}([1,0],P\mathbin{++}B\mathbin{++}B\mathbin{++}T).
}
	ag{G}
]

This is more than testing several numeric tails. I ran the 76-step path with
an opaque symbolic tail sentinel. Every attempted inspection or arithmetic
operation on the sentinel was instrumented to throw. The path completed,
the sentinel was untouched, and the final state was exactly
`CR([1,0], P ++ B ++ B ++ T)`.

Independent concrete suffix checks also passed for
`T = []`, `[0]`, `[1]`, `[3,0,0]`,
`[12,0,0,0,12,0,0,0]`, the actual (U), and `[7,5,3,1]`.

The old simulator reported zero calls to closeTokDR and closeTokCR. That count is invalid: it bypassed the source-required DR right-head-one token branch. The corrected replay invokes tok_DR_2_0_closed and misses the claimed endpoint.

## 3. Withdrawn infinite-extension conclusion

The claimed recurrence C_n -> C_(n+1) is withdrawn as a source-stack identity. It follows only from the defective projected successor. The corrected replay of the 76-step path invokes the source-required DR right-head-one token closure and misses the displayed endpoint. The claimed root reachability of C_1 at outer index 22083 is also withdrawn because the preceding DR corridor omitted the r1=1 token branch.

## 4. Historical reproduction (not source-valid)

The macro uses the exact array-based `step`, `bounceCR`, `bounceDR`,
`normalizeEL`, `closeTokDR`, and `closeTokCR` definitions from
`im-results/agent12-cryptid-root-invariant/verify_root_corridor_macro.js`.
The following checks are the minimal extension to that harness:

```js
const P = [0,0,1,0,19];
const B = [0,0,0,2,0,0,0,2,0,0,0,16];
const U = [0,0,0,12,0,0,0,12,0,0,0,12,0,0,0,2,0,0,0,0];

assertState("H7 growth seed",
  run(H(7), 157),
  state("CR", [1,0], [...P, ...B, ...U]));

assertState("76-step growth",
  run(state("CR", [1,0], [...P, ...B, ...U]), 76),
  state("CR", [1,0], [...P, ...B, ...B, ...U]));
```

The symbolic-tail check additionally replaces the suffix with an opaque
sentinel and rejects any attempt to inspect it.

The former formalization target is withdrawn. Do not formalize (G) as a source identity. The current target is the 19-step DR-to-CR root closure and the 36-step CR recurrence in [DRHeadOneCycle.md](../agent48-cryptid-root-cycle/DRHeadOneCycle.md). The 157-step H(7)-to-C1 entry remains unverified.

## 5. Historical branch certificate (omits the required token closure)

The old simulator labeled the 76 transitions as follows. This certificate is invalid for the pinned source: at least one DR right-head-one case is mislabeled as an ordinary clause, whereas mode_DR_n_n_closed requires tok_DR_2_0_closed. The branch counts below are historical only.

```
CR10 CR1e EL0 EL+ DL+ DR0+ DR0+ DRempty
EL+ DL0 EL0 EL0 EL0 EL0 EL+ DL0 EL0 EL+ DL0 EL0 EL+
DL+ DR0+ DR0+ DR++ CR0 CR0 CR10 CR10 CR10 CR10 CR11e
EL+ DL0 EL0 EL0 EL0 EL+ DL0 EL0 EL+ DL0 EL0 EL+
DL0 EL0 EL+ DL+ DR0+ DR0+ DR++ CR0 CR0 CR10 CR11
EL0 EL0 EL+ DL0 EL0 EL+ DL+ DR0+ DR0+ DR++
CR0 CR0 CR0 CR0 CR0 CR0 CR0 CR0 CR0 CR10 CR10
```

Branch counts:
- `CR10`: 8
- `CR1e`: 1
- `CR11e`: 1
- `CR11`: 1
- `CR0`: 13
- `EL0`: 16
- `EL+`: 12
- `DL0`: 8
- `DL+`: 4
- `DR0+`: 8
- `DR++`: 3
- `DRempty`: 1

The sum is 76. The symbolic-tail execution also checked every inspected
head and second element: the sentinel was never reached. This gives a
compact branch-level certificate for translating the macro into the
source `mode_*_closed` lemmas.
