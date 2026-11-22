# H-phase 76-step tail-parametric growth macro

**Status: source-transcribed macro candidate; not a Lean theorem.** The previous withdrawal by Agent 48 was based on misreading the Nat split in mode_DR_n_n_closed. The source tokenizes only right-head 0 in DR; positive heads, including 1, take the ordinary branch. With b==0 restored, the 76-step H-phase CR test passes and makes zero token-normalizer calls. The H(7) entry and root reachability remain separate obligations. See [ModeDRBranchAudit.md](../agent12-cryptid-root-invariant/ModeDRBranchAudit.md). A prior CI patch attempt failed because it named the private evalStackCfg definition; Agent 48 updated the patch script to use the public closedStackSystem.evalStackCfg field, but that patch has not received local Lean preflight or a new CI run. A second unverified script, im-results/agent48-623-tight-window/patch_hphase_entry_growth.py, proposes both the 526-step H(7)-to-C1 entry and the 254-step tail-parametric growth theorem in the #85 source.

The preceding corridor return map and the (F\to G\to H) macros are in
`im-results/agent12-cryptid-root-invariant/RootCorridorMacro.md`.

## 1. H(7)-to-C1 entry (source-transcribed candidate)

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
The resulting right list has length 37. This H(7)-to-C1 entry is a standalone
projected transition; the old root-to-H(7) connection is withdrawn by the
source token-normalizer correction in TokenNormalizerCorrection.md. Do not
use the previous macro-22,083 index as a root-reachability claim.

The 157 outer successors have an exact branch-counted cost of **526 raw TM
steps**, with zero token-normalizer calls. The #85 source execute-length
counts are: CR0 44×2=88; CR10 14×5=70; CR11 6×16=96; EL0 28×2=56;
EL+ 20×1=20; DL0 12×6=72; DL+ 8×4=32; DR0+ 16×4=64; DR++ 7×3=21;
CR1e 1×6=6; DRempty 1×1=1. Total 526. This is a V8/branch-count result,
not a Lean theorem.

## 2. 76-step tail-parametric identity (candidate)

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

With the source-correct DR split b==0, the 76-step path makes zero calls to closeTokDR and closeTokCR. The DR right-head-one cases take the ordinary branch, as required by mode_DR_n_n_closed.

## 3. Infinite extension in the projected system

If the tail-parametric identity (G) is proved against the source stack successor, it gives an infinite projected orbit from C1. The right-list length increases by 12 on every 76-successor macro. This is not yet a blank-root nonhalting proof: the H(7)-to-C1 entry and, especially, the root reachability of H(7) must be established separately, with the exact #490/#85 source encoding.

## 4. Reproduction and formalization target

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

Formalization target: prove (G) for every finite suffix T by composing the exact source mode clauses, then separately prove the 157-step H(7)-to-C1 entry and a source-valid root connection. Only after those steps may the projected infinite orbit be lifted to the original TM.

## 5. Finite branch certificate for the 76-step macro

The 76 transitions, in order, have the following branch labels. These labels name only ordinary outer clauses; none denotes a token closure. In particular, any DR right-head-one case is handled by the positive-r1 ordinary branch of mode_DR_n_n_closed.

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
