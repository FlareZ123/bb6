# Post-reset paired carry output map

**Agent48, 2026-11-21.** Intermediate formalization design connecting Agent49's 66-state paired carry invariant to the arbitrary-length affine pair-stream bridge in [SourceCarryAffineBridge.lean](SourceCarryAffineBridge.lean).

## 1. Exact state interpretation

For `BB6PostResetCarry.State s` in [PostResetCarryPairInvariant.lean](../agent49-parity623/PostResetCarryPairInvariant.lean), the full carry state after a reset is:

| Branch | Previous digits | x-carry | y-carry |
|---|---|---:|---:|
| L | `(s.px,s.py)` (only `s.py` is used in the x formula) | `leftA s.la` | `0` |
| R | `(s.px,s.py)` | `rightA s.ra` | `rightB s.ra` |

The omitted L y-carry is genuinely zero on every reset-output label and remains zero:
[
b_L'=\left\lfloor\frac{p_y+b_L}{3}\right\rfloor
=\left\lfloor\frac{p_y}{3}\right\rfloor=0
\qquad(p_y\in\{0,1,2\},\ b_L=0).
]

I joined the 54 `full_dfa_output_labels` in `SourceCarryResetProduct.json` against the 54 seed states in `PostResetCarryPairClosure.json`: 54/54 matched, with identical previous pairs and L y-carry 0. This is a finite data check, not a formal theorem about the DFA generator.

## 2. Output maps and state update

For input digit pair ((x,y)\in\{0,1,2\}^2), the output pairs are:

[
O_L(s,x,y)=
\left(
\operatorname{emod}(x-p_y+\operatorname{leftA}(s.la),3),
\operatorname{emod}(p_y,3)
\right),
]
[
O_R(s,x,y)=
\left(
\operatorname{emod}(-x-p_x-p_y+\operatorname{rightA}(s.ra),3),
\operatorname{emod}(p_x+p_y+\operatorname{rightB}(s.ra),3)
\right).
]

The current `step s x y` in Agent49's file updates the previous pair to ((x,y)), and updates the carry codes by encoding:
- L: (a_L'=\lfloor(x-p_y+a_L)/3\rfloor);
- R: (a_R'=\lfloor(-x-p_x-p_y+a_R)/3\rfloor), (b_R'=\lfloor(p_x+p_y+b_R)/3\rfloor).

The existing `leftNext_valid` and `rightNext_valid` lemmas give exactly the finite ranges needed to prove that `leftA (encodeLeft a_L') = a_L'`, and that `rightA/rightB (encodeRight a_R' b_R') = (a_R',b_R')`. The L y-carry remains 0.

## 3. Useful Lean interface

A small addition to Agent49's module can define `leftOutputPair` and `rightOutputPair` by the formulas above, then define `runLeftOutput` and `runRightOutput` recursively over `List (Fin 3 × Fin 3)`:

```lean
def runLeftOutput (s : State) : List (Fin 3 × Fin 3) → List (Int × Int)
  | [] => []
  | (x,y)::xs =>
      leftOutputPair s x y :: runLeftOutput (step s x y) xs

def runRightOutput (s : State) : List (Fin 3 × Fin 3) → List (Int × Int)
  | [] => []
  | (x,y)::xs =>
      rightOutputPair s x y :: runRightOutput (step s x y) xs
```

The intended theorems, with the input word mapped to its integer digit pairs, are:
- for every allowed state (s) and finite word (w), `runLeftOutput s w` equals `leftCarryOutputPairs s.py (leftA s.la) 0 (toIntPairs w)`;
- for every allowed state (s) and finite word (w), `runRightOutput s w` equals `rightCarryOutputPairs s.px s.py (rightA s.ra) (rightB s.ra) (toIntPairs w)`.

Proof: induction on (w). Use `allowed_step` to preserve `Allowed`, then `leftNext_valid`/`rightNext_valid` to show the encoded next carry decodes to the floor-divided carry. The output formulas are definitional.

This makes the 66-state `allowed_runWord_closed` result an actual paired-transducer closure, not just a carry-set invariant.

## 4. Connection to the affine successor bridge

The arbitrary-length theorems in [SourceCarryAffineBridge.lean](SourceCarryAffineBridge.lean) identify:
- L pair output with the first (n) ternary digit pairs of ((x'/(3K),y'/(3K)));
- R pair output with the same actual successor quotient pair, under ((x/K)/3=x/(3K)).

Thus, after a reset word has placed the paired carry state in one of the 54 seed labels, the 66-state invariant keeps the paired carry state in the 66-state closure while the remaining source suffix is read. The pair-output map then produces the actual successor pair digits. This is the finite-state interface needed to compose the next shifted reset recognizer.

**Scope:** this note is a proof design and finite data join, not a completed Lean theorem. It does not prove the authentic root's S-window language is closed, nor that every successor window contains a reset. The remaining root-language/phase closure is still the substantive obstacle.
