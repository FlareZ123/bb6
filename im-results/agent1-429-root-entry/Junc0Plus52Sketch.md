# Candidate uniform +52 Junc(0) return family

Status: algebraic composition derived from existing source theorems; not yet
formalized or CI-certified. This is the next high-value continuation after
`Junc924To1008.lean`.

## General parameterization

Take natural parameters (v,k) satisfying

[
v+2k=379,quad v-kge 6,quad 3k-v+15ge0,quad 5k-3v+29ge0.
]

The current source lemmas compose as follows.

1. Seven outer-safe steps:
   [
   J(0,2v+742)	o J(381,2v+1)
   ]
   in 191,493 steps, head displacement +741.

2. Uniform low43, with parameters ((v,k)):
   [
   J(381,2v+1)	o J(2k+9,4v-2)
   ]
   in (4v^2+22v+38k+174) steps, head displacement (6-2v).

3. One outer-safe step with (U=2k+9):
   [
   J(2k+9,4v-2)	o J(4k+21,4(v-k)-23)
   ]
   in (operatorname{outerCost}(2k+9,0)=4(2k+9)^2+10(2k+9)+27)
   steps, head displacement (4k+21).

4. Low-odd with
   [
   v_o=2(v-k)-12,quad n=3k-v+15:
   ]
   [
   J(4k+21,4(v-k)-23)	o J(2n+6,4v_o+2)
   ]
   in (4v_o^2+22v_o+22n+100) steps, head displacement (2-2v_o).

5. Low42 with
   [
   j=4(v-k)-23,quad k_{42}=5k-3v+29:
   ]
   [
   J(2n+6,4v_o+2)	o J(0,4(v+k+9))
   ]
   in (4j^2+22j+18k_{42}+79) steps, head displacement
   (-(2j+4k_{42}+5)).

The endpoint width simplifies under (v+2k=379):
[
4(v+k+9)=2v+794.
]
Thus this is a (+52) return
[
J(0,2v+742)longrightarrow J(0,2v+794).
]
The head shifts sum to (-39), independent of (v,k).

The nonnegativity conditions reduce to odd (v) with
(131le vle177), and (k=(379-v)/2). There are 24 candidate instances.
The route cost is the sum of the five displayed segment costs; it is
parameter-dependent.

## Two consecutive root-connected instances

| (v) | (k) | Start | End | Steps | Head shift |
|---:|---:|---:|---:|---:|---:|
| 133 | 123 | J(0,1008) | J(0,1060) | 544,773 | -39 |
| 159 | 110 | J(0,1060) | J(0,1112) | 673,655 | -39 |
| **Combined** | | **J(0,1008)** | **J(0,1112)** | **1,218,428** | **-78** |

The parameter checks are concrete:
- ((133,123)): (v_o=8,n=251,j=17,k_{42}=245).
- ((159,110)): (v_o=86,n=186,j=173,k_{42}=102).

Composing the two instances with the current 3,363,397-step blank-root
candidate through J(0,1008) gives a candidate blank-root prefix through
J(0,1112) at **4,581,825** steps. The final live Junc(0,1112) endpoint
would imply all-prefix physical C/01 exclusion.

## Formalization plan

1. Expose/reuse the arbitrary-head lift of
   `physical_low43_junc_to_junc` from `Low43C0Uniform.lean`.
2. Prove a generic seven-step outer ladder
   (J(0,741+r)	o J(381,r)).
3. Package the five-segment composition as a parameterized
   `junc0_plus52_physical` theorem under the constraints above.
4. Instantiate ((133,123)) and ((159,110)), then compose with
   `blank_root_to_junc0_1008`.
5. Add the concrete theorem names to the focused axiom audit and rerun the
   original-source CI.

Do not promote this sketch to `results/` until the Lean proof and full
transitive axiom audit pass.


## Rejected +60 attempt

An attempted Junc(0,1112) -> Junc(0,1172) extension is invalid. After
reaching Junc(499,159), the proposed second low-odd parameters would be
(v=79) and (n=(499-79-3)/2=417/2), which is not a natural number.
The apparent 1,004,130-step route therefore does not exist as written and
must not be used. This is a parity obstruction, not a Lean issue.
