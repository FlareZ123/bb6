# Uniform exact original-TM63 counted binary borrow

**Agent 26, 2026-11-03, R005 grant 4. Intermediate, locally Lean-kernel-checked.**

Original published BusyCoq TM63 table: `1RB---_1LC0RF_1RE0LD_0LC1RB_1RA1RE_1RE0RD`. Pinned [SOBCv5.v TM63](https://github.com/ccz181078/busycoq/blob/3f302b87f5fb933c46e97672ffbb6907f373fb6e/verify/SOBCv5.v#L10750-L10830). The provided Lean source implements its literal eleven defined primitive transitions; undefined A/1 is frozen.

## Exact universal theorem

For **every** `k,c : Nat` and arbitrary finite physical tape exteriors `ls,rs`, start at state D with the head on the **last digit** of the left physical word `100(111)^k`; to the right put `011100(111)^(c+1)000 rs`. The farther-left exterior is `ls`. After **exactly `48+12k+12c` primitive original-machine steps**, state D and the exact original head coordinate are restored, the left word is `111(100)^k`, and the right word is `011100(111)^(c+2) rs`. Both farther exteriors are unchanged. There is **no earlier undefined A/1 halt query**, even at the endpoint. The three explicit input zeros are necessary guards.

Lean proved the all-parameter original-primitive-action configuration equality `TM63Uniform.counted_all` and all-prefix safety `TM63Uniform.counted_no_early_halt` in the exact finite-zipper semantics `rawStart/rawEnd`. Both theorems have **only [propext, Quot.sound]** in their printed axiom audit. No `sorry`, `native_decide`, extra axioms, or mathlib. Lean 4.36.0-rc2 was run locally successfully on **2026-11-03**.

The proof decomposes the run into `prep_all` (9k initial head transfer), `d6/d_loop/d9` (15+3k D-to-E gate), `e_loop/e6`, `c_loop/c27` (33+12c E-to-D return). All loops are mathematically uniform by induction. The theorem extends the original-machine k=0 and k=1 proofs by Agent2 to all trailing-zero lengths k, converting Agent24's finite-tested `C_Inc0_micro=48+12*v₂(z)+12c` into a cylinder-wide primitive theorem. The word encodings are `d0=100`, `d1=111`; alignment with published `S1` is syntactic and needs an independent formal bridge.

## Check and reproduce

- Recover the exact `UniformTM63.lean` from [UniformTM63-verified.lean.gz.b64](UniformTM63-verified.lean.gz.b64) using [unpack.py](unpack.py); its source SHA-256 is `ea3a8facf99464a982d56b8e46ab5f6391cffe092da566ae9402a97c9bfa3aa5` (21,373 bytes; 483 lines). The archive's Git blob SHA is `992bcc73a22536cd2f33492d90dd16de1d0ea7d0`. Then compile the recovered source with Lean 4.36.0-rc2; its final two `#print axioms` checks are included.
- Run [verify_uniform.py](verify_uniform.py), an independent literal-RLE sparse signed-tape simulator. It passed **3,100 deterministic full physical-tape tests** for k=0..30, c=0..19, five randomized arbitrary left/right exteriors per pair; seed 2026110326. Exact head, full tape, state, primitive count and absence of premature halt were all checked.

## Scope

The actual blank-rooted champion halting time, Rocq-to-Lean original `LC/S1` semantic import, all reset/drain costs, source CI reproduction and any universal BB(6) upper bound remain open. Published `TM63.halt` is an uncounted existential proof. This is a **synthetic-tape local counted result** with no newly determined BB(6) value, no new BB(6) bound, and no holdout decision. It belongs in `im-results/` pending prior-art comparison and independent source integration.
