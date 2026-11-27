# Root-scale finite-stack and symbolic-sweep pilot (2026-11-27)

This is intermediate research, not a global BB(6) upper bound. The primary E1=1RE sibling proof is separately maintained in ../agent4-raw56-reparent.

## Two large root branches

Both use original canonical cut depth 7, cap 1000, lookback 32 and the frozen cross-branch FAR bank. Tables are 1RB---_1RC---_0RD---_1LD1LE_---{E1}_------.

| E1 | open leaves | FAR-bank accepted candidates | further finite stack | late last-hole | FAR6 | universal growth checked in Lean | unresolved |
|---|---:|---:|---:|---:|---:|---:|---:|
| 0RD | 17081 | 16395 | 674 | 1 | 0 | 11 | 0 |
| 1LC | 22268 | 21356 | 862 (includes M19569 run-stack certificate) | 28 | 1 | 21 | 0 |

Both branches are candidate-complete, not aggregate-certified. M19569 is now kernel-proved nonhalting for every compatible completion; the aggregate branch covers remain outstanding.

### M19569: exact finite run-stack invariant

Table `1RB0LE_1RC---_0RD1RA_1LD1LE_1RF1LC_0RD0RA`. At primitive step 34 the blank orbit enters A with left word 001 and right word 0111, nearest cell first. Write the left word as 00 followed by positive one-runs separated by single zeros, and the right word as positive zero/one run pairs. Trailing blank zeros are immaterial. The left stack alphabet is a positive run length; the right alphabet encodes (b,c) as 256b+c.

[m19569_certificate.py](m19569_certificate.py) discovers a finite inverse-edge graph using the nearest two left runs and three right pairs as summaries. Discovery uses arithmetic return formulas, but its separate verifier does not invoke those formulas. It verifies 706 finite primitive traces with arbitrary untouched suffixes, checks 30,449 combinations of possible residual stack states, and checks the exact blank entry. The discovery fixed point has 13,679 microconfigurations, 1,057 non-bottom inverse edges, 36 left and 444 right summaries, and 706 section pairs. The only hole is B1; no replay uses it.

**Soundness argument.** Interpret state 0 as accepting the empty stack. An edge (t,x,s) accepts x::tail at t whenever tail is accepted at s. A section is permitted if its concrete left/right run stacks are accepted by some listed state pair. For any accepted stack, popping at most two/three symbols along its accepting derivation yields one of the enumerated (prefix, residual state) pairs. If a prefix is shorter than the pop limit, the remainder is empty; otherwise the remainder is arbitrary. Primitive framed replay refuses to read an unknown suffix, and checks the exact resulting prefixes (up to trailing zero padding only on known blank ends). Therefore each successful replay holds for every represented suffix and never accesses B1. The verifier checks that the rewritten prefixes can be pushed onto the same residual states to produce another permitted section pair. All costs are positive. Starting with the checked step-34 entry, induction supplies arbitrarily long live prefixes for every completion of B1. The general soundness argument is formalized in [RunStack.lean](RunStack.lean): `Rule.sound`, `Stack.pops_complete`, `Stack.pushes_sound`, `Cert.closed`, and `Cert.never`. The concrete certificate is checked by 36 separately compiled row theorems, each by `rfl`, and the exact step-34 entry is kernel checked.

Reproduce with Lean 4.36.0-rc2 and the exact accepted closure from artifact 15160313745 (set LEAN_PATH to its a1-raw56-root-consumer directory plus the current directory):
```sh
python3 m19569_certificate.py --write M19569.json
python3 emit_run_stack.py M19569.json
lean -j1 -o RunStack.olean RunStack.lean
lean -j1 -o M19569Data.olean M19569Data.lean
for i in $(seq 0 35); do lean -j1 -o M19569Check$i.olean M19569Check$i.lean || exit 1; done
lean -j1 -o M19569Final.olean M19569Final.lean
```
Locally all 36 row checks and final theorem compiled successfully against that exact original-source closure. The final exported theorems `BB6.Agent4M19569.never` and `BB6.Agent4M19569.cover_never : Cover NeverHalts p` report only [propext, Classical.choice, Quot.sound]. The untrusted generator emits balanced function lookups and sharded row checks to avoid exceeding 4 GiB with a single large array-based proof. No native_decide or admitted goals. Source commit 521cb67169453e3e000c418727c1576b52778e7a, generator commit 739628e0c632f0dc7eef6c50dc783fbcd0d5e087. No global cut is claimed.

### M5334: exact 25-block growth

For M5334 (`1RB0LA_1RC0RA_0RD1RF_1LD1LE_0RB1LC_---1RA`), use `P=011` and the original zipper convention (left stack includes the scanned cell). Define `G(n)=A(P P^n 01111110, 0^10)`. The exact blank entry is `run0 p 8505 blankZ = some (G 23)`. For every natural `n`, `run0 p (9509+500*n) (G n) = some (G (n+25))`. The derivation contains 25 left sweeps of cost `13n`, 25 right sweeps of cost `7n`, five arbitrary-tail single-block identities, and 9509 fixed transitions. This proves nonhalting for **every** completion of F0, using the original raw-machine semantics through `never_of_growth`.

Reconstruct the certificate with `python3 generate_m5334.py > Raw56LCM5334.lean`; compile with Lean 4.36.0-rc2 and `LEAN_PATH` pointing to the exact accepted artifact 15160313745. The [generator](generate_m5334.py) is untrusted; its emitted Lean source proves all steps using `rfl`, `sweepL`, `sweepR`, `join0`, and `omega`. The local full proof and split proof both compiled; the exported `epoch`, `entry`, and `never` use only `[propext, Quot.sound]`. Generator SHA256 `2bcd9f263c601ae6fd9259167dca22edb3481876d1496ad38ecfd400675f8aaf`; generated source SHA256 `26271eb0d6f2f584295d44d4cf27738b5def1756baf8fb04ee67ed4bbe786c37`. No parent aggregate or roster cut is asserted.

### M20376: base-four carry invariant

M20376 (`1RB---_1RC0LB_0RD1LA_1LD1LE_1RF1LC_0LE0RF`) is now closed for every compatible completion by [Raw56LCM20376.lean](Raw56LCM20376.lean). The exact blank entry at step 27 reaches A with left stack `001` (scanned cell included), right `110`. The general family has right `11(1111)^n0` and left a word of digits `00ab`, optionally ending with `001`. Digits with `a=0` increment to `a=1` in `26+4n` steps; digit `a=1,b=0` changes to `a=0,b=1` in `30+4n`; `a=b=1` removes that digit and increases carry depth in ten steps. The first two cases prepend `n` zero digits and reset carry depth; empty and truncated final digit have checked extension rules. All macro identities hold for arbitrary untouched suffixes. Positive-cost closure gives arbitrarily long original-machine live prefixes. `BB6.Agent4Raw56LCM20376.never` compiled with Lean 4.36.0-rc2 against artifact 15160313745, importing `SweepPumping` from that exact accepted closure, with only `[propext, Quot.sound]`. No aggregate parent proof yet. Source SHA256 `7cc528a9008b659bf13d1ac58eb48b2088d85a535fcf1a002699365c372fc19d`.

All 29 late queries are last-hole, maximum 10814 (1LC). No assumption of nonhalting from finite observation. FAR and finite-stack candidates require original checker acceptance; every generated growth lemma and the M20376 and M5334 invariants already checked against accepted upstream artifact 15160313745 with Lean 4.36.0-rc2, standard axioms propext and Quot.sound only.

## Reusable advances

1. fastabstract.cpp evaluates dynamic two-sided inverse-pop closure in C++ over ngram, run-length, lag-XOR and periodic-block states; portfolio_fast.py provides the ordered 3126 parameter tuples. All accepted candidates regenerated with independent Python abstractions and full finite relation closure validation.
2. symbolic_sweep.py discovers exact repeated-block zipper return patterns; emit_symbolic.py proves local arbitrary-tail sweep identities by rfl and composes universal repetitions using sweepL/sweepR and moveCut. All 27 generated 0RD/1LC one-variable proofs checked. Finite samples are only search heuristics; kernel proof quantifies all n.
3. multi_sweep.py / emit_multi.py extend to multiple independent counters and untouched suffixes. M26 in 1LC has G(n,m)=A([], 0010 (1010)^n 0 (10)^m 1111); entry 86, G(0,3); G(n,m+1) -> G(n+1,m) in 16n+22 steps; G(n,0) -> G(0,2n+5) in 48n+124 steps. Inductive closure yields nonhalting.
4. grammar_discover.py / emit_grammar.py prove M4517 and M4598 via a shared block grammar: A([0,0], P++R or Q++R), P=000, Q=011, R a concatenation of X=1111, Z=0000, V=0011, Y Z^n W (Y=1000,W=0111). Eight parametric return rules establish closure for arbitrary finite words. Entry 44 QX. Both original-machine proofs checked.
5. merge_cert.py improves profile-quotient by testing closure of individual merges, with a final full relation check. This is an optional discovery optimization.

## Exact replay

Combine the six text pieces in lexicographic order and decode:
```sh
cat pilot.tar.xz.b64.0* | base64 -d > pilot.tar.xz
sha256sum pilot.tar.xz
# overlay in extracted primary source archive directory
tar -xJf pilot.tar.xz
g++ -O3 -std=c++17 fastabstract.cpp -o fastabstract
g++ -O3 -std=c++17 query_batch.cpp -o query_batch
python scan_banked.py 0RD 1LC
python emit_symbolic.py E10RD E11LC
python emit_multi.py
python emit_grammar.py
```
Archive SHA256 7511d777aac6b8b98beb351584c90ee4744a79ca232b7bb4f1b6ac2f09c56523, 25124 bytes. Six git blobs checked individually. Primary archive supplies cut/farbank/abstraction helpers; build as in its README. For discovery use fast_root_batch.py, residual_root.py. Compile generated rootgrowth/*.lean with LEAN_PATH pointing to extracted artifact a1-raw56-root-consumer. *.finite.json is compact frozen parameter dictionary plus rows of open index, parameter ID and state count. *.unresolved includes pre-growth residuals, not only remaining unresolved. *.query has first-query witness or -1. *.far6 records extra candidate. Rebuild canonical cut with bound large enough to cover the actual weighted last-hole times; no aggregate bound claimed here.

Expected SHA256:
- E10RD.open 778cf100f9bf4149614dcfa9cc81f48f3411c805d10e951b7d94e46f54c595ee
- E10RD.json a5de65867db6c04b7a7009245af4d1622fd887060578156af74907c2e2ab9409
- E10RD.far afb983bd39d6d2ae9c7cf19fe7525c72ee1336fe27a8cf43aa394dea7b4c0268
- E11LC.open a80d75685e57c600f900d23070564150e28890f55716148614742037ad5bd3f2
- E11LC.json 9290f487ee632665754e37d7ffb2a95cb66e65666b20303d1efc0e8405d09cc7
- E11LC.far da5d5aa7121decf64e4b4f1d49a41086396e1c4cd9d01ba59f29c1ab1a0c6396

Reused upstream accepted compiled dependencies rather than rebuilding their source. All 30 growth proofs were locally elaborated and checked. No new axioms or admitted goals.
