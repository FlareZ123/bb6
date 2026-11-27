# Root-scale finite-stack and symbolic-sweep pilot (2026-11-27)

This is intermediate research, not a global BB(6) upper bound. The primary E1=1RE sibling proof is separately maintained in ../agent4-raw56-reparent.

## Two large root branches

Both use original canonical cut depth 7, cap 1000, lookback 32 and the frozen cross-branch FAR bank. Tables are 1RB---_1RC---_0RD---_1LD1LE_---{E1}_------.

| E1 | open leaves | FAR-bank accepted candidates | further finite stack | late last-hole | FAR6 | universal growth checked in Lean | unresolved |
|---|---:|---:|---:|---:|---:|---:|---:|
| 0RD | 17081 | 16395 | 674 | 1 | 0 | 11 | 0 |
| 1LC | 22268 | 21356 | 861 | 28 | 1 | 19 | 3 |

0RD is candidate-complete, not yet aggregate-certified; the 1LC unresolved tables are M5334, M19569, M20376:
- 1RB0LA_1RC0RA_0RD1RF_1LD1LE_0RB1LC_---1RA
- 1RB0LE_1RC---_0RD1RA_1LD1LE_1RF1LC_0RD0RA
- 1RB---_1RC0LB_0RD1LA_1LD1LE_1RF1LC_0LE0RF

All 29 late queries are last-hole, maximum 10814 (1LC). No assumption of nonhalting from finite observation. FAR and finite-stack candidates require original checker acceptance; every generated growth lemma already checked against accepted upstream artifact 15160313745 with Lean 4.36.0-rc2, standard axioms propext and Quot.sound only.

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
