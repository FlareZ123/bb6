# Raw139 E0=0LF — candidate partition and residual proofs

Parent `[7,24,11,24,14,24,24,16,20,11,24,24]` (normalized row (2,0LF)). All six state labels are introduced. **The full parent Cover remains open.** 

## Witness census

The original 24-way census (ordinary moves 0..23; replay 450, cycle period 120, FAR dimension 1/2) has 27,887 splits and 641,402 ordinary leaves: 425,251 translated cycles, 156,031 last-hole queries, 47,474 FAR, and 12,646 opens. New `replay.cpp` emits the entire witness tree as JSON, including actual cycle, query and FAR witnesses. Compile with g++ -O3 -std=c++17; run without arguments. The reproduced JSON SHA-256 is `7b5f285a7ce7e323e3d3f6f0c85fe0ba60177d694be3e5d35b87f05b7491052b`; the original open-list SHA-256 is `f8c4e5d966547e2929994d1fc685a12b1e49bfb800eb2092ae3b3b9a5e463996`.

Initial block search closed 12,226, exact late queries 142, leaving 273 opens and five late multi-hole splits. The latter add 120 ordinary children, yielding 27,892 splits / 641,517 ordinary leaves. Extended replay/FAR closed 135 cycles, 95 FAR, 7 last-hole; second block pass closed 145 (139 reflected). Largest classified finite query 19,001, giving a candidate weighted bound 19,007, conditional on complete source certification. Every split also requires its halting branch. 

## Eleven exceptional one-hole tables

| ID | Exact table | Status |
|---:|---|---|
|1307|7,13,11,17,14,21,24,16,20,11,1,2|Lean accepted|
|2040|7,3,11,5,14,13,24,16,20,11,2,22|Lean accepted locally|
|3002|7,23,11,13,14,1,24,16,20,11,3,6|Lean accepted|
|3862|7,10,11,19,14,17,24,16,20,11,3,0|Open|
|3863|7,10,11,21,14,17,24,16,20,11,3,0|Lean accepted locally|
|3864|7,10,11,22,14,17,24,16,20,11,3,0|Lean accepted|
|4125|7,9,11,24,14,21,2,16,20,11,3,0|Lean accepted|
|4344|7,12,11,24,14,21,23,16,20,11,3,13|Lean accepted|
|9015|7,21,11,24,14,3,0,16,20,11,14,17|Lean accepted|
|10338|7,21,11,1,14,24,3,16,20,11,15,20|Lean accepted|
|11287|7,8,11,3,14,21,24,16,20,11,19,2|Lean accepted|

`E0LFPortfolio.lean` proves `BB6.Agent14E0LFPortfolio.closedRows_never` for the ten accepted rows, uniformly for compatible completions. Local Lean 4.36.0-rc2 accepted the portfolio using original-source dependency artifacts (byte-identical overlap), with propext, Classical.choice, Quot.sound only. The 2040 strong-induction repair compiles; its proof uses only propext and Quot.sound. See [Residual2040.md](Residual2040.md) and [Residual10338.md](Residual10338.md).

Source artifacts: run 45839040551 / 15126193553 (3864,4344,11287,10338); run 45900252441 / 15156641852 (partial build: 9015 accepted, 2040 induction spelling repaired locally); run 45900259143 / 15156118522 (3002,4125); run 45900264710 / 15155651254 (1307). Agent3's 3863 translated cycle, now kernel-accepted locally via Agent14's packed zipper replay, has entry 30,522, period 61,735, left boundary -169, displacement -349. See sibling dossier agent3-raw139-zeroLF-context/CYCLE3863.md. The earlier side-cycle witnesses are:

| ID | Entry | Period | Direction | Boundary | Displacement |
|---:|---:|---:|---|---:|---:|
|3864|1443|672|left|-2|-12|
|4344|5234|1112|left|-8|-8|
|11287|2656|948|right|-7|10|

3862 remains the only mathematically undecided exceptional row. The exact buffered sweep rules are formalized in Agent3's E0LFSweep.lean. Neither a long finite run nor a failed abstraction is evidence of universal nonhalting.

## Reproduction

Run `python /path/to/repo/im-results/agent14-raw139-e0-zeroLF/discover.py 4` in a scratch directory with g++ and Python 3. It reconstructs the two-stage witness discovery using Agent48 blockcert and census.cpp, including extended search. Combined discovery was rerun end to end on the exact replay tree, reproducing all eleven exceptional tables. Its compressed deterministic recipe data are preserved in `recipes.b64` and checked by `decode.py` (decoded SHA-256 `6a8e0dc217b60d744754451eeaa17929556baf1c17a9201e82f1c682b420a861`). `long.cpp` supports exact finite block-macro replay: compile with g++ -O3 -std=c++17, feed residual ID followed by the 12 codes, specify primitive-step limit as first argument. `emit9015.py` produces the width-four block-FAR certificate (width,cap,modulus,runs,reflect,phase)=(4,1,2,3,false,false), 99 left states/255 right nodes. Parent packaging must retain exact table identities and account for all halting branches. No global roster reduction follows from these local proofs.

## Conditional parent composition (23:02 UTC)

`PackedZipWindow.lean` proves that sentinel-bit natural zipper replay is equivalent to the original list zipper, including the exact left-half-line guard. `emit_cycle3863_packed.py` and `shard3863.py` generate and split all 181 primitive replay chunks into bounded-memory modules; explicit join parameters prevent accidental reduction of long executions during elaboration. Local kernel accepted all chunks, their joins, and `BB6.Agent14E0LF3863.never` under Lean 4.36.0-rc2 with only propext, Classical.choice, Quot.sound. The updated ten-row portfolio also compiled.

`ConditionalHybrid.lean` gives kernel-checked compositional soundness of first-hole certificates with an explicit proposition premise, including weighted halting branches. `assemble.py` expands the complete tree to 27,892 splits and 641,517 ordinary leaves: 425,386 cycles, 156,180 last-hole, 47,569 FAR, 12,371 block-FAR, 11 exceptional. The only outstanding premise in packed mode is the exact weighted Cover at 19,007 of table `[7,10,11,19,14,17,24,16,20,11,3,0]` (3862). This is inside F0=1RA, root index 18 in byMove order. The other 23 root proofs have premise True. The root00 proof was accepted locally. All source shards were generated locally; the complete source closure and parent theorem `BB6.Agent14E0LFParent.weighted_conditional` still require kernel acceptance. `prepare.sh` and `compose.py` reproduce the sharded closure in the existing E0 workflow. Source pin d778a640cac0ab4ac49fe020d321bde11afba066, CI run [45908439166](https://github.com/FlareZ123/bb6/actions/runs/45908439166) queued at 23:01:53Z.

The 19,007 bound remains conditional; no removal from the outer canonical roster is asserted.
