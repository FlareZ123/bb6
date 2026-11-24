# Cryptids #429: original-source halting gates and inverse obstructions

**Research state (24 November 2026): source-verified necessary halting-gate reductions; the genuine blank-start decision remains open.** The full original argument, residue derivations, experiments and verification chronology remain in [FULL_RESEARCH_LOG.md](FULL_RESEARCH_LOG.md).

## Source and strongest integrated gate

The rooted machine is `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`. The pinned [Cryptids source](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA.lean) accelerates the authentic blank run into counters `J(u,w)`, with a potential halt when `w+1=2u`.

[SourceRawHalt44.lean](SourceRawHalt44.lean) composes all-time rooted modular exclusions into an original raw-machine halting equivalence restricted to **44 necessary terminal residue classes modulo 1024**. The full source build succeeded in [manual CI 41869801195](https://github.com/FlareZ123/bb6/actions/runs/41869801195). Earlier six-class and finer inverse chains, parity restrictions, rank checkpoint proofs and source links are in the [full log](FULL_RESEARCH_LOG.md). Repeated proofs of one congruence class provide independent verification of the same exclusion.

[No765HalfREADME.md](No765HalfREADME.md) describes a separate four-lift mod-8192 restriction with its own source-integration evidence. Its claims need separate verification before composing them with the 44-class theorem.

## Missing blank-root result

None of the surviving necessary gates has been shown reachable by the authentic blank orbit; there is also no uniform nonreachability proof. The presence of parametric **synthetic** halting states in arbitrary moduli does not establish actual blank ancestry. See the [all-moduli limitation](../agent6-429-coprime-moduli/AllMixedModuliZeroSector.md).

[Q0Mod128SixRows.md](Q0Mod128SixRows.md) records a new provisional inverse-tree reduction: six of the sixteen `u mod 16` sectors of the outstanding `(n mod 32, d mod 16) = (23, 7)` q0 family appear excluded using the existing positive-even-eight root invariant. It is not yet compiled against the full source dependency closure, and ten sectors remain open; do not treat it as an integrated result.

**Next proof:** constrain genuine blank-root feeders into all surviving halting gates, including exceptional inverse parents. Check overlap with earlier #429 certificates before producing another residue claim. No #429 halt/nonhalt decision or BB(6) result follows.

## q0 depth-16 inverse sieve (computational; not source-integrated)

[Q0Depth16InverseSieve.md](Q0Depth16InverseSieve.md) and its [C++ reproducer](Q0Depth16InverseSieve.cpp) enumerate the exact inverse branches for the outstanding q0 family against the already source-certified root invariants from Agents 1, 6, and 39. The depth-16 sieve leaves 31,376 residue classes modulo 2^22 (1,004,032 lifts modulo 2^27), and identifies a correction to the older [Q0ResidueCoverage note](../agent1-429-q0-23-7/Q0ResidueCoverage.md): its u=26 mod-64 row substitutes the k residue for u=58. This remains an intermediate computational filter, not a Lean theorem or reachability result. The surviving inverse paths are synthetic candidates; the next step must distinguish genuine blank-root ancestry rather than blindly increasing the modulus.

## Exact affine reset certificates

The accelerator has a proof-carrying fast-forward mechanism, rather than separate manually scanned plateaus.

- [BB429AffinePump.lean](BB429AffinePump.lean): all eleven successful branches preserve affine lines `u(i)=u₀+2pi, w(i)=w₀+4qi`. The guard is a linear inequality/equality in `g=w-2u`, a fixed residue modulo four, and (for the +7 branch) a linear constraint on w. Thus checking both endpoints of a parameter interval suffices for the entire interval. `checkWord_sound` proves the whole branch word against `BB429.next`; `repeated_pump` proves every repetition of a translation by `4q`, with its exact macro time.
- [BB429AffineReplay.lean](BB429AffineReplay.lean): a compact block certificate is (word length, repetition count, quarter of translation). The checker reconstructs the word, independently checks its endpoint guards and output slopes, and composes all blocks via `replay_sound`. A single-count block uses the exact source run.
- [affine_replay.py](affine_replay.py) generates these certificates with arbitrary precision integers, choosing maximal valid guard horizons; [BB429AffineCSV.lean](BB429AffineCSV.lean) replays and checks every endpoint and cumulative time, starting from (0,0).
- [BB429AffineExamples.lean](BB429AffineExamples.lean) is a concrete kernel-checked ten-block transfer: `BB429.run 233404010 (0,402653204) = some (0,1207812076)`. Its prepared start is a root state in the numerical replay, but the complete root prefix to it has not yet been established as a kernel proof. The first full F^26 Eodd phase uses 4,575,604 cycles, not merely the 3,128,158-cycle subphase previously located. The +136 phase has 51,540 total 35-step cycles, ending at root macro time 343,764,243 (correcting the earlier scan-only one-step discrepancy).

**Verification boundary:** the two proof modules and examples compiled locally on Lean 4.36.0-rc2 against the matching BB429Rank definitions and run-add theorem, with only `propext, Classical.choice, Quot.sound`. Full untouched-module CI is not claimed. The Python generator's 100,000-row certificate was independently replayed by the Lean VM, yielding

    accepted 100000 blocks; root macro time 130346087692; state (11, 450565424558)

This is a finite computational root trajectory; the general replay soundness theorem is kernel checked, but the entire concrete CSV equality has not been reduced in the kernel. Times are accelerator transitions, not original raw steps. The old finite scans are subsumed by this method: [first pump](BB429RootResetPump.md), [nested pump](BB429NestedResetPump.md), [+204](BB429Return204Pump.md), [+112](BB429Return112Pump.md). Their C++ files remain as independent finite evidence.

To reproduce from this directory with Lean 4.36.0-rc2:

```sh
export LEAN_PATH=.:../agent5-429-rank
lean -o ../agent5-429-rank/BB429Rank.olean ../agent5-429-rank/BB429Rank.lean
lean -o BB429AffinePump.olean BB429AffinePump.lean
lean -o BB429AffineReplay.olean BB429AffineReplay.lean
lean BB429AffineExamples.lean
python3 affine_replay.py 100000 blocks.csv
lean --run BB429AffineCSV.lean blocks.csv
```

## Uniform dyadic-band transfer (all parameters, locally kernel-checked)

Write `F` for the first branch, and `Eodd`, `Eeven`, `Oodd`, `Oeven` for the successful gap branches in the affine checker. For every `k ≡ 2 (mod 4)` and `w ≡ 0 (mod 4)`,

    L_k = 6*2^k - 6 - 3*k
    U_k = 12*2^k - 18 - 3*k
    d_k = 3*k + 10
    L_k <= w <= U_k  ==>  run(k+1,(0,w)) = some(0,w+d_k).

The exact branch word is F^k Eodd. All repeated blocks are certified until the exit interval `U_k < z <= U_k+d_k`. This replaces each individual plateau calculation with a universal theorem.

More strongly, put `n=k-2`, `X=2^n`, so `n ≡ 0 (mod 4), n >= 4`. The following **single all-scale transfer theorem** covers every possible exit offset, including the exceptional equality branches:

    w % 4 = 0
    48*X - 3*n - 24 < w <= 48*X - 8
       ==> exists t,z:
         run(t,(0,w)) = some(0,z)
         z % 4 = 0
         64*X - 3*n - 12 < z <= 64*X + 3*n + 48.

The proof composes a finite boundary dispatcher, the eleven-section plateau `F^n Eeven` (translation 3n+20), its unique R0 exception, and the alternating eleven/zero pair plateau `F^(n+1) Oodd Eodd F^(n+3) Oeven Eeven` (translation 6n+60), followed by a final eleven-to-zero block. The generic translation-exit theorem handles arbitrary repetition counts. It is independent of the original blank trajectory and proves a positive interval of progress for **all** eligible prepared states, not only sampled scales.

Lean source modules `BB429SectionBands.lean`, `BB429BandBridge.lean`, `BB429BandTransfer.lean` are archived together in [bandproof.tar.xz.b64](bandproof.tar.xz.b64), restored by [restore_bands.py](restore_bands.py). All three compiled locally against the matching BB429Rank declarations with Lean 4.36.0-rc2, standard axioms only; complete original dependency CI is not claimed. Restore and compile in order after BB429Rank:

    python3 restore_bands.py
    lean -o BB429SectionBands.olean BB429SectionBands.lean
    lean -o BB429BandBridge.olean BB429BandBridge.lean
    lean BB429BandTransfer.lean

**Remaining exact induction gap:** if this entire outgoing zero-section interval can always be transferred to the next admissible dyadic zero plateau, or to a certified escape corridor, one can iterate the resulting scale theorem starting from a verified blank-origin plateau. Finite experiments confirm many scales, but no uniform theorem yet covers the intermediate region beyond `64*X`. There are synthetic halting seeds in the reset section, so a proof must actually control the entrance set, not merely all sufficiently large states with matching parity. Neither #429 nor BB(6) has been decided.
