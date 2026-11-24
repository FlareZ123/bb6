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


## Positive-deviation closure and the remaining low-side obstacle

For `n % 4 = 0`, `n >= 8`, `X = 2^n`, a second uniform theorem now covers the entire interval immediately following the preceding transfer. `BB429HighTransfer.high_exit` proves:

    W % 4 = 0
    64*X - 3*n - 12 < W <= 72*X + 20*n + 200
        ==> exists t,Z:
            run(t,(0,W)) = some(0,Z)
            Z % 4 = 0
            72*X - 3*n - 6 <= Z <= 72*X + 20*n + 200.

For a state below the upper boundary, `high_return` gives strictly positive progress to another zero section with Z <= W+20*n+200. The proof uses the odd-rank phases: for R=2u+w, deviation d>0 is defined by w+d=u+12 if R%4=1, and w+d=u+8 if R%4=3. While the ordinary O/F pair persists, d quadruples, while rank grows by only 10 or 14. Bounded evacuation thus forces a reset. The exceptional rank-two reset is excluded by a uniform arithmetic theorem: for odd p >=5, p%4=1, even k, (2^p+1) does not divide 18*2^k+6*(p+4).

The subsequent proof handles both odd phases and both section counters. In `BB429HighComplete.high_shape_rank_zero`, suppose a=3 or 14, k>=13 odd, u+3=a*2^k, R>=100, and d>0 as above; if R%4=3 also suppose k%4=1. Then there exists a strictly positive successful trajectory to a section with u=0 or 11 and rank divisible by four. The eleven family excludes all exceptional rank-two resets by divisibility; the zero family has two explicit exceptions (9*d=9*2^k+36 or 129*d=9*2^k+60), and both are proved to return safely to rank zero. The restriction on the odd phase index is essential to the stated theorem.

**A concrete obstruction to blanket low-side induction.** Let

    W = 1857086700988517619948591230277803361979046502287420036813712432.

The locally kernel-checked `BB429LowCounterexample.finite_halt` establishes W%4=0, 72*2^204-3*204-6 < W < 96*2^204, and

    run 217 (0,W) = some
      (464271675247129404987147807569450840494761625571855009203428277,
       928543350494258809974295615138901680989523251143710018406856553)

with next of that endpoint equal to none. Its branch word is F^207 followed by Oeven F Oodd F Oeven F Oodd F F F. This is a prepared-state halt, **not a blank-origin halt**. It disproves the idea that every zero-section seed of the correct rank residue in the low-side interval is safe. A genuine ancestry invariant or a successful actual-root trajectory to an escape ray/halting gate is needed.

The checked source modules are in [highbandproof.tar.xz.b64](highbandproof.tar.xz.b64) and [highcomplete.tar.xz.b64](highcomplete.tar.xz.b64). After restoring and compiling the preceding three band modules to .olean, compile in dependency order:

    for f in BB429HighBand BB429BoundaryDivisor BB429HighTransfer \
             BB429HighTrue BB429ElevenDivisor BB429ZeroTrueDivisor \
             BB429ElevenHigh BB429ZeroHigh BB429HighComplete BB429LowCounterexample; do
      lean -o "$f.olean" "$f.lean" || exit 1
    done

All these modules compiled locally with standard axioms only, against the matching BB429Rank declarations. Full original dependency CI remains outstanding.

## Rank-return search and burst-aware replay

The rank-coordinate implementation [rank_return.cpp](rank_return.cpp) uses A=2u+6, R=2u+w. For an affine family R(i)=R+4i after a reset, A(i)=A-4Pi with P>=0; F doubles P and either ordinary O branch maps P to 2P+1. Thus the gap increases monotonically with i and the endpoint horizon can be propagated by a simple integer inequality. It skips maximal F bursts by their exact closed form, and writes certificate triples as unsigned varints. The wide version in [fastwide.tar.xz.b64](fastwide.tar.xz.b64) supports ranks up to 2^120.

The same archive contains `BB429FastReplay.lean` and `BB429FastBinary.lean`. The first proves `fastBlockNext_sound` by checking the maximal F burst's two affine endpoint guards and composing with the individual branch checker. The latter independently replays binary certificates. Its first 100,000-block test from blank accepted exactly time 128984533101 and state (11,445665742842). This is computational replay, not a kernel reduction of that concrete prefix. The C++ exploratory search then reached, in 460 million blocks from blank, the endpoint (0,22045380913412580068) at accelerator time 6772774729502350152. The entire latter prefix has not been independently replayed; it is neither a raw-machine step count nor a proof of nonhalting.

To reproduce the search from restored sources:

    g++ -O3 -std=c++20 rank_return_wide.cpp -o rank_return_wide
    ./rank_return_wide 100000000 rank100m.bin
    ./rank_return_wide 10000000 - 11 501949805622249686 152192404125175966

The optional final three arguments are section u, w and accumulated macro time; use each printed endpoint to resume. The program stops if it detects a halt, a known escape ray, or a resource/rank limit. For independent replay compile the fast Lean modules after the affine and section modules, then run `lean --run BB429FastBinary.lean certificate.bin` (optionally with the same starting u,w,time). Do not treat a cutoff as a nonhalting decision.

**Remaining research:** the uniform transfer is now established through the high side of 72X. Beyond it, the mixed low-side O/F words are the real obstruction; the explicit halt above shows why a scale interval with rank congruence alone cannot be a global invariant. BB(6) remains unknown.
