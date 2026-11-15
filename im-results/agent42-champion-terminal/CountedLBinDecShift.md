# Counted TM63 LBinDec shift hypothesis: exact (4+12n) decomposition

**Status:** exact finite-transition decomposition identified; arbitrary-context Lean theorem not yet formalized. Do not treat this note as a certified reset-prefix result.

## Target source obligation

In the pinned BusyCoq TM63 proof, `LC_Inc` is obtained from `LBinDec_spec`; the latter reduces the binary decrement to the repeated-block hypothesis in `LInc`. In the notation of `verify/SOBCv5.v` (TM63 module), the relevant shape is

```text
l <* d0 <* d1^n <| r   -->+   l <* d1 <* d0^n |> r
```

where `d0 = <[1;0;0]>`, `d1 = <[1;1;1]>`, `l <| r` is state D with right context `[0] *> r`, and `l |> r` is state B with the head moved into `r`. The custom `<[x;..;y]>` notation in `Helper.v` builds the stream-order word `[y,...,x]`; `l <* xs` is `Str_app xs l`. Thus the left stream is nearest-cell-first and the d0 block is `[0,0,1]` in that stream order.

## Exact decomposition

For every (n\geq0), the H-run decomposes into three source-connected phases:

1. **Carry-hole sweep: (9n) steps.** Apply `Agent48Champion.counted_left_sweep` from `CountedSweep.lean` to (3n) consecutive ones, with a zero immediately to the right. Its primitive transition is
   - D on 1: write 1, move R, enter B;
   - B on 0: write 1, move L, enter C;
   - C on 1: write 0, move L, enter D.
   
   These three moves shift the zero one cell left. Repeating over (3n) cells costs (3(3n)=9n) and moves the head from (h) to (h-3n).

2. **Four-step base bridge: (4) steps.** At the new head (h'=h-3n), the local symbols at (h'-1,h',h'+1) are all zero. The exact transitions are
   - D on 0: write 0, L, C;
   - C on 0: write 1, R, E;
   - E on 0: write 1, R, A;
   - A on 0: write 1, R, B.
   
   This writes ones at (h'-1,h',h'+1) and ends in state B at (h'+2).

3. **B/F/D right sweep: (3n) steps.** The rightward run of (3n) ones now starts at (h'+2). The repeating three-step transition is
   - B on 1: write 0, R, F;
   - F on 1: write 0, R, D;
   - D on 1: write 1, R, B.
   
   It transforms each physical block (111) into (001), moves right three cells, and returns to state B. An induction identical in shape to `counted_right_sweep` in `CountedSweep.lean`, but rotated to start in B, gives exactly (3n) steps.

The final head is at (h'+2+3n=h+2), in state B. The left stream is precisely the target `[1] ++ d0^n ++ d1 ++ l`, and the right context is the original (r). Therefore the total is

[
9n+4+3n=\boxed{4+12n}.
]

A direct simulator using the original TM63 table and the exact Coq stream orientation reproduces (4,16,28,40,52,64,76,88) for (n=0,ldots,7). The decomposition above explains the coefficient 12 structurally; the finite simulation is corroboration, not the proof.

## Formalization path

- Reuse `counted_left_sweep` with parameter (3n).
- Add a four-step `D)-zero bridge theorem with the three zero hypotheses above.
- Add `counted_right_sweep_B` by copying the induction pattern of `counted_right_sweep`, using the B/F/D transition cycle and the tape update (h\mapsto0,h+1\mapsto0,h+2\mapsto1).
- Prove the `sweptLeft (3*n)` tape identities: the zero reaches (h-3n+1), the d0 boundary remains available for the four-step bridge, and (3n) ones occupy the right-sweep interval beginning at (h-3n+2).
- Compose with `run_append` to obtain a fully quantified, arbitrary-exterior-tape theorem for the `LInc` H-hypothesis.

Then lift this counted H-hypothesis through the same `not_full_Inc` / `LBinDec_spec` argument used by BusyCoq. The repeated carry count is the trailing-one count of the complemented `BinDec) word, hence should become (v_2(k)) for the decremented counter (k) (check the successor convention at the theorem boundary).

This is a promising route to the universal outer-counter decrement used by Rst0/Rst1/Rst2. It does **not** yet prove the complete reset prefix or the exact TM63 score.


## Refined phase-level tape account

The finite trace factorization is now explicit. Let (h) be the initial head position and (h'=h-3n).

- The initial left stream has (d_1^n) at its head, then (d_0), then arbitrary (l); the right stream begins with the distinguished zero and then arbitrary (r).
- The first phase is exactly `counted_left_sweep` with parameter (3n), not a new 9n-step primitive. Its theorem contributes (3(3n)=9n) steps. It shifts the zero left to (h'+1), leaving the d0 boundary zeros at (h'-1,h'), and a run of (3n) ones at (h'+2,ldots,h'+3n+1).
- The base bridge consumes the three zeros at (h'-1,h',h'+1), writes ones there, and ends in state B at (h'+2).
- The new B/F/D sweep consumes the (3n) ones beginning at (h'+2), in (n) groups of three. Each group writes physical (001) and advances the head by three. Its exact tape update must be composed with the preceding left sweep and base bridge; because the target stream is nearest-first, do not identify the physical (001) block naively with the stream word (d_0).
- The composed target is state B at (h+2), with nearest-first left stream ([1] ++ d_0^n ++ d_1 ++ l), and right tail (r). This is the `LInc` H target.

The formal proof obligations are therefore narrowly localized: the four-step bridge, the B-starting right-sweep induction, and the tape-function identity for the composition. The 9n phase is already covered by the existing source-certified `counted_left_sweep` theorem.
