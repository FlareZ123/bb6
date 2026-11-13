# Next m=0 even-even sum-zero high-stop candidates

**Status: algebraically derived candidates only. Not Lean-formalized, not source-certified, and not included in results/.**

The source-certified four-family sieve in M0EvenEvenSumZeroResidual.md suggests two immediate extensions. Both use s≡5 (mod 8), so the existing all-s theorem excludes L_s. Their B_s branches reduce by exact six-of-eight parent arithmetic to even-even sum-zero targets with S%4≠0. The generic source parent theorem should then reduce each target to direct and bounce parents; the formulas below indicate both are odd-image forbidden after the stated chains. A future agent should formalize and compile these chains before promoting either family.

## Candidate 5: s=1024w+229

Here t=2s+1=2048w+459, so the high-stop parameters would be

j=14695+65536w,   k=44092+196608w.

The B_s target is

(20664+92160w, 48446+216064w).

Five six-of-eight inverse steps give the sequence

1. (69108+308224w, 24222+108032w)
2. (93328+416256w, 12110+54016w)
3. (105436+470272w, 6054+27008w)
4. (111488+497280w, 3026+13504w)
5. (114512+510784w, 1512+6752w).

The last target has coordinate sum 8S with S=14503+64692w and S%4=3. Its direct parent is

(116022+517536w, 755+3376w),

and its depth-one bounce parent is

(29004+129384w, 44261+197452w).

Both have odd right coordinate and coordinate sum 1 modulo four. If the exact generic parent theorem applies as stated, this closes B_s; L_s is already closed by s%8=5.

## Candidate 6: s=1024w+533

Here t=2s+1=2048w+1067, so the high-stop parameters would be

j=34151+65536w,   k=102460+196608w.

The B_s target is

(48024+92160w, 112590+216064w).

Three six-of-eight inverse steps give

1. (160612+308224w, 56294+108032w)
2. (216904+416256w, 28146+54016w)
3. (245048+470272w, 14072+27008w).

The last target has coordinate sum 8S with S=32390+62160w and S%4=2. Its direct parent is

(259118+497280w, 7035+13504w),

which is odd-image forbidden. Its bounce parent is

(64778+124320w, 104202+199984w).

That bounce parent has even right coordinate and sum 4 modulo eight. One six-of-eight inverse gives

(168978+324304w, 52100+99992w),

whose sum is 6 modulo eight. A second gives

(221076+424296w, 26049+49996w),

which is odd-right and has sum 1 modulo four. Thus the bounce branch also appears closed, conditional on formalizing the exact parent and six-of-eight steps.

## Potential coverage gain

The two candidate t-cylinders, t≡459 (mod 2048) and t≡1067 (mod 2048), are disjoint from each other and from the four source-certified cylinders. If both are proved, the odd-t parameter density would rise from 23/512 to 3/64. This is still only a density within the m=0 high-stop parameter ray.

## Suggested formalization

Add source theorems blank_no_B_s229, blank_no_A_s229, blank_no_high_m0_j14695, high_stop_mzero_14695 and their s=533 analogues to the standalone BB6.Agent11M0SumZeroVerified module. Reuse blank_no_L_s_mod8_five, blank_no_sumzero_target, six_even_right_blank_reach_iff, blank_no_odd_sum_one, and mzero_first_two_reach. Do not mark these candidates proven until the original-source Lean CI passes with no sorryAx.
