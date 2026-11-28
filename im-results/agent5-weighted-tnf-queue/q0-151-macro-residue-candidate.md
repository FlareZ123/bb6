# q0-151 F0-open: finite macro grammar certificate candidate

Partial table `1RB1LC_1RC0RD_0LA1RD_1RB0RE_1LC1RF_---0RC`. Do not count this leaf resolved until the source macro semantics and abstraction closure are kernel-certified.

## Exact macro semantics (discovery)
At B or C, the right word is a finite list of positive 1-run lengths separated by single zeros, with blank suffix. Left is a stack of marker-free binary segments separated by 00. Current segment S begins and ends 1; saved segments begin/end 1 or are empty exterior blanks. Pushing a marker stores S and creates new segment. Popping nearest 00 converts it and a two-bit guard to 1111, restores previous S++1111, and scans the transferred current segment as right word. Infinite exterior blank pairs supply empty segments.

Write A=10, W=unprocessed suffix beginning with1 or empty. B and C macros on a run of length 4a+r:
- r=1: B,a=0 appends 01, B; B,a>0 pushes 00 and sets S=A^(2a-1)11, B; C appends A^(2a)11, B.
- r=0,a≥1: B pushes and sets S=A^(2a-2)111, C; C appends A^(2a-1)111, C.
- r=2,a>0 at B: a local push/pop extends S by 1111, right becomes A^(2a-1)1W, B.
- r=2 at C: pop previous marker transferring S A^(2a)1W.
- r=2,a=0 at B: W empty → pop transferring S1111; W starts run of length 4j+1 → pop transferring S111V if j=0, or S1110 A^(2j-1)1V if j>0, where V is after that run; W starts run 4j (j≥1) → append S1110 A^(2j-1)11, B at V. W starting residue2 is unsafe.
- B at blank: pop transferring S. C at blank (S ends three ones): pop transferring S with final 1 removed.
- residue3 at B/C is unsafe.

The left scan is exact: at C with right guard10, left head1 takes 5 steps to move one cell left while transferring a 1 into right behind guard; left head0 with previous left1 takes 2 steps to move two left while transferring 10; left 00 takes 5 steps to pop and form 1111. Right E-loop on 1111 consumes it in 4 steps, outputs 1010. These gadgets need source proofs.

## Candidate inductive abstraction
Use 2 modes N,P for run residues: 1 keeps mode; 0 sets P; 2 allowed only P then sets N; 3 disallowed. Both modes accept end. Thus no3, and between any two residue2 runs there must be a residue0. Right word type is a set of starting modes (P or both), and END distinguishes exactly empty. Keep first run category separately: length 1,2,3,4 exact; lengths >=5 encoded 5+((n-1)%4). For remaining suffix store its exact mode set, or END. Left segment summary: first closed run category (optional); transformation of modes through further closed runs; last partial run category. Concatenation computes exact first category and residual acceptance type. All macro output repetitions of 10 have summary effects saturated once at least two copies are seen; representative parameter a=3 covers all a≥3, with categories enforcing a=0,1,>=1,>=2 as appropriate.

Start B with S=1, empty right and empty saved stack after initial A0. Compute fixed point on control (q, right summary, current left summary), and a set of possible saved left summaries (initial empty). For pushes add saved symbol, for pops allow EVERY saved summary independently, restore it by appending 1111. Computed finite closure: 814 control states, 50 saved segment summaries, zero bad transitions. Matched pushdown saturation also passes (786 states), but the coarser 814-state invariant is simpler and stronger. This candidate is mathematically distinct from failed raw FAR search. First-run category and END must be preserved: dropping either introduces spurious bad branches.

The discovery Python implementation is adjacent. Need formalize source macros and category/concatenation exactness, then prove finite closure with kernel-reduced certificate. No unbounded conclusion yet. Authentic q0-148 is independently closed; parent CI run 46117423502 queued.
