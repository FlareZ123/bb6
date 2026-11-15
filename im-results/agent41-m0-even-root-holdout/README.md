# m=0, n=8q+6 small-instance replay

The candidate middle17 root prefix ends in the marker-0 family
\[
S_1(L,8q+6,0,a,0,b,h),
\]
with the actual root parameters q=4k+1 and very large L,a,b. A direct
small-instance search did not find the q4 reset pattern used by the preceding
rows, so this directory records a finite exploratory replay rather than a
claimed theorem.

## Experimental observations

Using the original TM2 transition table and minimal width L=bit_length(8q+6),
a=1, and q=0..3:

- b=0: q=0 halts after 1,025 steps and q=3 after 11,993; q=1,2 survive 200,000 steps.
- b=1: q=0 halts after 1,583 steps and q=3 after 19,103; q=1,2 survive 200,000 steps.
- b=2: q=0..3 all survive 200,000 steps.

For q=1, a=1, and b=0,1,2, the same 200,000-step survival was observed at widths L=4,5,8,12. At the cutoff the b=0 and b=1 cases are in state3, while b=2 is in state4. Increasing L shifts the leftmost visited coordinate and changes the marked-cell count, so the width is a real part of the initial configuration.

The exact raw observations are reproducible with m0_even_replay.py. The script accepts --max-steps (default 200,000) and prints CSV.

## Evidence boundary

These are finite simulations only. A run that survives the horizon is not a nonhalting proof. The small configurations do not instantiate the actual root, whose q=4k+1, L, a, and b are determined by the large first-section arithmetic. In particular, minimal-width behavior must not be silently promoted to a statement about the authentic root.

The next useful step is to translate the middle17 S1 endpoint into Agent49's upstream highLevelState D(a,d) coordinates and apply the source-verified ternary / fatal-drain analysis, or prove a new invariant for this exact even-zero sector. Do not duplicate an existing m=0,n=16r+7 proof: that is a different earlier row.
