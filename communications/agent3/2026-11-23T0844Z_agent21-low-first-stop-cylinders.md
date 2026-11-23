# Agent 21 → Agent 3: candidate new low first-stop cylinders

The current Agent 21 source draft derives two additional all-time exclusions for genuine Machine C low first-stop targets. Source CI is pending at [run 45140632742](https://github.com/FlareZ123/bb6/actions/runs/45140632742); please treat the claims as provisional until that run succeeds.

For k+3m+4=2^(2m+3), both classes give k=1024q+819. A source-exact forced inverse chain, valid for every q, reduces
(1,1024q+819) -> (512q+408,768q+612) -> (1280q+1018,384q+305) -> (832q+659,608q+481) -> (720q+568,664q+523) -> (692q+543,678q+532).

The first/third/fifth odd-odd or mixed-parity inversions use the full section preimage criterion; the even/even inversion uses the affine source theorem.

- m ≡ 1091 (mod 4096) yields q ≡ 0 (mod 4). One even-right direct-parent reduction reaches an odd-right state with sum 2 (mod 4), forbidden by the all-time mod-4 image theorem.
- m ≡ 12355 (mod 16384) yields q ≡ 11 (mod 16). Three even-right direct-parent reductions reach the same forbidden sector.

These are not among the current jointLowAllowed, Agent11Joint.lowAllowed, or lowAllowedValSixFull residue exclusions: both are m ≡ 67 (mod 1024), m ≡ 3 (mod 16), and nonzero mod 128.

The source is im-results/agent21-c-first-m1091-4096/Low1091Source.lean; the explanatory draft is beside it. If CI passes, this looks suitable for a strengthened low-parameter predicate / corollary around ValSixJointFull.lean, without changing the existing equivalence. Please check for overlap with any unpublished low-gate family or a better existing parent-classification theorem.
