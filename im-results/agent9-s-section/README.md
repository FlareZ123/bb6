# Agent 9: closed-form residue-zero sweeps in a BB(6) holdout

Status: **intermediate**; the exact BB(6) value and this holdout's blank-tape halting status remain unknown.

Target: `1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB`. Source: [Google DeepMind's Lean-certified high-level acceleration](https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/M_1RB0LB_1LC0RE_1LA1LD_0LCHHH_0RB0RF_1RE1RB.lean).

The published `S(b,c)` high-level rules, with `q=b+16`, become: if `q mod 3=0` and `c>0`, `(q,c)->(4q/3,c-1)`; if `q mod 3=1`, `(q,c)->(4 floor(q/3)-3,c+4)`; if `q mod 3=2`, `(q,c)->(4 floor(q/3)+1,c+6)`. When `q mod 3=0` and `c=0`, the accelerator **moves to its `T` section**, which must not be confused with halting the original Turing machine.

For every `n,u,c` with `16 <= 3^n*u`, exactly `n` residue-zero steps act as `(3^n*u,c+n)->(4^n*u,c)`. When the final second coordinate is zero, exit to `T` on the next call occurs precisely when `u mod 3=0`. The complete source for `SBurst.lean` is preserved as five ordered base64-gzip shards `lean-gzip-01.txt`, `lean-gzip-02.txt`, `lean-gzip-03.txt`, `lean-gzip-04a.txt`, and `lean-gzip-04b.txt`. Run `python reconstruct.py` (requires the `filelock` Python package) to reconstitute the Lean source using a checksum-verified atomic write, then `lean SBurst.lean` with Lean 4.36.0-rc2. Its SHA-256 must be `0796a6dc7a3c1ff4beecd888a0545bf8ee2557497d9e0bec8da5e25a5d2b816c`. All `#print axioms` show only standard `propext` and `Quot.sound`, with no sorry. The source independently restates the published `S` map. This is an arithmetic acceleration for synthetic inputs; it makes no new claim about a blank-tape orbit.
