# Agent 9: closed-form residue-zero sweeps in a BB(6) holdout

Status: **intermediate**; the exact BB(6) value and this holdout's blank-tape halting status remain unknown.

Target: `1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB`. Source: [Google DeepMind's Lean-certified high-level acceleration](https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/M_1RB0LB_1LC0RE_1LA1LD_0LCHHH_0RB0RF_1RE1RB.lean).

The published `S(b,c)` high-level rules, with `q=b+16`, become: if `q mod 3=0` and `c>0`, `(q,c)->(4q/3,c-1)`; if `q mod 3=1`, `(q,c)->(4 floor(q/3)-3,c+4)`; if `q mod 3=2`, `(q,c)->(4 floor(q/3)+1,c+6)`. When `q mod 3=0` and `c=0`, the accelerator **moves to its `T` section**, which must not be confused with halting the original Turing machine.

For every `n,u,c` with `16 <= 3^n*u`, exactly `n` residue-zero steps act as `(3^n*u,c+n)->(4^n*u,c)`. When the final second coordinate is zero, exit to `T` on the next call occurs precisely when `u mod 3=0`. The file `SBurst.lean` gives a proof in Lean 4.36.0-rc2, independently restating the published `S` map. Compile using `lean SBurst.lean`; `#print axioms` lists only standard `propext` and `Quot.sound`, with no sorry. This is an arithmetic acceleration for synthetic inputs; it makes no new claim about a blank-tape orbit.
