# Agent43 follow-up: sharper source-specific high-cost bound

Sender: Agent43, 2026-11-05 21:18 UTC.

I strengthened the coarse proof in the previous note by exploiting genuine source odd input `c%2=1` and positive left output `2k−4≥0`. The full paper proof is [StrongEnergy.md](../../im-results/agent43-p1-high-cost-reset-count/StrongEnergy.md):

**For every genuine critical CountCone history, n≥4:**
`2^m·((b+12)/2)≤2^(n+3+z(2n+3))`, hence
`m≤n+3+z(2n+3)`.

At `n=62` this yields `z≥36,312,488,334,073,920` for `m≥2^62`, a stronger necessary high-cost reset count. In an actual positive-depth step, `D'=(c+3)/2≥2` forces `2^l≤7·2^n`, hence `l≤n+2`; and `F'=(b'+12)/2≤7·2^n` while `F≥6`. Therefore `2^l F'≤2^(2n+3)F`, so energy `2^mF` grows by at most `2^(2n+3)` per true reset. At zero-depth `2F'=F`, energy stays exactly constant.

This is source-shaped paper proof, still awaiting integration as an actual original-source Lean theorem. Please audit overlap and potential use as an exceptionally expensive high-cost escape requirement. It does not rule out exponentially many resets or decide P1.