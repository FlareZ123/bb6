# Agent 2: E-triple first-return verification and exact ladder index

Original six-state machine: `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`.

**Original source Lean4.36 local certification:** [ETripleFullSource.lean](ETripleFullSource.lean) establishes the universal strict first F/0 return `I_(3k+4)(0(10)^q111ys) → I_(8k+9)((01)^(q+2)0ys)` at `12k²+49k+58+6q` primitive steps, with no intervening physical F/0. [ETripleLadderSource.lean](ETripleLadderSource.lean) inductively proves that **every** positive F/0 checkpoint through arbitrary `m` consecutive E sections occurs at its specified recursive return time. Both compile locally against SHA-verified original `Boundary.lean` and unchanged original dependency blobs. Audits: first theorem `[propext, Quot.sound]`; the all-times equivalence `[propext, Classical.choice, Quot.sound]`.

**Power-normalized source theorem:** [ETripleLadderIndex.lean](ETripleLadderIndex.lean) locally proves original-run `power_ladder_source` for all m,u,q,ys. In the notation `I_n(r)`, input `I_(3^(m+1)(u+1)+1)(0(10)^q 1^(3m+3) 0 ys)` reaches `I_(3*8^m(u+1)+1)(0(10)^(q+2m) 111 0 ys)` in exact recursive `totalCost m u q` steps. Its index and endpoint proofs print only `[propext, Quot.sound]`.

**Arithmetic closed-form derivation (paper, independently checked against 1,404 exact recursive examples; not separately Lean certified):** set `v=u+1`. Then

```text
totalCost(m,u,q)
 = 108*v²*(64^m-9^m)/55
   + 15*v*(8^m-3^m)
   + 6*m²+(6q+15)*m.
```

At intermediate stage j (0<=j<m), `k_j+1=8^j*3^(m-j)*v`, `q_j=q+2j`. Thus the stage cost expands to `12(k_j+1)²+25(k_j+1)+21+6q+12j`. Sum the two finite geometric progressions and the arithmetic progression. Divisibility by 55 follows from `64≡9 (mod55)`. This formula is an exact mathematical derivation from the source-certified stage recurrence, but no new standalone Lean cost-formula theorem is claimed.

**Scope:** all these theorems concern specially prepared synthetic physical F/0 configurations; membership in an original blank-tape trajectory remains unknown. The 11-case rooted observation SourceContract remains unproved. The GitHub committed text modules were reconstructed from locally compiled text, so an independent exact-remote-byte source build is still required when Actions runners recover. Separate literal 12-rule simulator [test_e_triple_first.py](test_e_triple_first.py) passed 9,444 configurations and 5,079,807 primitive transitions. This is intermediate mathematical work, not a BB(6) determination.

**Byte-exact crosscheck:** The locally compiled `ETripleLadderIndex.lean` git-blob hash matches the committed blob `131db0c1216bcccb39e013289b11ad57d6883f13`; `ETripleLadderSafe.lean` also matches its committed blob `43f4ae3fadfe1d1d3544e1585e4fa9544cf544b0`. These exact committed files compile locally against source-built dependencies. The other newly committed source files have 2–6-byte differences from their compiled local copies, so independent exact-blob verification remains appropriate.
