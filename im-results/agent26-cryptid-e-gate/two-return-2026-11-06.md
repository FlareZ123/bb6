# Two-return D-start cryptid identities (Agent 26, 2026-11-06)

Intermediate, source-connected symbolic work. Exact BB(6) is unresolved; these are conditional synthetic F-section returns, not blank-root decisions.

With I_n(Y) the F/0 blank-left section carrying right tape 1^nY, and P_q=(10)^q:

* For all t,q,Y: I_(9t+7)(0 P_q 1101010111 Y) reaches I_(64t+33)((01)^2 0 1^(2q+3) (01)^4 0Y) in exactly 876t²+1187t+454+4q raw steps. Source E1101010111ThenE.lean, successful original-source CI 42133588002.
* For all t,u,Y with an extra literal zero after the exceptional word: I_(9t+10)(0 P_(3u+2) 1101010111 0Y) reaches I_(64t+16u+93)(Y) in exactly 876t²+384tu+2411t+48u²+554u+1729 raw steps. Sources E1101010111ThenAFive.lean and E1101010111ThenAFivePolynomial.lean, successful original-source CI 42134719036.
* Candidate for q=3u+1 with the same zero guard: I_(9t+10)(0 P_(3u+1) 1101010111 0Y) reaches I_(64t+16u+71)(0 1^14 Y) in 876t²+384tu+2219t+48u²+506u+1472 raw steps. Sources E1101010111ThenAQ1.lean and E1101010111ThenAQ1Polynomial.lean. The first CI 42135112492 failed at a boundary rewrite; subsequent corrected source passed all full original-source Lean modules including the explicit polynomial in manual CI 42135505118. Only standard Lean axioms were printed. The first failed CI is superseded.

Both successful CI proofs print standard axioms only. The E-to-E branch has 715 independent raw first-return regressions. Genuine blank-root reachability and uniform word-language closure remain open. Keep this intermediate work in im-results/.
