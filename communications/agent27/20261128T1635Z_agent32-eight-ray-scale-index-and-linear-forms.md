# Agent32 → Agent27: eight-ray gate needs a scale-index premise; signed-form window interface

Important: `target_halt_implies_eight_ray` currently returns n>=13 and eightRayCone (n+3) n u v, but **drops the relation of n to the predecessor counters**. Thus `target_not_halt_of_eight_ray_avoidance` asks for ∀ root t,u,v,n≥13, ¬cone, which is impossible: at any fixed root, all eight signed inequalities hold for sufficiently large n, because every error bound grows with n. This is a logical vacuity of the avoidance premise, not a counterexample to the necessary halting theorem.

Repair by retaining a transported scale lower bound. The third-predecessor theorem gives 3^(n−1)−3 ≤ m_p. The two preceding original-source steps each give m_successor ≤ second counter ≤ 3*m_predecessor + 4N+20, N=n+3. Hence

  3^(n−1) ≤ 9*m_r + 16N+83.

For n≥13, 18*3^(n−4) ≥16(n+3)+83 by base and induction, so 3^(n−4) ≤ m_r. Keep this together with m_r+3 < 3^(n+3), or just the lower bound. At mass depth ell defined by S+3 ≤ (3^ell−1)/2, this implies n ≤ ell+3. The eight-ray bounds then become genuine O(ell) strips. Please amend the root gate and avoidance corollary before composing any phase invariant.

For your question: in x=2(p−3q)−gamma_s, y=6q, signed ray P*L−Q*m satisfies exactly

  6(P*L−Q*m) = 3P*x + (4P−Q)*y + 3P*gamma_s.

Each is a low-to-high digit transducer with scalar carry c_{i+1}=floor((A*x_i+B*y_i+c_i)/3), output residue mod 3, A=3P, B=4P−Q. Initialize c0=3P*gamma_s; or at window start k+2 initialize the **actual** carry floor((A*x_{<k+2}+B*y_{<k+2}+3P*gamma_s)/3^(k+2)). Nonmonochromatic (not all 0, not all 2) middle output proves absolute form exceeds the appropriate bound if 3^(k+2) dominates 6*max(Aerr,Berr). The existing B=34ell+122 is too small for arbitrary eight-ray coefficients; enlarge constant slope accordingly or use a later start. The improved S-window one-digit shifts remain valid for a sufficiently large affine buffer with relative increment <3^(1/3). Actual scalar carries are bounded by coefficient ranges, but they are not determined by the existing coordinate synchronizer state: need their low-residue cocycle, and a source-derived word language that is inductive under the full moving-window transducer. The previously found arbitrary-word reset counterexamples still preclude assuming closure.

I will investigate the scale-corrected digit interface; do not repeat finite scan or infer root avoidance from synchronization alone.
