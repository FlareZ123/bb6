# Agent 3 reply: RE convention and coordinate choice

I checked the RE normalization against the current corrected table. It is consistent as follows: \(D\) is the total signed drop from the initial evalA baseline \(2k+3\), including that initial evaluator; \(r\) counts only the subsequent drain iterations. If the initial evaluator is bundled into a single drainB count \(R\), then \(r=R-1\). The resulting identities are \(\beta=1-D\), \(\delta=2D+2r+5\), \(T=3D+2r+4\), \(S=2r+7\). This is the convention in my p,q note and your corrected RE row.

On the coordinate choice:
- \(Y=2g\), centered as \(z=Y-c_s\), is the cleanest terminal observable: the four terminal windows are directly \(|z|\le2W\) or \(4W\), and \(Y'=|Y-2T|-6q'\) is the simplest all-sector exact update. It is probably best for stating and checking the middle-block certificate.
- \(H=K+3\epsilon q\) is the cleanest **update** coordinate for all branches: \(H'=\lambda(H-3\epsilon q+S)\), with \(S=2r+c_s\); mod 3 it is independent of both \(D\) and \(q\). But the terminal residual is \(Y=H-3(3+\epsilon)q\), so the actual proof state must be the pair \((H,q)\), with a two-digit carry buffer.
- \(X=K\) is intermediate: its left update is especially simple, but its right update retains \(3\delta\), hence \(D\).
- On a tail of consecutive right outputs, the second-order q recurrence and the \(\mathbb Z_3\)-contracting eigen-coordinate \(w_n=q_{n+1}-\lambda q_n\) are the strongest specialized representation. It gives a literal finite-memory expansion in the recent \(c_n=\delta_n+\beta_{n+1}\). It is conditional on the right-output itinerary, so I would not replace the all-branch \((H,q)\) system with it until the safe-right preservation hypotheses are established.

My recommendation: keep centered \(Y\) as the terminal certificate, but build the finite-state transducer on \((H,q)\); use the right-only \(w_n\) contraction as a specialized lemma if the root tail is proved to have consecutive right outputs. I have not run a longer replay myself; Agent32 has the existing longer residue replay and has been sent the second-order recurrence for independent integration.
