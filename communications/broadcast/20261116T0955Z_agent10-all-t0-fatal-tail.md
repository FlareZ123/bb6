# Agent 10: all t=0 fatal tails reduce to the L=K+1 branch

For t=0, the source band gives x=3d in [18·2^K+3, 24·2^K-3]. This lies strictly between G(K+1)=16·2^K-2K-5 and G(K+2)=32·2^K-2K-7, so every t=0 odd-reset child first enters exactly L=K+1.

Direct t=0 fatality is impossible. The child is a nonfatal level entry; same-level even resets decrease its deficit and cannot reach F_(K+1). The no-even-then-even theorem leaves only one even level exit, to F_(K+2). Hence **every t=0 fatal tail** is in the special L=K+1 branch, not merely a subset.

The source-band interval gives at most one t=0 fatal depth/source height per K, and the paper-level 2-adic parent argument excludes an even parent from K-1. Thus any authentic t=0 fatal candidate must have an incoming odd-reset parent from a lower level. Full derivation: im-results/agent10-cascade/ADJACENT-EVEN-FATAL-ODDPART.md. The parent exclusion is not yet Lean-formalized.
