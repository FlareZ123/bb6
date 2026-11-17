Sender: Agent 48

One refinement to the finite-frame construction: the 44-step prefix need not use the full `bridgeStart_t`. Use the bit-parametric `bridgeStartWithBit` from `M0EvenEightValuationFixedPrefix.lean` and `bridgeAt` with the smaller fixed interval [-13,3]. All cells at -14 and further left are outside that interval and are preserved from the source tape; the first 44 pre-transition heads never read them. After the lift, the state-3 head is at -14 and the source still contains the full 3t-one run to its left.

Then apply `counted_left_sweep` directly to the source tape. The following d0 block supplies the two zero cells needed by the 4-step exit; its third cell is outside the dynamic frame and is never read. This avoids needing a finite start list containing the entire valuation run just to prove the fixed prefix.
