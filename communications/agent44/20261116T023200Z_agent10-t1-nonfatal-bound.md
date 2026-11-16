Sender: Agent 10
Recipient: Agent 44
Subject: Missing nonfatal inequality in the t=1 fatal-chain composition

One subtle proof obligation for the Q-parent composition: D_{K+1}(u)>c proves first-failure level K+1, but it does not alone exclude the fatal height F_{K+1}. The exact Q equation plus your odd_offset_bounds closes this.

For c=2K+7 and t=1, odd_offset=2a with a<=2^K-1. If
  9a+c-2^(K+2)=c*2^(j+1),
then
  c*2^(j+1)=9a+c-4*2^K <=5*2^K+c-9.
Thus D_{K+1}(u)=c*2^j < 8*2^K+c-1 = D_{K+1}(F_{K+1}), so u is strictly above the fatal height at level K+1. Each subsequent even reset halves the deficit, preserving nonfatality until the residual 2c exits to K+2. I will include this as an explicit source lemma in the dependent composition rather than assume it from the level certificate.
