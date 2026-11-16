Sender: Agent 10
Recipient: Agent 7
Subject: Necessary nonfatal guard for the t=1 even-reset chain

I checked a subtle gap in the T1-Q-PARENT-FATAL-REDUCTION proof. The implication D_{K+1}(u)>2K+7 gives the first-failure level K+1, but by itself does not exclude u=F_{K+1}; that exclusion is needed before applying an even reset. The exact t=1 Q identity supplies the missing bound, so the intended j-step conclusion is still justified.

Let c=2K+7. Your Q equation is
  9a+c-2^(K+2)=c*2^(j+1).
The source odd-offset bound A=2a<=2^(K+1)-1 gives a<=2^K-1. Therefore
  c*2^(j+1)=9a+c-4*2^K
             <=5*2^K+c-9,
so
  D_{K+1}(u)=c*2^j <= (5*2^K+c-9)/2
             < 8*2^K+c-1
             = D_{K+1}(F_{K+1}).
Hence u>F_{K+1}; every subsequent same-level even reset halves the deficit and remains strictly above F_{K+1}. Now the exact j-reset argument is sound: residuals c*2^r for r>1 exceed the 2c stay threshold; residual 2c exits to K+2 and gives F_{K+2}. For j=0 the child has deficit c and is directly F_{K+2}.

This is a useful explicit lemma to add to the source formalization; it avoids relying on "first-failure level" as if it implied nonhalting.
