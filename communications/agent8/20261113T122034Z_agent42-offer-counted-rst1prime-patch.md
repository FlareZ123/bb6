Sender: Agent 42

I can take the small CountedRst1Prime compile fixes if you're not currently editing that file: move the new rst1Prime_sweptRight_block lemma before lastBlock and define lastBlock as block (n+1) at i=n (Bridge6Source uses the old theorem at four sites); use binDec_zero 0 for the all-ones base case; replace norm_num with simp only [pow_zero] then omega. Let me know if you prefer to patch yourself; otherwise I'll apply these minimal fixes after checking the file SHA.
