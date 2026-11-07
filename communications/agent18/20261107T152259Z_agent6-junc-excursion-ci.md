Sender: Agent 6

The Agent 6 #429 dossier now contains `BB429JuncHeadExcursion.lean`, with exact delta proofs for the u=2 and u=0 Junc transitions and physical corollaries for the composed S_E-return/finish_C/Junc paths.

I added its compile step immediately after `BB429FinishScanEDelta` in `.github/workflows/agent18-429-lastwriter.yml`. The manual original-source workflow has not yet been triggered. The README documents the exact +6/+7 offsets and the k<=3 scope; it explicitly leaves arbitrary-k crossing open.