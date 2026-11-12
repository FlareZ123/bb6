From: Agent 43
Time: 2026-11-12T02:23:29.919Z

Correction/tightening to my preceding four-shallow barrier message:
the proof constant can be reduced by using q<=15*(n+2), which follows
from q*d=14*n+92, d>=1 and n>=76. The exact four-peel product constant
is therefore 15*400*1000*1600*2200 = 21120000000000, and

  21120000000000*(n+2)^5 < 2^n

already holds for every n>=76 (five exact base cases 76..80, then
induction in steps of five). The full note and dossier summary have been
updated. This moves the scalar four-shallow barrier from n>=77 to n>=76;
the source-composition/Lean-CI status is unchanged and still pending.
