# Sibling 42: closed candidate even-bank arithmetic system

This is a candidate full orbit model, not a complete Lean nonhalting certificate. All three mixed bank recurrences and their general word operations have local kernel proofs (linked below). Source composition of all terminal formulas and the exact initial entry remains required.

The three ordinary banks A,B,C have a homogeneous left exponent p, triplet count n, and tail rank s in 0..5. The large-bank recurrence is p += 12 and z = 6n+s decreases by 11. Therefore the terminal has n=0 or 1. For all reachable banks in the candidate, p is even and at least 20. In particular odd mixed A and B terminals are unnecessary for this invariant. The candidate arithmetic program raw140_42_arithmetic.py defines the 36 even-exponent terminal cases plus ordinary D/A0/A2/B0 auxiliary sections. Its 100,000-step calculation from A(12472,0,3) visits every terminal and finds no missing branch. This is a finite check of a model, not a proof of the machine or even the induction on all input exponents.

## New exact return from the exceptional A-tail 11

Lean checked Raw14042ExtraTail.return11:

    AR(3^p2,(115)^(n+2)11) -> AR(3^(p+12)2,(115)^n542), p>=1.

The 49-step framed prep ER(1X,11)->EL(3X,542) is combined with transferMany42 and start42. Axiom set [propext, Classical.choice, Quot.sound]. This returns the C35221 exceptional exit to the ordinary A-bank.

## Remaining C terminals

C315 at p even enters DL(6^(p+2)4,46221); dIter starts with right word 4 and right-tail rank 2. Hence it yields B(2p+8,floor((p+4)/6),(p+4)%6). This is a direct paper specialization of the already-proved dIter/dEndE/eEven.

For C35221 p even, the checked mixed D pair gives a=b=p/2+1 after the residual 6 is consumed. In detail, j=(p-4)/2, a=3+j, (n,s)=divmod(j+2,6). After phase1 the configuration is DL(4,4^(a+1)05 1^(a-1)5(115)^n s). If a odd (p divisible by 4), dEndE and eIter leave a single four before 05. The common marker conversion followed by odd pumping of the ones produces A(2p+10,n,s). If a even (p = 2 mod 4), eEven yields BR(5^(2a+4),05 1^(a-1)5(115)^n s). The 20-step prefix enters ER(1115^(2a+3),1^(a-1)5(115)^n s). The remaining coupled bank rotates the A suffix and generates the exceptional tail 11, with output AR(3^(3p+26)2,(115)^floor(p/4)11). Applying return11 yields A(3p+38,p/4-2,0). These latter depletion formulas were verified on small even examples, and require an unbounded symbolic proof.

Prior local mixed proof modules: Raw14042Mixed, Raw14042BMixed, Raw14042BMixedEnd, Raw14042Word, Raw14042AWord, Raw14042DMixed. Related dossiers Raw14042Mixed.md, Raw14042BMixed.md, Raw14042Word.md, Raw14042DMixed.md. The authentic root and all large-bank return paths must be linked before reporting the sibling or the parent solved.

Reproduce the new local proof using generate_raw140_42_extratail.py to generate Raw14042ExtraTailLocal.lean; then compile Raw14042ExtraTail.lean against the Raw14042Bank dependency closure with Lean 4.36.0-rc2. The exact literal source is M42 in Raw140VariantTransfer.
