# Sibling 42: even-bank invariant and source proof obligations

The arithmetic system is inductively closed, with a **kernel-checked authentic blank entry** into B(32,1,1) at primitive time 5,985. The missing obligation is the complete positive-time source realization of its step function. No nonhalting Cover is claimed yet.

## Arithmetic closure

The A,B,C sections have homogeneous left exponent p, triplet count n, and tail rank s in 0..5. The large-bank recurrence adds 12 to p and subtracts 11 from z=6n+s. Hence its terminal has n=0 or 1. The existing [Raw14042ArithmeticInvariant.lean](Raw14042ArithmeticInvariant.lean) proves preservation of p>=24, p even, and s<6 for every arithmetic transition, including all 36 terminal cases. Odd mixed A and B terminals are therefore unnecessary for this invariant.

[Raw14042Growth.lean](Raw14042Growth.lean) extends that prior result: every arithmetic step increases p by at least 12; the orbit starting at B(32,1,1) satisfies p>=32+12k at section index k. Its conditional `root_unbounded` proves that every primitive prefix of M42 exists once a section encoding, its exact root equality, and a positive-time source step theorem are supplied. This eliminates the need for further bounded scans of the arithmetic model.

## Authentic entry

[Raw14042Entry.lean](Raw14042Entry.lean) proves `run M42 5985 primBlank = some rootS5.prim` with rootS5 = BR(5^32,64464). Five exact RLE macro segments (256,256,256,256,152 events after the first two primitive steps) have primitive costs 1045,779,769,773,2617. This short certified root bypasses the earlier longer entry route via A(12472,0,3).

## General D return

[Raw14042DGeneral.lean](Raw14042DGeneral.lean) proves for arbitrary k,h and initial B-tail s, provided k+h is odd:

    DL(6^k4,4^h tail(s))
       -> BR(5^(2(k+h)+2),(644)^floor((k+rank(s))/6) tail(t)),
    rank(t) = (k+rank(s)) mod 6.

The common-table dIter/dEndE/eEven composition is lifted to M42. This directly provides all odd-total D auxiliary returns, including h=11, and the D phase of C315 (k=p+2,h=1,rank(s)=2), whose result is B(2p+8,floor((p+4)/6),(p+4)%6). All ten terminal-to-D paths are now composed in `Raw14042DTerminals.lean` (6e0102cc).

## Terminal source progress

34 of 36 terminal families have local kernel-checked symbolic source reachability proofs: ten D routes in `Raw14042DTerminals`, ten even C routes and three direct returns in `Raw14042CTerminals` (223ef72a), and ten odd B routes in `Raw14042BTerminals` (e35531fe). General C and B returns are in `Raw14042CGeneral` (c38b824a) and `Raw14042BGeneral` (478ebeda). Local long affine witnesses were split into shorter checked segments; original generated dependency closure CI remains to be completed. The two mixed terminal families B62542 and C35221 now have full depletion proofs, both odd-bank exits, and the complete even C-bank exit (see below). The even B-bank exit and common encoding/positive-time step remain.

## A5215 resolved for both even-exponent classes

For p>=24 even, let j=(p-8)/2. [Raw14042AMixedTerminal.lean](Raw14042AMixedTerminal.lean) proves the exact common depletion into BL([],2^(j+6)46 4^(j+3)(644)^floor((j+5)/6)tail(s)), rank(s)=(j+5)%6. [Raw14042MixedOuter.lean](Raw14042MixedOuter.lean) supplies exact framed conversions and repeated pumps. When j is odd, `a5215_mod2` returns B(2p+6,floor((j+5)/6),(j+5)%6). When j is even, [Raw14042AMixedEven.lean](Raw14042AMixedEven.lean) supplies a new 66 boundary sweep, D iteration, two E banks and two consumed 644 triplets; `a5215_mod0` returns B(3p+20,p/4-1,1). Both theorems are source-level Reach M42 results, compiled locally under Lean 4.36.0-rc2 with [propext, Classical.choice, Quot.sound]. The new intermediate sweep theorems require only [propext, Quot.sound]. Commits 7dc9d1bb and 8ed47fed. No Cover reduction claimed.

## Remaining terminal realization

The prior exact local proof `Raw14042ExtraTail.return11` provides

    AR(3^p2,(115)^(n+2)11) -> AR(3^(p+12)2,(115)^n542), p>=1.

The 49-step framed prep ER(1X,11)->EL(3X,542) is combined with transferMany42 and start42. This returns the C35221 exceptional exit to the ordinary A-bank.

For C35221 p even, the checked mixed D pair gives a=b=p/2+1 after the residual 6 is consumed. In detail, j=(p-4)/2, a=3+j, (n,s)=divmod(j+2,6). After phase1 the configuration is DL(4,4^(a+1)05 1^(a-1)5(115)^n s). If a odd (p divisible by 4), dEndE and eIter leave a single four before 05. The common marker conversion followed by odd pumping of the ones produces A(2p+10,n,s). If a even (p = 2 mod 4), eEven yields BR(5^(2a+4),05 1^(a-1)5(115)^n s). The 20-step prefix enters ER(1115^(2a+3),1^(a-1)5(115)^n s). The remaining coupled bank rotates the A suffix and generates exceptional tail 11, with output AR(3^(3p+26)2,(115)^floor(p/4)11). Applying return11 yields A(3p+38,p/4-2,0). The outer composition is now kernel-checked in `Raw14042MixedExitEvenC.cEvenExit` (p=4k+6 gives A(12k+44,k+1,11) before return11). `Raw14042MixedFront.cDeplete` and `.bDeplete` establish both arbitrary-length mixed depletions; `Raw14042MixedExitOdd.cExit` and `.bExit` establish the complementary odd-bank exits with arbitrary suffixes. All five new reachability laws require only propext and Quot.sound. The exact even B exit and terminal-level assembly remain; no Cover is claimed.

Prior local mixed proof modules: Raw14042Mixed, Raw14042BMixed, Raw14042BMixedEnd, Raw14042Word, Raw14042AWord, Raw14042DMixed. Related dossiers Raw14042Mixed.md, Raw14042BMixed.md, Raw14042Word.md, Raw14042DMixed.md. All large-bank and terminal source paths must be linked to the arithmetic step function before reporting the sibling or parent solved.

## Reproduction and status

Lean 4.36.0-rc2, original dependency closure from artifact 15220415544, exact literal M42 in Raw140VariantTransfer. Newly compiled Entry, DGeneral and Growth modules have only standard axioms [propext, Classical.choice, Quot.sound] (step_growth needs only propext and Quot.sound). The A5215 modules were locally compiled with the artifact closure plus the original LowLocal and Mixed generators; full current-source CI still pending. Generator fix 744cff7f binds p even when confined to untouched frames; BGeneral exitFront no longer unfolds Reach after introducing the existential witness. Monolithic LowLocal (2.62 MB) exceeded local memory and will be split at theorem boundaries. Reproduce ExtraTailLocal with generate_raw140_42_extratail.py, then compile Raw14042ExtraTail.lean against the Raw14042Bank dependency closure.
