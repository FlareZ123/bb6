# Arbitrary-word A-tail and mixed D recurrence

Four main theorems locally checked by Lean 4.36.0-rc2 with axioms [propext, Quot.sound]: Raw14042AWord.bounce, mixTail, Raw14042DMixed.pair, pairs.

The first provides a direct word-preserving bounce on arbitrary W in {1,5}*:

    ER(1X, W s) -> EL(X,1 W (115)^carry(s)next(s)).

Here s is the existing A six-tail cycle; arbitrary left context X and arbitrary word W. Forward scans transfer each 1 to encoded 3 and each 5 to encoded 1, then a fixed suffix bridge changes s. Reverse scans use EL3 and EL(1X,1Y)->EL(X,15Y). Thus the word is reconstructed in its original order.

The D mixed recurrence is:

    DL(66X,4^a 2 1^b 5 W s)
      -> DL(X,4^(a+1) 2 1^(b+1) 5 W (115)^carry(s)next(s)), a,b>=1.

First lift and scan all a fours, use the local marker bridge CR(4Z,421Y)->DL(55Z,05Y), and sweep the resulting a+1 fives. Next scan all a+1 fours, invoke mixTail (which composes CR(4Z,405Y)->ER(1255Z,Y), the arbitrary-word bounce, and EL(255Z,Y)->DL(5Z,21Y)), and sweep a+1 fives. pairs proves k iterations and exact carry accumulation. No variant row used.

Generate Raw14042AWordLocal.lean with generate_raw140_42_aword.py. Compile Raw14042DMixed against the Raw140ERSuffix and Raw140DoubleLocal closure.

The C terminal 35221 at exponent p enters DL(6^(p+1)4,4215542), and finite first four left-six iterations give DL(6^(p-3)4,444211151121). This is P(a=3,b=3,W empty,s=1121) in mathematical exponents. The pair theorem now gives exact large-bank growth. Depletion and exit must still be composed. The earlier B62542 (p even) paper-level arithmetic reduction is B->C(3p+18,p/4-1,rank1) for p divisible by 4, and C(2p+4,floor((p/2+1)/6),(p/2+1)%6) otherwise. Tested on even p=16..44; not yet source-composed. Candidate arithmetic orbit then reaches C-terminal 35221 at p=824490759875322. This is not a blank-root proof.
