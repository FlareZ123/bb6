# General DFA zero-prefix transient obstruction

**Stronger than the permutation-group argument.** The new proof works for arbitrary deterministic automata on canonical LSB-first binary words. It uses the full prepared-halting residue/phase density theorem established mathematically by [Agent 17](../agent17-sheep-terminal-extension/README.md). The discrete pumping implication is kernel-checked against the actual SheepEven.Step/Steps model; the prepared-density input remains a paper theorem, not an end-to-end Lean theorem.

## Statement

Let D have initial state q0 and zero transition A. Let t be the transient length of the A-orbit of q0 before entering its cycle. Suppose the accepted integer set I is closed under every genuine nonterminal raw section edge and excludes all halting powers. Then every accepted positive nonterminal x=2^a*u (u odd >=3) satisfies a<t.

In particular, if I contains the genuine seed 5, every actual section value has valuation strictly less than t. Any n-state DFA has t<=n-1. The previously recorded exact authentic first-even orbit reaches valuation 18 at return index 366704 (see Agent17's memory, bit length 294398, SHA256 09cedb9c0602e43308a65a8acebef84e87aae678d2471a8a52d536a10bca7928). Thus any such invariant requires at least 20 states and a zero-prefix transient of at least 19. If the actual orbit has unbounded valuation, there can be no regular-language invariant whatsoever. That unboundedness is not proved here.

## Proof

Choose a common period p>0 divisible by all cycles of the zero transition A. There is a global threshold T such that for every automaton state q, A^n(q)=A^m(q) whenever n,m>=T and n=m mod p. For the initial state this holds already at threshold t.

Assume 2^a*u is accepted for some a>=t, with u>=3 odd. All inputs 2^e*u with e>=t and e=a mod p are accepted by zero-prefix periodicity. Their genuine section successors are

    y_e = 2^e*u + e + c,

where c=3 for u=3 and c=(u-1)/2 otherwise. Put delta=e+c and let ell be its canonical binary length. For sufficiently large delta in residue a+c modulo p, e=delta-c>=t and e-ell>=T. In reading order the word of y_e is the word for delta, followed by e-ell zeros, followed by the word for u. Now for any b>=ell+T with b=a mod p, the integer y'=2^b*u+delta has exactly the same automaton outcome: its zero-gap length b-ell agrees modulo p with e-ell and both are at least T. Thus all such y' are accepted.

We show this family contains an entire sufficiently large arithmetic/logarithmic cell. Let p_odd be the odd part of p and let L=lcm(p,ord_(p_odd)(2)), with order 1 for p_odd=1. Restrict b to a mod L and take b large. Then 2^b*u modulo p is constant (dyadic component zero, odd component fixed). Choose fixed real 0<alpha<beta<2^(-T-1). Require

    alpha*2^b < delta < beta*2^b,
    delta = a+c mod p.

The gap inequality b>=ell+T holds because delta<2^(b-T-1). Also e=delta-c tends to infinity and exceeds ell+T and t. As b varies in the fixed congruence class, these are precisely a fixed residue modulo p and the log2 phase interval (a+log2(u+alpha), a+log2(u+beta)) modulo L, for all sufficiently large y in that cell. If needed take an open subinterval not meeting a phase boundary. Each such y has the indicated representation y=2^b*u+delta; its delta has the required residue by the constancy of 2^b*u modulo p. Hence the entire cell is accepted.

Agent17's density theorem already gives a prepared halting state in every even residue/phase cell. For completeness it extends to odd cells: refine any odd progression to x=1+2^h*v, with fixed h>=1 and v odd in a fixed progression (choose any odd positive representative !=1, use its exact valuation of x-1, then fix v modulo twice the original modulus). The genuine maximal odd block sends x to y=1+3^h*v, an even progression. The ratio y/x tends to (3/2)^h. Choose a small open target log-phase interval so all sufficiently large corresponding x are in the desired source phase interval. Even halting density gives y in the target progression and interval; its unique preimage x is a prepared halting state. All sufficiently large members of the accepted cell therefore cannot avoid halting. If p is odd, one can simply refine to the even parity progression. This proves the contradiction.

## Discrete verification

Run reconstruct.py to restore SheepAutomata.lean; use the actual SheepEven.lean reconstructed from ../agent16-sheep-even-return/. Compile SheepEven to .olean and check the new file with LEAN_PATH=. and Lean 4.36.0-rc2. SHA256 of SheepAutomata.lean: 9abe5c90439901736b47737087eb8f95c7efde1ce4ec7f789f7cc21d3cc1604b.

The Lean declarations value_gap, pump, high_valuation_impossible have exactly [propext, Quot.sound]. The last theorem consumes the explicit arithmetic hypothesis PumpDense and the eventual periodicity equations. Those equations are elementary finite-function facts; PumpDense follows by the residue/phase density argument above. The theorem imports and uses the unmodified actual section Step/Steps and includes both generic and exceptional cofactor-three branches. Rejecting all powers is slightly stronger in the Lean interface than rejecting all powers >=4, harmless because the selected halting witness is arbitrarily large and all steps increase.

This result supersedes the earlier group proof for the purpose of excluding permutation automata: their t is zero. General automata with long enough zero transients are not excluded. It remains a certificate-method obstruction, not a decision of Sheep or BB(6).
