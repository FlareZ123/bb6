# Obstructions for even-only binary automata

This extends ZERO-TRANSIENT.md to a genuinely weaker invariant requirement: accept even states, close under complete first-even returns only, reject halting powers >=4. Intermediate odd states need not be accepted. The actual starting even state is 10.

**Theorem.** For an n-state LSB-first DFA satisfying those requirements, with zero transient t, every accepted even nonterminal x=2^a*u>=6 has a<t. For every generic such state (u>=5), let F(x)-1=2^h*v (v odd). Then h<2(a+1)n+a+2. Thus existence of an even-return regular invariant would imply bounded a and h along the authentic generic trajectory. No claim of unbounded actual valuations is made.

## High-a pumping for even-only closure

Let p be a positive common period for all DFA zero-transition cycles, T a common transient threshold. If a>=t, every 2^e*u with e>=t, e congruent a mod p, e>=1, is accepted. Set c=3 for u=3 and c=(u-1)/2 otherwise. Choose e0 large in that progression, h=v2(e0+c-1), P=lcm(p,2^(h+1)). Restrict e=e0+P*m with e>h. Then F(x_e)-1=2^h*v_e with v_e odd, and its exact even successor is

  E(x_e)=2^(e-h)*w+delta_e,
  w=3^h*u, delta_e=1+3^h*(e+c-1)/2^h.

The delta_e form an even-valued arithmetic progression with positive step Q=3^h*P/2^h (even). For e large the binary word of E is a low block delta_e, a zero gap of length e-h-width(delta_e), and the fixed high block w. Pumping the gap via global period p shows acceptance of every 2^b*w+delta_e for b congruent e0-h mod p, b>=width(delta_e)+T, provided e-h>=width(delta_e)+T.

Let L=lcm(p,ord_{oddpart(Q)}(2)), taking order 1 for oddpart=1. Choose b congruent e0-h mod L, sufficiently large that 2^b*w mod Q is constant. Restrict alpha*2^b<delta_e<beta*2^b for fixed 0<alpha<beta<2^(-T-1). The acceptance conditions hold for all sufficiently large y in the resulting single residue class mod Q and open log2 phase interval mod L. Every such y is even; the representation follows by choosing the unique b in the progression with y/2^b in (w+alpha,w+beta) and recovering delta. Agent17's prepared-halting density theorem in ../agent17-sheep-terminal-extension/README.md gives an arbitrarily large prepared-halting even state in that cell. Its entire path between even endpoints is a genuine sequence of complete even returns. Closure contradicts terminal exclusion. This proves the high-a bound for even-only invariants without relying on odd acceptance.

## High-h pumping for even-only closure

Put D=2^(a+1)+1, so D*u+2a=2^(h+1)*v+3. For each prefix position i with 1<=i<=h+1, r_i=u mod2^i obeys D*r_i+2a=2^i*c_i+3 with 0<c_i<D. The carries at positions separated by a multiple of L0=2(a+1) are equal: writing r_j=r_i+2^i*B yields D*B+c_i=2^(j-i)*c_j, and 2^L0=1 mod D. Reduce modulo D and use 0<c_i,c_j<D.

Let w_u be canonical bit length of u. Because D*u+2a-3<2^(a+2+w_u) and v>=1, h<=w_u+a. If h>=n*L0+a+2, all n+1 prefix positions 1,1+L0,...,1+n*L0 lie within h+1 and strictly before the final canonical digit (i<=w_u-1). Two carry/DFA states repeat, by pigeonhole. Write i<j, ell=j-i>0. Pump the fixed block of ell input bits between them; this preserves the DFA output and the carry. More precisely, if u=r+2^i*(B+2^ell*z), then replacing the B block with m+1 repetitions gives a positive odd u_m>=5 and

  D*u_m+2a=2^(h+1+ell*m)*v+3.

The entire geometric family Y_m=1+3^(h+ell*m)*v is therefore accepted, using only exact generic even-return closure. The Lean theorem repeated_prefix_pump checks precisely this implication, including carry extraction and the true SheepEven.Steps witness.

The family is dyadically dense in an even residue class: restrict m=2k, g=3^(2ell), s=v2(g-1)>=3, K=3^h*v odd. Repeated squaring gives v2(g^(2^j)-1)=s+j. Inductively the powers g^k exhaust the subgroup of residues 1 mod2^s modulo every 2^(s+j): appending 2^j to an exponent toggles precisely the next bit. Consequently 1+K*g^k exhausts every residue refining 1+K mod2^s, with arbitrarily large k by adding a period. Choose p'=max(s,t,1). The coherent dyadic path-lifting theorem of Agent40 (../agent40-sheep-coherent-audit/README.md) supplies an entire dyadic arithmetic progression in that class whose sufficiently large members reach a multiple of 2^p' under genuine generic even returns. Some Y_{2k} lies in it. Its accepted endpoint either is a terminal power or has valuation >=t, both impossible. This proves the h bound.

For raw-section invariants there is the simpler stronger h<=n: the odd state 1+2^h*v itself is accepted, and its word has h-1 zeros after the first 1; a repeat within that run pumps h directly. Carry pumping is needed only because even-only closure does not require that intermediate odd state.

## Formal status and reproduction

SheepBlockPump.lean imports the existing SheepAutomata and SheepEven. The checked declarations prefix_carry, carry_period_mod, repeated_prefix_pump, geometric_pump, genericClosed_of_even use only propext and Quot.sound. The finite-state pigeonhole and width estimate, even-only high-a extension, geometric-family density and final contradiction are written mathematical proofs, depending on the previously written Agent17/40 density and coherent lifting results. No claim of end-to-end kernel checking of those analytic/combinatorial dependencies.

Decode SheepBlockPump.lean.xz.b64 with xz; compressed SHA256 f877d5b5449176801ad8164c43d58020bbea9df3ecf2fae46ec9727311972211, source SHA256 a49ef7e7af2b00abfbe4696ae2eac6e3d6ee4299d061832b4e060a528ecd41c5. Reconstruct and compile SheepEven and SheepAutomata first, then compile SheepBlockPump with LEAN_PATH=. using Lean 4.36.0-rc2.
