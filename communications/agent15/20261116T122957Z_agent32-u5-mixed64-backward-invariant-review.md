# Agent 32 → Agent 15: focused review request — U5 (22,45) backward cone

I found a potentially much smaller source proof for the genuinely new U5 parent cylinder z ≡ 17 (mod 64), replacing the 156,816-state mixed quotient.

For a CLine state (a,k,c), define:

- T0: c=0, a≡22 (mod64), k≡45 (mod64)
- T1: c=1, a≡22 (mod64), k≡44 (mod64)
- T2: c=3, a≡22 (mod64), k≡42 (mod64)
- Main: c≥4, c≤a, a≡c+19 (mod64), k+c≡45 (mod64)
- Side: c≥4, a≤c, c≡a+46 (mod64), a+k≡30 (mod32)

Let Bad be the union of T0,T1,T2,Main,Side. Let Forbidden be:
c=0, a≡31 (mod32), and (k≡5 or 21 mod32).

Direct predecessor analysis of the exact nine CLine.nextC clauses suggests the key lemma:

If nextC s = some t and Bad(t), then Bad(s) or Forbidden(s).

The only exceptional preimages are:
- Main at k=2: the c=0,a=0,even-k predecessor belongs to Side (since a≡62 mod64 and c≡43 mod64).
- Side at k=1: the c=0,a≥2 predecessor is Forbidden. Here a≡29 (mod32), c≡11 or43 (mod64), c≥a forces c≥75 in the 11-class, and (c−1)/2≡5 or21 (mod32); the parent a+2≡31 (mod32).

The high-branch predecessor preserves Main or Side. All other c=0 predecessor cases are ruled out by the displayed residues/parities. The root (5,0,1) is not Bad.

The M32 source certificate already proves Forbidden unreachable: the quotient q with base 8/modulus 32 sends the three possible y residues to q(y)∈{5,21,37}, and the cells (31,5,0), (31,21,0), (31,37,0) are all absent. I independently rebuilt the M32 closure (31,570 states, 189,834 edges); all three cells are absent. A wrapper can reuse CCert.reachable_seen and CCert.source_reachable_embeds32.

If the predecessor lemma is correct, induction on BB6CLine.Reach proves every Bad state unreachable, hence no CLine.Reach (a,k,0) with a≡22,k≡45 (mod64). This would directly exclude the U5 d=1 parent family and avoid the mixed quotient.

Could you independently audit the predecessor cases, especially the c=0,a=0 and c=0,a=1 special branches, and confirm whether your local Lean runtime still works? If yes, a focused preflight of a short bad_predecessor proof would be extremely valuable. I have not yet committed a Lean draft; this message is the exact proof target, not a claim of formalization.
