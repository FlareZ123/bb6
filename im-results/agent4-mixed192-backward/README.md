# Machine C mixed-192 backward cores: executable candidate certificate

**Status: experimental computational certificate, awaiting successful Lean proof.** Machine C and BB(6) remain open. This dossier contains no claimed new source-kernel theorem yet. It identifies all-natural candidate reverse invariants for the original Agent11 Machine C acceleration and checks them on a finite quotient, with a separate explicit transport argument still requiring a machine-checked audit.

## Proposed mathematical statement

Use the *unchanged* original counter transition BB6CLine.nextC from im-results/agent11-c-line/CLine.lean and its actual initial triple (5,0,1). Four proposed blank-unreachable terminal residue cylinders are

- A: (a mod 192, k mod 192, c) = (35,61,0), (131,157,0)
- B: (a mod 192, k mod 192, c) = (83,13,0), (179,109,0).

Each core has seven low-counter congruence families and high-sector arithmetic clauses in BackwardMod192.lean and BackwardMod192B.lean. The currently authored Lean low predicates name one singleton residue pair per core; the exhaustive checker separately verifies a strictly stronger version including both companion pairs. Those enlarged predicates require an updated Lean source theorem, so do not infer companion cylinder certification from the current draft Lean file.

For c=0 or 1, define w=k+c. The proposed enlarged core A low predicate contains coupled special pairs (a%192,w%192)=(35,61) or (131,157) and seven (a%96,w%48) pairs:

  (0,25), (10,19), (34,7), (46,4), (48,1), (58,43), (82,31).

Core B has coupled special pairs (83,13) and (179,109), and seven (a%96,w%48) pairs:

  (10,43), (24,37), (34,31), (46,28), (58,19), (72,13), (82,7).

For c>=2, set d=(a-c)%96 and t=(a+k)%192. High A is the disjunction of

  (d,t%48) in {(7,26),(8,27),(17,33),(31,38),(32,39),
  (43,47),(45,46),(55,2),(56,3),(65,9),(79,14),
  (80,15),(86,21),(93,22)}

or (d=32,t=93) or (d=35,t%96=45).
High B is the disjunction of

  (d,t%48) in {(7,2),(8,3),(17,9),(21,10),(31,14),
  (32,15),(38,21),(43,23),(55,26),(56,27),
  (65,33),(69,34),(79,38),(80,39)}

or (d=80,t=93) or (d=83,t%96=45).

Both enlarged sets contain 11,444 of the 192*192*98 projected triples. Both omit the actual root (5,0,1). Exact reverse closure should prove that their complements contain every finite-time blank-entry state.

## Exact, independently reproducible finite check

The self-contained C++17 checker check_core.cpp reproduces the nine cases of the original map, then tests all **28,459,008 representative transitions**. The quotient is

  q(a,k,c)=(a%192,k%192,c) for c<2,
  q(a,k,c)=(a%192,k%192,2+(c-2)%96) for c>=2.

For each abstract state (a0,k0,c0), the checker enumerates a in {a0,a0+192}, k in {k0,k0+192}, and c in {c0} for c0<2 or {c0,c0+96} for c0>=2. For each actual transition from one of these representatives, it checks the contrapositive closure: if the successor belongs to the proposed bad set, the predecessor belongs too. It checks four variants: A/B, original singleton special pair or enlarged two-pair version. The observed output for each variant was PASS with 28,459,008 edges and rootBad=0; counts are 11,442 abstract bad states in the original singleton version, 11,444 in the enlarged version. The checker is deterministic and uses no finite orbit cutoff.

**Why representative enumeration should lift to all naturals:** All low/high bad clauses depend solely on q. The original transition tests exact exceptional counters 0/1/2/3, parity, and affine expressions whose quotient residues are determined by a,k modulo 192 and high c modulo 96. For residues 0/1 in a and 0 in k, taking both the small representative and one +192 representative covers the exceptional-vs-positive branch. For c residues 2/3/4, both c0 and c0+96 cover boundary-to-low versus remaining-high successors. For every larger real input, the transition's quotient successor therefore coincides with one of these checked representatives. A formal Lean proof of this soundness or an all-natural symbolic backward-closure theorem is still required before calling the result kernel certified.

The author independently simulated 12 million bounded concrete triples per singleton variant, and 6 million additional triples per enlarged version, finding no violation. Those sampled screens are secondary checks; the exhaustive finite representative graph is the primary computational evidence.

## Halting-equation intersection and comparison with earlier work

Agent15's exact immediate second stopping condition has a=2j+3 and

  k+j+3m+5=2^(2m+2)*(j+3).

For m>=2, 2^(2m+2)%192=64. Each of the four candidate terminal cylinders therefore corresponds to six residue pairs (j,m) modulo192, totaling 24. An independent B8/M16/M32/M64/M128/M256/M512 and mixed96 census found five illustrative residue pairs

  (j,m)%192=(16,122),(112,154),(88,146),(136,162),(160,170)

whose targets are absent in mixed192 while *present* in B8/M256 and B8/M32. B8/M512 also excludes them computationally; its 52,736,417-state closure was independently externally computed by Agent41 but has not been fully certified within Lean's kernel. Relative to full prior source mathematics, novelty of the proposed congruences remains to be reviewed. Agent47's valid 96-modulus C/D inverse proofs were already subsumed by fully kernel-certified B8/M32 and are **not** claimed as new here.

## Verification work and immediate next step

The Lean drafts BackwardMod192.lean and BackwardMod192B.lean reuse the existing Agent4 exact counter interpreter and attempt all-natural backwards-closure via Presburger arithmetic. Source provenance is the prior Lean-checked A4Backward.nextC_source_equal bridge to *unmodified* CLine. The manual .github/workflows/agent4-machine-c-backward.yml builds from unmodified sources. The first monolithic CI attempt 41720094304 received a runner shutdown, and the second run 41720917299 was canceled after prolonged arithmetic proof execution. A source-preserving five-module decomposition is provided by tools/agent4_split_mixed192.py, and the subsequent CI should identify the individual difficult lemma. A successful final build must independently recheck the full source, prove the enlarged four-target theorem, and audit final axioms for the absence of sorryAx or added assumptions.

No change to results/ is appropriate before the proof is validated and novelty externally assessed. This investigation has not resolved the actual Machine C halting behavior or determined BB(6).
