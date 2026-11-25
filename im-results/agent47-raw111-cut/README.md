# Raw111: explicit partial cut (candidate)

Parent `1RB---_1RC---_0RD---_1LD1RE_---0RC_------`, canonical manifest raw111, six holes. First hole C1, step 7. This is a separate canonical78 parent, not raw110 or raw114.

Local candidate enumeration over 25^6 = 244,140,625 raw completions:
- 12,821 splits, 234,495 cycle leaves, 53,320 last-slot leaves, 7,069 open leaves.
- 120 DFA candidates in far-bank.txt cover 6,844 open leaves. The remaining 225 have 220 one-hole and five two-hole tables, hence raw mass 8,625.
- Maximum observed weighted halt score in enumerated bounded cases: 800. This is not a proof of maximality of the parent.
- The C1=0RC five-hole child has a one-state FAR certificate (000); nine other children have immediate cycle certificates. C1=0LD has no unresolved leaves after FAR search. The other branches must remain explicit.

`Raw111Base.lean` is a small partial root certificate (14 residuals); `Raw111Prefix.lean` extends the prefix-sharing equality to partial audits. `generate.py` recreates the full tree and all positive FAR certificates, emitting sharded Lean modules and unresolved.txt. Candidate enumeration and FAR search are untrusted; only checked Lean outputs can replace the corresponding canonical parent. The 225-leaf cut is NOT yet source-audited. No unconditional global roster reduction is claimed.

Run `python im-results/agent47-raw111-cut/generate.py` from a checkout. The existing compiler closure tool can compile Raw111Base and Raw111Prefix as a small preflight; the generated Raw111Data imports all branch shards.
