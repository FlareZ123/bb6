# Raw124 F1=0LF / F0=1RC: checked late-query certificates

The exact remaining child is `1RB---_1RC---_0RD---_1LD1RE_---1LF_1RC0LF`. Its discovery partition has 143 splits, 1829 cycle leaves, 1164 last leaves and 297 open leaves. Of the latter, four one-hole leaves now have original-semantics local Lean proofs of a weighted bound 108667; the other 293 require their respective nonhalting certificates and the whole rich-audit root has not yet been accepted.

| Leaf (zero-based open-list index) | Exact table | First undefined query after moves |
|---|---|---:|
| M77 | 1RB0LC_1RC---_0RD0RD_1LD1RE_0RA1LF_1RC0LF | 108665 |
| M81 | 1RB1LD_1RC---_0RD0RD_1LD1RE_0RA1LF_1RC0LF | 108421 |
| M91 | 1RB0LC_1RC---_0RD0RF_1LD1RE_0RA1LF_1RC0LF | 103183 |
| M94 | 1RB1LD_1RC---_0RD0RF_1LD1RE_0RA1LF_1RC0LF | 102939 |

For each leaf the first undefined slot is B/1. If assigned halt, the weighted score includes the normalized prefix and incoming delay, bounded by 108667; if assigned any ordinary transition, the table has no halt and is nonhalting. Each theorem `BB6.Agent12LateRCM<i>.bound_all` proves `∀ m, compatible table m → WeightedBound 108667 m`. This closes all 25 literal completions of each leaf, 100 total in the disjoint partition.

## Reproduction

Unpack the pinned bundle with unpack.py. In the resulting directory compile partition.cpp and run the first two commands in reproduce.sh to generate rc.open and rc.json; exact SHA256 values e70042677f994e37339e7d1ad707ac3b3bd4172aad2c89fa15364bcc5f8aed9e and 8eafc439ae0076103fef4d0946346d8aa94fcc2226c358bd3250e3bd761ba15d respectively. Copy generate_late_verified.py from this directory into the unpacked directory and run it there **instead of** gen_late_packed.py, fix_late.py and split_late.py. The new generator emits base modules, groups of five 2000-move-or-shorter segment checks, and a small explicitly indexed composition for each leaf. It emits the original exported namespace and theorem interface for gen_audit.py.

Use accepted Raw58 core artifact 15090715339 (ZIP SHA256 2231c274970b233002894c3fa097e3b81ad1484a3db0809c0148f8c03e26c477), merge its contents into core, and compile PackedRC.lean followed by LateRCBridge.lean. The latter now imports only PackedRC; Raw124FastAudit was an unused import. With LEAN_PATH set to core, compile all modules listed in late77.order, late81.order, late91.order and late94.order in order, e.g. `lean -j 2 -o <module>.olean <module>.lean`. Chunk modules may be compiled independently after their base. Local check used Lean 4.36.0-rc2, all 52 generated modules passed; first_query axiom profile [propext, Quot.sound], bound_all [propext, Classical.choice, Quot.sound]. PackedRC.known_read and LateRCBridge.bounded_of_query also passed with those respective profiles. No native oracle or sorryAx.

This is original-semantics local object-link acceptance against the accepted common core, not a new source-rebuild CI verdict or complete parent closure. Remaining priority: grouped mask/suffix automata and the exhaustive RichRCAudit root, then compose with Raw124ZeroLFAccepted.cover_of_last. Do not regenerate these four late traces using the old uncorrected generator.
