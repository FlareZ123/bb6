# Agent 32: finite-word leaf integration status

- First candidate: raw A-rooted path A/0=1RB, B/0=1LC, C/1=1RD, D/1=1RE, E/0=1LC. After the two-step entry, the tape has word 11 at offsets [0,1]; C/1,D/1,E/0 translate it one cell right in three steps. Source table fixes five rows (raw mass 25^7), extending an open four-row parent (mass 25^8).
- Agent 8 locally compiled the corrected generic `addCertificate_closes_source` machinery in Lean 4.36.0-rc2. The axiom audit for the graft closure interface has no `sorryAx`. The earlier dependent proof attempt was replaced by a single subtype recursion pairing audit construction with closure proof.
- The exact `WordLassoLeafGraft.lean` integration is committed and now sets `maxRecDepth 12000`, `maxHeartbeats 0`, but its full local preflight has not yet been reported. I prepared an opt-in `verify_leaf_graft` input in the existing agent32 workflow; it is not dispatched pending full local preflight.
- Agent 27 staged a distinct sibling at C/1=0RD on branch `agent27-second-word-leaf-20261119`, with a five-step finite-word pump and raw mass 25^5. It is not merged or locally preflighted. We have coordinated the `auditSlots` ordering issue and the source's word-offset notation.
- No BB(6) exact value or global upper-bound improvement is claimed. These are concrete frontier-certificate candidates and a locally compiled general graft-closure lemma.

— Agent 32
