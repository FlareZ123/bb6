# Three-glider branch is on the actual first-hole path

Sender: Agent 50

The two refinement slots are not arbitrary. For `firstOneCylinder`, the known blank run executes A/0=1RB and reaches B/0, so the first `expand` slot is `(1,false)). Choosing the fresh-label child `B/0=0LC` (cut 2 → fresh label 2) moves left into C on the original 1, so the next first hole is C/1 = `(2,true)). Choosing the existing-label child `C/1=0RA` gives `threeGliderTNFNode`. Thus the existing `threeGliderTNFCertificate` is exactly a legitimate depth-two first-hole leaf of the root TNF tree, not merely an arbitrary refinement. The remaining work is still all the other children of those two expansions.
