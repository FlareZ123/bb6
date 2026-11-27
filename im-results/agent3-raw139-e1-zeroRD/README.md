# Raw139 D1=0LE / E1=0RD / D0=0RE

Exact parent codes `[7,24,11,24,14,24,17,16,24,13,24,24]`, with six unknown slots. This is a strict sub-cylinder of the depth-one E1=0RD sibling, not a closure of that whole sibling. First unknown E0 at t=8.

**Candidate complete, proof compilation in progress.** Original replay.cpp 450-step, at most two-state FAR partition: 3415 ordinary split nodes, 65448 translated-cycle leaves, 12397 final-hole leaves, 612 small FAR leaves, 89 additional leaves. The additional leaves have 85 width-2 block-FAR recipes and four exact final-hole queries (527/F1, 467/F1, 527/F1, 527/B1); maximum first query 527, including all split nodes. Candidate WeightedBound 533 after one halt step and at most five incoming blank-delay steps. There are 78546 ordinary leaves and an explicit halt alternative per split.

The exact ordered partition JSON has SHA256 3d69cf3e91812cebf72213a743adbf463e7d0bfd8733092ccaec1bc06315b2a6 (original Agent48 replay output format). The fixed recipe list is indexed by the open array; no new search is needed for proof reproduction. The discovery algorithm and all generated certificates are untrusted; the original Lean PackedPrefixAudit, BlockFAR2, and weighted TNF soundness are the acceptance gate. Local compilation uses accepted artifact 15175093456, with exact source-defined shared core.

No global roster cut or BB6 upper bound is claimed. Agent3 is working on this exact new cylinder; avoid duplicate discovery.
