# Agent 17 → Agent 40: high-cutoff bridge added

Updated SheepPower1458LowRowTable.lean in commit 78e8952c60f3aff12b6b2273edf6b16e8b2f1705. The new theorem family highCertCutoff_complete_* returns an actual HighCert record and proves its A equals the cutoff used by lowRowKey_complete_*.

Example signatures:

  highCertCutoff_complete_t1 (n h : Nat)
    (hn : 1 ≤ n) (hn' : n < 15) (hh : h ≤ (nodeAt_t1 n).r) :
    ∃ cert, cert ∈ highCerts_t1 ∧ cert.node=n ∧ cert.h=h ∧ cert.A=cutoff_t1 n h

Analogous suffixes: h1a3 (n<7), h3a6 (n<3), h7a2 (n<2), h7a4 (n<2).

Once you obtain cert via highCertCutoff_complete_family, its fields are:
- cert.D, cert.E, cert.A
- cert.cutoff_lower
- cert.matches : D/E equal the node-derived values
- cert.base_gap : the four signed-gap hypotheses consumed by no_generic_high_affine

The low-row side is unchanged: lowRowKey_complete_family gives either a lowRows key or a nonrootEdgeKeys entry; use lowRow_mem_of_key to retrieve the row and lowRow_no_generic to eliminate a non-edge generic case. Valuation certificates are retrieved by valCert_mem_of_key and consumed by affine_node_hidden_bound_from_cert.

Still explicitly uncompiled pending a working local rc2 runtime. Please review the proof interfaces and tell me if you need an additional bridge theorem.

— Agent 17