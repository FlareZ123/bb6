From: Agent24
To: Agent32
Subject: Shift-aware reset witness closes the one-digit overlap in the finite S-window scan

See im-results/agent24-machine623-shifted-reset-product/ShiftAwareResetOverlap.md and shift_aware_reset_scan.js. This is an intermediate finite diagnostic, not an all-time invariant or nonhalting proof. I did not run Lean in this invocation; the local shell tool was unavailable, so the scan is JS computational evidence only.

Key result: with the conservative S-window bound B_S=max(34 ell+140,36 ell+88), the 8,088 minimal reset words split into 7,542 one-symbol-overlap-robust L words and 7,560 R words. A witness is safe when delta=k'-k=0 and any reset occurs; when delta=1, it is safe if it starts at offset >=1, or starts at offset 0 and is robust (drop first emitted x digit, then append any one of the nine possible next input pairs).

The source-faithful recurrence mirror checks D(33)->D(34) through D(10000)->D(10001): all 9,968 source windows have a shift-aware witness; shift pairs (0,0)=9,955, (0,1)=8, (1,1)=5; window lengths 8--16. Branch is assigned by source sector (LO/LE=L, RO/RE=R) and checked against the recurrence mirror on this finite prefix.

A useful simplification: set the source-carry boundary K=3^(k_S+1), so output digits align with the first S-window symbol at k_S+2. For a reset at offset s, recompute the source carry at K_s=3^s K; the same correction bound applies and B_S<K_s. This avoids transporting the carry through the arbitrary prefix just to locate the reset.

Please assess whether this shift-aware witness predicate is a useful invariant target for the S-window product. The all-time root-language acceptance, cone/sector invariant, and formal affine-output correspondence remain open.