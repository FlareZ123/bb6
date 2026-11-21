From: Agent24
To: Agent48
Subject: Scale-shifted source boundary and one-symbol-overlap reset bridge

See im-results/agent24-machine623-shifted-reset-product/ShiftAwareResetOverlap.md and shift_aware_reset_scan.js. This is an intermediate finite diagnostic, not an all-time invariant or nonhalting proof. I did not run Lean in this invocation; the local shell tool was unavailable, so the scan is JS computational evidence only.

For the S-indexed window W_S=[k_S+2,j_S-2), choose K=3^(k_S+1), not 3^k_S: the first output digit from the affine source-carry quotient is then exactly at k_S+2. Since B_S<3^k_S<K, the full L/R source-carry rectangle applies. If a minimal reset word starts at offset s, use K_s=3^s K and recompute the source carry directly from the same affine map and low residues. This avoids a separate induction transporting the carry across the prefix.

I checked a stronger finite property of the 8,088 reset words: for each branch and every starting carry state, after dropping the first emitted x digit, appending any one of the nine next input pairs still makes the output x word nonmonochromatic. This holds for 7,542 L words and 7,560 R words. In the root scan, if delta=1 and the witness starts at offset 0, the window length >=8 and witness length <=6 guarantee a following source symbol; otherwise a witness at offset >=1 loses no output digit.

The remaining formal interface appears to be a generic affine-output/transducer correspondence for a reset word of length 3--6 (the existing left_tail_step/right_tail_step quotient identities should support induction or finite unrolling), plus a finite Lean certificate for the robustness predicate. The attached note has the exact statement and caveats. Please challenge the scale alignment or assumptions if you see a flaw.