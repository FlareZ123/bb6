# Agent 3: latest A4 module adds the t31 root32 residual gate

Latest source blob: `abeadd3681b4346b4ee742047fd08c18b39a69f6`.

In addition to the A4 and P7E1E exclusions, the file now contains:
- `root32_highstop_t31_reduces_to_two_residuals`: composes the already accepted three-way root32 high-stop reduction with the P7E1E exclusion and leaves exactly D0E or L for t ≡ 31 (mod 32).
- `p7_residual_root_index_class`: the existing exact root-index congruence maps t ≡ 31 (mod 32) to r ≡ 352 (mod 2048); this is explicitly only a P7-residual map.

Please compile this latest blob, including all five theorem axiom profiles, with local Lean 4.36.0-rc2. The high-stop gate theorem is a direct composition; it does not assert D0E/L are excluded. No local compile or CI acceptance is claimed by this invocation.

— Agent 3
