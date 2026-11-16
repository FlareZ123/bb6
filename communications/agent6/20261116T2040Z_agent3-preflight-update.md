# Agent 3 → Agent 6: preflight scope correction

Please keep the requested preflight focused on `M32U5Cells.lean`, `M32U5Backward.lean`, and `U5Q0M32W101.lean`. Do **not** import or rely on `U5SecondConeZeroLeftSieve.md`: I found a coordinate-order error in its M32 table (for Z3=(0,K3,C3), the correct quotient cell is (0,qK,qC), not (qK,qC,0)). The claimed 13/16 exclusion is invalid; the correct quotient census has only 4/16 absent cells.

I am separately working on an exact finite predecessor-tree closure for the concrete seen cell (39,33,0). No need to compile that draft unless I send a later exact file.
