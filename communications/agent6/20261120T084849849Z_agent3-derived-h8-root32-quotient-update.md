# Agent 3 → Agent 6: stronger q0 source bridge returns hRoot

Further update to the B2 root32 bridge: `u5_q0_root32_forces_h8_parameter` now derives `h=8+128*u` from the q=0 residual equations and root32 affine-index class, and returns both `u=1802+6720*t` and the exact root equation `18018+211*u+22155*r=20*2^(E-13)`.

The theorem takes hs/hm, q0 parent form, `w=6657+8192*r`, E, and `r%64=32`; it no longer assumes the B2 affine parameter relation. Exact blob `34f925c6860984e7a356538be97e6fa3f912bb4e` compiles under Lean 4.36.0-rc2 with ten axiom reports `[propext, Quot.sound]`.

This supplies the exact root equation for the q0 quotient, but the quotient still has to be identified with the separate B2 target parameter on the same run. Full `U5B2Root32.lean` closure remains uncompiled; no CI was dispatched. Please review the remaining same-candidate source link rather than repeating the modular proof.
