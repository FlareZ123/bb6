# Reusable Lean source-congruence certification bridge

Agent 14, 2026-11-05. Independently locally kernel-compiled with Lean 4.36.0-rc2. Source file `SheepGenericSourceMod.lean`, SHA256 `97a2bf3ddd2215a387662589194352085e5a22ebdf73449a6dea352308fe594f`, is a separate user-visible artifact of this invocation. It depends only on the earlier `Sheep648Period.lean` from Agent14 and Lean Std.

The theorem `SheepGenericSourceMod.no_mod_eq_from_period` proves that if `m>1`, `q>0`, `2^p % m=1`, `p` divides `P*q`, and every `t<q` satisfies `(2^(R+P*t)+B)%m != L%m`, then **every natural k** satisfies `(2^(R+P*k)+B)%m != L%m`. Local axiom audit: `[propext, Quot.sound]`, no sorry.

The theorem `SheepGenericSourceMod.no_source_eq_from_mod` proves that a complete all-k modular non-equality `(2^(R+P*k)+3*D)%m != (2*a*D+2*Q)%m`, with `m=D*(2^(a+1)+1)`, contradicts the **full exact original-source generic inverse equality** `D*(2^(a+1)+1)*v+2*a*D+2*Q=2^(R+P*k)+3*D`, for every natural `v,k`. Its axiom audit is `[propext]` only. No sign normalization, signed remainder, quotient compensation, or special small cases are required. The proof simply applies the remainder operation to the exact source equality and cancels the modulus multiple.

These theorems are useful for a single certificate checker that consumes the entire 222-family complete-period arithmetic table and closes each original-source necessary edge. Unlike the individual 1080 source-low transport lemmas already compiled locally, this general bridge permits a uniform generation path for all source equations and all low valuations. The complete original-source machine import for the 222-class certificate is still pending; the base machine and BB(6) are unresolved.
