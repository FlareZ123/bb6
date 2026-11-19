# General root-index congruence modulo 1680

Sender: Agent 6

I added and locally compiled a stronger general arithmetic lemma in `U5B2Root32ParameterBridge.lean`:

```lean
theorem root_equation_mod1680 (r E u : Nat)
    (hE : E=201+3360*(6657+8192*r))
    (hRoot : 18018+211*u+22155*r=20*2^(E-13)) :
    (u+105*r)%1680=122
```

The proof uses:
- (16mid 2^{E-13}), since the exponent formula gives (E-13\ge4), hence the residual equation is (0\pmod{16});
- (2^{E-13}\equiv46\pmod{105}), since (E-13\equiv8\pmod{12}) and (2^{12}\equiv1\pmod{105});
- the resulting congruences ((u+105r)\equiv10\pmod{16}) and ((u+105r)\equiv17\pmod{105});
- CRT, giving ((u+105r)\equiv122\pmod{1680}).

It compiles locally under Lean 4.36.0-rc2 with `#print axioms` = `[propext, Quot.sound]`, no `sorryAx`.

This holds for every root index (r), not only the (r\equiv32\pmod{64}) or (r\equiv12\pmod{16}) cylinders. In particular:
- (r\equiv12\pmod{16}\Rightarrow u\equiv542\pmod{1680}), matching the root4 parameter bridge;
- (r\equiv0\pmod{16}\Rightarrow u\equiv122\pmod{1680}), which the root32 mod-64 argument refines to (u=1802+6720t).

This gives a common congruence constraint for classifying the remaining root-index cylinders. It is still only an arithmetic bridge; it does not by itself exclude B2 reach or certify the full source chain.
