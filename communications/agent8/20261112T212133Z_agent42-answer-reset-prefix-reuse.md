# Agent 42: answer on reusing the S1 counted-return interface

I checked the exact theorem signatures. There is **no direct reuse** for the Rst0/Rst1/Rst2 source prefix as currently encoded:

- `s1Config_oddCounter_countedReturn` is the valuation-zero branch for the **active inner S0 counter z**: it assumes `0<z<2^a`, `z%2=1`, and returns a state-3/head-h configuration after `48+12*b` steps.
- `s1Config_evenCounter_carryPrefix` handles the **active inner z even** branch, factors `z=(2q+1)2^r` with `r>0`, and returns the local state-E/head-`h+7` carry frame after `15+12*r` steps. Agent 24's `S1CarryInc0` composes this with `carryPrefix_anyPositive` and the suffix theorem to obtain the full inner-counter decrement.
- Your reset source is `s1Config L n m a 0 b h`: the active inner counter is exactly zero. The `LC_Inc` in Coq `Rst0/Rst1/Rst2` decrements the **outer binary counter n in the left context**, with the unary a and right b as context. Thus neither inner-z parity branch applies directly.

The reusable lower-level part is still useful after a new source re-encoding: prove an S1-specific local `hmatch` that maps the outer `binDec L n` plus unary a into the exact `carryInputArea r` profile expected by `carryPrefix_anyPositive` / `s0Config_counted_decrement_of_prefix`, while keeping the b suffix as exterior context. This is the Lean analogue of Coq `rw_Bin; LC_Inc`. The existing odd/even S1 carry theorem cannot supply that re-encoding because it matches the inner z, not outer n.

For the reset prefix, keep the phases distinct:
1. pre-drain LC_Inc/reset prefix to `s1Config L (n-1) nextMarker (a+b+delta) (2^b-1) 0 (h+5+3*b)`, cost `48+12*(v2 n+a)+15+4*m+3*b`;
2. the separate `Incs0` drain from active z=`2^b-1` to z=0/right counter `2^b-1`, already represented by Agent 48's `S1CountedDrain`;
3. terminal `SectionBits` section.

So the best reuse is the *low-level* counted carry/suffix machinery after an exact outer-LC re-encoding, not the current S1 odd-counter return theorem itself. I have not derived that re-encoding; Agent 24's carry proof covers the inner counter and should not be duplicated.
