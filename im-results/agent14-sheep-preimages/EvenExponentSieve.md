# Infinite two-generation sieve for Sheep Machine halting powers

Agent 14, 2026-11-02. **Status: complete written arithmetic proof, only the residue class 8 modulo 72 is currently certified in Lean.** This is intermediate research, not a BB(6) decision.

## Theorem (written proof)

Let `R={8,16,40,56,64}`. For **all** `r∈R` and all natural `q`, the true blank-entry return trajectory of the Sheep Machine, starting at `t=5`, cannot visit the halting state

```
    2^(r+72*q).
```

This extends the kernel-certified `r=8` case already proved in `Triple.lean`. No external novelty is asserted. These five disjoint arithmetic progression classes can be handled by the same uniform modular sieve.

## Proof

Write `j=r+72q` where `r∈R`. Then `j` is even, divisible by eight, at least eight, not divisible by six, and not congruent to 14 modulo 18.

The return map for odd part `u=t/2^a` with `a=v₂(t)` is:

- `u=1`: halt.
- `u=3`: `F(t)=t+a+3`.
- odd `u>=5`: `F(t)=t+a+(u-1)/2`.

The existing Lean theorem `no_high_v2_power_preimage` proves that if a generic (`u>=5`) source returns to any pure power of two, its valuation must be `a<=1`. The `u=3` branch never returns a power of two, by the proved interval between consecutive powers.

For `j` divisible by eight, `a=1` is impossible: the return equation would yield `2^(j+1)=5u+1`, while `2^(j+1) ≡ 2 (mod 5)`. Therefore the **sole possible predecessor** of `2^j` is the generic source with `a=0`, necessarily

```
    t_j=(2^(j+1)+1)/3.
```

Since `j` is even, the numerator is divisible by three, and for `j>=8` the value `t_j` is odd and exceeds five. We show this candidate has **no incoming section edge**.

A generic source `s=2^a*u` with odd `u>=5` returning to `t_j` satisfies

```
  2*t_j=(2^(a+1)+1)*u+2*a-1,
  2^(j+2)+5=3*(2^(a+1)+1)*u+6*a.
```

For `a>=1`, rearrange as `2^(j+2)=3*(2^(a+1)+1)*u+(6a-5)`. For `a>=5`, let `M=2^(a+1)+1` and `D=6a-5`. Induction from `a=5` proves `1<D<2^a`. Reducing modulo `M` and using `2^(a+1)≡-1 mod M` reduces the equation to `2^h ≡ ±D mod M` for `0<=h<=a`. The positive alternative is impossible because `2^h` is 1 or even while `D` is odd and greater than one. The negative alternative would force `2^h=M-D>2^a`, contradicting `h<=a`. This exclusion is already Lean-certified in `no_high_feeder` for exponent class `j=8+72q`; the proof makes no special use of that exponent.

For `a=4`, the equation modulo `M=33` requires `2^(j+2)≡19 (mod 33)`. The complete periodic residue set of powers of two modulo 33 is `{1,2,4,8,16,32,31,29,25,17}`, excluding 19.

For `a=0,1,2,3`, reduce the second displayed equation modulo `3*(2^(a+1)+1)`. The necessary conditions are:

| Valuation a | Modulus | Required exponent class |
|---|---:|---|
| 0 | 9 | `j ≡ 0 mod 6` |
| 1 | 15 | `j ≡ 2 mod 4` |
| 2 | 27 | `j ≡ 14 mod 18` |
| 3 | 51 | `j ≡ 4 mod 8` |

All four are excluded by the chosen residue classes. The periods of 2 modulo these moduli are respectively 6, 4, 18, 8. There are no generic predecessors of `t_j`.

Finally, the `u=3` branch is also impossible as a parent of `t_j`: multiplying `F(3*2^a)=t_j` by three and rearranging would give

```
    2^(j+1)=9*2^a+3*a+8.
```

For `a=0`, the right side is 17, strictly between 16 and 32. For every `a>=1`, induction proves `3a+8<7*2^a`, so the right side is strictly between `2^(a+3)` and `2^(a+4)`. It therefore cannot be a power of two. This interval argument is kernel-certified as `no_triple_feeder` for `j=8+72q`, but itself does not rely on the exponent.

Thus `t_j` has no incoming edge and is distinct from the initial state `5`; the true return trajectory never reaches it. Since every possible predecessor of `2^j` is `t_j`, the return trajectory cannot reach `2^j`. QED.

## Verification and limitations

Direct Python full-predecessor enumeration confirms all 155 cases `j=r+72q`, `r∈R`, `0<=q<=30`, including the 2,224 exponent boundary. The all-exponent claim above is mathematical reasoning and stands independently of this finite check.

**Formal-certification boundary:** `Triple.lean` currently proves `no_reached_power_72` only for `r=8`. Formalize the other four classes or a parameterized CRT exclusion before promoting this broader result as kernel-certified. `CounterBridge.lean` separately proves the forward simulation of published section edges by the counter accelerator, with reverse completeness still to be established.
