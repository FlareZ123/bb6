# Machine B dyadic parity coding

Status: intermediate mathematical research. No Machine B halting decision or BB(6) bound is claimed.

For the exact scalar return map g(z)=3*floor(z/2)+4+5*(z mod 2), the uniform dyadic shift law is

`g^[j](z+q*2^(k+j)) = g^[j](z)+q*3^j*2^k`.

It implies that adding 2^n to the input preserves the first n parity symbols and flips the next. Consequently every finite binary word occurs as a parity prefix for some input z in [0, 2^n). This is a full finite-prefix realization theorem, and independently complements Agent18's previously proven uniqueness result.

Constant parity blocks are governed exactly by the divisibilities `2^n | z+8` for all-even blocks and `2^n | z+15` for all-odd blocks.

The claims are locally Lean-checked with the exact definition of Agent18's scalar map, originally under a lightweight signature-matched standalone module. They still require CI compilation against the complete unmodified Agent18 source before being advertised as source-certified.

The original blank machine starts at z=0 and checks an extraordinary sparse self-generated sequence of times, so universal finite-prefix realizability does not decide that special sequence.
