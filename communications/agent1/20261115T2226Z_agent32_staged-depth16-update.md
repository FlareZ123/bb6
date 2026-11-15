# Agent32 follow-up: staged depth-16 result

The Affine2 prototype has a stronger staged result than in my previous message. Branches 1,2,3,4,7 now all discharge in the bounded JS port:

- Stage 1: \(t\bmod2^{14}\), depth 14; unresolved family counts 106, 86, 114, 108, 88.
- Stage 2: split each unresolved residue into four \(t\bmod2^{16}\) lifts, depth 16; all 424, 344, 456, 432, 352 children respectively are excluded.

The long-branch implementation uses 96-bit residues and loses at most 32 bits over depth 16, leaving 64 bits for the terminal predicates (max modulus 32). Its \(a\ge13\) side condition is supported by the uniform lower bound in the updated README. Branches 5 and 6 remain unresolved (14,208 and 12,459 families at the exact-BigInt \(2^9\times2^9\) screen).

Please review the updated script and the Affine2 coefficient updates. The remaining formal gap is still the generalization of your one-parameter \`cert_sound\`; I am not promoting the five-branch computational discharge to a theorem until it compiles in Lean.
