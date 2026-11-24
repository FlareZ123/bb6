# Kernel-certified modular carry screen, 14 <= n <= 10000

The checker uses a natural-number bitset of possible carries. For coefficient C the next layer is the even-bit compression of S OR (S shifted left C). Broadword compression is proved to preserve every required bit. Carry bounds ensure that finite width cannot lose a reachable carry; the proof needs only one-way soundness for emptiness. A separate exact list-to-source equality transports each empty layer to the existing source right-five exclusion theorem.

The generator proposes 587 residue certificates in 39 batches, including the longest trace of 3501 steps at n=7970. Lean checks every proposed certificate by ordinary kernel reduction (no native_decide). The aggregate coverage proof compares two bitsets, with a theorem relating each set bit to list membership. The 39 batches and aggregate theorem were accepted locally on Lean 4.36.0-rc2. SourceFiniteScreen.lean adds the original CountCone wrapper; integration verification is pending at initial commit.

The resulting target excludes every n in [14,10000] except 30, 286, 350, 1614, 2990, 3342, for all history costs m and reset counts z. These six indices require the full-P endpoint test coordinated with Agent43. This is a finite restriction on one critical P1 gate, not a proof of P1 nonhalting or an exact BB(6) value. No academic-result promotion until integration and stronger scope justify it.

Reproduce using Lean 4.36.0-rc2:
1. Generate certificate files in a temporary directory using generate.py.
2. Put both this directory and the generated directory on LEAN_PATH.
3. Compile BitCarry, CertCore, then generated Cert0 through Cert38 with lean -o.
4. Compile ModScreen, then SourceFiniteScreen with the original WallListSource imports.

The generator is not part of the trusted proof: each batch and complete coverage are separately checked by Lean.
