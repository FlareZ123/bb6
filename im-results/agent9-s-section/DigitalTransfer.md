# S-to-T transfer guard is an exact finite 3-adic cylinder property

**Intermediate research, Agent 9, 2026-11-02.** This extends [DigitalAperiodic.md](./DigitalAperiodic.md). It neither decides cryptid_9 nor BB(6).

The [original DeepMind certified accelerator](https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/M_1RB0LB_1LC0RE_1LA1LD_0LCHHH_0RB0RF_1RE1RB.lean) contains S(b,c) whose q=b+16 projection is a 3-branch piecewise map f(q), as documented in the companion report. For each n>=0, define `transferWithin n q c` to mean the S section transfers to the T section on one of its first n attempted calls, using the original exact c updates: -1 at q%3=0 (except the transfer guard at c=0), +4 at residue1, +6 at residue2. When transfer happens, this predicate stops; the underlying q-only map is used only to express the recursion.

**Lean-certified universal theorem `Agent9.transfer_cylinder_exact`:** for every n,c and q,r with 16<=q<=r,

`3^n | (r-q) -> (transferWithin n q c <-> transferWithin n r c)`.

The proof composes the exact residue-history cylinder theorem `digital_cylinder_exact` with an induction proving that the c trajectory and transfer decisions depend only on the residue word. The 3^n modulus is exact as a residue-history classifier, but it is not claimed minimal for the Boolean transfer outcome.

This turns an n-step transfer inquiry from any fixed S entry into a precise arithmetic union of base-3 cylinders. For the actual blank-derived entry S(b=125,c=3), q=141, this gives rigorous finite-horizon transfer-exclusion classes of all nonnegative q congruent to 141 modulo 3^n. Infinite-horizon safety for q=141 remains open, and a finite-horizon class gives no such result.

Proof source: [DigitalTransfer.lean.gz.b64](./DigitalTransfer.lean.gz.b64), single base64-encoded gzip containing the entire Lean 4.36.0-rc2 source. Decode with standard Python base64 and gzip libraries and check its SHA-256 `f8b33583b5611a4d162c375594724eae2639a49b4a3745e485c14a77a177b4e1` before compiling. The source is standalone, contains all first-stage proofs and source branch identities, and prints `[propext, Quot.sound]` for the transfer theorem, without sorryAx. Verified locally by the Lean kernel; copied compressed source was independently checked against the local exact byte stream using length=3332 and FNV32=a93c9a8.

**Next mathematical bottleneck:** Construct an effectively checkable infinite symbolic language or inductive region that excludes all transfer-admissible cylinders containing q=141. This theorem supplies exact finite cylinder semantics; it does not exhibit the requisite global language.
