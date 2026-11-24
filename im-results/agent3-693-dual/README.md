# #693: parity-separated exact inverse and dual gate reduction

**Status:** locally kernel-checked arithmetic reduction, not an authentic-root decision. The original source is [pinned upstream #693](https://github.com/google-deepmind/cryptids/blob/3647718b5df22e1a61462dec0376bd204526285a/BusyBeaver/BB6/M_1RB1RC_1LC1LC_1RE0LD_1LB1RF_HHH1RA_0RD1RD.lean), whose highLevelNext and start are transcribed exactly. Its published halting equivalence is an external premise; the upstream module itself has not been imported into this local check.

## Coordinates
Write E=u, O=v when p=0 and E=v+1, O=u when p=1 in the previous [inverse-ray model](../agent3-693-inverse-rays/README.md). Both counters are >=2, start (3,4), first reset (8,4). Encoding is (a,c)=(6E-10,O-E) if E<=O, and (6O-7,E-O-1) otherwise.

- E=O or E=O+1: halt.
- O=E+1: reset to (3E-1,4).
- E=O+2: reset to (2,3O+1).
- O>=E+2: regular E step (3E,O-E).
- E>=O+3: regular O step (E-O,3O+1).

The sum E+O strictly increases in every nonterminal transition. All predecessors of (X,Y) are precisely the following, when the respective guard holds:
1. (X/3,Y+X/3), X>=6, X mod 3=0, Y>=2.
2. (X+(Y-1)/3,(Y-1)/3), X>=3,Y>=7,Y mod 3=1.
3. ((X+1)/3,(X+1)/3+1), X>=5,X mod 3=2,Y=4.
4. ((Y-1)/3+2,(Y-1)/3), X=2,Y>=7,Y mod 3=1.

At most two predecessors; reset outputs have unique predecessors. A particular target's reachability is decidable by finite backward recursion with its sum as fuel. This is not a uniform decision of the infinite target set.

## Exact dual semigroup
A gate is any O-E in {-2,-1,0,1}, including terminal and reset. A line (A,B,D) means AO-BE=D. Let L be the least family containing (1,1,d) for -2<=d<=1 and closed under
- P_E(A,B,D)=(A,A+3B,D)
- P_O(A,B,D)=(3A+B,B,D-A).

For every E,O>=2, the regular orbit reaches a gate (allowing zero steps) iff some line in L satisfies AO-BE=D.

Proof: all lines obey A,B>=1, -A-3<=2D, D<=1. Forward pullback identities are immediate from the regular affine maps. Conversely, at a nongate state any matching P_E line forces E+2<=O: if O<E then A(O-E)<=-A but 3BE+D>=6B-(A+3)/2>-A. Any matching P_O line forces O+3<=E, since B(E-O)=3AO+A-D>0. Thus the line's last constructor gives a legal regular transition and a matching shorter line. Induction yields an actual first-gate path, with early gates allowed. A shortest witnessing word reaches its gate at exactly its length; if it encountered a gate earlier the corresponding prefix would give a shorter line. This eliminates spurious guard crossings in the existential test without any unbounded search over terminal parameters.

The authentic post-reset question is now whether a generated triple satisfies 4A-8B=D. This is still open. Failure of this equation for all generated triples would immediately certify no further gate from (8,4), hence nonhalting. Existence of a triple requires determining whether the first gate halts or resets and continuing accordingly.

## Reproduction
Decode proof.tar.xz.b64 using base64 -d, extract with tar -xJf. Archive SHA-256 0acd55bb7bd103c0bdbea80806d60c034fbe36da8394b23b14d5d5d9dfcd0231. Lean 4.36.0-rc2 (b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a). In the extracted directory:
```sh
lean -o ExactInverse693.olean ExactInverse693.lean
LEAN_PATH=. lean Conjugacy693.lean
LEAN_PATH=. lean DualGate693.lean
```
Audited theorems next_valid_rank, parents_iff, inverse_exact, exact_decision, conjugacy, forward_transport, reverse_transport, root_halts_iff, dual_good, forcedEven, forcedOdd, gate_iff_dual all use only propext, Classical.choice, Quot.sound. No sorryAx. The textual upstream import remains unverified locally because the shell cannot resolve github.com and does not have that mathlib project. The arithmetic transcription is explicitly identified, not a replacement for source provenance.
