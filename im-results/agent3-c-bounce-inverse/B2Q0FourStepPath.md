# Root32 B2→high-stop inverse chain

**Status: intermediate source-orbit reduction, not a Machine C nonhalting proof.** The same-parameter forward path and q=0 residual parameter bridge are explicit. The new local Lean source-parent chain reduces exact root32 high-stop reachability to D0E(t), L(t), or P7E1E(t). A corrected paper-level analysis of P7E1E produces an additional odd/odd high-valuation residual A4(t) on eight of the nine indexed t-cylinders. Consequently the earlier claims excluding r≡9568 and r≡10592 (mod 16384) are not established: their t=47 and t=31 mod256 classes retain A4. The t≡1 mod16 cylinder has a paper-level A4 exclusion, but it is not yet Lean-formalized. The core inverse modules compile locally; exact transitive import-closure compilation and CI remain outstanding.

## 1. The same-parameter forward path

The five forward edges, the exact root parameter bridge, and the B2-to-high-stop path remain as recorded in the preceding sections of this dossier. The reverse source-parent chain is now formalized in `Root32HighStopIntegrated.lean`, `Root32HighStopS1.lean`, and `Root32HighStopP7.lean`.

## 2. Exact S1 parent fan

The S1 target has a complete source-parent classification. Under the exact root32 B0 exclusion and u≡2 (mod 8), its only surviving parents are D0(u) and P7(u). The source-level proof is `S1_reach_implies_D0_or_P7` in `Root32HighStopS1.lean`.

## 3. Corrected P7 source-parent fan

Both D0 and P7 are even/even sum-zero targets. Their exact source-parent alternatives are:

\[
\begin{aligned}
D_0(u)&:\quad (874496u+58806,87040u+5852),\quad (218624u+14700,414976u+27902),\\
P_7(u)&:\quad (525656u+35334,261460u+17576),\quad (131414u+8832,458581u+30824).
\end{aligned}
\]

**Correction (2026-11-21):** the former P7 bounce-left coordinate `131414u+8830` was wrong by two. Since the sum quotient is `S=65707u+4417`, the source theorem gives `2*S-2=131414u+8832`. This changes the residue of the next parent and invalidates the old one-step P7E exclusion.

The direct parent of D0 is excluded: its sum is `961536u+64658 ≡ 2 (mod 8)`, so its forced even-right predecessor is `(961536u+64656,43520u+2925)`, an odd-right target with sum `1005056u+67581 ≡ 1 (mod 4)`. Thus reachability of D0 forces `D0E(u)=(218624u+14700,414976u+27902)`.

For P7, the direct branch is forced through `R1(u)=(787116u+52908,130730u+8787)` by the even-right inverse, then through the exact odd-a depth-zero parent `R2(u)=(458923u+30845,(589653u+39630)/2)`. A further even-right inverse gives `L(t)=(5065196640t+1358307257,990617040t+265648583)` when `u=1802+6720t`.

The corrected P7 bounce branch is `P7E(u)=(131414u+8832,458581u+30824)`. Its first even-right parent is `P7E1(t)=(3964766400t+1063210644,1540832160t+413196892)`. Crucially this target has sum `5505598560t+1476407536=8*(688199820t+184550942)`, with quotient congruent to two modulo four. Therefore the even-right uniqueness theorem does not apply at this stage. The exact even/even sum-zero parent fan instead leaves:

\[
\begin{aligned}
P_{7E,2}(t)&=(5505598560t+1476407534,770416080t+206598445),\\
P_{7E,1E}(t)&=(1376399640t+369101882,2835015540t+760251268).
\end{aligned}
\]

The direct parent `P7E2` is excluded: its sum-plus-one is `6276014640t+1683005980 ≡ 4 (mod 8)`, so its unique odd-a depth-zero parent is `(3138007320t+841502987,1954211700t+524050715)`, which is odd/odd with sum two modulo four and is excluded by `blank_no_odd_sum_two`.

The bounce parent `P7E1E` has a further paper-level source parent for every odd t:

\[
A_4(t)=\left(2814461475t+754739388,\frac{4231969245t+1134865019}{2}\right).
\]

For `t≡1 (mod 16)`, A4 has even right coordinate and sum three modulo eight; its forced even-right parent is odd-right with sum two modulo four, so this branch is excluded on that cylinder. For `t≡3 (mod 4)`, however, A4 is odd/odd with sum divisible by eight, not sum two modulo four. It is not excluded by `blank_no_odd_sum_two`. The eight remaining root32 parameter classes therefore retain the explicit odd/odd residual A4(t). Its sum modulo 32, in the order `t≡47,31,79,15,159,719,1167,7839`, is `16,24,0,0,24,0,0,24`. The existing `oddodd_sum16_blank_reach_iff` handles the first residue class modulo 32 only; the other high-valuation odd/odd source fans remain to be resolved. `oddodd16_double_forbidden_rectangle` does not directly apply to A4, whose coordinates are `(1,7) mod 8`, rather than its required `(5,3) mod 8`.

## 4. Status of the previously claimed high-stop progressions

The earlier versions of this dossier described `r≡9568,10592 (mod 16384)` and `r≡224 (mod 1024)` as complete high-stop exclusions. **Withdraw that status pending the corrected P7 bounce branch.** Those compositions closed the D0E and L alternatives but relied on the now-invalid immediate P7E no-parent claim.

The exact inverse chain is now Lean-checked through:

\[
T(u)\text{ reachable}\Longrightarrow D_{0E}(t)\text{ reachable}\ \lor\ L(t)\text{ reachable}\ \lor\ P_{7E1E}(t)\text{ reachable}.
\]

The eight cylinders with `t≡15 (mod 16)` retain A4 and include the t=47 and t=31 classes underlying the former r=9568 and r=10592 claims. The t=1 mod16 cylinder has a further paper-level exclusion of A4, but that argument also needs a Lean source-parent proof before the former r=224 claim can be treated as established.

The linked dossiers `Root32HighStopR9568.md`, `Root32HighStopR10592.md`, and `Root32HighStopR224.md` remain useful for their D0E/L sub-branch calculations, but they are not complete high-stop exclusions until the P7 bounce/A4 alternative is closed. Do not count these three progressions as proven nonhalting or high-stop exclusions in coverage summaries.

## 5. Verification boundary and next decisive action

- The T→Q→S3→S2→S1 inverse chain, the S1→D0∨P7 fan, the P7→L∨P7E1E fan, and D0→D0E are Lean-compiled in the three source modules under Lean 4.36.0-rc2 with precompiled dependencies.
- `Root32HighStopAxiomAudit.lean` prints the axiom profiles of the composed chain and key source lemmas; the local output contains no `sorryAx` in those audited dependencies.
- The exact transitive import closure of the new modules has not yet been rebuilt from source; no CI run is being treated as a substitute.
- The D0E/L branch calculations and A4 follow-on are still paper-level; the earlier r=9568/r=10592/r=224 exclusion status is withdrawn pending closure of the P7 bounce/A4 branch.

The next decisive action is to resolve the eight odd/odd A4(t) source-orbit families (`t≡15 mod16`), separately formalize the t≡1 mod16 A4 exclusion, then re-evaluate the D0E/L sub-branch dossiers and rebuild the exact transitive Lean import closure. Do not add further residue cylinders before these blockers are resolved.
