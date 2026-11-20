# S-indexed mass-window reset diagnostic

**Status:** exact recurrence replay over an existing finite root interval; not an all-time proof.

This test transfers the 263-state common-reset DFA to the **S-indexed mass window** from Agent 41's `MonotoneMassWindow.md`, rather than reusing the q-indexed diagnostic window.

For each source root transition (D(a,d)\to D(a',d')), put (S'=a'+d'), let (ell') be least with ((3^{\ell'}-1)/2\ge S'+3), and set
[
B' = \max(34\ell'+140,36\ell'+88).
]
Let (k') and (j') be least with (3^{k'}>B') and (3^{j'}>(B')^3). Using the exact next-state signed coordinates (x',y'), the tested word is
[
((x'_i,y'_i): k'+2\le i\le j'-3),
]
the full next-state middle interval used by the mass-window argument.

## Results

- Root transitions (n=33\ldots10000): **9,968**.
- Common reset DFA acceptance: **9,968 / 9,968**, with no failures.
- First accepting end position: at most **12** symbols.
- Acceptance-end histogram: `{"3":2196,"4":4210,"5":2241,"6":866,"7":290,"8":105,"9":37,"10":14,"11":6,"12":3}`.
- Observed S-window shifts: `(k'-k,j'-j)=(0,0)`: 9,955; `(0,1)`: 8; `(1,1)`: 5. All are within the source-proved bounds `k'-k ∈ {0,1}`, `j'-j ∈ {0,1,2,3}`.
- Extending the same check to transitions (n=9\ldots32) gives 21 finite-prefix failures and three passes (indices 28, 31, 32). The 21 failing output words are short constant/near-constant blocks; the exact list is recorded in the JSON. Thus the reset invariant can be started at state (D(33)) after explicitly checking the finite prefix.
- Testing only the old-output overlap ([k+3,j-2)), without the full next-state high extension, fails at three transitions (34, 36, 38), while the full next-state middle interval succeeds. The high extension is therefore genuinely relevant and must be included in the transducer phase.

## Interpretation

This is the first reset-language diagnostic aligned with the **correct S-indexed inductive window**. It resolves the earlier q/S indexing mismatch: the q-indexed 262 boundary-phase list remains useful as a separate diagnostic, but this test uses the mass-indexed next-state interval directly.

The finite result strongly supports the candidate invariant: after the explicit prefix to (D(33)), the full S-indexed middle word contains a common reset pattern by position 12. It does not yet prove this for all future states. The remaining mathematical task is to derive a source-level finite/weighted phase transition that preserves this reset property under every exact branch and the mass-window shift, rather than extending the scan horizon.

Machine-readable summary: [MassWindowResetDiagnostic.json](MassWindowResetDiagnostic.json).
