# A-step2 root near-hit: eight digits of the external halting cylinder

**Status: exact integer computation in the source-family interpreter; not a Lean proof of the composed root path.**

The reproducible script is [`halting-cylinder-root-shadow.py`](./halting-cylinder-root-shadow.py). It imports the existing [`macro_engine.py`](../agent37-root-language-pilot/macro_engine.py) rather than reimplementing its transition rules, and compares its first 20,000 sections from `Config(9, "")` with the external trace in [`macro_trace.json`](../agent4-cryptid-macro-replay/macro_trace.json).

Let
[
C=1975700577069254261393123959451562008800234946348086,
]
the published starting residue for the external halting cylinder.

The best pure-unary section in this finite interpreter run occurs at section index **13,233**. Its exact arithmetic properties are:
- suffix is empty;
- (v_3(n-C)=8), so (n=C+3^8p);
- (p\equiv2\pmod3);
- (n\bmod3^{10}=36961), whereas (C\bmod3^{10}=23839).

Starting from this section, the next nine branch letters are
[
\texttt{EEBBEBEEE},
]
whereas the external 107-call certificate begins
[
\texttt{EEBBEBEEB}.
]
Thus the two paths agree for eight branches and diverge at the ninth: the interpreter's root path takes E where the published certificate takes B.

The same 20,000-section replay encounters three `E_pairs_1100` transitions at indices 8,394, 9,422, and 12,089, with input (n\bmod27=22,10,22), respectively. These are important source-composition points; the Python interpreter's transition outputs do not by themselves establish a composed original-machine run.

## Interpretation and next proof obligation

This is a useful target for a source-level composition theorem, not evidence that the authentic blank root reaches section 13,233. The existing `ARegular3AdicBridge.lean` explicitly does not identify the A-step2 macro endpoints with all DRegular first returns. To promote this observation to a theorem, one must prove the relevant A-step2/source-family transitions and compose their `ObsEq` runs from the authentic blank-root prefix. The three `E_pairs_1100` transitions should be checked against the exact hypotheses of `EAllDouble.lean` and the corresponding source-family lemmas; no unproved residue generalization should be inferred from the interpreter.

The separate [`HaltingCylinderShadowFast.lean`](./HaltingCylinderShadowFast.lean) candidate concerns the DRegular source-connected 2,640-step, seven-branch shadow. It is a different path and remains uncompiled.


## Relation to prior root scans

The existing `im-results/agent37-root-language-pilot/README.md` already reports a separate 2.7-million-section root scan with a best 21/108 prefix match. This 20,000-section observation does **not** improve that record. Its value is the compact, reproducible index-13,233 checkpoint and its exact (3)-adic valuation, which can serve as a small regression target for a future formal source interpreter.
