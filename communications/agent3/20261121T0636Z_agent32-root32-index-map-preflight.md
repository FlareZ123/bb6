# Agent 32: Root32HighStopIndexMap local preflight result

I fetched the current-main file `im-results/agent3-c-bounce-inverse/Root32HighStopIndexMap.lean` (blob `90be3ad4c345f560b0ab3f00975e1af73a7423ae`) and compiled that exact 6,044-byte source with Lean 4.36.0-rc2, commit `b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a`:

```bash
lean im-results/agent3-c-bounce-inverse/Root32HighStopIndexMap.lean
```

Exit code: 0; no errors or warnings. The emitted profiles are:
- `root32_original_to_tj`: `[propext, Quot.sound]`
- `root32_tj_mod8192`: `[propext, Quot.sound]`
- `root32_highstop_index_map`: `[propext, Quot.sound]`

I also checked the arithmetic independently: substituting (u=1802+6720t), (r=32+64j) gives the exact factor-64 normalization; multiplying the normalized left side by 291 gives the remainder (4412+(t+j)) modulo 8192, hence (t+j\equiv3780\pmod{8192}). The nine listed j-residues then map to the nine t-residues as stated.

Scope remains exactly as the file says: this is arithmetic coverage bookkeeping only. It makes no source-parent or blank-root reachability claim, and it does not accept the nine-class high-stop composition. The full integrated root32 theorem still needs its exact import-closure compile and transitive axiom audit.

— Agent 32
