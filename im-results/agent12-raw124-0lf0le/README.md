# Raw124 F1=0LF / F0=0LE — complete weighted child cover

**Status:** all 206 generated Lean modules compiled locally under Lean 4.36.0-rc2 against the accepted Raw58 core artifact 15090715339. The final theorem `BB6.Agent12Raw124ZeroLF0LE.bound_all` proves `∀ m, compatible pChild m → WeightedBound 2455 m`. This is artifact-backed local kernel validation, not a fresh source CI acceptance.

Exact child: `1RB---_1RC---_0RD---_1LD1RE_---1LF_0LE0LF` (four holes, 25^4 = 390625 completions).

Partition (cap 3000, lookback 32): 65 splits, 970 cycle leaves, 401 last-hole leaves, 125 additional open leaves. Completion masses: cycles 334450, bounded 30850, additional certificates 25325. All 125 formerly open leaves closed by 90 FAR and 35 two-sided stack abstractions. Maximum first query 2449; weighted bound 2455. The final root checker and bound_all report [propext, Classical.choice, Quot.sound].

## Reproduce

In this directory unpack the committed generator and witnesses:

```python
import base64, gzip, json
from pathlib import Path
for name, content in json.loads(gzip.decompress(base64.b64decode(Path("bundle.json.gz.b64").read_bytes()))).items():
    Path(name).write_text(content)
```

Run `python generate_0le.py OUT`. The generator uses Agent2's exact fast_partition.cpp and asserts both partition and open-list digests. Apply the following mechanical substitution to the generated Lean files before building in build_order.txt order; it switches to the already accepted zipper-based checker, preserving every certificate and table.

```python
from pathlib import Path
out = Path("OUT")
for p in out.glob("Raw124*.lean"):
    p.write_text(p.read_text().replace("import Raw124FastAudit", "import ZipThreeHoleAudit")
      .replace("BB6.Agent2Raw124FastAudit", "BB6.Agent10ZipAudit")
      .replace("fastCheck", "zipCheck")
      .replace("fastQuery", "zipQueryOK")
      .replace("fastCertified", "certifiedZip"))
```

Build each module with `lean -o MODULE.olean MODULE.lean`, setting LEAN_PATH to the generated directory and accepted core dependency directory. Final module Raw124ZeroLF0LE.lean imports the composed root.

- Generator bundle Git blob: 45f20523afcb3552331c6565c0b4b515dd8abdfc.
- Partition SHA256: 2938053d34f3b121125d62b9ea0abae4e4e78e9226e8d37db4a6c2fdba4f8884.
- Open list SHA256: 10e1bd2fed98e528c4a647e5d1676fede7d36994d9a5b902b3e73ae2a4a6a88d.
- fast_partition.cpp Git blob: 004d096513b096e830846dcd71324db548f0bab7.
- Lean binary SHA256: db7f559d05795e7af52e42bc966c90240a39dcb9712161c54c97afa546e20c00.
- The original finite-ray checker became expensive on an entry 776 / period 866 cycle. The existing zipper checker completed it in about 8 seconds. M122 was reduced to a (6,2,3) run abstraction with 1011 abstract configurations, avoiding the larger timed-out abstraction.

No full Raw124 parent Cover or global exactness claimed here. This child is ready for parent composition with its siblings.
