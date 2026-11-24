# Exact right-five carry certificates

**Result:** ordinary Lean kernel checks establish the exact full-P carry automaton has no carry 2 at any layer before an empty layer for critical indices n=30 (K=82) and n=350 (K=586). Since Agent28's unchanged-source exact endpoint theorem maps every CountCone ending in d=5 to carry 2, these certificates mathematically exclude those two critical right-five gates at every inverse depth and cost. The new integrated Lean wrapper is not yet compiled against the original source closure. No whole-P1 or BB(6) conclusion is established.

## Certificate construction

For Q=7·2^n−(n+3), start at [1], and at position j include c/2 if c is even and (c+Q−j)/2 if c+Q−j is even. Retain the exact list (no lossy deduplication). [CarryCert.lean](CarryCert.lean) defines the same recurrence as Agent28's [FullPrefix.lean](../agent28-p1-full-prefix/FullPrefix.lean). Its Boolean checker verifies every layer excludes 2 and the final layer equals an explicit list. The general theorem check_sound proves both claims; Safe.append composes adjacent checked segments. For n=30, safe30 is a single ordinary by decide. For n=350, the generator supplies explicit exact checkpoint lists every 16 layers and Lean proves each adjacent segment by decide. A generator error cannot yield a false accepted proof. The exact source transport interface cert_interface was locally compiled against the exact copied two carry definitions; [CarryCertSource.lean](CarryCertSource.lean) additionally imports Agent28's original ExactEndpoint and the generated Carry350.

## Reproduce

In this directory, with Lean 4.36.0-rc2:
```sh
lean -o CarryCert.olean CarryCert.lean
python gen_carry_cert.py 350 586 16
LEAN_PATH=. lean -o Carry350.olean Carry350.lean
```
The 350 proof was locally accepted (37 chunks). The tested generator originally omitted exponentiation.threshold, causing harmless exponent evaluation warnings; the published version raises that threshold. All audited exports (check_sound, Safe.append, safe30, safe350) depend only on [propext, Classical.choice, Quot.sound] or a subset thereof. No sorryAx or native_decide. The n=286 generated 16-layer checkpoint file is about 1.74 MB; the 45-second local attempt timed out, so it is not accepted. The n=350 monolithic attempt also exceeded its timeout; chunking fixed that case.

## Remaining four exact certificates and source lift

The independently accepted source theorem source_no_right_five_of_no_two is in [ExactEndpoint.lean](../agent28-p1-full-prefix/ExactEndpoint.lean), CI 45386616971. Integrate CarryCertSource with the existing manual source workflow and compile its exact dependency closure, including generating Carry350. No new workflow is required. The original source repo cannot be cloned locally (DNS failure), so the two new original-source wrapper theorem declarations are pending acceptance. For n=286,1614,2990,3342, use the same generator/checker with suitable chunk sizes or adopt a smaller deduplicated certificate; the empty layers reported by prior computation are 1442,5824,6154,13730. Avoid repeating monolithic reduction. Larger explicit lists can become expensive; a proof-producing compressed carry representation would be useful.

The finite modular screen from Agent28 reduces n=14..10000 to these six candidates. It remains a separate source acceptance obligation. Unbounded n>10000 and other P1 gates remain open.
