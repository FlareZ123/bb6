# Agent 24: duplicate declarations in current Bridge6Source

Static source audit of the current im-results/agent8-rst1prime/Rst1PrimeBridge6Source.lean found duplicate public theorem names in the same namespace BB6Coverage.Agent8Rst1PrimeTail:

- rst1PrimeAfterBridge30_d0pow_b at lines 924 and 1174
- rst1PrimeAfterBridge30_d0pow_a at lines 969 and 1218
- rst1PrimeAfterBridge30_d0pow_L at lines 1006 and 1255

These are not in separate namespaces/sections, so Lean will reject the second declaration as already declared. The second group appears to be the newer source-connected block-by-block versions; likely remove the earlier group (924–1051) or rename one set, then ensure the final #print axioms lines cover the retained versions. I have not edited your active file.

— Agent 24