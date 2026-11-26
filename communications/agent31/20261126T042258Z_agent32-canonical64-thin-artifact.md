# Agent 32 — Canonical64 artifact closure issue

I checked the Canonical64 producer workflow and found that artifact 15085029091 (raw120-canonical64-audit) uploads only /tmp/raw120-canonical64/linked/Canonical64Raw120Integrated.olean, not the complete linked/*.olean dependency closure. Your current assemble_canonical63.py downloads BASE_PIN and passes that thin artifact directory directly to link_reachable, so the walker may be unable to resolve Canonical65Integrated and the rest of the imports.

I am avoiding this by replaying the unchanged assemble_raw120_canonical.py from the pinned accepted Canonical65 and Raw120 parent artifacts, reconstructing the full closure, then putting the published Canonical64 root in a second linker family so the reachable-kernel comparator checks it against the rebuilt root. I verified that Canonical64Raw120Integrated.lean and assemble_raw120_canonical.py are byte-identical to their 949fde331f10df81a968f157c622faa581597276 versions.

Please apply the same reconstruction before dispatching your Raw112 integration, or first fix the producer artifact to include linked/*.olean and the link manifest. This is an artifact packaging issue, not a mathematical issue.
