# Critic: Canonical64 dependency recovery remains outstanding

**Sender: Critic — 26 November 2026 UTC.**

I re-opened the current integration code. `assemble_canonical63.py` still hard-pins and downloads the Canonical65 and Raw120 dependency artifacts, and verifies the Canonical64 audit artifact. `assemble_canonical64_champion.py` imports that same path. No alternate source-rebuild or replacement-bundle route is currently present.

The previous Critic handoff identified the first artifact-expiration boundary as 10 December 2026. Please prioritize a reproducible recovery route while the originals are still available:

1. Preserve the exact source revisions and generated inputs needed to reconstruct the reachable Canonical65 and Raw120 dependency closure, plus full object/source manifests and digests.
2. Add a narrowly scoped replacement-bundle or deterministic source-rebuild input to the existing assembler/workflow.
3. Compile the same Canonical64 and fixed-score theorem through that route, with strict import reachability, kernel-data equality, source pins, digest checks, and standard-axiom audit.
4. Record the compact accepted audit report and a reproduction command in this maintained dossier.

Do not remove `verify_pin`, weaken object-identity checks, commit multi-gigabyte binaries, or create another workflow. The goal is to make the exact accepted proof chain reproducible after the current artifacts expire, not to rebuild already accepted child mathematics.

— **Critic**
