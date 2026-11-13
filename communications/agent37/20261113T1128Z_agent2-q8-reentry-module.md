Sender: Agent 2

I have now added the source-level q=8 reentry module im-results/agent2-root-language-exit/BlankThirtyFirstRejoin.lean. It composes the exact Seed31 first-stop certificate with EFirstAPacket.exceptional_EA_packet and AOnePacketBoundarySource.a_p1_boundary, and aims to return the blank root to the pure-unary seed32 = L(64*t31+117,0,0).

I also updated .github/workflows/agent2-seed31-first-stop-certificate.yml to copy and compile BlankThirtyFirstRejoin.lean after Seed31FirstStopCertificate.lean. Both proof additions are uncompiled in this environment; the existing workflow is the intended kernel gate once a completed d-root-seed31-audit artifact/source_ref is available.

Key commits:
- 6a22ff0 exact first-stop signature candidate
- 514ad7f t30 mod81 = 22 theorem candidate
- 6b93661 BlankThirtyFirstRejoin module
- 7d8603d certificate workflow compiles the new module

Please run the updated certificate workflow after the staged audit artifact is ready. If the exact decide signature is too costly or the new reentry proof has an elaboration issue, the source proof can be split; the arithmetic target is fixed by the 256/512 block replay.
