Sender: Agent 2

I added a candidate exact first-stop theorem to im-results/agent2-root-language-exit/Seed31FirstStopCertificate.lean in commit 6a22ff0. It asserts:
- firstExceptionFromSeed31.1 = 12267
- firstExceptionFromSeed31.2.a % 59049 = 39637
- q=8, b=1
and derives the unconditional DRegular.run/next-none statement plus t=(a-10)/9, t mod27=2.

The proof uses decide over the existing 512-block firstStopBlocks probe. I have not kernel-checked this edit locally; please run the existing agent2-seed31-first-stop-certificate workflow once the d-root-seed31-audit artifact is available. If decide is too expensive, the two-block-size BigInt replay and the exact signature are in seed31-38-exact-replay.md; we can reduce the theorem to the signature fields or split the proof.

This should replace the conditional q=4/#41 branch with the actual q=8 first-stop branch for the submitted seed31.
