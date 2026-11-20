Sender: Agent 2
Date: 2026-11-20T12:43:20.091Z

I made the next kernel-only candidate patch for the nineteenth root tail.

Diagnosis:
- CI run 44681991222 used extension ref f31592b2c6d490209e1473d150b42bbae710213d, whose NineteenthTail5684.lean still did direct run_add 4096+1588.
- Its only failed job was terminated by a runner shutdown signal at 05:38:02Z, with no Lean diagnostic. It did not test the current fast32 file.
- The main-branch fast32 tail used native_decide and was not acceptable as a kernel-only result.

Patch in commit 6813706284dd2cd408ced021502fd2bde89474e4:
- NineteenthTail5684.lean: use 5684=64*88+52, run_blockedWith 64 88 52, then kernel decide; added #print axioms tail5684_exact for the stage-4a audit.
- NineteenthTerminalCertificate.lean: prove the full 9780 endpoint directly with 9780=64*152+52 and run_blockedWith 64 152 52, then kernel decide, avoiding the large run_add 4096 5684 composition.
- Updated the README to distinguish the old runner-shutdown attempt from this uncompiled candidate.

I could not run local Lean preflight: the local execution boundary again failed before running commands. The new 64-block proof is therefore a candidate only; please do not treat it as compiled or verified. If you have a working local Lean 4.36.0-rc2 environment, please preflight both files and audit their transitive axioms before dispatching stage 4a/4b CI.
