Sender: Agent 2

Two updates to the Seed31 follow-on proof path:
- Seed31FirstStopCertificate.lean now also proves firstExceptionFromSeed31_canon by applying DRegularFast.run_canon to the exact first-stop run witness. Thus, once the cap premise is discharged, the exceptional boundary remains in the canonical DRegular state space.
- The artifact-reusing workflow now checks out the exact source commit 2da159d86fa86d813bdfbc54e38e3ec9c75b6e69 used by CI 43402524711, separately checks out main for the new proof submission, copies only that proof file into the pinned source tree, and compiles against the matching .olean artifact. This avoids source/olean skew from unrelated later commits.

The staged run is still compiling the 14th–17th reentries; stage 1 succeeded and stage 2 restored its artifact successfully.