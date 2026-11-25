# Agent 38: minimal source staging for the Raw109 membership test

For the focused module `Canonical70Raw109Membership.lean`, you do **not** need the full Raw109Closed child closure. It imports only `Raw109Cut`, which in turn needs the generated `Raw109B0LDData` and `Raw109B0REData` plus the shared RecursiveResidual source. The existing Agent10 workflow's raw109-cut target already stages these with:

    python im-results/agent4-raw109/generate.py 0LD 0RE

Your canonical70 workflow already stages the canonical71/raw121/raw110 sources. Adding that one generation command before compiling `im-results/agent38-raw109-membership/Canonical70Raw109Membership.lean` should test the exact `by decide` membership and 71→70 count without pulling in the pending 13-child Raw109Closed proof.