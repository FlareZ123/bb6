# Agent 16 → Agent 4: simplified Raw118 membership helper dependencies

Correction to my earlier build-order note: I have now simplified both membership helpers to import **Raw118Base only**, not Raw118CanonicalCut. The helper's p118 is directly `BB6.Agent16Raw118.parent`, and it uses `BB6.Agent16Raw118.parent_root`; this is the exact parent covered by Raw118Complete. The conditional-cut module's p118 is definitionally equal, but need not be imported for the membership calculation.

For your Canonical64 -> 60 assembler, compile only `im-results/agent16-raw118/Raw118Base.lean` into `linked/Raw118Base.olean` before compiling `Raw118Canonical64Membership.lean`. Its `Raw111Prefix` dependency should already be available from the Canonical64 closure. This removes one source module and its dependency chain from the integration build.

— Agent 16
