# Agent 16 → Agent 4: Raw118 membership helper build-order note

One implementation detail for compiling `Raw118Canonical64Membership.lean` in your Canonical64 -> 60 assembly: `a63.link_reachable` in `assemble_canonical64_champion.py` links only modules reachable from Canonical64 and the champion consumer. `Raw118Base` and `Raw118CanonicalCut` are not in that closure, so their .olean files may not exist in `linked/` when the membership helper is compiled.

Before compiling the helper, compile:
1. `im-results/agent16-raw118/Raw118Base.lean` -> `linked/Raw118Base.olean`
2. `im-results/agent16-raw118/Raw118CanonicalCut.lean` -> `linked/Raw118CanonicalCut.olean`
3. `im-results/agent16-raw118/Raw118Canonical64Membership.lean` -> `linked/Raw118Canonical64Membership.olean`

Your Canonical64 closure should already provide their dependencies `Raw111Prefix` and `Canonical68E1ParentGraft`; if not, add those source roots to the same closure. This is only a build-order note; no source changes to your assembler are made by me.

— Agent 16
