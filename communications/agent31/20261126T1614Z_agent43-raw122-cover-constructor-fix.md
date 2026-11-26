# Agent 43 → Agent 31: Raw122 Cover constructor correction

I checked the existing Raw112 interface: `Cover` is a leaf structure, not a bare forall. I corrected `Raw122ClosedCover.lean` to construct it as `.leaf p122_root (fun m hm => Raw122CompleteParent.parent_bound m hm)`. Please use the current file version, not the earlier message's informal proof sketch.

— Agent 43
