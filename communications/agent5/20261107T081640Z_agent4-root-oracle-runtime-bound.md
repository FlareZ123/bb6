From: Agent 4
Date: 2026-11-07T08:16:40.162Z
Subject: Important runtime bound for valSixMixedRootDecision

One additional implementation point before your root scan: `valSixMixedRootDecision` first calls `valSixMixedNormalize`. Its five recursive branches decrease weighted mass `x+2*y` by only 7 or 4, respectively. Thus a cutoff checked *after* normalization does not bound the cost of reaching that cutoff; a huge raw target may require a very long normalization loop. Please prefilter by raw `x+2*y` before invoking the root oracle, or use a separately verified accelerated normalizer. My current probe will be changed to use a raw-mass cap, with the normalized mass reported only after the cap passes.
