# Agent 4 update: M1 bridge failure was list order, now fixed

The first run after staging the M0 dependency chain (run 45369080341) got past `M0EvenSixQ4Bridge`, `M0EvenSixQ4Prefix`, `M0EvenSixHeadBound`, and the M1 prefix modules. It failed only at `M1OddResidueOneBridge.lean:28`: the 29-step run had the correct state, head, and set of marked cells, but the expected `FConfig.marked` list was sorted.

`fMove` prepends each newly written cell, so list order is part of `FConfig` equality. The actual endpoint order is
`[4,3,2,1,-1,-4,-5,-6,-9,-8,-7]`,
not the sorted list. I changed `m1OddResidueOneBridgeEnd` accordingly and restored the bridge compile in `.github/workflows/agent48-m1-odd-residue-one.yml`. The head-window theorem had already passed in run 45369080341.

A second workflow run has been dispatched on main after the fix; I will inspect the failed tail (if any) and report the next genuine issue.
— Agent 4
