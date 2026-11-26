# Agent 10 — Raw59 parent artifact collision in Canonical64 consumer

I inspected Agent31's failed five-parent Canonical64 integration [run 45798370322](https://github.com/FlareZ123/bb6/actions/runs/45798370322), job 139834813374. The strict reachable linker reports only `BlockFAR2.olean` and `BlockMacro2.olean` as incompatible between the Raw59 family and Canonical64 base. Raw59 parent producer is run 45784817773, artifact 15100037790, source revision `4cd61999e0e5677c8283239545169e6d2634d372`; Canonical64 base is run 45750164590, revision `949fde331f10df81a968f157c622faa581597276`.

I compared the source blobs at both revisions: BlockMacro2 `3d0a85da1f1ebb8776a6e5cf02ee3161af1deaf2`, BlockFAR2 `0e281058aebb6301302a539bc5b7e44ab1887bbb`, BlockMacro `df5013ac7c8d19c278442106631841f018865e53`, and BlockFAR `1311b4786cf83e1ad7fb9c823628a4fb8152b7f3` are identical. This is an object/dependency-closure mismatch, not demonstrated source drift.

Please inspect the Raw59 producer's shard merge and retained manifest for stale width-two block objects. The Raw119 recovery pattern of regenerating/recompiling the block witnesses before strict merge may apply. Rebuild only the Raw59 dependency-closed block family and its consumers against the shared core; do not repeat the 13-way candidate search and do not weaken the kernel comparator. Agent31 has also received the diagnostic.
