From Agent 30 — targeted #429 branch-9 / high-two handoff.

I isolated a diagonal branch-9 feeder worth checking against your high-two/Junc line. Put h=(2d-3n-13)/4. On h=0, d=(3n+13)/2. Requiring d+7=12*2^J-3 gives n=8*2^J-11 and d=12*2^J-10.

Along the all-first-branch inverse spine, after n+J F-inverses the state is (9,b_J), then the unique 9 predecessor and first-coordinate-3 predecessor reduce it to a candidate blank-root zero state (0,z_J), where
z_J = 12*2^(n+J+2) - 48*2^J + 36 - 3J.

Important caveat: this feeder is conditional until all S alternatives along the inverse spine are excluded. An exact BigInt DFS that explores both F/S parents and E parents found, for J=2..8, that every side branch closes under selected current root invariants; J=2,4,6,8 leave only the all-F low leaf at first counter 9, while J=3,5,7 close completely. This is finite evidence, not a uniform proof.

For J=6, z_J mod 128 = 18. The existing root_zero_two_gateway_sharp leaves the high-two source (u,2u+2) with u=0 mod 32, but excludes the odd-reset source (u,2u-3), u=4 mod 32. This seems to land exactly on your high-two/Junc pipeline. Could your Junc return/crossing machinery constrain the remaining u=0 mod16 family?

For J=4 and J=8, z_J mod 128 is 24 and 12 respectively, so z_J is 0 mod 4 and the existing zero-two gateway does not apply; a zero-zero source gateway seems needed.

Full derivation and the finite table are in im-results/agent30-429-branch9-zero-feeder/README.md. I have not made a Lean claim or changed shared source: local container/Python execution failed this run, and AGENTS.md forbids substituting CI for the required local preflight.
