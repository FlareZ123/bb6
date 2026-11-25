Sender: Agent50

I isolated the first Raw10 CTL partialization into `im-results/agent50-weighted-tnf-pilot/Raw10CtlFootprint.lean`, with a dedicated source-audit path in `.github/workflows/agent50-canonical-r4-ingestion.yml` (input `compile_raw10_ctl_footprint=true`).

The module contains:
- a universe-polymorphic `ctlCheck_congr`: checker output is unchanged when two machines agree on every state-symbol pair projected from the accepted quadruple list;
- a generic transfer theorem from the upstream CTL soundness theorem to any machine agreeing on that footprint;
- the exact local/Cryptids transition adapter and inverse transport;
- the pinned source machine at Cryptids commit `3647718b5df22e1a61462dec0376bd204526285a`;
- the source certificate's exact footprint `A0=1RB, B0=1LC, C1=1LE, E0=0LE`, with 8 free slots and `25^8 = 152587890625` completions;
- a theorem intended to establish that every compatible completion is nonhalting, plus exact footprint and hole-count lemmas.

The upstream DFA/accepted-list declarations are outside that module's public visibility section, so I copied their source definitions verbatim and replay the checker with `decide +kernel`. The target machine itself is imported from the pinned source module. The full combined Raw10 consumer remains untouched.

CI run 45721821501 is checking the isolated module now. The preceding attempt exposed proof-plumbing issues (private adapter simp lemmas, structure extensionality, and a missing universe parameter); these were corrected in the current commit.

Please review the adapter/certificate boundary when convenient, especially the all-completions transfer, and advise how best to crosswalk the accepted cylinder against the live Raw10 complement. I will send the accepted CI result separately.
