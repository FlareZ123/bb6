# D-root Seed31 audit diagnostic

Source workflow run: 43383130552

## Error and axiom markers
884:im-results/agent2-packet-shift/P2ResetRegularReentry.lean:16:2: error: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
889:'BB6.P2ResetRegularReentry.e_two_reset_regular_reentry' depends on axioms: [sorryAx]

## Final 100 audit lines
'CryptidBoundary.full_A_1100' depends on axioms: [propext, Quot.sound]
'CryptidBoundary.a1100_prefix_nonPhysical' depends on axioms: [propext, Quot.sound]
'CryptidBoundary.sweepD_noF' depends on axioms: [propext, Quot.sound]
'CryptidBoundary.a1100_first_physical' depends on axioms: [propext, Quot.sound]
'CryptidBoundary.a110111_start' depends on axioms: [propext]
'CryptidBoundary.a110111_run' depends on axioms: [propext, Quot.sound]
'CryptidBoundary.full_A_110111' depends on axioms: [propext, Quot.sound]
'CryptidBoundary.a110111_prefix_nonPhysical' depends on axioms: [propext, Quot.sound]
'CryptidBoundary.a110111_first_physical' depends on axioms: [propext, Quot.sound]
'BB6.CryptidAGenericClosure.lift_first_return' depends on axioms: [propext, Quot.sound]
'BB6.CryptidA110111CodeFirst.full_A_code_110111_first_return' depends on axioms: [propext, Quot.sound]
im-results/agent2-packet-shift/AP2PacketBoundarySource.lean:44:33: warning: This simp argument is unused:
  List.append_assoc

Hint: Omit it from the simp argument list.
  [apply] simp [CryptidA.wordCode, ih]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
im-results/agent2-packet-shift/AP2PacketBoundarySource.lean:53:29: warning: This simp argument is unused:
  List.append_assoc

Hint: Omit it from the simp argument list.
  [apply] simp [CryptidA.wordCode, CryptidBoundary.pairs, List.replicate_succ, ih]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
im-results/agent2-packet-shift/AP2PacketBoundarySource.lean:87:6: warning: This simp argument is unused:
  List.append_assoc

Hint: Omit it from the simp argument list.
  [apply] simp [CryptidBoundary.pairs, CryptidBoundary.oppairs, ih]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
'BB6.Agent2AP2PacketBoundary.a_p2_packet_reentry' depends on axioms: [propext, Quot.sound]
'BB6.Agent31SecondSource.first_source' depends on axioms: [propext, Quot.sound]
'BB6.Agent31SecondSource.second_source' depends on axioms: [propext, Quot.sound]
'BB6.Agent31SecondSource.two_returns_source' depends on axioms: [propext, Quot.sound]
'BB6.Agent31PacketSource.b_packet' depends on axioms: [propext, Quot.sound]
'BB6.Agent31PacketSource.e_packet' depends on axioms: [propext, Quot.sound]
im-results/agent2-packet-shift/BoundaryBZero.lean:45:51: warning: This simp argument is unused:
  List.append_assoc

Hint: Omit it from the simp argument list.
  [apply] simp [regularSection, oppairs, List.replicate_succ]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
'BB6.Agent2BoundaryBZero.b_zero_source' depends on axioms: [propext, Quot.sound]
'BB6.Agent2BoundaryBZero.e_one_regular' depends on axioms: [propext]
im-results/agent35-d-sixth-rejoin/SixthRejoin.lean:83:13: warning: This simp argument is unused:
  List.append_assoc

Hint: Omit it from the simp argument list.
  [apply] simp [init]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
'BB6.Agent35SixthRoot.universal_reentry' depends on axioms: [propext, Quot.sound]
'BB6.Agent35SixthRoot.true_root_t_mod27' does not depend on any axioms
'BB6.Agent35SixthRoot.blank_sixth_reentry' depends on axioms: [propext, Classical.choice, Quot.sound]
'BB6.Agent35SeventhRoot.terminal34_exact' does not depend on any axioms
'BB6.Agent35SeventhRoot.seventhException_original' depends on axioms: [propext, Classical.choice, Quot.sound]
'BB6.Agent35SeventhRoot.seventhReentry_original' depends on axioms: [propext, Classical.choice, Quot.sound]
'BB6.Agent2EighthRoot.terminal6046_exact' does not depend on any axioms
'BB6.Agent2EighthRoot.eighthException_original' depends on axioms: [propext, Classical.choice, Quot.sound]
'BB6.Agent2EighthRoot.eighthReentry_original' depends on axioms: [propext, Classical.choice, Quot.sound]
im-results/agent31-d-exceptional/PacketRank.lean:53:8: warning: Variable name `h` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _h

Note: This linter can be disabled with `set_option linter.unusedVariables false`
'BB6.Agent31PacketRank.one_is_terminal' does not depend on any axioms
'BB6.Agent31PacketRank.advance_rank' depends on axioms: [propext, Quot.sound]
'BB6.Agent31PacketRank.normalizeWithCount' depends on axioms: [propext, Quot.sound]
'BB6.Agent31PacketPaths.edge_sound' depends on axioms: [propext, Quot.sound]
'BB6.Agent31PacketPaths.edge_rank' depends on axioms: [propext, Quot.sound]
'BB6.Agent31PacketPaths.path_sound' depends on axioms: [propext, Quot.sound]
'BB6.Agent31PacketPaths.path_rank_bound' depends on axioms: [propext, Quot.sound]
'BB6.Agent31PacketPaths.path_count_bound' depends on axioms: [propext, Quot.sound]
im-results/agent2-packet-shift/PacketP2ResetSource.lean:72:29: warning: This simp argument is unused:
  List.append_assoc

Hint: Omit it from the simp argument list.
  [apply] simp [List.replicate]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
'BB6.Agent2PacketP2Reset.e_two_reset' depends on axioms: [propext, Quot.sound]
im-results/agent2-packet-shift/PacketP2ResetSource.lean:151:54: warning: This simp argument is unused:
  List.append_assoc

Hint: Omit it from the simp argument list.
  [apply] simp [BB6.Agent2BoundaryBZero.regularSection, marker]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
'BB6.Agent2PacketP2Reset.b_zero_any' depends on axioms: [propext, Quot.sound]
'BB6.Agent2PacketP2Reset.e_two_k0_regular' depends on axioms: [propext, Quot.sound]
im-results/agent2-packet-shift/P2ResetRegularReentry.lean:16:2: error: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
'BB6.P2ResetRegularReentry.e_two_reset_regular_reentry' depends on axioms: [sorryAx]

## Seed31 probe output
