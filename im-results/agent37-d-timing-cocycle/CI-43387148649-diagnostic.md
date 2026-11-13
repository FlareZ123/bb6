# D-root Seed31 audit diagnostic

Source workflow run: 43387148649

## Error and axiom markers
897:im-results/agent2-packet-shift/PacketSafeExit.lean:153:7: error: unknown tactic
898:im-results/agent2-packet-shift/PacketSafeExit.lean:152:25: error: unsolved goals
908:im-results/agent2-packet-shift/PacketSafeExit.lean:152:2: error: unsolved goals
920:im-results/agent2-packet-shift/PacketSafeExit.lean:143:33: error: unsolved goals
931:'BB6.Agent2PacketSafe.normalize_p2_exit' depends on axioms: [propext, sorryAx, Quot.sound]

## Final 100 audit lines
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
'BB6.P2ResetRegularReentry.e_two_reset_regular_reentry' depends on axioms: [propext, Quot.sound]
'CryptidA.a_pairs_triples' depends on axioms: [propext, Quot.sound]
'CryptidA.a_pairs_triples_nil' depends on axioms: [propext, Quot.sound]
im-results/agent32-cryptid-third/CryptidThree.lean:16:58: warning: This simp argument is unused:
  pairs

Hint: Omit it from the simp argument list.
  [apply] simp [eThree, sweepB, packetThree, run, step, goL, goR]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
'CryptidBoundary.eThree_front' depends on axioms: [propext]
'CryptidBoundary.eThree_run' depends on axioms: [propext, Quot.sound]
'CryptidBoundary.full_E_three' depends on axioms: [propext, Quot.sound]
im-results/agent2-packet-shift/PacketSafeExit.lean:153:7: error: unknown tactic
im-results/agent2-packet-shift/PacketSafeExit.lean:152:25: error: unsolved goals
c : Packet
ha : c.a ≥ 4
hp : c.p % 3 = 2
d : Packet := (normalizeWithCount c).snd
he : advance d = none
hamin : d.a ≥ 4
hpmod : d.p % 3 = 2
h2 : d.a % 3 = 2
⊢ d.q = 0
im-results/agent2-packet-shift/PacketSafeExit.lean:152:2: error: unsolved goals
case pos
c : Packet
ha : c.a ≥ 4
hp : c.p % 3 = 2
d : Packet := (normalizeWithCount c).snd
he : advance d = none
hamin : d.a ≥ 4
hpmod : d.p % 3 = 2
h2 : d.a % 3 = 2
hq : d.q = 0
⊢ d.a % 3 = 0 ∨ d.a % 3 = 2 ∧ d.q = 0 ∨ d.a % 3 = 1 ∧ d.p = 2
im-results/agent2-packet-shift/PacketSafeExit.lean:143:33: error: unsolved goals
case neg
c : Packet
ha : c.a ≥ 4
hp : c.p % 3 = 2
d : Packet := (normalizeWithCount c).snd
he : advance d = none
hamin : d.a ≥ 4
hpmod : d.p % 3 = 2
h2 : ¬d.a % 3 = 2
⊢ d.a % 3 = 0 ∨ d.a % 3 = 2 ∧ d.q = 0 ∨ d.a % 3 = 1 ∧ d.p = 2
'BB6.Agent2PacketSafe.normalize_p2_exit' depends on axioms: [propext, sorryAx, Quot.sound]
'BB6.Agent2PacketSafe.advance_pmod' depends on axioms: [propext, Quot.sound]
'BB6.Agent2PacketSafe.normalize_pmod' depends on axioms: [propext, Quot.sound]
'BB6.Agent2PacketSafe.normalize_amin' depends on axioms: [propext, Quot.sound]
'BB6.Agent2PacketSafe.normalize_terminal' depends on axioms: [propext, Quot.sound]
'BB6.Agent2PacketSafe.normalize_safe_exit' depends on axioms: [propext, Quot.sound]

## Seed31 probe output
