# D-root Seed31 audit diagnostic

Source workflow run: 43388459155

## Error and axiom markers
907:im-results/agent2-packet-shift/PacketP2ReentryOrE.lean:86:30: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
929:im-results/agent2-packet-shift/PacketP2ReentryOrE.lean:119:28: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
953:'BB6.Agent2PacketP2ReentryOrE.p2_packet_reentry_or_E' depends on axioms: [propext, sorryAx, Quot.sound]
954:'BB6.Agent2PacketP2ReentryOrE.p2_packet_reentry_or_reset' depends on axioms: [propext, sorryAx, Quot.sound]

## Final 100 audit lines
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
'BB6.Agent2PacketSafe.normalize_p2_exit' depends on axioms: [propext, Quot.sound]
'BB6.Agent2PacketSafe.advance_pmod' depends on axioms: [propext, Quot.sound]
'BB6.Agent2PacketSafe.normalize_pmod' depends on axioms: [propext, Quot.sound]
'BB6.Agent2PacketSafe.normalize_amin' depends on axioms: [propext, Quot.sound]
'BB6.Agent2PacketSafe.normalize_terminal' depends on axioms: [propext, Quot.sound]
'BB6.Agent2PacketSafe.normalize_safe_exit' depends on axioms: [propext, Quot.sound]
'BB6.Agent2PacketNormalizeSource.advance_edge' depends on axioms: [propext, Quot.sound]
'BB6.Agent2PacketNormalizeSource.normalized_path' depends on axioms: [propext, Quot.sound]
'BB6.Agent2PacketNormalizeSource.normalized_original_source' depends on axioms: [propext, Quot.sound]
'BB6.Agent2PacketNormalizeSource.normalized_source_safe_boundary' depends on axioms: [propext, Quot.sound]
im-results/agent2-packet-shift/PacketP2ReentryOrE.lean:86:30: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  run (12 * k * k + 49 * k + 40) (packet (3 * k + 2) 0 d.p (false :: List.replicate 6 true))
in the target expression
  run (12 * k * k + 49 * k + 40) (packet (3 * k + 2) 0 d.p fixedTail) = regularSection (8 * k + 9 + d.p) 1 5

c : Packet
ha : c.a ≥ 4
hp : c.p % 3 = 2
d : Packet := (normalizeWithCount c).snd
T0 : Nat
h0raw : run T0 (physical (toState c) fixedTail) = physical (toState (normalizeWithCount c).snd) fixedTail
h0 : run T0 (packet c.a c.q c.p fixedTail) = packet d.a d.q d.p fixedTail
hpD : d.p % 3 = 2
hamin : d.a ≥ 4
hB : d.a % 3 = 2 ∧ d.q = 0
k : Nat := (d.a - 2) / 3
hk : 3 * k + 2 = d.a
hshape : packet d.a d.q d.p fixedTail = packet (3 * k + 2) 0 d.p fixedTail
hB0 :
  run (12 * k * k + 49 * k + 40) (packet (3 * k + 2) 0 d.p (false :: List.replicate 6 true)) =
    regularSection (8 * k + 9 + d.p) 1 5
⊢ run (12 * k * k + 49 * k + 40) (packet (3 * k + 2) 0 d.p fixedTail) = regularSection (8 * k + 9 + d.p) 1 5
im-results/agent2-packet-shift/PacketP2ReentryOrE.lean:119:28: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  run (Agent2PacketP2Reset.eTwoTime k d.q) (packet (3 * k + 4) d.q 2 (false :: List.replicate 6 true))
in the target expression
  run (Agent2PacketP2Reset.eTwoTime k d.q) (packet (3 * k + 4) d.q 2 fixedTail) =
    packet (8 * k + 5) 0 (2 * d.q + 6) Agent2PacketP2Reset.marker

c : Packet
ha : c.a ≥ 4
hp : c.p % 3 = 2
T0 : Nat
d : Packet
hd : d = (normalizeWithCount c).snd
h0 : run T0 (packet c.a c.q c.p fixedTail) = packet d.a d.q d.p fixedTail
haE : d.a % 3 = 1
hpE : d.p = 2
hamin : d.a ≥ 4
k : Nat := (d.a - 4) / 3
hk : 3 * k + 4 = d.a
hshape : packet d.a d.q d.p fixedTail = packet (3 * k + 4) d.q 2 fixedTail
hreset :
  run (Agent2PacketP2Reset.eTwoTime k d.q) (packet (3 * k + 4) d.q 2 (false :: List.replicate 6 true)) =
    packet (8 * k + 5) 0 (2 * d.q + 6) Agent2PacketP2Reset.marker
⊢ run (Agent2PacketP2Reset.eTwoTime k d.q) (packet (3 * k + 4) d.q 2 fixedTail) =
    packet (8 * k + 5) 0 (2 * d.q + 6) Agent2PacketP2Reset.marker
'BB6.Agent2PacketP2ReentryOrE.p2_packet_reentry_or_E' depends on axioms: [propext, sorryAx, Quot.sound]
'BB6.Agent2PacketP2ReentryOrE.p2_packet_reentry_or_reset' depends on axioms: [propext, sorryAx, Quot.sound]

## Seed31 probe output
