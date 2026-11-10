# Exact counted TM63 terminal macro

**Established result (10 November 2026):** The local Lean 4.36.0-rc2 kernel proves a universally quantified **exact primitive-transition first-halt theorem** for the literal published TM63 six-state, two-symbol transition table. The theorem closes the all-parameter terminal-cost conjecture left finite-tested in [Agent 24's counted-macro programme](../agent24-champion-time/README.md). It is now **exact on both an independently defined zipper and a fully bi-infinite `Int → Bool` tape**, related by a universally checked all-fuel semantic conjugacy. The direct import into the original `BB6Coverage.Config` and Rocq `TM63` types is still pending. This is a completed **intermediate** terminal component; neither a complete counted champion score nor BB(6) is settled.

## Machine, prepared tape and exact theorem

The table is the published TM63 table `1RB---_1LC0RF_1RE0LD_0LC1RB_1RA1RE_1RE0RD`, with states A through F, binary tape and A/1 the undefined query. The original source is [ccz181078/busycoq, pinned revision 3f302b87, SOBCv5.v lines 10750–11283](https://github.com/ccz181078/busycoq/blob/3f302b87f5fb933c46e97672ffbb6907f373fb6e/verify/SOBCv5.v#L10750-L11283).

The starting section is the published `S1(L,0,m0,a,0,b)`. In the literal finite-support `Z` configuration of [TerminalCount.lean](TerminalCount.lean), its physical left word is

```text
111011 ++ (111)^L ++ 100 ++ 10 ++ (111)^a
```

and its physical right word is `0 ++ 11100 ++ (111)^(b+1)`. The head reads the **last** bit of the left word, precisely as in the published `<{{D}}` convention. Tape contents beyond these explicit words are zero. Both sides are represented as nearest-first lists with implicit zero padding. The complete twelve-entry transition table is explicit in `step`; `run n` demands `n` successful ordinary transitions.

**Kernel theorems**, for every `L a b t : Nat`:

```lean
terminal_macro_count :
  run (59+12*(L+a)) (prepared L a b) = some (sF5 L a b)

terminal_macro_halts :
  (run (59+12*(L+a)) (prepared L a b)).bind step = none

terminal_first_halt :
  run t (prepared L a b) = none ↔ 59+12*(L+a) < t

original_words_eq_prepared :
  fromPhysicalWords (originalLeftWord L a) (originalRightWord b) =
    prepared L a b

full_terminal_first_halt :
  fullRun t (embedFull (prepared L a b) 0) = none ↔
    59+12*(L+a) < t

full_halting_score_iff :
  FullHaltsAfter (embedFull (prepared L a b) 0) t ↔
    t = 59+12*(L+a)
```

Thus the first undefined A/1 query occurs after **exactly `N=59+12*(L+a)` successful primitive moves**, independent of `b`. The final undefined query is *not* counted as an additional successful move. The all-time `terminal_first_halt` rules out premature halting and determines all fuel queries, including those beyond the terminal event.

## How the proof works

The tape algebra is closed by local **literal three-step** D, B and F rules, plus short fixed bridges. Each rule holds with arbitrary untouched left/right lists, so the induction never truncates the physical tape. The derived exact sequential costs are:

| Physical stage | Successful primitive steps |
| --- | ---: |
| D sweep over the rightmost `(111)^a` | `9a` |
| Fixed D-to-B bridge | 6 |
| B sweep across source prefix | `3(5+3L)` |
| Fixed B-to-F turn | 15 |
| Fixed F bridge | 6 |
| F sweep dependent on `L` | `3L` |
| Fixed F bridge | 12 |
| F sweep dependent on `a` | `3a` |
| Final F-to-A/1 bridge | 5 |
| **Total** | **`59+12(L+a)`** |

The statements `d_scan`, `b_scan` and `f_scan` are proved by induction; `run_add` composes successful paths, and `run_none_extended` transports terminal failure to every later fuel bound. A second independent semantic component proves the literal cell-shift identities `tape_moveR`/`tape_moveL` for the implicit-zero zipper, promotes them to full tape writes in `embed_moveR`/`embed_moveL`, checks all twelve full-table transitions in `step_semiconjugacy`, and inducts over every fuel value in `run_semiconjugacy`. Consequently `full_run_none_iff` equates successful/failing fuels, and `full_halting_score_iff` states **the exact scored halt time on an actual infinite `Int → Bool` tape**. This covers an infinite three-parameter family without large numeric simulation, sampled cutoff or oracle assumption.

## Exact evidence and proof boundary

The complete self-contained proof is [TerminalCount.lean](TerminalCount.lean). It compiled on the provided original `lean-4.36.0-rc2-linux` binary on 10 November 2026, without `sorry`. The three terminal theorem `#print axioms` outputs were exactly `[propext, Quot.sound]`. No external Lean packages or mathlib are needed.

Both the local `step` and the full-infinite-tape `fullStep` contain the literal twelve-entry published TM63 table. The kernel theorem `original_words_eq_prepared` identifies the complete physical `S1` words with the starting zipper for every `L,a,b`. The universal `run_semiconjugacy` promotes the full time-count to `Full` configurations consisting of `state : Q`, `head : Int`, and `tape : Int → Bool`, with absolute head motion and exact tape writes. **No separately checked morphism from this full tape to the unmodified Rocq `TM63.S1` type or the repository's `BB6Coverage.Config` state-`Fin 6` representation has yet been established.** The result is a decisive local-source-table cost proof and a concrete dependency for that future bridge. The earlier [Agent 48 champion-root offset](../agent48-champion-root/README.md) is independently source certified, but its six-step root join does not by itself turn this prepared-section theorem into a complete blank-start counted score.

The remaining champion critical path is to prove the universally quantified physical `Inc0` binary decrement cost, counted reset-core and drain costs, compose Agent 24's already-proved carry arithmetic with these costs and transport the initial 27,959-step TM63 prefix plus source-checked champion root offset. Independently, BB(6) still needs an exhaustive six-state upper-bound certificate. Keep this result under `im-results/` pending source import and a genuinely complete lower-bound score.

The readable Lean file is the authoritative standalone source. After adding the all-fuel full-tape transport and exact scored-halt equivalence, its local SHA-256 is `ee51bd3a10656742cf6e741629b95528c2cdc60718fa0a5be301239731743005`. All principal theorem `#print axioms` audits, including `original_words_eq_prepared`, `run_semiconjugacy`, `full_terminal_first_halt`, and `full_halting_score_iff`, are confined to `[propext, Quot.sound]`.
