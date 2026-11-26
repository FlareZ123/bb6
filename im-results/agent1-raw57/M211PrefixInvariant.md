# M211: a finite exact prefix-rewrite nonhalting invariant

## Claim and evidence

For the exact partial table `1RB1LB_1RC0LE_0RD0RF_1LD1RE_1RA0LA_1RD---`, every compatible completion has an infinite blank-tape execution. This is a finite-certificate mathematical argument with an executable independent checker. The regular-language proof itself compiled locally under Lean 4.36.0-rc2 with standard axioms [propext, Classical.choice, Quot.sound]. The original-source `NeverHalts` theorem is pending a focused CI audit; this is not yet an accepted Raw57/1LB or parent Cover.

## Exact section and invariant

Write `root(w) = Z0(1, [], w.tail)` in the original SweepPumping zipper (the leading zero of w denotes the current blank cell, and the right list excludes that cell). Exact entry from blank occurs at primitive step 14,922, with

    0100001001001001001001001001001000000100001001001001001001001000000100100100100100000010000100000000100100100001000000100100001001001001001000010010010010010000101

The certificate comprises 57 positive-cost rules (k,d,c), with |k|≤161. Every rule has the exact arbitrary-tail semantics

    run0 table c (root (k ++ R)) = some (root (d ++ R))

for every finite Boolean suffix R. The direct zipper checker inserts a fresh opaque marker at the suffix boundary and rejects any attempted entry into it. It checks exact return of the marker and the empty left stack. The Lean operational adapter uses literal arbitrary-tail `rfl` equalities.

A reverse-prefix pushdown saturation constructs an NFA with 1,763 states and 1,819 edges; trimming unreachable/non-coaccessible states yields 1,232 states and 1,267 edges, with initial state 0 and final state 163. The checker independently verifies:

1. The exact entry word is accepted.
2. For every (k,d,c), the NFA frontier after k is a subset of the frontier after d. Thus every accepted word k++R rewrites to another accepted word d++R.
3. Every accepted word has at least one rule prefix. The finite product of the NFA with the unmatched-prefix trie has no accepting state. In the trimmed NFA, every trie-miss has empty frontier, and no internal trie node has an accepting frontier.

These conditions do not trust saturation correctness or a bound on the orbit. Let L be the accepted language. From any root(w) with w∈L, condition 3 supplies a rule; the exact arbitrary-tail macro returns to root(v), with v∈L by condition 2, at strictly positive primitive cost. Starting with the exact entry, induction produces live prefixes of arbitrary length, independently of the missing F1 transition. The source adapter invokes `Agent4Live.never_of_live` to transport these prefixes to all compatible original machines.

## Reproduction

Run `python m211_prefix_certificate.py` and `python m211_emit_lean.py` from this directory. The first checks entry, rules, automaton closure and totality; the second regenerates the Lean sources from the same deterministic rule discovery (first 100 section returns), with a balanced-tree edge lookup to keep kernel checking tractable. Source templates: `m211_invariant.lean.in` and `m211_source.lean.in`. The manual `agent6-raw57-siblings.yml` selector `child=m211` compiles the exact source dependency closure and audits the theorem axioms.

The rule discovery and finite automaton are not claimed to characterize every reachable word exactly; an inductive over-approximation is sufficient. No BB(6) upper bound, full Raw57 child/parent closure or global count change follows from this single leaf.
