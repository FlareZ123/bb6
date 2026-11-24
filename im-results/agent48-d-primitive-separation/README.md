# Cryptid D: pairwise disjoint primitive orbits, including terminal gates

**Scope:** The four authentic D-family roots, identified with the common literal D transition table by the existing conjugacy and blank-start bridges. Their entire head-relative primitive trajectories are pairwise disjoint, including any eventual halting configurations. Each individual live trajectory also has no repeated head-relative configuration. This is an all-time, computer-assisted mathematical theorem building on the prior source-certified macros and exact finite rank abstraction; the new height and final separation arguments are not yet end-to-end Lean-certified. It does **not** decide any root's halting status or BB(6).

## 1. Notation and the first-event bridge

Use the canonical section and rank of [Agent3's density proof](../../results/2026-11-24-d-density-one-agent3.md): F/0, all cells left of the head blank, right tape (1^n s) with implicit blanks, (s) empty or beginning 0 and ending 1. For any finite right word (w), (R(w)) is the trimmed length plus twice the number of occurrences of 011. Use the total selected affine recurrence and E guard 00101010 from that proof and [Agent32's original-source total affine theorem](../../results/2026-11-24-d-global-affine-completeness-agent32.md).

**The selected recurrence is a strict first-physical-return or first-halt-gate recurrence.** Indeed the positive-time initial F-to-A/B/E prefix has no F state before its stated endpoint, by `prefixA_positive_noF`, `prefixB_positive_noF`, `prefixE_positive_noF` in [PrefixNoF.lean](../agent2-cryptid-continuity/PrefixNoF.lean). The endpoints are in A/B/E. In the A case the finite greedy 10/111 token word has no F before its endpoint by `original_word_noF` (used, for example, in [FullWordPairsFirst.lean](../agent37-cryptid-model-bridge/FullWordPairsFirst.lean)). A residual starting in 0 takes the one A0 step to B0; a residual starting 110 takes the three A0,B1,A1 steps to E0, with one additional pair. These short steps contain no F. A far explicit blank used for a final token or delimiter has no physical effect.

At an E front with left stack (00(10)^{4k+3}11) in nearest-first order (possibly with additional token pairs), the explicit guard consists of its first eight cells. By the original-source one-cell exit theorem, all intermediate steps before each first-left exit preserve the unconsumed left context. At most eight left cells are consumed before a B/D sweep or halt; see `eGuard_ok`, `guardSafe_sound` and `e_guard_total` in the [guard-source archive](../agent32-d-route-dag/guard-source.tar.xz.b64). The far-left 11 marker is never touched by this front corridor. Equivalently, its `safeRun` witness in the stripped guard lifts with the pair padding and marker as a common far-left frame (cf. `safeRun_padL` in AllGuard.lean and `run_protected` in [ProtectedMarker.lean](../agent31-cryptid-boundary/ProtectedMarker.lean)). Thus no intermediate F/0 in this corridor has a blank left tape. This conclusion also holds during a terminal excursion, before the F/1 gate. The B or D sweep has no F before the endpoint by `sweepB_firstF` (used in [BFirstReturn.lean](../agent2-cryptid-continuity/BFirstReturn.lean)) and `sweepD_noF` ([A1100First.lean](../agent31-cryptid-boundary/A1100First.lean)). It ends at the selected physical F/0 section. No earlier F/1 gate is possible along a successful return, or before a later live gate, since the halt freezes the source state. This proves strictness of the chosen macro, including the halt branch, for every canonical finite suffix and (n >= 2).

## 2. A uniform excursion-height certificate

**Lemma.** Starting with any live state q (A through F), any finite right word w including the scanned cell, and an arbitrary left context, write the initial head coordinate as 0. In every finite primitive prefix up to and including a possible halt gate, whose head has never entered cell -1, the endpoint head coordinate is at most
```text
R(w)+4.
```
The prefix may end at an F/1 halt gate. The same bound holds for every head coordinate in such a prefix.

Use the unchanged 11-bit abstraction, exact rank edit gains, and certified finite-return relation (X) of [Agent3's checker](../agent3-d-density-drift/certificate.py). A row ((r,j,g)) of (X[q,c]) covers a returning first-left excursion with output state (r), written right-word class (j) (excluding the consumed left bit), and rank gain at most (g). The relation need not describe every nonreturning computation; no such assumption enters this lemma.

For a right move in state/class ((q,c)), writing (b) and entering (r), each possible pop edge has class (j) and exact gain (g_1). Add the inequalities
```text
H(q,c) >=  1+g_1+H(r,j).
```
For every return edge ((r_2,k,g_2) in X[r,j]) followed by prepending (b) to get class (l) with gain (g_3), also require
```text
H(q,c) >=  g_1+g_2+g_3+H(r_2,l).
```
There are no constraints for a left move or a halt. Impose (0 <= H <= 4). The attached finite checker constructs H and checks all inequalities exactly; the maximum is 4.

Proof by strong induction on the finite prefix length, with bound (R(w)+H(q,c(w))): at length zero, use nonnegativity. If a positive prefix remains on the right side, the first move must be right. If it has not returned to the initial cell, apply induction at cell 1 and the first inequality. If it has returned to the initial cell, take its first such return; the first-left-exit relation X bounds that excursion, prepending the initially written bit gives the next right word, and induction on the remaining shorter prefix applies the second inequality. These two cases also cover prefixes ending immediately upon return or at a terminal gate. No bound on simulation duration or unproved eventual return is used. The certificate is checked by `terminal_height.py`; iteration is only an untrusted finite potential generator.

The same checked X has maximal rank gain 2 for any returning excursion, and any single prepended bit increases rank by at most 3. Thus after (p) completed E-guard exits the scanned-plus-right word has rank at most (R(s)+5p).

## 3. Terminal marker-distance bounds

Let (D) be the distance in tape cells from the head at an eventual terminal F/1 gate to its leftmost 1. Such a 1 exists and is at the unchanged far-left marker. If the chosen section ((n,s)) is terminal in its next macro, then
```text
8n - 26 <= 3D <= 8(n + R(s)) + 120. (T)
```

For E ((n=3k+4)), the distance at entry to the E guard is (8k+10). Before the gate, let (p <= 8) be the number of completed first-left exits. The next excursion has not entered the next left cell, so its relative head offset (d) satisfies (0 <= d <= R(s)+5p+4) by the lemma (a gate immediately after an exit uses (d=0)). The exact terminal distance is (D=8k+10-p+d). Hence
```text
8k+2 <= D <= 8k+R(s)+46,
    8n-26 <= 3D <= 8(n+R(s))+106.
```
The B branch never halts. For a terminal A branch ((n=3k+3)), after its tokens the residual canonical word (u) satisfies (3T <= 8(R(s)-R(u))), where (T) is the unary contribution of those tokens (2 per 10, 8 per 111); this is precisely the token-rank inequality of [the phase-separation proof](../../results/2026-11-24-d-four-root-phase-separation-agent3.md). The close branch cannot halt; the 110 branch gives an E guard with one extra pair and a right word of rank at most (R(u)) (drop the first three bits). Its initial marker distance is (8k+12+T), and the same E argument gives
```text
8k+4+T <= D <= 8k+48+T+R(u).
```
Using (3T+3R(u) <= 8R(s)) proves (T) also for A. These estimates allow arbitrarily long finite suffixes.

## 4. Disjoint terminal bands and complete noncoalescence

Let (a=8/3). For each of the four established anchors ((n_i,s_i)), define (L_i=5n_i-23), (U_i=5(n_i+R(s_i))+27). By [Agent3's all-time phase inequalities](../../results/2026-11-24-d-four-root-phase-separation-agent3.md), at the (t)-th successful return after that anchor,
```text
5n-23 >= a^t L_i,    5(n+R(s))+27 <= a^t U_i.
```
The anchor data (seeds 5,9,15,39 respectively) are ((123501,9),(196699,0),(276715,0),(277451,0)), where the second coordinate denotes rank. All four are reached by positive live macro paths computed exactly from the source-derived recurrence there; the pre-anchor trajectories therefore cannot already have halted.

If a macro after (t >= 0) successful returns ends at a terminal gate, (T) implies
```text
a^{t+1}L_i+18 <= 5D <= a^{t+1}U_i+128.
```
Even the enlarged bands ([a^{t+1}L_i,a^{t+1}U_i+128]) are pairwise disjoint over every (t >= 0) and root index (i). The exact checks are (8(L_{i+1}-U_i)>384) for adjacent anchors and (64L_0>24U_3+1152) for the wrap to the next phase; growth of (a^{t+1}) proves every later comparison. Therefore two distinct authentic roots cannot have the same terminal head-relative configuration, even if both halt at widely different macro indices. The marker distance is invariant under spatial translation.

Suppose any two distinct authentic D trajectories coalesce in the common literal source, at any two primitive times, modulo tape translation. The machine is deterministic on head-relative tapes, so all subsequent configurations coincide. If the common future halts, the terminal gates coincide (or the frozen states coincide, which equally implies the same marker distance), contradicting the terminal bands. If the common future does not halt, total strict first-event recurrence gives infinitely many physical F/0 returns, all of which are selected returns. Beyond both anchors, the common returns contradict the disjoint selected phase bands. This argument also handles coalescence before either anchor: in the halting case both anchors are already known to be live; in the nonhalting case choose a common section beyond both finite prefixes.

Finally an individual live trajectory cannot repeat a head-relative configuration. Such a repetition forces a periodic nonhalting future. The same total strict recurrence supplies infinitely many physical F/0 returns, whose unary lengths are strictly increasing since (3n' >= 8n-23) and each root starts with (nge5). A finite cycle cannot contain these increasing section lengths. This statement excludes repetitions only up to the terminal gate; the artificial frozen state of course repeats after halting.

## Evidence and next question

Run `python3 im-results/agent48-d-primitive-separation/terminal_height.py` from the repository root. It imports the original rank abstraction and extends it by the new finite height certificate and exact terminal-band comparisons. Local exact evaluation of the same rank/edit/exit rules gave X closure in 13 rounds, height closure in 4 sweeps, max H=4; all closure inequalities and enlarged-band tests passed. No search along large blank trajectories is required.

The original-source prefix, guard, padding and sweep lemmas are previously kernel-certified. The new mathematical induction, terminal geometry and deterministic noncoalescence proof are paper arguments supported by the finite checker, not an end-to-end Lean proof. The evidence advances all-time structural separation, but neither establishes an actual halt nor all-time halt avoidance for an individual root. In particular a proposed shortcut merging two roots by any finite primitive prefix is impossible, not merely at the selected macro endpoints. The next substantive decision obligation is still a terminal route or all-time invariant for each of the four roots.
