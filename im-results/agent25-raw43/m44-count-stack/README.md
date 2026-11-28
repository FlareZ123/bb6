# M44: count-stack pushdown safety certificate

**Intermediate computational nonhalting candidate**, 2026-11-28. Raw43 B1=0LE/E0=1LA frozen row i44:
`1RB0LA_1RC0LE_0RD1RA_1LD0RB_1LA1LF_---0LD`.
The sole unspecified slot is F0. This approach covers arbitrary tape lengths, unlike the older conditional return in M44Sweeps.lean. Exact source-connected Lean transport is still required; do not put this row into the certified growth map yet.

## Exact section recurrences

At A scanning zero, encode the left ray (nearest first, excluding scan) by a list L of counts of ones, each followed by a separator zero, with trailing zero counts omitted. Encode the right ray (nearest first, including scan) by R of zero gaps before successive ones; after the last one the ray is blank. L=[] has virtual head a=0 and tail t=[]. Otherwise L=a::t. Let R=g::r if nonempty. Concatenation of count lists is denoted by ++. C removes trailing zero counts in a left list.

The following positive-cost macro table was obtained by literal transition calculation, and checked on 10,000 randomized admissible sections against a direct primitive simulator. It is a claimed exact recurrence, pending formal proof. The two unsafe input guards are g=1 with a<2, and g=3 without a following gap 1. A0 cannot have g=0.

| Right pattern | New L | New R | Primitive moves |
|---|---|---|---:|
| [] | t | [a+2,1] | a+9 |
| 1::r, a>=2 | C([2,a-2]++t) | increase head(r) by 1 if present | 7 |
| 2::r, r=[] or head(r) != 0 | (a+3)::t | r | 3 |
| 2::0::r | t | increase head(r) by a+5 if present | a+7 |
| 3::1::r, r=[] or head(r) != 0 | [2,0,a+2]++t | r | 6 |
| 3::1::0::r | [0,a+2]++t | increase head(r) by 4 if present | 9 |
| g::r, g>=4 | t | [a+2,1,g-4]++r | a+9 |

The empty and g>=4 branches use the eight-move prefix A0 B0 C0 D0 D0 D1 B1 E0 followed by an A1 sweep through a+1 ones. The g=2 short branch has A0 B0 C1, with an A1 sweep exactly when the next gap is zero. The g=3 branches use A0 B0 C0 D1 B0 C1 and the optional three A1 moves. The g=1 branch uses A0 B1 E1 F1 D1 B0 C1. In particular all listed paths avoid F0. Empty right cases use implicit blank cells.

## Finite safety reduction

The left stack is represented by a bottom-up partial deterministic graph. State 0 denotes empty, push(0,0)=0 implements trailing-zero omission, and every other edge push(t,a)=l preserves the actual integer count a as head[l]. Every possible predecessor t of l is included in the pop relation. Missing pushes are classified as bad, rather than discarded. Graph discovery used a capped 6-group left suffix abstraction with one bottom token, a million concrete macro steps and 62 counterexample-guided edge additions, but none of those steps need be trusted: graph.json is the fixed finite proof input. Every represented count is exact and <=12. A successor that would need another count is caught as a bad missing push.

The right stack is retained without depth truncation. Its alphabet has exact gaps 0..12, four classes 13+(g mod 4) for g>=13, and end marker 17. A high class has representatives base+4k, k>=0, where base is the first member >=13. For a shift d>=-4, the first two representatives exhaust all output classes: at most the first crosses below 13; all remaining ones have the same residue. This is why the finite image rule is sound for every integer gap.

The seven control phases per left state are main, inc, s2, s20, s3, s3n, s30. They unfold the table into single-pop pushdown rules (maximum push length 3). Every possible left pop is used; every undefined left push and unsafe right guard goes to the universal bad language. Right stacks end in marker 17, which stands for the implicit zero ray. See verify.py for exact construction.

For a rule (p,x)->(q,w), a P-automaton edge p -x-> s is required whenever q -w-> s is a path. The automaton has the additional accepting state U=2646, with self-loops for every symbol. Each bad guard gets an edge to U. Thus all bad configurations are accepted, and acceptance is backward closed along every rule by concatenation of paths. Any configuration outside the accepted language stays outside it; no bad guard or missing left push is reachable. This argument does not rely on the saturation being least, and needs no upper bound on the right stack length. Root is (0,[17]).

## Reproduction

```
python verify.py
```

Expected independent bitset saturation and subsequent closure audit: 378 left states, 442 recorded push edges (plus virtual bottom zero); 2647 P-automaton states, 18 symbols, 33882 non-bad rules and 17887 bad guards; 58790 automaton edges in 28 rounds. Root is rejected. An earlier separately implemented worklist saturation at cutoff 32 produced a safe certificate with 108160 edges. The smaller cutoff 13 is sufficient.

This establishes a complete finite **macro-level** safety candidate, with a simple path-closure proof obligation. The remaining trust boundary is exact source-connected Lean proof of the seven raw recurrences, the finite graph/rule coverage and certificate closure. A possible route is to quotient the NFA, or shard a bitset checker. Do not claim a source-accepted Raw43 Cover or exact BB(6) from this intermediate result.
