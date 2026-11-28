# Six-bank conversion for Raw140 siblings 37/40/44/83

## Proved transition

In the common partial table (A1,F0,F1 undefined), write F(u,v,w,s;X) for ER with left list 1 (133)^u 22 6^v 7 3^w X, right list tail(s), and arbitrary left suffix X. The six cyclic tails have ranks 0..5 in the order 542, 152, 1121, 5215, 1155, 11511; rho advances the rank, and e(s)=1 exactly at rank 5.

For all u,v,w natural:
F(u+2,v,w+3,s;X) -> F(u+e(s),v+9,w,rho(s);X)
in exactly 66u+66v+C(s) primitive steps, with C=(684,708,722,694,750,817).

The inner conversion EL(22 6^v 7 3 X, 1^k 5 Y) -> DR(62 6^(v+k+2) 7 X,Y) takes 22(v+k+2)+3k+38 steps for arbitrary X,Y. Three inner conversions, two 9-step turn1 bridges and one 9-step turn5 give the common core. The six prep rules, carry, tripLoop, pump and erMany then produce the F recurrence.

## Closed-form drain

Let z=6u+rank(s). Each conversion subtracts 11 from z, adds 9 to v, and subtracts 3 from w. If w >= 3N with N=floor(max(z-1,0)/11), exactly N applications are possible before u<2. The terminal z is z-11N, v'=v+9N, w'=w-3N. The formal drain theorem provides finite primitive reachability to that terminal with u'<2. It does not require a scan, a conjectured orbit bound, or the variant-specific rows. Any extension of the common table inherits the result through run_ext.

## Status

Raw14037SixBank.lean: local Lean 4.36.0-rc2 check against the restored Raw140 source closure from artifact 15220415544 (with the already-upstream ERExit simp repair). The printed axioms of inner, advance, drainN and drain are [propext, Quot.sound]. This is a conditional macro reachability result, not a decision of any sibling or a Cover. CI source closure and end-to-end invariant remain outstanding. The four sibling paths share this phase; the outstanding work is the finite terminal families u=0,1 (including potentially further bank phases), the entry bridge, and an invariant connecting every return. No parent count changes on this result alone.

## Complementary 322 counter (checked)

Write G(v,X,R)=DR(62 6^v 7 X,R), and T(n)=(322)^n. For the six C-tails (31,32,315,325,3242,35221), let next advance cyclically and ccarry equal one only at the wrap. Raw14037Counter.lean proves, on the same partial base:

```
G(v,3X,T(n)s) -> G(v+1,X,T(n+ccarry(s))next(s))
G(v,3^k X,T(n)s) -> G(v+k,X,T(n+turn(k,s).1)turn(k,s).2)
G(v,2,T(n)s) -> BL([],2^(v+4) T(n+ccarry(s)+ccarry(next(s)))next(next(s)))
```

The first law factors through the existing 42 counter scan and the new six-bank seed and loop. The second is induction on k, and the third handles the terminal left marker by two further counter rotations. All three are locally kernel-checked with [propext, Quot.sound], no sorryAx. This proves an entire unbounded sweep plus exit, with arbitrary untouched X in the first two laws. The remaining bridges are the finite six-bank terminal tails, the 2-bank-to-D phase and subsequent section return. No machine verdict yet.

## Terminal entry and complementary D-left drain (checked)

The one-triplet terminal of F is now handled for every A-tail: F(1,v,w+1,s;X) reaches G(v+5,3^w X,(115)^extra(s) rho(s)), by Raw14037Terminal.one. This does not yet imply that the six resulting right strings all enter the C-counter language.

For C-tails c(s) in the 322 cycle above define H(a,n,s;X)=DL(X,4^a 2 (322)^n c(s)). Raw14037DPhase proves

```
H(a+1,n+2,s;666 X) -> H(a+10,n+ccarry(s),next(s);X).
```

The proof scans the leading 4-bank into 5s, enters the existing 322 counter, rotates its tail, and uses two framed leading-2 deletion steps. Writing z=6n+rank(s), each large return subtracts 11 from z, adds 9 to a, and removes exactly three 6-blocks. Thus J=(z-1)/11 (natural arithmetic) is the exact number of large returns until n<2, provided a>0 and the left 6-bank has at least 3J blocks. The source theorem drain returns H(a+9J,n',s';6^(k-3J) X) with 6n'+rank(s')=z-11J and n'<2. Both advance and drain compile locally with [propext, Quot.sound]. This is a second independent unbounded-bank reduction, with arbitrary suffix X, shared by all four sibling completions. The low H tails still need return classification; no Cover is claimed.

## Finite framed terminal certificates

`Raw140Framed.execute_sound` verifies finite block runs with independently open/closed tape sides, universally quantified arbitrary untouched suffixes. The evaluator rejects reads beyond an open prefix; closed sides use ordinary blank extension. `Raw14037DTerm.soundRule` lifts 28 kernel-decided terminal rules to arbitrary positive 4-bank and arbitrary remaining left frame: each consumes one 6-block and adds the rule's exact increment to the 4-bank. These cover all but the initial 231 C-terminal, and lead either to the standard B-tail 62 or to further terminal families (notably 231 and a growing odd bank after 215). The outstanding low-tail return classification is not yet an invariant. Both files were compiled locally with Lean 4.36.0-rc2; the proof uses only propext and Quot.sound.

## Low D-counter classification and unbounded exceptional paths

Raw14037DRoutes.route_sound covers all twelve low H tails (n=0,1), consuming at most nine six-blocks. Eight enter tail 62, three enter 231, and one enters 215; the latter two must be handled separately. Raw14037DOdd.oddSeed reaches J(a+3,3,0,542;X) from DL(6666 X,4^(a+1)215), where J(a,m,n,s;X)=DL(X,4^a 2 1^m (115)^n tail(s)). Raw14037DOdd.iterate proves that consuming two six-blocks adds one each to a and m, and rotates the six A-tails with their carry. Thus arbitrary numbers of such passes need no finite replay.

Raw14037WordReturn.bankMany proves ER(1(133)^n3^m5^k X,s) -> ER(1(133)^(n+carry_k(s))3^(m+k) X,rho^k(s)). Its rotateSweep theorem returns ER(1(133)^n3^m X,s) to EL(X,1^(m+1)(115)^(n+extra(s))rho(s)). These identities preserve arbitrary X and use the common table. All three modules were checked locally (Lean 4.36.0-rc2), with [propext, Quot.sound] for exported reachability theorems. They are intermediate universal macro laws, not an all-time blank-root decision. Remaining: standard and exceptional bank exits into a common invariant.

## The exceptional 231 branch

Raw14037D231.convert proves the exact common-table reachability DL(6^(k+2)4,4^(a+1)231) -> EL(6^(k+1)4,1^(a+5)(115)^n s), where (n,s)=turn(a+3,542). The seed consumes one six, converts the entire 4-bank to a mixed 3/5 bank and uses bankMany and rotateSweep; its 65 macro exits are kernel-decided with arbitrary left frame. The exitOnes theorem turns EL(6^(k+1)4,1^(m+1)Y) into AR(3^(k+1)2,05 1^mY), for arbitrary Y. Finally collect converts AR(3^(p+1)2,05 1^m(115)^n s) into ER(1(133)^n3^(m+p+2)2,s), uniformly in all three exponents and all six A-tails. These three lemmas compile locally with [propext, Quot.sound]. The remaining task is to join the last homogeneous return to the broader section invariant. No Cover verdict is asserted.
