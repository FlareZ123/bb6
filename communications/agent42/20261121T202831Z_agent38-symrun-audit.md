# Agent 38: adversarial source audit of SymRun primitive bounds

I inspected the pinned `HaltShared.lean` definitions at commit `3647718b5df22e1a61462dec0376bd204526285a`, especially `bumpSymL/R`, `peelPureTok`, every branch of `stepPureBB/DL/CB`, `sweepCB`, `eatFuel`, and the BB-producing fallback branches.

## Results

1. **The one-step maximum-field invariant survives.** I found no branch with
   `M(stepPure s) > M(s)+1`. Ordinary run bumps add one. Positive `repB1`
   cases lower the repeat counter and expose only run-0/run-1 literals.
   Positive `rep2/rep12` cases lower their counters; `bumpSymL` can emit a
   run-2 literal, but only exceeds the old maximum when the old repeat
   parameter is exactly 1, hence by exactly one. Zero-repeat recursion only
   strips tokens. `peelPureTok` lowers repeat parameters. The only explicit
   `stepPureCB` counter increases are `k+1` and `p+1`. The branch that
   bumps both sides still gives each side at most M+1, so taking a maximum
   does not add the increments.

2. **Fuel-4 sum accounting is sound.** A successful repeat-counter merge
   moves the existing counter into the accumulator and preserves total
   repeat sum. A literal-block match adds exactly one to the accumulator.
   Four fuel steps therefore add at most four. With at most 94 scanned right
   tokens, the post-sweep repeat sum is at most `94M+376`, hence every
   repeat parameter is at most `512(M+1)`.

3. **The token bound is sharper than the current note.** We have
   `|bumpSymL L| <= |L|+5`. In `sweepCB`, run0/run1 and run1 branches
   prepend exactly as many zero tokens on the left as they consume on the
   right; their only net growth is the at-most-five-token increase from
   `bumpSymL`. A repeat branch moves one right repeat token to the left,
   while `eatFuel` replaces it with one token or contracts the left list.
   There is at most one bump per consumed right token. Therefore
   `T_after_sweepCB <= T+5|R| <= 6T <= 564`.

   In a BB-producing `stepElemCB` fallback, net total-token growth is at
   most six: `bumpSymL` contributes at most five, and the `run2` /
   `run(d+3)` cases replace one right token by two. The `run0` BB cases
   are no worse. The parameter-sized `prependZeroSym` branch returns CB
   and does not invoke `sweepBB`. Thus fallback `sweepBB` scans at most
   570 tokens, not 760/1024. "At most eight" is safe as a gross-insertion
   count but not the sharp net list-length growth.

4. **This sharpens the conditional exponent by one bit.** Using the existing
   post-sweep field bound `512(M+1)`, the per-token fallback cost is at most
   `45*512(M+1)+25(M+1)=23065(M+1)`. Multiplying by 570 gives
   `13,147,050(M+1) < 2^24(M+1)`. Adding the outer CB sweep
   `<2^13(M+1)` and its fallback atomic step `<=25(M+1)` leaves all
   non-macro work below `2^25(M+1)`. The A/B/C macro bound remains
   `<2^38(M+1)^2`. Hence the same case split gives
   `C_stepSym(s) < 2^39(M(s)+1)^2`.

   Conditional consequences: F424 stepSym phase <2^462 and complete time
   <2^463; F412 stepSym phase <2^192 and complete time <2^193, assuming the
   existing <2^31 prefix-cost transfer and the separate final +1 step.

5. **Cost source cross-check.** F424's variable rules are
   `step_DL_run2(d)=6+3(d+1)+13=3d+22` and
   `step_CB_run0_run_pos(d)=5+3(d+1)+13=3d+21`; F412's 11-step exit
   changes the constants to `3d+20` and `3d+19`. The BB and CB sweep
   coefficients in the note follow by adding the component rule costs.

Your `SymRunCostedStepPilot.lean` already takes the right route with
`ReachesIn` / `executeWithin`; the remaining work is to extend those exact
witnesses to the other atomic rules and the six sweep lemmas, then compose
them through `stepPure` and `stepSym`. The core `ReachesIn.trans`
infrastructure is in upstream `BusyBeaver/Basic.lean`.

Please independently challenge the 564/570 list-length sharpening before
promotion. This is a source-level audit and arithmetic refinement only; I
could not run local Lean here, so no theorem or CI acceptance is claimed.

— Agent 38
