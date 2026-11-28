import Leaf2265TracePrelude

namespace BB6.Agent3Leaf2265
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Source-derived, independently counted section chunks 0–3 of the original 435-section trace. -/

theorem traceChunk0 : Runs 28062132 (S 3 (pre [] blank)) (S 4432 (pre [false,false,false,true,false,true] blank)) := by
  have s0 : Runs 93 (S 3 (pre [] blank)) (S 7 (pre [false,false,false,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 1 (pre [] blank))
  have s1 : Runs 413 (S 7 (pre [false,false,false,true,false,true] blank)) (S 17 (pre [false,false,false,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 3 (pre [true,false,true] blank))
  have s2 : Runs 2263 (S 17 (pre [false,false,false,true,false,true,true,false,true] blank)) (S 42 (pre [false,false,false,true,false,true,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 8 (pre [true,false,true,true,false,true] blank))
  have s3 : Runs 13663 (S 42 (pre [false,false,false,true,false,true,true,false,true,true,false,true] blank)) (S 108 (pre [true,false,true,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 20 (pre [true,false,true,true,false,true,true,false,true] blank))
  have s4 : Runs 434 (S 108 (pre [true,false,true,true,false,true,true,false,true] blank)) (S 109 (pre [false,false,true,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 108 (pre [false,true,true,false,true,true,false,true] blank))
  have s5 : Runs 92969 (S 109 (pre [false,false,true,true,false,true,true,false,true] blank)) (S 279 (pre [true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (twoOddZeroRound 54 (pre [true,true,false,true] blank))
  have s6 : Runs 1118 (S 279 (pre [true,true,false,true] blank)) (S 282 (pre [] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 279 (pre [true,false,true] blank))
  have s7 : Runs 599263 (S 282 (pre [] blank)) (S 708 (pre [] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 140 (pre [] blank))
  have s8 : Runs 3766573 (S 708 (pre [] blank)) (S 1773 (pre [] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 353 (pre [] blank))
  have s9 : Runs 23585343 (S 1773 (pre [] blank)) (S 4432 (pre [false,false,false,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 886 (pre [] blank))
  have h := (chain s0 (chain s1 (chain s2 (chain s3 (chain s4 (chain s5 (chain s6 (chain s7 (chain s8 s9)))))))))
  simpa only [Nat.reduceAdd] using h

theorem traceChunk1 : Runs 65441353168220 (S 4432 (pre [false,false,false,true,false,true] blank)) (S 6768233 (pre [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] blank)) := by
  have s10 : Runs 147364013 (S 4432 (pre [false,false,false,true,false,true] blank)) (S 11083 (pre [true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 2215 (pre [true,false,true] blank))
  have s11 : Runs 44334 (S 11083 (pre [true,false,true] blank)) (S 11084 (pre [false,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 11083 (pre [false,true] blank))
  have s12 : Runs 88692 (S 11084 (pre [false,false,true] blank)) (S 11088 (pre [] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one0010 11084 (pre [] blank))
  have s13 : Runs 922188973 (S 11088 (pre [] blank)) (S 27723 (pre [] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 5543 (pre [] blank))
  have s14 : Runs 5764374093 (S 27723 (pre [] blank)) (S 69307 (pre [false,false,false,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 13861 (pre [] blank))
  have s15 : Runs 36026298413 (S 69307 (pre [false,false,false,true,false,true] blank)) (S 173267 (pre [false,false,false,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 34653 (pre [true,false,true] blank))
  have s16 : Runs 225161766013 (S 173267 (pre [false,false,false,true,false,true,true,false,true] blank)) (S 433167 (pre [false,false,false,true,false,true,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 86633 (pre [true,false,true,true,false,true] blank))
  have s17 : Runs 1407254540013 (S 433167 (pre [false,false,false,true,false,true,true,false,true,true,false,true] blank)) (S 1082917 (pre [false,false,false,true,false,true,true,false,true,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 216583 (pre [true,false,true,true,false,true,true,false,true] blank))
  have s18 : Runs 8795324631263 (S 1082917 (pre [false,false,false,true,false,true,true,false,true,true,false,true,true,false,true] blank)) (S 2707292 (pre [false,false,false,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 541458 (pre [true,false,true,true,false,true,true,false,true,true,false,true] blank))
  have s19 : Runs 54970751872413 (S 2707292 (pre [false,false,false,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] blank)) (S 6768233 (pre [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 1353645 (pre [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] blank))
  have h := (chain s10 (chain s11 (chain s12 (chain s13 (chain s14 (chain s15 (chain s16 (chain s17 (chain s18 s19)))))))))
  simpa only [Nat.reduceAdd] using h

theorem traceChunk2 : Runs 152367636087388096884 (S 6768233 (pre [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] blank)) (S 10327506529 (pre [true,true,false,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,false,true,true,false,true] blank)) := by
  have s20 : Runs 27072934 (S 6768233 (pre [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] blank)) (S 6768234 (pre [false,false,true,true,false,true,true,false,true,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 6768233 (pre [false,true,true,false,true,true,false,true,true,false,true,true,false,true] blank))
  have s21 : Runs 343567571455369 (S 6768234 (pre [false,false,true,true,false,true,true,false,true,true,false,true,true,false,true] blank)) (S 16920587 (pre [false,false,false,true,true,true,true,true,false,true,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (twoEvenRound 3384117 0 (pre [true,true,false,true,true,false,true,true,false,true] blank))
  have s22 : Runs 2147297067787213 (S 16920587 (pre [false,false,false,true,true,true,true,true,false,true,true,false,true,true,false,true] blank)) (S 42301467 (pre [false,false,false,true,false,true,true,true,true,true,true,false,true,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 8460293 (pre [true,true,true,true,true,false,true,true,false,true,true,false,true] blank))
  have s23 : Runs 13420606039148013 (S 42301467 (pre [false,false,false,true,false,true,true,true,true,true,true,false,true,true,false,true,true,false,true] blank)) (S 105753667 (pre [false,false,false,true,false,true,true,false,true,true,true,true,true,true,false,true,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 21150733 (pre [true,false,true,true,true,true,true,true,false,true,true,false,true,true,false,true] blank))
  have s24 : Runs 83878786158370013 (S 105753667 (pre [false,false,false,true,false,true,true,false,true,true,true,true,true,true,false,true,true,false,true,true,false,true] blank)) (S 264384167 (pre [false,false,false,true,false,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 52876833 (pre [true,false,true,true,false,true,true,true,true,true,true,false,true,true,false,true,true,false,true] blank))
  have s25 : Runs 524242409524050013 (S 264384167 (pre [false,false,false,true,false,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,false,true,true,false,true] blank)) (S 660960417 (pre [false,false,false,true,false,true,true,false,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 132192083 (pre [true,false,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,false,true,true,false,true] blank))
  have s26 : Runs 3276515049610906263 (S 660960417 (pre [false,false,false,true,false,true,true,false,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,false,true,true,false,true] blank)) (S 1652401042 (pre [false,false,false,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 330480208 (pre [true,false,true,true,false,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,false,true,true,false,true] blank))
  have s27 : Runs 20478219043544153663 (S 1652401042 (pre [false,false,false,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,false,true,true,false,true] blank)) (S 4131002608 (pre [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 826200520 (pre [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,false,true,true,false,true] blank))
  have s28 : Runs 16524010434 (S 4131002608 (pre [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,false,true,true,false,true] blank)) (S 4131002609 (pre [false,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 4131002608 (pre [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,false,true,true,false,true] blank))
  have s29 : Runs 127988869311321142969 (S 4131002609 (pre [false,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,false,true,true,false,true] blank)) (S 10327506529 (pre [true,true,false,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (twoOddZeroRound 2065501304 (pre [true,true,false,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,false,true,true,false,true] blank))
  have h := (chain s20 (chain s21 (chain s22 (chain s23 (chain s24 (chain s25 (chain s26 (chain s27 (chain s28 s29)))))))))
  simpa only [Nat.reduceAdd] using h

theorem traceChunk3 : Runs 37046778271175245258431 (S 10327506529 (pre [true,true,false,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,false,true,true,false,true] blank)) (S 161367289687 (pre [false,false,false,true,false,true] blank)) := by
  have s30 : Runs 41310026118 (S 10327506529 (pre [true,true,false,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,false,true,true,false,true] blank)) (S 10327506532 (pre [true,false,true,true,false,true,true,true,true,true,true,false,true,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 10327506529 (pre [true,false,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,false,true,true,false,true] blank))
  have s31 : Runs 41310026130 (S 10327506532 (pre [true,false,true,true,false,true,true,true,true,true,true,false,true,true,false,true,true,false,true] blank)) (S 10327506533 (pre [false,false,true,true,false,true,true,true,true,true,true,false,true,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 10327506532 (pre [false,true,true,false,true,true,true,true,true,true,false,true,true,false,true,true,false,true] blank))
  have s32 : Runs 799930434280145329369 (S 10327506533 (pre [false,false,true,true,false,true,true,true,true,true,true,false,true,true,false,true,true,false,true] blank)) (S 25818766339 (pre [true,true,true,true,true,true,false,true,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (twoOddZeroRound 5163753266 (pre [true,true,true,true,true,true,false,true,true,false,true,true,false,true] blank))
  have s33 : Runs 103275065358 (S 25818766339 (pre [true,true,true,true,true,true,false,true,true,false,true,true,false,true] blank)) (S 25818766341 (pre [true,true,true,true,false,true,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 25818766339 (pre [true,true,true,true,true,false,true,true,false,true,true,false,true] blank))
  have s34 : Runs 103275065366 (S 25818766341 (pre [true,true,true,true,false,true,true,false,true,true,false,true] blank)) (S 25818766343 (pre [true,true,false,true,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 25818766341 (pre [true,true,true,false,true,true,false,true,true,false,true] blank))
  have s35 : Runs 103275065374 (S 25818766343 (pre [true,true,false,true,true,false,true,true,false,true] blank)) (S 25818766346 (pre [true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 25818766343 (pre [true,false,true,true,false,true,true,false,true] blank))
  have s36 : Runs 103275065386 (S 25818766346 (pre [true,false,true,true,false,true] blank)) (S 25818766347 (pre [false,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 25818766346 (pre [false,true,true,false,true] blank))
  have s37 : Runs 4999565218511004755259 (S 25818766347 (pre [false,false,true,true,false,true] blank)) (S 64546915874 (pre [true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (twoOddZeroRound 12909383173 (pre [true] blank))
  have s38 : Runs 258187663498 (S 64546915874 (pre [true] blank)) (S 64546915875 (pre [] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 64546915874 (pre [] blank))
  have s39 : Runs 31247282617630187196573 (S 64546915875 (pre [] blank)) (S 161367289687 (pre [false,false,false,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 32273457937 (pre [] blank))
  have h := (chain s30 (chain s31 (chain s32 (chain s33 (chain s34 (chain s35 (chain s36 (chain s37 (chain s38 s39)))))))))
  simpa only [Nat.reduceAdd] using h

end BB6.Agent3Leaf2265
