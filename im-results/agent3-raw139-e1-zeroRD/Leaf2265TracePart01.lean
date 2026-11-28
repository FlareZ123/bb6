import Leaf2265TracePrelude

namespace BB6.Agent3Leaf2265
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Source-derived, independently counted section chunks 4–7 of the original 435-section trace. -/

theorem traceChunk4 : Runs 13857724561228466359874436433 (S 161367289687 (pre [false,false,false,true,false,true] blank)) (S 98490777396984 (pre [false,false,true,true,false,true] blank)) := by
  have s40 : Runs 195295516357768160633213 (S 161367289687 (pre [false,false,false,true,false,true] blank)) (S 403418224217 (pre [false,false,false,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 80683644843 (pre [true,false,true] blank))
  have s41 : Runs 1220596977229999730594263 (S 403418224217 (pre [false,false,false,true,false,true,true,false,true] blank)) (S 1008545560542 (pre [false,false,false,true,false,true,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 201709112108 (pre [true,false,true,true,false,true] blank))
  have s42 : Runs 7628731107677412860608663 (S 1008545560542 (pre [false,false,false,true,false,true,true,false,true,true,false,true] blank)) (S 2521363901358 (pre [true,false,true,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 504272780270 (pre [true,false,true,true,false,true,true,false,true] blank))
  have s43 : Runs 10085455605434 (S 2521363901358 (pre [true,false,true,true,false,true,true,false,true] blank)) (S 2521363901359 (pre [false,false,true,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 2521363901358 (pre [false,true,true,false,true,true,false,true] blank))
  have s44 : Runs 47679569423160325851899219 (S 2521363901359 (pre [false,false,true,true,false,true,true,false,true] blank)) (S 6303409753404 (pre [true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (twoOddZeroRound 1260681950679 (pre [true,true,false,true] blank))
  have s45 : Runs 25213639013618 (S 6303409753404 (pre [true,true,false,true] blank)) (S 6303409753407 (pre [] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 6303409753404 (pre [true,false,true] blank))
  have s46 : Runs 297997308895130241159574413 (S 6303409753407 (pre [] blank)) (S 15758524383517 (pre [false,false,false,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 3151704876703 (pre [] blank))
  have s47 : Runs 1862483180594327629381587263 (S 15758524383517 (pre [false,false,false,true,false,true] blank)) (S 39396310958792 (pre [false,false,false,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 7879262191758 (pre [true,false,true] blank))
  have s48 : Runs 11640519878714153720525332413 (S 39396310958792 (pre [false,false,false,true,false,true,true,false,true] blank)) (S 98490777396983 (pre [true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 19698155479395 (pre [true,false,true,true,false,true] blank))
  have s49 : Runs 393963109587934 (S 98490777396983 (pre [true,false,true,true,false,true] blank)) (S 98490777396984 (pre [false,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 98490777396983 (pre [false,true,true,false,true] blank))
  have h := (chain s40 (chain s41 (chain s42 (chain s43 (chain s44 (chain s45 (chain s46 (chain s47 (chain s48 s49)))))))))
  simpa only [Nat.reduceAdd] using h

theorem traceChunk5 : Runs 825973109347399461147980981419776 (S 98490777396984 (pre [false,false,true,true,false,true] blank)) (S 24045599950436088 (pre [] blank)) := by
  have s50 : Runs 72753249241968877746040161619 (S 98490777396984 (pre [false,false,true,true,false,true] blank)) (S 246226943492462 (pre [false,false,false,true,true,true,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (twoEvenRound 49245388698492 0 (pre [true] blank))
  have s51 : Runs 454707807762303023643316085463 (S 246226943492462 (pre [false,false,false,true,true,true,true] blank)) (S 615567358731158 (pre [true,true,true,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 123113471746230 (pre [true,true,true,true] blank))
  have s52 : Runs 2462269434924634 (S 615567358731158 (pre [true,true,true,true] blank)) (S 615567358731160 (pre [true,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 615567358731158 (pre [true,true,true] blank))
  have s53 : Runs 2462269434924642 (S 615567358731160 (pre [true,true] blank)) (S 615567358731162 (pre [] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 615567358731160 (pre [true] blank))
  have s54 : Runs 2841923798514449298833011338463 (S 615567358731162 (pre [] blank)) (S 1538918396827908 (pre [] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 307783679365580 (pre [] blank))
  have s55 : Runs 17762023740715354285258225702573 (S 1538918396827908 (pre [] blank)) (S 3847295992069773 (pre [] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 769459198413953 (pre [] blank))
  have s56 : Runs 111012648379471060465263712385343 (S 3847295992069773 (pre [] blank)) (S 9618239980174432 (pre [false,false,false,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 1923647996034886 (pre [] blank))
  have s57 : Runs 693829052371694031725498400664013 (S 9618239980174432 (pre [false,false,false,true,false,true] blank)) (S 24045599950436083 (pre [true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 4809119990087215 (pre [true,false,true] blank))
  have s58 : Runs 96182399801744334 (S 24045599950436083 (pre [true,false,true] blank)) (S 24045599950436084 (pre [false,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 24045599950436083 (pre [false,true] blank))
  have s59 : Runs 192364799603488692 (S 24045599950436084 (pre [false,false,true] blank)) (S 24045599950436088 (pre [] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one0010 24045599950436084 (pre [] blank))
  have h := (chain s50 (chain s51 (chain s52 (chain s53 (chain s54 (chain s55 (chain s56 (chain s57 (chain s58 s59)))))))))
  simpa only [Nat.reduceAdd] using h

theorem traceChunk6 : Runs 307703297535806305851132729063829747907 (S 24045599950436088 (pre [] blank)) (S 14676269500998589612 (pre [false,false,false,true,true,true] blank)) := by
  have s60 : Runs 4336431577323090223072359799938973 (S 24045599950436088 (pre [] blank)) (S 60113999876090223 (pre [] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 12022799975218043 (pre [] blank))
  have s61 : Runs 27102697358269315397052245651874093 (S 60113999876090223 (pre [] blank)) (S 150284999690225557 (pre [false,false,false,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 30056999938045111 (pre [] blank))
  have s62 : Runs 169391858489183218977301539970829663 (S 150284999690225557 (pre [false,false,false,true,false,true] blank)) (S 375712499225563892 (pre [false,false,false,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 75142499845112778 (pre [true,false,true] blank))
  have s63 : Runs 1058699115557395114851009632562046413 (S 375712499225563892 (pre [false,false,false,true,false,true,true,false,true] blank)) (S 939281248063909733 (pre [true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 187856249612781945 (pre [true,false,true,true,false,true] blank))
  have s64 : Runs 3757124992255638934 (S 939281248063909733 (pre [true,false,true,true,false,true] blank)) (S 939281248063909734 (pre [false,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 939281248063909733 (pre [false,true,true,false,true] blank))
  have s65 : Runs 6616869472233719519479278847027825369 (S 939281248063909734 (pre [false,false,true,true,false,true] blank)) (S 2348203120159774337 (pre [false,false,false,true,true,true,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (twoEvenRound 469640624031954867 0 (pre [true] blank))
  have s66 : Runs 41355434201460746961522445991527293463 (S 2348203120159774337 (pre [false,false,false,true,true,true,true] blank)) (S 5870507800399435842 (pre [false,false,false,true,false,true,true,true,true,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 1174101560079887168 (pre [true,true,true,true] blank))
  have s67 : Runs 258471463759129668450810209443051225663 (S 5870507800399435842 (pre [false,false,false,true,false,true,true,true,true,true] blank)) (S 14676269500998589608 (pre [true,false,true,true,true,true,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 2935253900199717920 (pre [true,false,true,true,true,true,true] blank))
  have s68 : Runs 58705078003994358434 (S 14676269500998589608 (pre [true,false,true,true,true,true,true] blank)) (S 14676269500998589609 (pre [false,false,true,true,true,true,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 14676269500998589608 (pre [false,true,true,true,true,true] blank))
  have s69 : Runs 117410156007988716902 (S 14676269500998589609 (pre [false,false,true,true,true,true,true] blank)) (S 14676269500998589612 (pre [false,false,false,true,true,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (oneHighRound 14676269500998589609 0 (pre [] blank))
  have h := (chain s60 (chain s61 (chain s62 (chain s63 (chain s64 (chain s65 (chain s66 (chain s67 (chain s68 s69)))))))))
  simpa only [Nat.reduceAdd] using h

theorem traceChunk7 : Runs 18340287274374305184179219985798388383069210 (S 14676269500998589612 (pre [false,false,false,true,true,true] blank)) (S 3583073608642233792748 (pre [] blank)) := by
  have s70 : Runs 1615446648494560429138428064108943225213 (S 14676269500998589612 (pre [false,false,false,true,true,true] blank)) (S 36690673752496474033 (pre [true,true,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 7338134750499294805 (pre [true,true,true] blank))
  have s71 : Runs 146762695009985896134 (S 36690673752496474033 (pre [true,true,true] blank)) (S 36690673752496474035 (pre [true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 36690673752496474033 (pre [true,true] blank))
  have s72 : Runs 146762695009985896142 (S 36690673752496474035 (pre [true] blank)) (S 36690673752496474036 (pre [] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 36690673752496474035 (pre [] blank))
  have s73 : Runs 10096541553091002684866975932118130710093 (S 36690673752496474036 (pre [] blank)) (S 91726684381241185093 (pre [] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 18345336876248237017 (pre [] blank))
  have s74 : Runs 63103384706818766782711766685269346565343 (S 91726684381241185093 (pre [] blank)) (S 229316710953102962732 (pre [false,false,false,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 45863342190620592546 (pre [] blank))
  have s75 : Runs 394396154417617292389655374673402386406013 (S 229316710953102962732 (pre [false,false,false,true,false,true] blank)) (S 573291777382757406833 (pre [true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 114658355476551481365 (pre [true,false,true] blank))
  have s76 : Runs 2293167109531029627334 (S 573291777382757406833 (pre [true,false,true] blank)) (S 573291777382757406834 (pre [false,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 573291777382757406833 (pre [false,true] blank))
  have s77 : Runs 4586334219062059254692 (S 573291777382757406834 (pre [false,false,true] blank)) (S 573291777382757406838 (pre [] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one0010 573291777382757406834 (pre [] blank))
  have s78 : Runs 2464975965110108077495541728333954442755223 (S 573291777382757406838 (pre [] blank)) (S 1433229443456893517098 (pre [] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 286645888691378703418 (pre [] blank))
  have s79 : Runs 15406099781938175484390132685390922072733023 (S 1433229443456893517098 (pre [] blank)) (S 3583073608642233792748 (pre [] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 716614721728446758548 (pre [] blank))
  have h := (chain s70 (chain s71 (chain s72 (chain s73 (chain s74 (chain s75 (chain s76 (chain s77 (chain s78 s79)))))))))
  simpa only [Nat.reduceAdd] using h

end BB6.Agent3Leaf2265
