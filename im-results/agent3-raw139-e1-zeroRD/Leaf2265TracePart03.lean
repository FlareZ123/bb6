import Leaf2265TracePrelude

namespace BB6.Agent3Leaf2265
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Source-derived, independently counted section chunks 12–15 of the original 435-section trace. -/

theorem traceChunk12 : Runs 538980197880759556801213706656131060884812513118326056413176520591447 (S 31824086553930841894108585445848 (pre [] blank)) (S 19423880953326929867009634671538842 (pre [false,false,false,true,false,true] blank)) := by
  have s120 : Runs 7595793637440613558653049759874968380595897540753496152907751773 (S 31824086553930841894108585445848 (pre [] blank)) (S 79560216384827104735271463614623 (pre [] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 15912043276965420947054292722923 (pre [] blank))
  have s121 : Runs 47473710234003834741581560999220541384133980307327732742263814093 (S 79560216384827104735271463614623 (pre [] blank)) (S 198900540962067761838178659036557 (pre [false,false,false,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 39780108192413552367635731807311 (pre [] blank))
  have s122 : Runs 296710688962523967134884756245125400142722945904370756959263289663 (S 198900540962067761838178659036557 (pre [false,false,false,true,false,true] blank)) (S 497251352405169404595446647591392 (pre [false,false,false,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 99450270481033880919089329518278 (pre [true,false,true] blank))
  have s123 : Runs 1854441806015774794593029726532028778378494360208271276528919646413 (S 497251352405169404595446647591392 (pre [false,false,false,true,false,true,true,false,true] blank)) (S 1243128381012923511488616618978483 (pre [true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 248625676202584702297723323795695 (pre [true,false,true,true,false,true] blank))
  have s124 : Runs 4972513524051694045954466475913934 (S 1243128381012923511488616618978483 (pre [true,false,true,true,false,true] blank)) (S 1243128381012923511488616618978484 (pre [false,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 1243128381012923511488616618978483 (pre [false,true,true,false,true] blank))
  have s125 : Runs 11590261287598592466206435790825248236926545462094827352219791606619 (S 1243128381012923511488616618978484 (pre [false,false,true,true,false,true] blank)) (S 3107820952532308778721541547446212 (pre [false,false,false,true,true,true,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (twoEvenRound 621564190506461755744308309489242 0 (pre [true] blank))
  have s126 : Runs 72439133047491202913790223692657770402581383815004883735958223079213 (S 3107820952532308778721541547446212 (pre [false,false,false,true,true,true,true] blank)) (S 7769552381330771946803853868615533 (pre [true,true,true,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 1553910476266154389360770773723105 (pre [true,true,true,true] blank))
  have s127 : Runs 31078209525323087787215415474462134 (S 7769552381330771946803853868615533 (pre [true,true,true,true] blank)) (S 7769552381330771946803853868615535 (pre [true,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 7769552381330771946803853868615533 (pre [true,true,true] blank))
  have s128 : Runs 31078209525323087787215415474462142 (S 7769552381330771946803853868615535 (pre [true,true] blank)) (S 7769552381330771946803853868615537 (pre [] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 7769552381330771946803853868615535 (pre [true] blank))
  have s129 : Runs 452744581546820018211188898079111725428086061959396001677317726565463 (S 7769552381330771946803853868615537 (pre [] blank)) (S 19423880953326929867009634671538842 (pre [false,false,false,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 3884776190665385973401926934307768 (pre [] blank))
  have h := (chain s120 (chain s121 (chain s122 (chain s123 (chain s124 (chain s125 (chain s126 (chain s127 (chain s128 s129)))))))))
  simpa only [Nat.reduceAdd] using h

theorem traceChunk13 : Runs 32125270491070873510101738787077151372062914017103888096304753619523077290 (S 19423880953326929867009634671538842 (pre [false,false,false,true,false,true] blank)) (S 4742158435870832487062899089731163483 (pre [true,false,true,true,false,true] blank)) := by
  have s130 : Runs 2829653634667625113819930612994448089686728353976926340386889075645663 (S 19423880953326929867009634671538842 (pre [false,false,false,true,false,true] blank)) (S 48559702383317324667524086678847108 (pre [true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 9711940476663464933504817335769420 (pre [true,false,true] blank))
  have s131 : Runs 194238809533269298670096346715388434 (S 48559702383317324667524086678847108 (pre [true,false,true] blank)) (S 48559702383317324667524086678847109 (pre [false,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 48559702383317324667524086678847108 (pre [false,true] blank))
  have s132 : Runs 388477619066538597340192693430776892 (S 48559702383317324667524086678847109 (pre [false,false,true] blank)) (S 48559702383317324667524086678847113 (pre [] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one0010 48559702383317324667524086678847109 (pre [] blank))
  have s133 : Runs 17685335216672656961374566331215305416512290544088256379826724607496343 (S 48559702383317324667524086678847113 (pre [] blank)) (S 121399255958293311668810216697117782 (pre [false,false,false,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 24279851191658662333762043339423556 (pre [] blank))
  have s134 : Runs 110533345104204106008591039570095657639209256317618485685814861825674263 (S 121399255958293311668810216697117782 (pre [false,false,false,true,false,true] blank)) (S 303498139895733279172025541742794458 (pre [true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 60699627979146655834405108348558890 (pre [true,false,true] blank))
  have s135 : Runs 1213992559582933116688102166971177834 (S 303498139895733279172025541742794458 (pre [true,false,true] blank)) (S 303498139895733279172025541742794459 (pre [false,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 303498139895733279172025541742794458 (pre [false,true] blank))
  have s136 : Runs 2427985119165866233376204333942355692 (S 303498139895733279172025541742794459 (pre [false,false,true] blank)) (S 303498139895733279172025541742794463 (pre [] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one0010 303498139895733279172025541742794459 (pre [] blank))
  have s137 : Runs 690833406901275662553693997313097890594871841558443452738897060689910093 (S 303498139895733279172025541742794463 (pre [] blank)) (S 758745349739333197930063854356986157 (pre [false,false,false,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 151749069947866639586012770871397231 (pre [] blank))
  have s138 : Runs 4317708793132972890960587483206861804836768763650273610667148813957145663 (S 758745349739333197930063854356986157 (pre [false,false,false,true,false,true] blank)) (S 1896863374348332994825159635892465392 (pre [false,false,false,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 379372674869666598965031927178493078 (pre [true,false,true] blank))
  have s139 : Runs 26985679957081080568503671770042886261261171029330880118418083728307506413 (S 1896863374348332994825159635892465392 (pre [false,false,false,true,false,true,true,false,true] blank)) (S 4742158435870832487062899089731163483 (pre [true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 948431687174166497412579817946232695 (pre [true,false,true,true,false,true] blank))
  have h := (chain s130 (chain s131 (chain s132 (chain s133 (chain s134 (chain s135 (chain s136 (chain s137 (chain s138 s139)))))))))
  simpa only [Nat.reduceAdd] using h

theorem traceChunk14 : Runs 11967764510084845248654466113438915661408265534894983684913726561423167090177557 (S 4742158435870832487062899089731163483 (pre [true,false,true,true,false,true] blank)) (S 2894383810956318656654601495197243338542 (pre [false,false,false,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] blank)) := by
  have s140 : Runs 18968633743483329948251596358924653934 (S 4742158435870832487062899089731163483 (pre [true,false,true,true,false,true] blank)) (S 4742158435870832487062899089731163484 (pre [false,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 4742158435870832487062899089731163483 (pre [false,true,true,false,true] blank))
  have s141 : Runs 168660499731756753553147948562768039393701032906213787528572473237135906619 (S 4742158435870832487062899089731163484 (pre [false,false,true,true,false,true] blank)) (S 11855396089677081217657247724327908712 (pre [false,false,false,true,true,true,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (twoEvenRound 2371079217935416243531449544865581742 0 (pre [true] blank))
  have s142 : Runs 1054128123323479709707174678517300246092077494767065359877005480488820329213 (S 11855396089677081217657247724327908712 (pre [false,false,false,true,true,true,true] blank)) (S 29638490224192703044143119310819771783 (pre [true,true,true,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 5927698044838540608828623862163954355 (pre [true,true,true,true] blank))
  have s143 : Runs 118553960896770812176572477243279087134 (S 29638490224192703044143119310819771783 (pre [true,true,true,true] blank)) (S 29638490224192703044143119310819771785 (pre [true,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 29638490224192703044143119310819771783 (pre [true,true,true] blank))
  have s144 : Runs 118553960896770812176572477243279087142 (S 29638490224192703044143119310819771785 (pre [true,true] blank)) (S 29638490224192703044143119310819771787 (pre [] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 29638490224192703044143119310819771785 (pre [true] blank))
  have s145 : Runs 6588300770771748185669841740733126540594756011350538257983449394474807659213 (S 29638490224192703044143119310819771787 (pre [] blank)) (S 74096225560481757610357798277049429467 (pre [false,false,false,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 14819245112096351522071559655409885893 (pre [] blank))
  have s146 : Runs 41176879817323426160436510879582040877605781687533637748241191741311806428013 (S 74096225560481757610357798277049429467 (pre [false,false,false,true,false,true] blank)) (S 185240563901204394025894495692623573667 (pre [false,false,false,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 37048112780240878805178899138524714733 (pre [true,false,true] blank))
  have s147 : Runs 257355498858271413502728192997387755482257527088567170016119030947809436570013 (S 185240563901204394025894495692623573667 (pre [false,false,false,true,false,true,true,false,true] blank)) (S 463101409753010985064736239231558934167 (pre [false,false,false,true,false,true,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 92620281950602197012947247846311786833 (pre [true,false,true,true,false,true] blank))
  have s148 : Runs 1608471867864196334392051206233673471757163023157249647824772899835335594550013 (S 463101409753010985064736239231558934167 (pre [false,false,false,true,false,true,true,false,true,true,false,true] blank)) (S 1157753524382527462661840598078897335417 (pre [false,false,false,true,false,true,true,false,true,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 231550704876505492532368119615779467083 (pre [true,false,true,true,false,true,true,false,true] blank))
  have s149 : Runs 10052949174151227089950320038960459198464902591867072386964903014999664005906263 (S 1157753524382527462661840598078897335417 (pre [false,false,false,true,false,true,true,false,true,true,false,true,true,false,true] blank)) (S 2894383810956318656654601495197243338542 (pre [false,false,false,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 578876762191263731330920299039448667708 (pre [true,false,true,true,false,true,true,false,true,true,false,true] blank))
  have h := (chain s140 (chain s141 (chain s142 (chain s143 (chain s144 (chain s145 (chain s146 (chain s147 (chain s148 s149)))))))))
  simpa only [Nat.reduceAdd] using h

theorem traceChunk15 : Runs 114121834959619426843559320362203937465055504746546074363632576330369832748943724775 (S 2894383810956318656654601495197243338542 (pre [false,false,false,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] blank)) (S 282654669038702993813925927265355794779842 (pre [false,false,false,true,false,true] blank)) := by
  have s150 : Runs 62830932338445169312189500243502869990376697361059639231964097828795927603528663 (S 2894383810956318656654601495197243338542 (pre [false,false,false,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] blank)) (S 7235959527390796641636503737993108346358 (pre [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 1447191905478159328327300747598621669270 (pre [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] blank))
  have s151 : Runs 28943838109563186566546014951972433385434 (S 7235959527390796641636503737993108346358 (pre [true,false,true,true,false,true,true,false,true,true,false,true,true,false,true] blank)) (S 7235959527390796641636503737993108346359 (pre [false,false,true,true,false,true,true,false,true,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 7235959527390796641636503737993108346358 (pre [false,true,true,false,true,true,false,true,true,false,true,true,false,true] blank))
  have s152 : Runs 392693327115282308201184376521892937440360875673540100964690166691634065106299219 (S 7235959527390796641636503737993108346359 (pre [false,false,true,true,false,true,true,false,true,true,false,true,true,false,true] blank)) (S 18089898818476991604091259344982770865904 (pre [true,true,false,true,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (twoOddZeroRound 3617979763695398320818251868996554173179 (pre [true,true,false,true,true,false,true,true,false,true] blank))
  have s153 : Runs 72359595273907966416365037379931083463618 (S 18089898818476991604091259344982770865904 (pre [true,true,false,true,true,false,true,true,false,true] blank)) (S 18089898818476991604091259344982770865907 (pre [true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 18089898818476991604091259344982770865904 (pre [true,false,true,true,false,true,true,false,true] blank))
  have s154 : Runs 72359595273907966416365037379931083463630 (S 18089898818476991604091259344982770865907 (pre [true,false,true,true,false,true] blank)) (S 18089898818476991604091259344982770865908 (pre [false,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 18089898818476991604091259344982770865907 (pre [false,true,true,false,true] blank))
  have s155 : Runs 2454333294470514426257402353261830859003883563853288560273681755163761356292301659 (S 18089898818476991604091259344982770865908 (pre [false,false,true,true,false,true] blank)) (S 45224747046192479010228148362456927164772 (pre [false,false,false,true,true,true,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (twoEvenRound 9044949409238495802045629672491385432954 0 (pre [true] blank))
  have s156 : Runs 15339583090440715164108764707886442868773820026612591576920408688289883907555237613 (S 45224747046192479010228148362456927164772 (pre [false,false,false,true,true,true,true] blank)) (S 113061867615481197525570370906142317911933 (pre [true,true,true,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 22612373523096239505114074181228463582385 (pre [true,true,true,true] blank))
  have s157 : Runs 452247470461924790102281483624569271647734 (S 113061867615481197525570370906142317911933 (pre [true,true,true,true] blank)) (S 113061867615481197525570370906142317911935 (pre [true,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 113061867615481197525570370906142317911933 (pre [true,true,true] blank))
  have s158 : Runs 452247470461924790102281483624569271647742 (S 113061867615481197525570370906142317911935 (pre [true,true] blank)) (S 113061867615481197525570370906142317911937 (pre [] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 113061867615481197525570370906142317911935 (pre [true] blank))
  have s159 : Runs 95872394315254469775679779424290267929845985425076013257542227783338796519242749463 (S 113061867615481197525570370906142317911937 (pre [] blank)) (S 282654669038702993813925927265355794779842 (pre [false,false,false,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 56530933807740598762785185453071158955968 (pre [] blank))
  have h := (chain s150 (chain s151 (chain s152 (chain s153 (chain s154 (chain s155 (chain s156 (chain s157 (chain s158 s159)))))))))
  simpa only [Nat.reduceAdd] using h

end BB6.Agent3Leaf2265
