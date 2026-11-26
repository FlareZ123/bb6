import PackedGuardedReplay
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6.Agent6E0ZeroRF1892
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent6GuardedTail BB6.Agent6PackedReplay

def p : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨true,false,3⟩)
  | 2,true => some (some ⟨false,false,2⟩)
  | 3,false => some (some ⟨true,true,0⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨true,true,2⟩)
  | 5,false => some (some ⟨false,false,3⟩)
  | 5,true => some (some ⟨false,true,3⟩)
  | _,_ => none

def bits (s : String) : List Bool := s.toList.map (· == '1')
def P := bits "010110011110011110111101111111101111110011110111101111011110111100"
def B := bits "111111001111111101111111101111011110111111111100111100111101111111111111111111100111111111111111111001111000111111111111"
def T := bits "111111001111111101111111101111011110111111111100111100111101111111101111111111111111011111111000111111111111011111111111111111111111111110111111110111111110111111110111111111111111100111101111111111111100111111110111101111001111011110111111111111111100111111001111"
def C (u : List Bool) : Z0 := ⟨0,P++u,[]⟩
def family (k : Nat) := C (rep B k ++ T)


private def seedC0 : PZ := ⟨2,2064382,156⟩

private theorem seedH0 : prun p false 512 (pack (⟨0,[],[]⟩)) = some (seedC0) := by decide +kernel

private def seedC1 : PZ := ⟨2,59,164610687⟩

private theorem seedH1 : prun p false 512 (seedC0) = some (seedC1) := by decide +kernel

private def seedC2 : PZ := ⟨3,127,42144265209⟩

private theorem seedH2 : prun p false 512 (seedC1) = some (seedC2) := by decide +kernel

private def seedC3 : PZ := ⟨2,511963,164610687⟩

private theorem seedH3 : prun p false 512 (seedC2) = some (seedC3) := by decide +kernel

private def seedC4 : PZ := ⟨3,511999,42144265209⟩

private theorem seedH4 : prun p false 512 (seedC3) = some (seedC4) := by decide +kernel

private def seedC5 : PZ := ⟨4,549193514957,160761⟩

private theorem seedH5 : prun p false 512 (seedC4) = some (seedC5) := by decide +kernel

private def seedC6 : PZ := ⟨4,140599645696511,2510⟩

private theorem seedH6 : prun p false 512 (seedC5) = some (seedC6) := by decide +kernel

private def seedC7 : PZ := ⟨4,36857353521852284923,158⟩

private theorem seedH7 : prun p false 512 (seedC6) = some (seedC7) := by decide +kernel

private def seedC8 : PZ := ⟨3,8455446071,2697233157759⟩

private theorem seedH8 : prun p false 512 (seedC7) = some (seedC8) := by decide +kernel

private def seedC9 : PZ := ⟨4,9078966289945579487,10046⟩

private theorem seedH9 : prun p false 512 (seedC8) = some (seedC9) := by decide +kernel

private def seedC10 : PZ := ⟨3,594999134777923692527597,5⟩

private theorem seedH10 : prun p false 512 (seedC9) = some (seedC10) := by decide +kernel

private def seedC11 : PZ := ⟨2,2014,11584527408037334148927⟩

private theorem seedH11 : prun p false 512 (seedC10) = some (seedC11) := by decide +kernel

private def seedC12 : PZ := ⟨3,35181073352607676,2634016550⟩

private theorem seedH12 : prun p false 512 (seedC11) = some (seedC12) := by decide +kernel

private def seedC13 : PZ := ⟨3,8795268338153470,10221113290⟩

private theorem seedH13 : prun p false 512 (seedC12) = some (seedC13) := by decide +kernel

private def seedC14 : PZ := ⟨5,2417624951802459498122903500,15⟩

private theorem seedH14 : prun p false 512 (seedC13) = some (seedC14) := by decide +kernel

private def seedC15 : PZ := ⟨4,36890029171790458650559,82310046⟩

private theorem seedH15 : prun p false 512 (seedC14) = some (seedC15) := by decide +kernel

private def seedC16 : PZ := ⟨4,2475647950645718627093435645693,156⟩

private theorem seedH16 : prun p false 512 (seedC15) = some (seedC16) := by decide +kernel

private def seedC17 : PZ := ⟨4,2535063501461215874143679641779197,146⟩

private theorem seedH17 : prun p false 512 (seedC16) = some (seedC17) := by decide +kernel

private def seedC18 : PZ := ⟨4,2595905025496285055123127956436934637,19⟩

private theorem seedH18 : prun p false 512 (seedC17) = some (seedC18) := by decide +kernel

private def seedC19 : PZ := ⟨3,158441468841325992133979977809917,41155059⟩

private theorem seedH19 : prun p false 512 (seedC18) = some (seedC19) := by decide +kernel

private def seedC20 : PZ := ⟨2,2595905025496285055123229171359939706,2510⟩

private theorem seedH20 : prun p false 512 (seedC19) = some (seedC20) := by decide +kernel

private def seedC21 : PZ := ⟨2,664551686527048974111546667868144660466,5017⟩

private theorem seedH21 : prun p false 512 (seedC20) = some (seedC21) := by decide +kernel

private def seedC22 : PZ := ⟨3,576406705809225939934,741409804944811742973926⟩

private theorem seedH22 : prun p false 512 (seedC21) = some (seedC22) := by decide +kernel

private def seedC23 : PZ := ⟨3,2722003708014792597967687597922326482120568,134⟩

private theorem seedH23 : prun p false 512 (seedC22) = some (seedC23) := by decide +kernel

private def seedC24 : PZ := ⟨1,680500927003698149491921899480581620629479,160761⟩

private theorem seedH24 : prun p false 512 (seedC23) = some (seedC24) := by decide +kernel

private def seedC25 : PZ := ⟨2,2854227760135319163206565990679001413732804837338,8⟩

private theorem seedH25 : prun p false 512 (seedC24) = some (seedC25) := by decide +kernel

private def seedC26 : PZ := ⟨2,10632826984432783585811279679384088198638,5267522791⟩

private theorem seedH26 : prun p false 512 (seedC25) = some (seedC26) := by decide +kernel

private def seedC27 : PZ := ⟨4,170125231750924537372980474870340798899196,329220126⟩

private theorem seedH27 : prun p false 512 (seedC26) = some (seedC27) := by decide +kernel

private def seedC28 : PZ := ⟨0,44597308752114361925102593604410618387402587966,2547⟩

private theorem seedH28 : prun p false 512 (seedC27) = some (seedC28) := by decide +kernel

private def seedC29 : PZ := ⟨2,166137921631762243528301244990567186426,172622922904479⟩

private theorem seedH29 : prun p false 512 (seedC28) = some (seedC29) := by decide +kernel

private def seedC30 : PZ := ⟨2,134205145050,213696827961925426685215478246605097795198⟩

private theorem seedH30 : prun p false 512 (seedC29) = some (seedC30) := by decide +kernel

private def seedC31 : PZ := ⟨4,2305626835863830527229,12438792500291335552763711782514⟩

private theorem seedH31 : prun p false 512 (seedC30) = some (seedC31) := by decide +kernel

private def seedC32 : PZ := ⟨4,633765878836167169519812605632121,45252063501871218446⟩

private theorem seedH32 : prun p false 512 (seedC31) = some (seedC32) := by decide +kernel

private def seedC33 : PZ := ⟨1,41534480635407051621650438922731257847,690491691617889⟩

private theorem seedH33 : prun p false 512 (seedC32) = some (seedC33) := by decide +kernel

private def seedC34 : PZ := ⟨2,162244064982058795397084647870930843,176765873054171775⟩

private theorem seedH34 : prun p false 512 (seedC33) = some (seedC34) := by decide +kernel

private def seedC35 : PZ := ⟨3,2922729242385098118967890369993555679934173031626747,73⟩

private theorem seedH35 : prun p false 512 (seedC34) = some (seedC35) := by decide +kernel

private def seedC36 : PZ := ⟨1,748218686050585118455779934718350254063148297723965431,39⟩

private theorem seedH36 : prun p false 512 (seedC35) = some (seedC36) := by decide +kernel

private def seedC37 : PZ := ⟨2,182670577649068632435493148124597229995885814874106,20577529⟩

private theorem seedH37 : prun p false 512 (seedC36) = some (seedC37) := by decide +kernel

private def seedC38 : PZ := ⟨4,158441469709041792379965476437948,23722900260414328857945630⟩

private theorem seedH38 : prun p false 512 (seedC37) = some (seedC38) := by decide +kernel

private def seedC39 : PZ := ⟨0,45667644412267158108873287031580482620841402023406,82305341⟩

private theorem seedH39 : prun p false 512 (seedC38) = some (seedC39) := by decide +kernel

private def seedC40 : PZ := ⟨2,11690916969540392475871561480084603550935398917992438,82312732⟩

private theorem seedH40 : prun p false 512 (seedC39) = some (seedC40) := by decide +kernel

private def seedC41 : PZ := ⟨1,3138256627776713364679551603338545472774563035093209382647711,33⟩

private theorem seedH41 : prun p false 512 (seedC40) = some (seedC41) := by decide +kernel

private def seedC42 : PZ := ⟨0,713556943941674345451145109868445040950646929914,690427267121102⟩

private theorem seedH42 : prun p false 512 (seedC41) = some (seedC42) := by decide +kernel

private def seedC43 : PZ := ⟨5,200848424177709655339491302613666910257572041235894786109603772,15⟩

private theorem seedH43 : prun p false 512 (seedC42) = some (seedC43) := by decide +kernel

private def seedC44 : PZ := ⟨4,822675145431898748270556375505579664415015080902225043906480701421,4⟩

private theorem seedH44 : prun p false 512 (seedC43) = some (seedC44) := by decide +kernel

private def seedC45 : PZ := ⟨2,47885995907237447581169915822426536144631395634829532794,674308289438⟩

private theorem seedH45 : prun p false 512 (seedC44) = some (seedC45) := by decide +kernel

private def seedC46 : PZ := ⟨3,200848424177709655339491302613666910257572041236748048734781414,41156486⟩

private theorem seedH46 : prun p false 512 (seedC45) = some (seedC46) := by decide +kernel

private def seedC47 : PZ := ⟨2,842419348922264318229049728517713576360975442847457287800488732893083,1255⟩

private theorem seedH47 : prun p false 512 (seedC46) = some (seedC47) := by decide +kernel

private def seedC48 : PZ := ⟨4,200848424177709655339491302613666910257572041236748048734875512,21070168062⟩

private theorem seedH48 : prun p false 512 (seedC47) = some (seedC48) := by decide +kernel

private def seedC49 : PZ := ⟨5,822675145431898748270556375505579664415015080905720007642763478936,5144065⟩

private theorem seedH49 : prun p false 512 (seedC48) = some (seedC49) := by decide +kernel

private def seedC50 : PZ := ⟨3,52651209307641519889315608032357098522560965177966080489136862658295,20578255⟩

private theorem seedH50 : prun p false 512 (seedC49) = some (seedC50) := by decide +kernel

private def seedC51 : PZ := ⟨4,3533362844862048919005376192520760124185144743836861492158539218828736200685,4⟩

private theorem seedH51 : prun p false 512 (seedC50) = some (seedC51) := by decide +kernel

private def seedC52 : PZ := ⟨2,3450549653185594647466187688008554808774555413903185050936073455887450078,160752⟩

private theorem seedH52 : prun p false 512 (seedC51) = some (seedC52) := by decide +kernel

private def seedC53 : PZ := ⟨4,49035259809011146323117993802164773012102549130065441963980,11311960344512104910⟩

private theorem seedH53 : prun p false 512 (seedC52) = some (seedC53) := by decide +kernel

private def seedC54 : PZ := ⟨0,226135222071171130816344076321328647947849263605559137236271512609421291289082,2⟩

private theorem seedH54 : prun p false 512 (seedC53) = some (seedC54) := by decide +kernel

private def seedC55 : PZ := ⟨4,226135222071171130816344076321328647947849263605559137236271512609421291667422,1254⟩

private theorem seedH55 : prun p false 512 (seedC54) = some (seedC55) := by decide +kernel

private def seedC56 : PZ := ⟨4,51417196589493671766909773469098729025938442556607500872876681190,707063488907634490⟩

private theorem seedH56 : prun p false 512 (seedC55) = some (seedC56) := by decide +kernel

private def seedC57 : PZ := ⟨4,237119966618500339666878806172713508350563989434462777886661067240118992093918920675,6⟩

private theorem seedH57 : prun p false 512 (seedC56) = some (seedC57) := by decide +kernel

private def seedC58 : PZ := ⟨3,15175677863584021738680243595053664534436095323805617784746308303367615494036851195888,2⟩

private theorem seedH58 : prun p false 512 (seedC57) = some (seedC58) := by decide +kernel

private def seedC59 : PZ := ⟨2,59279991654625084916719701543178377087640997358615694471665266810029748023581474715,80380⟩

private theorem seedH59 : prun p false 512 (seedC58) = some (seedC59) := by decide +kernel

private def seedC60 : PZ := ⟨0,210604837230566079557262432129428394090243860711864323575302886162426,22623838119249575539⟩

private theorem seedH60 : prun p false 512 (seedC59) = some (seedC60) := by decide +kernel

private def seedC61 : PZ := ⟨3,56533805517792782704086019080332161986962315901389784309067980585127399784419,84280582143⟩

private theorem seedH61 : prun p false 512 (seedC60) = some (seedC61) := by decide +kernel

private def seedC62 : PZ := ⟨4,15175677863584021738680243595053664534436095323805617784746308303367820379228167208909,1255⟩

private theorem seedH62 : prun p false 512 (seedC61) = some (seedC62) := by decide +kernel

private def seedC63 : PZ := ⟨4,215659353324099665466636730500534675548409713368949067341110155430326263,11313015875467804610⟩

private theorem seedH63 : prun p false 512 (seedC62) = some (seedC63) := by decide +kernel

private def seedC64 : PZ := ⟨4,53914838331024916366659182625133668887102428342237266835277538881665534,45252063501869986022⟩

private theorem seedH64 : prun p false 512 (seedC63) = some (seedC64) := by decide +kernel

private def seedC65 : PZ := ⟨1,248638306116960612166537111061359239732200985785231241785283515353446289492922837155903487,73⟩

private theorem seedH65 : prun p false 512 (seedC64) = some (seedC65) := by decide +kernel

private def seedC66 : PZ := ⟨2,3704999478414067807294981346448648567977562334913480904479079177281950257803917750,168577060839⟩

private theorem seedH66 : prun p false 512 (seedC65) = some (seedC66) := by decide +kernel

private def seedC67 : PZ := ⟨3,3884973533077509565102142360333738120815640402894238152895054927397598273527002427228150,643042⟩

private theorem seedH67 : prun p false 512 (seedC66) = some (seedC67) := by decide +kernel

private def seedC68 : PZ := ⟨4,14133451379448195676021504770083040496740578975347446077266995152595330268156,176748735307399071⟩

private theorem seedH68 : prun p false 512 (seedC67) = some (seedC68) := by decide +kernel

private def seedC69 : PZ := ⟨0,3290700581727594993082225502022318657660060323622880055864107973874,759130037754638876686578681⟩

private theorem seedH69 : prun p false 512 (seedC68) = some (seedC69) := by decide +kernel

private def seedC70 : PZ := ⟨2,56533805517792782704086019080332161986962315901389784309067987072040934799866,44187183826849730⟩

private theorem seedH70 : prun p false 512 (seedC69) = some (seedC70) := by decide +kernel

private def seedC71 : PZ := ⟨4,15539894132310038260408569441334952483262561611576952611580221485757863100077703008345723,160754⟩

private theorem seedH71 : prun p false 512 (seedC70) = some (seedC71) := by decide +kernel

private def seedC72 : PZ := ⟨4,1018422501855070667434136006907327445943095237776307166352521395290627316126692344354970791933,36⟩

private theorem seedH72 : prun p false 512 (seedC71) = some (seedC72) := by decide +kernel

private def seedC73 : PZ := ⟨4,15912851591485479178658375107926991342860863090254799474258146801416051814479568275909767158,80378⟩

private theorem seedH73 : prun p false 512 (seedC72) = some (seedC73) := by decide +kernel

private def seedC74 : PZ := ⟨0,15175677863584021738680243595053664534436095323805617784746310044685413183669632221182,21577863787279⟩

private theorem seedH74 : prun p false 512 (seedC73) = some (seedC74) := by decide +kernel

private def seedC75 : PZ := ⟨2,4073690007420282669736544027629309783772380951105228665410085581162509264612899006718605655661,80382⟩

private theorem seedH75 : prun p false 512 (seedC74) = some (seedC75) := by decide +kernel

private def seedC76 : PZ := ⟨4,3978212897871369794664593776981747835715215772563699868564536700354012953723534186248649980,329221350⟩

private theorem seedH76 : prun p false 512 (seedC75) = some (seedC76) := by decide +kernel

private theorem seedH77 : prun p false 430 (seedC76) = some (pack (family 0)) := by decide +kernel

theorem seed : run0 p 39854 (⟨0,[],[]⟩) = some (family 0) := replay_sound p false 39854 (⟨0,[],[]⟩) (family 0) (prun_join (prun_join (prun_join (prun_join (prun_join (prun_join (prun_join seedH0 seedH1) (prun_join seedH2 seedH3)) (prun_join (prun_join seedH4 seedH5) (prun_join seedH6 seedH7))) (prun_join (prun_join (prun_join seedH8 seedH9) (prun_join seedH10 seedH11)) (prun_join (prun_join seedH12 seedH13) (prun_join seedH14 seedH15)))) (prun_join (prun_join (prun_join (prun_join seedH16 seedH17) (prun_join seedH18 seedH19)) (prun_join (prun_join seedH20 seedH21) (prun_join seedH22 seedH23))) (prun_join (prun_join (prun_join seedH24 seedH25) (prun_join seedH26 seedH27)) (prun_join (prun_join seedH28 seedH29) (prun_join seedH30 seedH31))))) (prun_join (prun_join (prun_join (prun_join (prun_join seedH32 seedH33) (prun_join seedH34 seedH35)) (prun_join (prun_join seedH36 seedH37) (prun_join seedH38 seedH39))) (prun_join (prun_join (prun_join seedH40 seedH41) (prun_join seedH42 seedH43)) (prun_join (prun_join seedH44 seedH45) (prun_join seedH46 seedH47)))) (prun_join (prun_join (prun_join (prun_join seedH48 seedH49) (prun_join seedH50 seedH51)) (prun_join (prun_join seedH52 seedH53) (prun_join seedH54 seedH55))) (prun_join (prun_join (prun_join seedH56 seedH57) (prun_join seedH58 seedH59)) (prun_join (prun_join seedH60 seedH61) (prun_join seedH62 seedH63)))))) (prun_join (prun_join (prun_join (prun_join seedH64 seedH65) (prun_join seedH66 seedH67)) (prun_join (prun_join seedH68 seedH69) (prun_join seedH70 seedH71))) (prun_join (prun_join (prun_join seedH72 seedH73) (prun_join seedH74 seedH75)) (prun_join seedH76 seedH77))))

private def guardedPeriodC0 : PZ := ⟨2,349573760409582,5268033511⟩

private theorem guardedPeriodH0 : prun p true 512 (pack (C [])) = some (guardedPeriodC0) := by decide +kernel

private def guardedPeriodC1 : PZ := ⟨1,536813183,5523933507088542⟩

private theorem guardedPeriodH1 : prun p true 512 (guardedPeriodC0) = some (guardedPeriodC1) := by decide +kernel

private def guardedPeriodC2 : PZ := ⟨3,2305595062829969273,5144383⟩

private theorem guardedPeriodH2 : prun p true 512 (guardedPeriodC1) = some (guardedPeriodC2) := by decide +kernel

private def guardedPeriodC3 : PZ := ⟨3,154725865510527863510527999,1255⟩

private theorem guardedPeriodH3 : prun p true 512 (guardedPeriodC2) = some (guardedPeriodC3) := by decide +kernel

private def guardedPeriodC4 : PZ := ⟨3,604397912150499466932029,82313023⟩

private theorem guardedPeriodH4 : prun p true 512 (guardedPeriodC3) = some (guardedPeriodC4) := by decide +kernel

private def guardedPeriodC5 : PZ := ⟨4,154725865510527863534649331,41156510⟩

private theorem guardedPeriodH5 : prun p true 512 (guardedPeriodC4) = some (guardedPeriodC5) := by decide +kernel

private def guardedPeriodC6 : PZ := ⟨3,36889521005279508479,690427267121103⟩

private theorem guardedPeriodH6 : prun p true 512 (guardedPeriodC5) = some (guardedPeriodC6) := by decide +kernel

private def guardedPeriodC7 : PZ := ⟨4,144099691833753592,176749380383002598⟩

private theorem guardedPeriodH7 : prun p true 512 (guardedPeriodC6) = some (guardedPeriodC7) := by decide +kernel

private def guardedPeriodC8 : PZ := ⟨2,40560457402918499443244083966462,2511⟩

private theorem guardedPeriodH8 : prun p true 512 (guardedPeriodC7) = some (guardedPeriodC8) := by decide +kernel

private def guardedPeriodC9 : PZ := ⟨2,10632680545430667118049777147690582010,159⟩

private theorem guardedPeriodH9 : prun p true 512 (guardedPeriodC8) = some (guardedPeriodC9) := by decide +kernel

private def guardedPeriodC10 : PZ := ⟨3,604397913857080057915390,2761966753545418⟩

private theorem guardedPeriodH10 : prun p true 512 (guardedPeriodC9) = some (guardedPeriodC10) := by decide +kernel

private def guardedPeriodC11 : PZ := ⟨4,2595869273786784066800392687558559,164626034⟩

private theorem guardedPeriodH11 : prun p true 512 (guardedPeriodC10) = some (guardedPeriodC11) := by decide +kernel

private def guardedPeriodC12 : PZ := ⟨4,2658170136357666884403602112060063725,20578255⟩

private theorem guardedPeriodH12 : prun p true 512 (guardedPeriodC11) = some (guardedPeriodC12) := by decide +kernel

private def guardedPeriodC13 : PZ := ⟨3,633757146920601578808689620990,345213633560570⟩

private theorem guardedPeriodH13 : prun p true 512 (guardedPeriodC12) = some (guardedPeriodC13) := by decide +kernel

private def guardedPeriodC14 : PZ := ⟨4,2535028587682406315234759229310,86303093410874⟩

private theorem guardedPeriodH14 : prun p true 512 (guardedPeriodC13) = some (guardedPeriodC14) := by decide +kernel

private def guardedPeriodC15 : PZ := ⟨3,10632680545430667537614411574540171196,20576382⟩

private theorem guardedPeriodH15 : prun p true 512 (guardedPeriodC14) = some (guardedPeriodC15) := by decide +kernel

private def guardedPeriodC16 : PZ := ⟨3,713547112678752489210980430795842211597484025,19⟩

private theorem guardedPeriodH16 : prun p true 512 (guardedPeriodC15) = some (guardedPeriodC16) := by decide +kernel

private def guardedPeriodC17 : PZ := ⟨5,604397913857080057921264,185352452103664510738383⟩

private theorem guardedPeriodH17 : prun p true 512 (guardedPeriodC16) = some (guardedPeriodC17) := by decide +kernel

private def guardedPeriodC18 : PZ := ⟨2,41533908380588545069210357953609197,2697233170382⟩

private theorem guardedPeriodH18 : prun p true 512 (guardedPeriodC17) = some (guardedPeriodC18) := by decide +kernel

private def guardedPeriodC19 : PZ := ⟨4,696823352225344227751877124825019771189243,41156510⟩

private theorem guardedPeriodH19 : prun p true 512 (guardedPeriodC18) = some (guardedPeriodC19) := by decide +kernel

private def guardedPeriodC20 : PZ := ⟨5,696823352225344227751877124825801345785596,41156509⟩

private theorem guardedPeriodH20 : prun p true 512 (guardedPeriodC19) = some (guardedPeriodC20) := by decide +kernel

private def guardedPeriodC21 : PZ := ⟨3,680491554907562722413942504712696626929,168561344451⟩

private theorem guardedPeriodH21 : prun p true 512 (guardedPeriodC20) = some (guardedPeriodC21) := by decide +kernel

private def guardedPeriodC22 : PZ := ⟨2,38681466486853123706961389,2965351709979058112364542⟩

private theorem guardedPeriodH22 : prun p true 512 (guardedPeriodC21) = some (guardedPeriodC22) := by decide +kernel

private def guardedPeriodC23 : PZ := ⟨0,158439286730150395098102185934,723962819819105984391⟩

private theorem guardedPeriodH23 : prun p true 512 (guardedPeriodC22) = some (guardedPeriodC23) := by decide +kernel

private def guardedPeriodC24 : PZ := ⟨0,11149173635605507671782650716056097990277626,10288130⟩

private theorem guardedPeriodH24 : prun p true 512 (guardedPeriodC23) = some (guardedPeriodC24) := by decide +kernel

private def guardedPeriodC25 : PZ := ⟨3,182668060845760637694486949331863109474275294840,626⟩

private theorem guardedPeriodH25 : prun p true 512 (guardedPeriodC24) = some (guardedPeriodC25) := by decide +kernel

private def guardedPeriodC26 : PZ := ⟨2,2854188450715009963976358583310361085535551486,20578255⟩

private theorem guardedPeriodH26 : prun p true 512 (guardedPeriodC25) = some (guardedPeriodC26) := by decide +kernel

private def guardedPeriodC27 : PZ := ⟨3,47885336142351076607783586845651922995934955398741967,9⟩

private theorem guardedPeriodH27 : prun p true 512 (guardedPeriodC26) = some (guardedPeriodC27) := by decide +kernel

private def guardedPeriodC28 : PZ := ⟨3,10140114350729625286278542913403,1482819508542152445424633⟩

private theorem guardedPeriodH28 : prun p true 512 (guardedPeriodC27) = some (guardedPeriodC28) := by decide +kernel

private def guardedPeriodC29 : PZ := ⟨3,766165378277617225724537389530865474481998335136231409,39⟩

private theorem guardedPeriodH29 : prun p true 512 (guardedPeriodC28) = some (guardedPeriodC29) := by decide +kernel

private def guardedPeriodC30 : PZ := ⟨3,766165378277617225724537389530865474481998383984644045,67⟩

private theorem guardedPeriodH30 : prun p true 512 (guardedPeriodC29) = some (guardedPeriodC30) := by decide +kernel

private theorem guardedPeriodH31 : prun p true 276 (guardedPeriodC30) = some (pack (C B)) := by decide +kernel

theorem guardedPeriod : guardedRun p 16148 (C []) = some (C B) := replay_sound p true 16148 (C []) (C B) (prun_join (prun_join (prun_join (prun_join (prun_join guardedPeriodH0 guardedPeriodH1) (prun_join guardedPeriodH2 guardedPeriodH3)) (prun_join (prun_join guardedPeriodH4 guardedPeriodH5) (prun_join guardedPeriodH6 guardedPeriodH7))) (prun_join (prun_join (prun_join guardedPeriodH8 guardedPeriodH9) (prun_join guardedPeriodH10 guardedPeriodH11)) (prun_join (prun_join guardedPeriodH12 guardedPeriodH13) (prun_join guardedPeriodH14 guardedPeriodH15)))) (prun_join (prun_join (prun_join (prun_join guardedPeriodH16 guardedPeriodH17) (prun_join guardedPeriodH18 guardedPeriodH19)) (prun_join (prun_join guardedPeriodH20 guardedPeriodH21) (prun_join guardedPeriodH22 guardedPeriodH23))) (prun_join (prun_join (prun_join guardedPeriodH24 guardedPeriodH25) (prun_join guardedPeriodH26 guardedPeriodH27)) (prun_join (prun_join guardedPeriodH28 guardedPeriodH29) (prun_join guardedPeriodH30 guardedPeriodH31)))))

theorem pump (tail : List Bool) : run0 p 16148 (C tail) = some (C (B++tail)) := by
  have h := guardedRun_append p 16148 tail guardedPeriod
  simpa only [appendL,C,List.append_nil,List.append_assoc] using h

theorem growth (k : Nat) : run0 p 16148 (family k) = some (family (k+1)) := by
  simpa only [family,rep,List.append_assoc] using pump (rep B k ++ T)

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  never_of_growth p family 39854 (fun _ => 16148) seed (by intro k; decide) growth m hm
#print axioms seed
#print axioms guardedPeriod
#print axioms never
end BB6.Agent6E0ZeroRF1892
