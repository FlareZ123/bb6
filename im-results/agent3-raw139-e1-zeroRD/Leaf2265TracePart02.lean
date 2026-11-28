import Leaf2265TracePrelude

namespace BB6.Agent3Leaf2265
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Source-derived, independently counted section chunks 8–11 of the original 435-section trace. -/

theorem traceChunk8 : Runs 1093166308067697595609616103757349795252358675380 (S 3583073608642233792748 (pre [] blank)) (S 874773830234920359558032 (pre [false,false,false,true,false,true] blank)) := by
  have s80 : Runs 96288123637113596777545821491952529968363773 (S 3583073608642233792748 (pre [] blank)) (S 8957684021605584481873 (pre [] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 1791536804321116896373 (pre [] blank))
  have s81 : Runs 601800772731959979859885326425243451914320343 (S 8957684021605584481873 (pre [] blank)) (S 22394210054013961204682 (pre [false,false,false,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 4478842010802792240936 (pre [] blank))
  have s82 : Runs 3761254829574749874124059348057231434852455263 (S 22394210054013961204682 (pre [false,false,false,true,false,true] blank)) (S 55985525135034903011708 (pre [true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 11197105027006980602340 (pre [true,false,true] blank))
  have s83 : Runs 223942100540139612046834 (S 55985525135034903011708 (pre [true,false,true] blank)) (S 55985525135034903011709 (pre [false,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 55985525135034903011708 (pre [false,true] blank))
  have s84 : Runs 447884201080279224093692 (S 55985525135034903011709 (pre [false,false,true] blank)) (S 55985525135034903011713 (pre [] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one0010 55985525135034903011709 (pre [] blank))
  have s85 : Runs 23507842684842186713280969477871199958129016343 (S 55985525135034903011713 (pre [] blank)) (S 139963812837587257529282 (pre [false,false,false,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 27992762567517451505856 (pre [] blank))
  have s86 : Runs 146924016780263666958004659598566623865731059263 (S 139963812837587257529282 (pre [false,false,false,true,false,true] blank)) (S 349909532093968143823208 (pre [true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 69981906418793628764640 (pre [true,false,true] blank))
  have s87 : Runs 1399638128375872575292834 (S 349909532093968143823208 (pre [true,false,true] blank)) (S 349909532093968143823209 (pre [false,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 349909532093968143823208 (pre [false,true] blank))
  have s88 : Runs 2799276256751745150585692 (S 349909532093968143823209 (pre [false,false,true] blank)) (S 349909532093968143823213 (pre [] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one0010 349909532093968143823209 (pre [] blank))
  have s89 : Runs 918275104876647918487564113444250795975201441343 (S 349909532093968143823213 (pre [] blank)) (S 874773830234920359558032 (pre [false,false,false,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 174954766046984071911606 (pre [] blank))
  have h := (chain s80 (chain s81 (chain s82 (chain s83 (chain s84 (chain s85 (chain s86 (chain s87 (chain s88 s89)))))))))
  simpa only [Nat.reduceAdd] using h

theorem traceChunk9 : Runs 407241923424407666096504350456648474067742370499876891 (S 874773830234920359558032 (pre [false,false,false,true,false,true] blank)) (S 533919574117993383519308859 (pre [false,false,true,true,false,true,true,false,true,true,false,true] blank)) := by
  have s90 : Runs 5739219405479049490547266961288265125641413428013 (S 874773830234920359558032 (pre [false,false,false,true,false,true] blank)) (S 2186934575587300898895083 (pre [true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 437386915117460179779015 (pre [true,false,true] blank))
  have s91 : Runs 8747738302349203595580334 (S 2186934575587300898895083 (pre [true,false,true] blank)) (S 2186934575587300898895084 (pre [false,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 2186934575587300898895083 (pre [false,true] blank))
  have s92 : Runs 17495476604698407191160692 (S 2186934575587300898895084 (pre [false,false,true] blank)) (S 2186934575587300898895088 (pre [] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one0010 2186934575587300898895084 (pre [] blank))
  have s93 : Runs 35870121284244059315920648136182093701853217908973 (S 2186934575587300898895088 (pre [] blank)) (S 5467336438968252247237723 (pre [] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 1093467287793650449447543 (pre [] blank))
  have s94 : Runs 224188258026525370724504187534549059842888792874093 (S 5467336438968252247237723 (pre [] blank)) (S 13668341097420630618094307 (pre [false,false,false,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 2733668219484126123618861 (pre [] blank))
  have s95 : Runs 1401176612665783567028150967065815162708595684048413 (S 13668341097420630618094307 (pre [false,false,false,true,false,true] blank)) (S 34170852743551576545235767 (pre [false,false,false,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 6834170548710315309047153 (pre [true,false,true] blank))
  have s96 : Runs 8757353829161147293925943031598553613655074846766013 (S 34170852743551576545235767 (pre [false,false,false,true,false,true,true,false,true] blank)) (S 85427131858878941363089417 (pre [false,false,false,true,false,true,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 17085426371775788272617883 (pre [true,false,true,true,false,true] blank))
  have s97 : Runs 54733461432257170587037142666083982202160097345946263 (S 85427131858878941363089417 (pre [false,false,false,true,false,true,true,false,true,true,false,true] blank)) (S 213567829647197353407723542 (pre [false,false,false,true,false,true,true,false,true,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 42713565929439470681544708 (pre [true,false,true,true,false,true,true,false,true] blank))
  have s98 : Runs 342084133951607316168982139527346592291527074334928663 (S 213567829647197353407723542 (pre [false,false,false,true,false,true,true,false,true,true,false,true,true,false,true] blank)) (S 533919574117993383519308858 (pre [true,false,true,true,false,true,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 106783914823598676703861770 (pre [true,false,true,true,false,true,true,false,true,true,false,true] blank))
  have s99 : Runs 2135678296471973534077235434 (S 533919574117993383519308858 (pre [true,false,true,true,false,true,true,false,true,true,false,true] blank)) (S 533919574117993383519308859 (pre [false,false,true,true,false,true,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 533919574117993383519308858 (pre [false,true,true,false,true,true,false,true,true,false,true] blank))
  have h := (chain s90 (chain s91 (chain s92 (chain s93 (chain s94 (chain s95 (chain s96 (chain s97 (chain s98 s99)))))))))
  simpa only [Nat.reduceAdd] using h

theorem traceChunk10 : Runs 24273168099224697771490443568779603233188725495754014273890 (S 533919574117993383519308859 (pre [false,false,true,true,false,true,true,false,true,true,false,true] blank)) (S 130351458524900728398268765984 (pre [false,false,true,true,false,true] blank)) := by
  have s100 : Runs 2138025837197545726056138409420286390081581060944924219 (S 533919574117993383519308859 (pre [false,false,true,true,false,true,true,false,true,true,false,true] blank)) (S 1334798935294983458798272154 (pre [true,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (twoOddZeroRound 266959787058996691759654429 (pre [true,true,false,true,true,false,true] blank))
  have s101 : Runs 5339195741179933835193088618 (S 1334798935294983458798272154 (pre [true,true,false,true,true,false,true] blank)) (S 1334798935294983458798272157 (pre [true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 1334798935294983458798272154 (pre [true,false,true,true,false,true] blank))
  have s102 : Runs 5339195741179933835193088630 (S 1334798935294983458798272157 (pre [true,false,true] blank)) (S 1334798935294983458798272158 (pre [false,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 1334798935294983458798272157 (pre [false,true] blank))
  have s103 : Runs 10678391482359867670386177284 (S 1334798935294983458798272158 (pre [false,false,true] blank)) (S 1334798935294983458798272162 (pre [] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one0010 1334798935294983458798272158 (pre [] blank))
  have s104 : Runs 13362661482484660787850865245748640879307565862663878463 (S 1334798935294983458798272162 (pre [] blank)) (S 3336997338237458646995680408 (pre [] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 667399467647491729399136080 (pre [] blank))
  have s105 : Runs 83516634265529129924067907886038925642796046051519652573 (S 3336997338237458646995680408 (pre [] blank)) (S 8342493345593646617489201023 (pre [] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 1668498669118729323497840203 (pre [] blank))
  have s106 : Runs 521978964159557062025424424496305618907316453259227854093 (S 8342493345593646617489201023 (pre [] blank)) (S 20856233363984116543723002557 (pre [false,false,false,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 4171246672796823308744600511 (pre [] blank))
  have s107 : Runs 3262368525997231637658902652789066617710966084714329049663 (S 20856233363984116543723002557 (pre [false,false,false,true,false,true] blank)) (S 52140583409960291359307506392 (pre [false,false,false,true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 10428116681992058271861501278 (pre [true,false,true] blank))
  have s108 : Runs 20389803287482697735368141579410260526593935115871481496413 (S 52140583409960291359307506392 (pre [false,false,false,true,false,true,true,false,true] blank)) (S 130351458524900728398268765983 (pre [true,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 26070291704980145679653753195 (pre [true,false,true,true,false,true] blank))
  have s109 : Runs 521405834099602913593075063934 (S 130351458524900728398268765983 (pre [true,false,true,true,false,true] blank)) (S 130351458524900728398268765984 (pre [false,false,true,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 130351458524900728398268765983 (pre [false,true,true,false,true] blank))
  have h := (chain s100 (chain s101 (chain s102 (chain s103 (chain s104 (chain s105 (chain s106 (chain s107 (chain s108 s109)))))))))
  simpa only [Nat.reduceAdd] using h

theorem traceChunk11 : Runs 1446793562127631769865181658854964701568679837717715475363192176 (S 130351458524900728398268765984 (pre [false,false,true,true,false,true] blank)) (S 31824086553930841894108585445848 (pre [] blank)) := by
  have s110 : Runs 127436270546766860846050884878483458510081634536101541481619 (S 130351458524900728398268765984 (pre [false,false,true,true,false,true] blank)) (S 325878646312251820995671914962 (pre [false,false,false,true,true,true,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (twoEvenRound 65175729262450364199134382992 0 (pre [true] blank))
  have s111 : Runs 796476690917292880287818030487262829224887697640677915110463 (S 325878646312251820995671914962 (pre [false,false,false,true,true,true,true] blank)) (S 814696615780629552489179787408 (pre [true,true,true,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 162939323156125910497835957480 (pre [true,true,true,true] blank))
  have s112 : Runs 3258786463122518209956719149634 (S 814696615780629552489179787408 (pre [true,true,true,true] blank)) (S 814696615780629552489179787410 (pre [true,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 814696615780629552489179787408 (pre [true,true,true] blank))
  have s113 : Runs 3258786463122518209956719149642 (S 814696615780629552489179787410 (pre [true,true] blank)) (S 814696615780629552489179787412 (pre [] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 814696615780629552489179787410 (pre [true] blank))
  have s114 : Runs 4977979318233080501798862690618715378075804769978263150307213 (S 814696615780629552489179787412 (pre [] blank)) (S 2036741539451573881222949468533 (pre [] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 407348307890314776244589893705 (pre [] blank))
  have s115 : Runs 31112370738956753136242891816417889651460069159394718426133343 (S 2036741539451573881222949468533 (pre [] blank)) (S 5091853848628934703057373671332 (pre [false,false,false,true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroOddRound 1018370769725786940611474734266 (pre [] blank))
  have s116 : Runs 194452317118479707101518073852560891783139142899186416426620013 (S 5091853848628934703057373671332 (pre [false,false,false,true,false,true] blank)) (S 12729634621572336757643434178333 (pre [true,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 2545926924314467351528686835665 (pre [true,false,true] blank))
  have s117 : Runs 50918538486289347030573736713334 (S 12729634621572336757643434178333 (pre [true,false,true] blank)) (S 12729634621572336757643434178334 (pre [false,false,true] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one 12729634621572336757643434178333 (pre [false,true] blank))
  have s118 : Runs 101837076972578694061147473426692 (S 12729634621572336757643434178334 (pre [false,false,true] blank)) (S 12729634621572336757643434178338 (pre [] blank)) := by
    simpa [pre, P, G, O, S_consP] using (one0010 12729634621572336757643434178334 (pre [] blank))
  have s119 : Runs 1215326981990498169384487961579842185279884738479467663255100223 (S 12729634621572336757643434178338 (pre [] blank)) (S 31824086553930841894108585445848 (pre [] blank)) := by
    simpa [pre, P, G, O, S_consP] using (zeroEvenRound 6364817310786168378821717089168 (pre [] blank))
  have h := (chain s110 (chain s111 (chain s112 (chain s113 (chain s114 (chain s115 (chain s116 (chain s117 (chain s118 s119)))))))))
  simpa only [Nat.reduceAdd] using h

end BB6.Agent3Leaf2265
