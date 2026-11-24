import NearPowerGenerate

namespace BB6.Agent41NearPower

private def node0 : Cert := Cert.fork (-5924) (-5930) Cert.stop Cert.stop
private def node1 : Cert := Cert.fork (-27785) (-13719) Cert.stop Cert.stop
private def node2 : Cert := Cert.fork (-7160) (-7158) node0 node1
private def node3 : Cert := Cert.fork (-5540) (-5534) Cert.stop Cert.stop
private def node4 : Cert := Cert.fork (-5984) (-5994) node3 Cert.stop
private def node5 : Cert := Cert.fork (-7344) (-7346) node4 Cert.stop
private def node6 : Cert := Cert.fork (-23877) (-9851) Cert.stop Cert.stop
private def node7 : Cert := Cert.fork (-6444) (-6458) Cert.stop Cert.stop
private def node8 : Cert := Cert.fork (-8692) (-8690) node7 Cert.stop
private def node9 : Cert := Cert.fork (-15424) (-15438) node8 Cert.stop
private def node10 : Cert := Cert.fork (-29427) (-43453) node6 node9
private def node11 : Cert := Cert.fork (-16749) (-2731) Cert.stop node10
private def node12 : Cert := Cert.fork (-8083) (-22101) node11 Cert.stop
private def node13 : Cert := Cert.fork (-24137) (-10119) node12 Cert.stop
private def node14 : Cert := Cert.fork (-30235) (-44253) node13 Cert.stop
private def node15 : Cert := Cert.fork (-16041) (-1995) Cert.stop node14
private def node16 : Cert := Cert.fork (-27224) (-27222) Cert.stop Cert.stop
private def node17 : Cert := Cert.fork (-5915) (-19957) node15 node16
private def node18 : Cert := Cert.fork (-17673) (-3627) node17 Cert.stop
private def node19 : Cert := Cert.fork (-10799) (-24849) node18 Cert.stop
private def node20 : Cert := Cert.fork (-32313) (-18263) node19 Cert.stop
private def node21 : Cert := Cert.fork (-11416) (-11422) node5 node20
private def node22 : Cert := Cert.fork (-28521) (-14475) Cert.stop Cert.stop
private def node23 : Cert := Cert.fork (-23624) (-23614) node21 node22
private def node24 : Cert := Cert.fork (-5663) (-19709) Cert.stop node23
private def node25 : Cert := Cert.fork (-16909) (-2847) node24 Cert.stop
private def node26 : Cert := Cert.fork (-8487) (-22545) node25 Cert.stop
private def node27 : Cert := Cert.fork (-10931) (-24993) Cert.stop Cert.stop
private def node28 : Cert := Cert.fork (-25401) (-11335) node26 node27
private def node29 : Cert := Cert.fork (-10860) (-10858) node2 node28
private def node30 : Cert := Cert.fork (-9035) (-23101) Cert.stop node29
private def node31 : Cert := Cert.fork (-23489) (-9415) Cert.stop node30
private def node32 : Cert := Cert.fork (-7068) (-7066) Cert.stop node31
private def node33 : Cert := Cert.fork (-7067) (-21137) Cert.stop node32

def cert5288 : Cert := node33

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem checked5288 : check (fatalState 5288) cert5288=true := by decide +kernel

#print axioms checked5288
end BB6.Agent41NearPower
