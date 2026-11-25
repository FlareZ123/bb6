"""Candidate raw59 A1 child audits; reuse source enumerator and FAR masks."""
from pathlib import Path
from collections import Counter
from itertools import product
import hashlib,json,subprocess,sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'agent31-three-hole-tnf'))
from generate_four_hole import masks,slot,move,parse
import generate_sweeps as sweeps
MOVES=[w+d+q for w,d,q in product('01','LR','ABCDEF')]
SPECS={
'1RF':(376,None,None,1754,2531,45809,10651,'966f5c63047d899fff3664db39c92889553e9d5a266b9687b4a6c0c83da5dd7f','000 00100 00101 0010201 0010202 001020303 001020333 0010212 00102300402 001023101 00102310402 001023131 001023202 00102320402 001023231 00102343100 00102343444 00102344444 00120343323 0012101 001210321 001212333 001213121 00121314444 001213333 0012201 001230123 00123014101 0012301450125 001230145036503 0012301455555 001232201 00123224101 00123224122 00123224223 00123410121 00123412544674744 0012341415555 0012341567477087754 0012344514401 00123445674740147 001234546772389878a4aa8 001234563744389887443 0012345678444812348 0041115232323 0050104333132 005052224132422 10101 1010202 1012101 101213333 10123012424 10123212424 10123222423 10123224022 10123224101 10123440144 101234566712389a9a8896a 104245333613533'),
'1LA':(293,None,None,2881,1047,16645,4556,'939d46c990472741589354df08610a17377592d46cc746e115ac6f9050a6892e','000 00100 00101 0010201 0010202 001020303 0010212 001023201 00102320402 001023231 0012101 001210321 0012111 001212333 001213333 00121343333 00123014301 001232201 001232203 00123220422 00123220423 00123224022 00123224101 0012322452221 0012324054424 00123242344 0012341415555 001234425440623 0012344514401 0012344534444 00123445674740147 001234456778791772401 0012345234444 0012345434555 001234546772389878a4aa8 00123456147447477 001234563744389887443 0012345674891a78babb17bb7 0012345675554448141 001234567844898534848 0041115232323 00414570253666612 005052224132422 100 10101 1010202 1012101 1012121 101213333 10121334444 10121343321 10123012424 10123222401 10123222423 10123224101 10123440144 10123440344'),
'0RF':(223,None,None,745,2301,42708,9471,'26c1b90e0cecadf505e140fd637f98520c2fe75973d42abc83f1fe0b8d423564','000 00100 00101 0010202 00102343444 00102344444 0012101 001210321 001213333 00121342144 00121343333 001230123 00123014101 00123014141 00123014301 00123410121 0012341514454 0012344514401 00123445674740147 0020351434242 10101 1012101 1012121 101213233 101213333 10121343321 10123222401 10123222421 10123222423 10123224101 10123224324 10123414444 1012341555155 1012345444423 104245333613533'),
'0RC':(226,None,None,280,1787,31130,9692,'955687a364dde2051834b0cf4eab28372a1b1956646ffef64ba3985308787250','000 00101 0010201 0010202 001020303 00102343444 00102344444 0010234550255 00112344444 0012101 001213333 0012344514401 0012345614578234747 0012345670123458745 0012345678444812348 00414570253666612 100 10101 1012121 10121340121 10121343321 101230123 10123222423 10123224101 10123414444 101234567585555915888'),
'1RC':(190,None,None,647,1619,28427,8164,'bf5487839cac3bb6dceeffd1fb42d9d15bce9c5563df6d978cf6efc9a466a3ac','000 00101 0010202 001023100 001023101 001023231 0012101 001212333 00121304020 001213121 001213333 00121334133 00121342144 001230121 00123012423 00123014301 001232201 001232203 00123224101 00123224122 00123224123 00123224223 0012322452221 0012341544444 0012344514401 001234563744389887443 0012345672225285551 0012345674428449745a444 0012345675554448141 0050104333132 100 10100 10101 1012121 10123012424 10123222423 10123224022 10123224101 10123440144 10214675441134344'),
'0LD':(125,None,None,714,1413,25038,6748,'22602a319bce8dc7451b9cfef8b39db67fc9ff0bfcf718bea2cedc39dd6cfe0f','000 00100 00101 0010202 001020303 0010212 001023001 001023031 001023101 001023102 00102310434 0010231450201 001023200 001023201 001023202 001023210 001023231 00102324131 00102324141 00102324201 0010232450201 001023310 00102343444 00102344244 001210301 001210321 0012111 001212333 00121312431 00121314444 001213333 00121342144 00121344144 00123004010 001232201 00123220423 00123224101 00123224320 0012322452221 00123240344 0012341544444 001234156744894770644 00123440444 0012344534444 0012345678444812348 0041115232323 100 10101 1012101 101213333 10121343323 101230123 10123224322 104245333613533'),
'0RB':(241,None,None,308,1481,26750,7006,'9ebb3daf00c893b439f90ad922a54308fc143a709c0f41b0e66758d05a81e698','000 00100 00101 0010202 001020303 00102343444 0012101 001210321 001213121 00121342144 00123004010 001230123 00123014101 00123014356272343 00123104101 00123410121 0012344514401 00123445674740147 0012345650123782345 0012345678444812348 0020351434242 100 1012101 1012121 101213333 10121342144 10121343321 10123222423 1012322242511 1012322245521 101232242256223 10123414444 101234565554551 104245333613533 10623557155452376'),
'0RD':(157,12,8,85,632,11674,2778,'6145fc9050a5aeb9147edd345911ad9c81a8c3a0ec317bb01965fe2cf6bcbb75','000 00101 1012121 00102343444 1012101'),
'1LC':(84,None,None,178,1066,18816,5525,'b4de3ebe4f0b496574e81eadb4976e8a4f1bd6050c90b1c0d178034fded46a85','101213333 10101 001230120 000 0010201 001213333 00101 00123242344 001232201 0012101 0010202 0012111 00123224101 0012322452221 10123222401 00123224022'),
'1RB':(135,None,None,649,1398,25275,6231,'ac64fc94f0a887129e58a6d4e926f490d3d2428031f7853d63e902ae2c9583ab','000 00101 0010202 001020303 00102340101 001213121 00123014301 001232202 00123224101 00123224122 00123224221 0012341415555 0012344514401 0050104333132 005052224132422 1012101 10123212424 10123224322 10123440144 1012344555155 10214675441134344'),
'1RD':(93,None,None,682,547,9528,2372,'3e7403f557e1ba547bef92685c5e61e2a24480806109c1dcad6e55bc0e369dac','000 00101 0010202 001020303 0010212 001212333 001213333 001230123 00123224101 00414570253666612 0050104333132 005052224132422 10101 101121313 1012101 1012121 10121340121 10123222423 10123224101 10623557155452376'),
'0LC':(140,None,None,434,1478,25737,7824,'593b533deccd117e51edced82b9b658d50f564c2f2740fd6511d744c47fab032','000 00101 0010202 00102030401 001020333 001023101 001023202 00102324131 0010232450201 00102340101 00102340144 00112341244 0011234154434 00121232444 00121234444 00121314444 001213333 001232201 00123224122 00123224221 00123224223 0012322452220 0012341415555 003244416242354 10101 10121343321 104245333613533'),
'0RE':(167,None,None,672,1650,29417,7862,'08f9ccd750f3e6469cf8b15c7254b192e469ed0e2c35ba2d221afeeb517b1a11','000 00101 0010202 001020303 001213111 001213121 001213333 001230123 00123012423 00123012424 00123014301 00123014401 0012341415555 0012344514401 1012101 10123212424 10123222401 1012341235101 10123440144 1012344555155 1012345444423 10214675441134344 1042222345134 10c494424429282a552191a6c3b'),
}
AUTO={
'1RF':[
(32,'1RB1RF_1RC0LF_0RD---_1LD1RE_0RF1LA_1LB0LA',26,0,-2,'001','0101','01','R'),
(199,'1RB1RF_1RC1LE_0RD0LA_1LD1RE_---1LA_0RA0LC',21,0,-1,'0011','11','','R'),
(205,'1RB1RF_1RC---_0RD0LA_1LD1RE_---1LA_0RF0LC',23,0,-1,'0011','11','','R'),
(1096,'1RB1RF_1RC0RC_0RD0LA_1LD1RE_---1LA_0RE1LE',13,0,-1,'1111','111','','R'),
(1387,'1RB1RF_1RC0RC_0RD0LA_1LD1RE_---1LA_0RE1LF',11,5,-1,'1111','111','','R'),
],
'1LA':[
 (170,'1RB1LA_1RC0LD_0RD1LB_1LD1RE_0RF1LA_---1RC',65,0,-2,'111011','0101','01','R'),
 (286,'1RB1LA_1RC0LF_0RD0RF_1LD1RE_1RB1LA_---0LA',51,0,-2,'1100','1111','111111','R'),
 (301,'1RB1LA_1RC0LF_0RD0RF_1LD1RE_1RB1LA_---0LE',51,0,-2,'1100','1111','111111','R'),
 (558,'1RB1LA_1RC0RC_0RD0LF_1LD1RE_---1LA_1RF0RE',9,0,-1,'1111','111','','R'),
 (567,'1RB1LA_1RC0RC_0RD0RF_1LD1RE_0LA1LA_---0LE',9,0,-1,'1111','111','','R'),
 (1216,'1RB1LA_1RC0RF_0RD0RE_1LD1RE_---1LA_0RC0LA',30,0,-1,'11111111','111','','R'),
 (1217,'1RB1LA_1RC0RF_0RD0RE_1LD1RE_---1LA_0RD0LA',9,0,-1,'1111','111','','R'),
],
'0RF':[
 (130,'1RB0RF_1RC0RA_0RD---_1LD1RE_1LF1LA_1RD0LE',1,1,5,'0','10101010','1','L'),
 (294,'1RB0RF_1RC0LF_0RD0RB_1LD1RE_---1LA_1LE1LB',30,3,2,'001','0101','0101','L'),
 (337,'1RB0RF_1RC0LB_0RD1RA_1LD1RE_---1LA_1LF1LB',2153,1,-13,'0000000011111111111111111100000000000111','0000000000111','00000000000000000111','R'),
 (471,'1RB0RF_1RC---_0RD0LA_1LD1RE_1LF1LA_0LA1LE',13,0,-5,'011111','111111111','','R'),
 (473,'1RB0RF_1RC---_0RD1RC_1LD1RE_1LF1LA_0LA1LE',13,0,-5,'011111','111111111','','R'),
 (477,'1RB0RF_1RC---_0RD0LB_1LD1RE_1LF1LA_0RC1LE',12,5,-2,'11111','111','','R'),
],
'0RC':[(11,'1RB0RC_1RC---_0RD0LE_1LD1RE_1LF1LA_0RA0LB',11,1,-1,'0101','11','','R')],
'1RC':[(143,'1RB1RC_1RC0LF_0RD0RB_1LD1RE_---1LA_1LE1LB',26,3,2,'001','0101','0101')],
'0LD':[
 (192,'1RB0LD_1RC0RB_0RD0RF_1LD1RE_0RE1LA_---0RC',15,2,2,'0','00','10011'),
 (209,'1RB0LD_1RC0RF_0RD0LF_1LD1RE_0RE1LA_---0RB',15,2,2,'01','00','0011'),
 (258,'1RB0LD_1RC0RC_0RD0RB_1LD1RE_0RF1LA_---1LA',15,2,2,'0','00','10011'),
 (458,'1RB0LD_1RC0RB_0RD0RF_1LD1RE_1RB1LA_---0RC',13,2,2,'0','00','10011'),
 (473,'1RB0LD_1RC0RF_0RD0LF_1LD1RE_1RB1LA_---0RB',13,2,2,'01','00','0011'),
],
'0LC':[
 (177,'1RB0LC_1RC1RE_0RD1LE_1LD1RE_0RF1LA_---1RA',29,1,3,'0110','1110','1110'),
 (229,'1RB0LC_1RC---_0RD1LF_1LD1RE_0RF1LA_1RD1RA',18,5,2,'0011','1111','11'),
],
'0RE':[
 (55,'1RB0RE_1RC0LF_0RD1RE_1LD1RE_1LB1LA_---0LA',3,3,1,'001','11','1'),
],
}
MANUAL={
'1LA':(1911,'1RB1LA_1RC1LF_0RD0RC_1LD1RE_---1LA_1LB0LB','Raw59LACount','BB6.Agent32Raw59LACount'),
'0RC':(228,'1RB0RC_1RC---_0RD1LF_1LD1RE_0RA1LA_1RC0LF','Raw59RCBridge','BB6.Agent32Raw59RC0'),
'1RC':(485,'1RB1RC_1RC---_0RD1LF_1LD1RE_0RA1LA_1RC0LF','Raw59RCBridge','BB6.Agent32Raw59RC1'),
'1RB':(157,'1RB1RB_1RC0RF_0RD0RB_1LD1RE_---1LA_0RC0LD','Raw59RBCount','BB6.Agent32Raw59RB'),
'1RD':(499,'1RB1RD_1RC---_0RD0LE_1LD1RE_1LF1LA_0LB1LC','Raw59RDSweep','BB6.Agent32Raw59RD'),
}
MANUAL_MULTI={'1RF':[
 (389,"1RB1RF_1RC1RB_0RD---_1LD1RE_1LE1LA_0RA0LF","Raw59RFCounters","BB6.Agent32Raw59RFCount.M389"),
 (392,"1RB1RF_1RC1RA_0RD---_1LD1RE_0LE1LA_0RB0LF","Raw59RFCounters","BB6.Agent32Raw59RFCount.M392"),
 (393,"1RB1RF_1RC1RB_0RD---_1LD1RE_0LE1LA_0RB0LF","Raw59RFCounters","BB6.Agent32Raw59RFCount.M393"),
 (396,"1RB1RF_1RC0LA_0RD---_1LD1RE_1LE1LA_0RB0LF","Raw59RFCounters","BB6.Agent32Raw59RFCount.M396"),
 (397,"1RB1RF_1RC1RB_0RD---_1LD1RE_1LE1LA_0RB0LF","Raw59RFCounters","BB6.Agent32Raw59RFCount.M397"),
 (585,"1RB1RF_1RC0LE_0RD0RF_1LD1RE_0RC1LA_---0RE","Raw59RFTriple","BB6.Agent32Raw59RFTriple"),
 (803,"1RB1RF_1RC0LB_0RD0LD_1LD1RE_0RA1LA_---1LB","Raw59RFScan","BB6.Agent32Raw59RFScan.M803"),
 (804,"1RB1RF_1RC0LB_0RD0LE_1LD1RE_0RA1LA_---1LB","Raw59RFScan","BB6.Agent32Raw59RFScan.M804"),
 (805,"1RB1RF_1RC0LB_0RD0LF_1LD1RE_0RA1LA_---1LB","Raw59RFScan","BB6.Agent32Raw59RFScan.M805"),
 (806,"1RB1RF_1RC0LB_0RD0RA_1LD1RE_0RA1LA_---1LB","Raw59RFScan","BB6.Agent32Raw59RFScan.M806"),
]}
NGRAM={
'1RF':[
(14,'1RB1RF_1RC1LF_0RD0RA_1LD1RE_---1LA_0LE0LA',3,41),
(134,'1RB1RF_1RC0LF_0RD---_1LD1RE_1RA1LA_0RB0LB',8,168),
(136,'1RB1RF_1RC0LF_0RD---_1LD1RE_1RA1LA_0RE0LB',9,278),
(355,'1RB1RF_1RC0RE_0RD0RC_1LD1RE_1RA1LA_---0LE',5,407),
(363,'1RB1RF_1RC0RF_0RD0RC_1LD1RE_---1LA_1RA0LE',5,407),
(366,'1RB1RF_1RC1LF_0RD---_1LD1RE_0LA1LA_1RC0LE',3,38),
(376,'1RB1RF_1RC1LF_0RD0RA_1LD1RE_1RB1LA_---0LE',3,34),
(378,'1RB1RF_1RC1LF_0RD0RA_1LD1RE_1RC1LA_---0LE',4,69),
(776,'1RB1RF_1RC0LA_0RD0RC_1LD1RE_---1LA_0LF1LB',5,492),
(810,'1RB1RF_1RC0LB_0RD0RE_1LD1RE_0RA1LA_---1LB',9,1362),
(817,'1RB1RF_1RC0LB_0RD1RA_1LD1RE_0RA1LA_---1LB',9,1360),
(818,'1RB1RF_1RC0LB_0RD1RB_1LD1RE_0RA1LA_---1LB',9,1332),
(820,'1RB1RF_1RC0LB_0RD1RD_1LD1RE_0RA1LA_---1LB',6,4396),
(834,'1RB1RF_1RC0LF_0RD0RC_1LD1RE_---1LA_1RB1LB',5,439),
(1084,'1RB1RF_1RC0RA_0RD1LF_1LD1RE_---1LA_1LC1LE',5,145),
],
'1LA':[
 (4,'1RB1LA_1RC0LC_0RD0LA_1LD1RE_0RF1LA_0RA---',5,91),
 (5,'1RB1LA_1RC0LC_0RD0LA_1LD1RE_0RF1LA_0RD---',4,167),
 (7,'1RB1LA_1RC0LC_0RD0LA_1LD1RE_0RF1LA_1RB---',6,216),
 (272,'1RB1LA_1RC0LF_0RD---_1LD1RE_0RA1LA_---0LA',6,216),
 (273,'1RB1LA_1RC0LF_0RD---_1LD1RE_0RC1LA_---0LA',4,167),
 (275,'1RB1LA_1RC0LF_0RD---_1LD1RE_0RF1LA_0RA0LA',5,91),
 (276,'1RB1LA_1RC0LF_0RD---_1LD1RE_0RF1LA_0RD0LA',4,167),
 (278,'1RB1LA_1RC0LF_0RD---_1LD1RE_0RF1LA_1RB0LA',6,216),
 (364,'1RB1LA_1RC0LF_0RD0LD_1LD1RE_1RC1LA_---1LB',5,157),
 (381,'1RB1LA_1RC0LF_0RD1RC_1LD1RE_0RF1LA_---1LB',5,114),
 (382,'1RB1LA_1RC0LF_0RD1RC_1LD1RE_1LC1LA_---1LB',5,112),
 (384,'1RB1LA_1RC0LF_0RD1RC_1LD1RE_1RC1LA_---1LB',5,105),
],
'0RF':[
 (5,'1RB0RF_1RC1LB_0RD0LF_1LD1RE_---1LA_1LA0LA',4,74),
 (36,'1RB0RF_1RC1RA_0RD0LE_1LD1RE_1LC1LA_---0LB',4,271),
 (91,'1RB0RF_1RC1LE_0RD0RA_1LD1RE_1LB1LA_---0LE',7,424),
 (120,'1RB0RF_1RC0LB_0RD---_1LD1RE_1LF1LA_1RA0LE',8,236),
 (123,'1RB0RF_1RC0RD_0RD---_1LD1RE_1LF1LA_1RA0LE',7,207),
 (124,'1RB0RF_1RC1LA_0RD---_1LD1RE_1LF1LA_1RA0LE',8,161),
 (125,'1RB0RF_1RC1LD_0RD---_1LD1RE_1LF1LA_1RA0LE',8,169),
 (136,'1RB0RF_1RC1LF_0RD0RC_1LD1RE_1RA1LA_---0LE',3,120),
],
'0LD':[
 (210,'1RB0LD_1RC0RF_0RD0RC_1LD1RE_0RE1LA_---0RB',5,108),
 (254,'1RB0LD_1RC0RB_0RD0RC_1LD1RE_0RF1LA_---1LA',5,108),
 (354,'1RB0LD_1RC1RF_0RD1RA_1LD1RE_1LE1LA_---0RC',8,214),
 (474,'1RB0LD_1RC0RF_0RD0RC_1LD1RE_1RB1LA_---0RB',5,103),
 (584,'1RB0LD_1RC0LD_0RD0RF_1LD1RE_1RF1LA_---0RB',5,76),
 (596,'1RB0LD_1RC0RC_0RD0RE_1LD1RE_1RF1LA_---0RB',8,239),
 (597,'1RB0LD_1RC0RC_0RD0RF_1LD1RE_1RF1LA_---0RB',5,90),
 (600,'1RB0LD_1RC1LA_0RD0RC_1LD1RE_1RF1LA_---0RB',3,112),
 (607,'1RB0LD_1RC1RC_0RD0RF_1LD1RE_1RF1LA_---0RB',5,68),
 (614,'1RB0LD_1RC1RD_0RD0RB_1LD1RE_1RF1LA_---0RC',5,132),
 (701,'1RB0LD_1RC0RB_0RD0LB_1LD1RE_1RF1LA_---1RB',5,292),
],
'0RB':[(66,'1RB0RB_1RC0LF_0RD0RA_1LD1RE_---1LA_1LB0RC',9,1371),
       (70,'1RB0RB_1RC0LF_0RD0RC_1LD1RE_1RC1LA_1LB---',6,504)],
}
CHUNK=240
def generate(raw):
    B,first,first_slot,nopen,nsplit,ncycle,nlast,sha,bank=SPECS[raw]
    folder=ROOT/('generated_'+raw);folder.mkdir(exist_ok=True)
    parent=f'1RB{raw}_1RC---_0RD---_1LD1RE_---1LA_------'
    subprocess.run(['g++','-std=c++17','-O3',str(ROOT.parent/'agent2-tnf-raw99/enumerate.cpp'),'-o',str(folder/'enumerate')],check=True)
    subprocess.run([str(folder/'enumerate'),parent],cwd=folder,check=True)
    data=(folder/'open.txt').read_bytes();assert hashlib.sha256(data).hexdigest()==sha
    opens=data.decode().splitlines();assert len(opens)==len(set(opens))==nopen
    certs={};pumps={};imports=['Raw59Base']
    if raw in MANUAL:
        i,rle,module,ns=MANUAL[raw]
        assert opens[i]==rle
        pumps[rle]=(ns+'.table',ns+'.never');imports.append(module)
    for i,rle,module,ns in MANUAL_MULTI.get(raw,[]):
        assert opens[i]==rle
        pumps[rle]=(ns+'.table',ns+'.never')
        if module not in imports:imports.append(module)
    if raw in AUTO:
        module='Raw59Auto'+raw;ns='BB6Coverage.Agent31Pump.'+module
        pieces=['import SweepPumping','set_option maxRecDepth 100000','set_option maxHeartbeats 0','namespace '+ns,'open BB6Coverage']
        for i,rle,t,q,delta,pre,block,suf,*side in AUTO[raw]:
            assert opens[i]==rle
            p=sweeps.parse(rle)
            w=sweeps.W(pre,block,suf);v=sweeps.W(pre+block,block,suf);e=sweeps.W()
            st=sweeps.C(q,0,0,e,w) if side==['R'] else sweeps.C(q,0,0,w,e)
            target=sweeps.C(q,delta,0,e,v) if side==['R'] else sweeps.C(q,delta,0,v,e)
            ans=sweeps.pump(p,st,target,maxsteps=1000)
            assert ans is not None
            code,info=sweeps.generate(i,p,(t,None,st,target,ans))
            pieces.append(code);print('pump',rle,info)
            pumps[rle]=(ns+'.M'+str(i)+'.table',ns+'.M'+str(i)+'.never')
        pieces.append('end '+ns)
        (folder/(module+'.lean')).write_text('\n\n'.join(pieces)+'\n')
        imports.append(module)
    if raw in NGRAM:
        ng=ROOT.parent/'agent1-ngram'
        module='Raw59NGram'+raw;ns='BB6.Agent32Raw59NGram'+raw
        cases=NGRAM[raw]
        for i,rle,k,n in cases:
            assert opens[i]==rle
            pumps[rle]=(ns+'.p'+str(i),ns+'.never'+str(i))
        inputs=folder/'ngram-input.txt';outputs=folder/'ngram-output.txt'
        inputs.write_text(''.join(f'{i} {rle}\n' for i,rle,k,n in cases))
        subprocess.run(['g++','-std=c++17','-O3',str(ng/'ngram.cpp'),'-o',str(folder/'ngram')],check=True)
        with inputs.open() as inp, outputs.open('w') as out:
            subprocess.run([str(folder/'ngram'),'9'],stdin=inp,stdout=out,check=True)
        assert [tuple(map(int,line.split()[:3])) for line in outputs.read_text().splitlines()]==[(i,k,n) for i,rle,k,n in cases]
        subprocess.run([sys.executable,str(ng/'emit_ngram.py'),str(inputs),str(outputs),str(folder/(module+'.lean')),'--namespace',ns],check=True)
        imports.append(module)
    for rle in opens:
        if rle in pumps:continue
        for a in bank.split():
            try: masks(parse(rle),int(a[0]),[int(x,36) for x in a[1:]])
            except AssertionError: continue
            certs[rle]=a;break
        else: raise RuntimeError(('unresolved',rle))
    used=set()

    tree=json.loads((folder/'tree.json').read_text());assert tree[0]=='split';first,root_slot=tree[1:3]
    prefix=f'Raw59A{raw}'; ns=f'BB6.Agent32{prefix}'
    header=f'''set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace {ns}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
'''
    def emit(name,imports,body):
        (folder/(name+'.lean')).write_text(''.join('import '+i+'\n' for i in imports)+header+body+f'\nend {ns}\n')
    p=f'p{raw}'
    base=f'''
abbrev {p} : PartialMachine :=
  refine BB6.Agent32Raw59.p59 (0,true) (some {move(raw)})
theorem {p}_root : {p} initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem {p}_nohalt : weightedTNFNoAssignedHalt {p} :=
  weightedTNFNoAssignedHalt_refine _ _ _ BB6.Agent32Raw59.p59_nohalt

theorem split_checked (p : PartialMachine) (n : Nat) (s : Slot) (kids : Move → Audit)
    (hq : zipQueryOK {B} p n s = true)
    (hk : ∀ mv, zipCheck {B} (refine p s (some mv)) (kids mv) = true) :
    zipCheck {B} p (.split n s kids) = true := by
  change (zipQueryOK {B} p n s && allMoves (fun mv => zipCheck {B} (refine p s (some mv)) (kids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨hq, allMoves_of _ hk⟩
'''
    emit(prefix+'Base',imports,base)
    stats=Counter()
    def size(t):
        stats[t[0]]+=1
        return 1+sum(map(size,t[3])) if t[0]=='split' else 1
    size(tree)
    assert stats==Counter(split=nsplit,cycle=ncycle,last=nlast,open=nopen),stats
    def count(t):return 1+sum(map(count,t[3])) if t[0]=='split' else 1
    def render(t):
        tag,*v=t
        if tag=='cycle':
            e,k,r,b=v;return f'.cycle {e} {k} {str(r).lower()} ({b})'
        if tag=='last':
            n,s=v;return f'.last {n} {slot(s)}'
        if tag=='open':
            code=v[0];assert code not in used;used.add(code)
            if code in pumps:return '.proven '+ ' '.join(pumps[code])
            a=certs[code]
            d,D,L,R,z=masks(parse(code),int(a[0]),[int(x,36) for x in a[1:]])
            return f'.far {str(a[0]=="1").lower()} {d} ⟨0,{D},{L},{R},{z}⟩'
        assert tag=='split';n,s,kids=v;assert len(kids)==24
        return f'.split {n} {slot(s)} (byMove [\n'+',\n'.join(map(render,kids))+'])'
    def compose(pname,name,t):
        if count(t)<=CHUNK:
            return f'def t_{name} : Audit := {render(t)}\ntheorem c_{name} : zipCheck {B} {pname} t_{name} = true := by decide\n'
        assert t[0]=='split';_,n,s,kids=t
        out=[];names=[]
        for i,kid in enumerate(kids):
            a=f'{name}_{i:02}';names.append(a)
            out.append(f'abbrev p_{a} := refine {pname} {slot(s)} (some {move(MOVES[i])})\n')
            out.append(compose(f'p_{a}',a,kid))
        out.append(combine(pname,name,n,s,names))
        return ''.join(out)
    def combine(pname,name,n,s,names):
        cases='\n'.join(f'  · exact c_{names[12*w+6*r+q]}' for q,w,r in product(range(6),range(2),range(2)))
        return f'''
def k_{name} : Move → Audit := byMove [{','.join('t_'+x for x in names)}]
def t_{name} : Audit := .split {n} {slot(s)} k_{name}
theorem q_{name} : zipQueryOK {B} {pname} {n} {slot(s)} = true := by decide
theorem kcheck_{name} (mv : Move) : zipCheck {B} (refine {pname} {slot(s)} (some mv)) (k_{name} mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{cases}
theorem c_{name} : zipCheck {B} {pname} t_{name} = true :=
  split_checked {pname} {n} {slot(s)} k_{name} q_{name} kcheck_{name}
'''
    mods=[];names=[]
    for i,kid in enumerate(tree[3]):
        a=f'kid{i:02}';names.append(a);name=f'{prefix}Kid{i:02}';mods.append(name)
        emit(name,[prefix+'Base'],f'abbrev p_{a} := refine {p} {slot(root_slot)} (some {move(MOVES[i])})\n'+compose(f'p_{a}',a,kid))
    body=combine(p,'root',first,root_slot,names)
    body+=f'''
noncomputable def certificate{raw} : WeightedTNFCertificate {B} {p} 6 :=
  certifiedZip {B} {p} t_root {p}_root {p}_nohalt c_root
theorem all{raw} : ∀ m, compatible {p} m → WeightedBound {B} m := certificate{raw}.sound

#print axioms all{raw}
'''
    assert used==set(opens)
    emit(prefix+'Data',mods,body)
    print(raw,stats,'all FAR witnesses emitted')
if __name__=='__main__':
    for raw in sys.argv[1:] or SPECS:generate(raw)
