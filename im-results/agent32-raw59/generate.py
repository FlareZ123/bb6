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
'1RB':(157,'1RB1RB_1RC0RF_0RD0RB_1LD1RE_---1LA_0RC0LD','Raw59RBCount','BB6.Agent32Raw59RB'),
'1RD':(499,'1RB1RD_1RC---_0RD0LE_1LD1RE_1LF1LA_0LB1LC','Raw59RDSweep','BB6.Agent32Raw59RD'),
}
NGRAM={
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
    if raw in AUTO:
        module='Raw59Auto'+raw;ns='BB6Coverage.Agent31Pump.'+module
        pieces=['import SweepPumping','set_option maxRecDepth 100000','set_option maxHeartbeats 0','namespace '+ns,'open BB6Coverage']
        for i,rle,t,q,delta,pre,block,suf in AUTO[raw]:
            assert opens[i]==rle
            p=sweeps.parse(rle)
            st=sweeps.C(q,0,0,sweeps.W(pre,block,suf),sweeps.W())
            target=sweeps.C(q,delta,0,sweeps.W(pre+block,block,suf),sweeps.W())
            ans=sweeps.pump(p,st,target)
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
