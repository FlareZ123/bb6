"""Candidate raw59 A1 child audits; reuse source enumerator and FAR masks."""
from pathlib import Path
from collections import Counter
from itertools import product
import hashlib,json,subprocess,sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'agent31-three-hole-tnf'))
from generate_four_hole import masks,slot,move,parse
MOVES=[w+d+q for w,d,q in product('01','LR','ABCDEF')]
SPECS={
'0RD':(157,12,8,85,632,11674,2778,'6145fc9050a5aeb9147edd345911ad9c81a8c3a0ec317bb01965fe2cf6bcbb75','000 00101 1012121 00102343444 1012101'),
'1LC':(84,None,None,178,1066,18816,5525,'b4de3ebe4f0b496574e81eadb4976e8a4f1bd6050c90b1c0d178034fded46a85','101213333 10101 001230120 000 0010201 001213333 00101 00123242344 001232201 0012101 0010202 0012111 00123224101 0012322452221 10123222401 00123224022'),
'1RB':(135,None,None,649,1398,25275,6231,'ac64fc94f0a887129e58a6d4e926f490d3d2428031f7853d63e902ae2c9583ab','000 00101 0010202 001020303 00102340101 001213121 00123014301 001232202 00123224101 00123224122 00123224221 0012341415555 0012344514401 0050104333132 005052224132422 1012101 10123212424 10123224322 10123440144 1012344555155 10214675441134344'),
'1RD':(93,None,None,682,547,9528,2372,'3e7403f557e1ba547bef92685c5e61e2a24480806109c1dcad6e55bc0e369dac','000 00101 0010202 001020303 0010212 001212333 001213333 001230123 00123224101 00414570253666612 0050104333132 005052224132422 10101 101121313 1012101 1012121 10121340121 10123222423 10123224101 10623557155452376'),
}
MANUAL={
'1RB':(157,'1RB1RB_1RC0RF_0RD0RB_1LD1RE_---1LA_0RC0LD','Raw59RBCount','BB6.Agent32Raw59RB'),
'1RD':(499,'1RB1RD_1RC---_0RD0LE_1LD1RE_1LF1LA_0LB1LC','Raw59RDSweep','BB6.Agent32Raw59RD'),
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
