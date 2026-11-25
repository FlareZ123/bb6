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

# Source enumeration identity checked before witness IDs are used.
SHA={"0LA":"a5e3ebed97f785a6dd4bda19e287181f6006bb25ec1ea98c8be9a8faa34021f2","0LB":"e9bc14f016b31fbc0329f9e939284728b801bc28d726334fe50bcabc55520c3d","0LE":"c66f48a6dc225ebddb3c47047671d76ddc17e4f4dd667171b1b0e9bb58e85b64","0LF":"261c0a98de5344c67b6df23131d62889f2f7d09807ce96fda41c6f1d66fc7e41","1LB":"ff5fdd9701e08e27486507d0bd04ba75e35de720180cee463467d72ecacd9c95","1LE":"abbf73f7877a7cd3359542f6afbcc7b78c10e49b228c1098920910a3fb39b795","1LF":"8851e9944d2e0688f4979e868d44e63a7f20a6583c342db91025984ddda04d16"}
BANK="""000 100 00100 00101 10101 0010201 0010202 0010212 0012101 0012111 0012201 1010202 1012101 1012121 001020303 001020333 001023001 001023031 001023100 001023101 001023102 001023131 001023200 001023201 001023202 001023210 001023230 001023231 001210301 001210321 001212333 001213121 001213133 001213333 001230120 001230121 001230123 001232201 001232202 001232203 101121313 101213101 101213233 101213333 101230123 00102030401 00102030402 00102034332 00102310402 00102310434 00102320402 00102324131 00102324201 00102340101 00102340144 00102343444 00112341244 00112344444 00120342444 00121032421 00121232444 00121314144 00121314444 00121334133 00121334444 00121342144 00121343333 00121344144 00121344444 00123004010 00123012424 00123014101 00123014141 00123014301 00123014401 00123042323 00123104101 00123220422 00123220423 00123224022 00123224101 00123224122 00123224123 00123224221 00123224223 00123224320 00123240344 00123242344 00123242444 00123410121 00123440444 00123442044 10102323402 10121134344 10121334344 10121334444 10121340121 10121342144 10121343321 10121343323 10121343334 10121344144 10123012424 10123014301 10123212423 10123212424 10123222401 10123222414 10123222421 10123222423 10123224101 10123224123 10123224301 10123224322 10123224324 10123414144 10123440144 10123440344 0010231450201 0010232450201 0010234550255 0012301450125 0012301455555 0012322424522 0012322452201 0012322452202 0012322452220 0012322452221 0012324054424 0012341415555 0012341514454 0012341544444 0012344254401 0012344514401 0012344534444 0012345234444 0013501333324 0020351434242 0023405023431 0041115232323 0050104333132 1012322242511 1012322245521 1034242514343 1034245414445 001230145036503 001234425440623 003244416242354 005052224132422 101232242256223 101234565554551 104245333613533 104245333613534 00123014356272343 00123412544674744 00123445674740147 00123456147447477 00414570253666612 10623557155452306 10623557155452346 10623557155452376 10635175524757455 0012345670123458745 0012345672225285551 0012345675554448141 0012345678444812348 0041717263804731754 0041717263804771754 0072588250341462582 1073715688236333463 1082322222345681537 1082322222345681547 001234456778791772401 001234563744389887443 001234567844898534848 002784591863745997889 004525710591555527638 004525716597555527038 008794742743071946549 101234567585555915888 001234546772389878a4aa8 0012345674428449745a444 0048a253251526642374133 0012345674891a78babb17bb7 001858946663264a847614731 006c3287a7a28518888447889b6 006c348717a2851b878447889b1 10c494424429282a552191a6c3b 10c494474429282a552191a6c3b 10ad41c974f1g52g95ebdd67d58475ab59b 0025fgh591747948141f5766553c749f3e2ad 0016c8933bfbe1dii4f9fbe4i21f89ef8ii9394""".split()
SWEEPS="""0LB 54 331 1 R 0000000 111111 111111111111111111 -3
0LB 65 154 1 R 000001100000 1100000110 110 -10
0LB 66 158 1 R 000001100000 1100000110 110 -10
0LB 67 160 1 R 000001100000 1100000110 110 -10
0LB 68 162 1 R 000001100000 1100000110 110 -10
0LB 191 769 1 R 0001111011110111101111 011110110 0111101001111011 -2
0LB 225 206 4 L 0 10111101 101111011011111111 4
0LB 232 345 1 R 00 011011011 01101101101101100011 -6
0LB 258 2 2 L 0 00000 11 2
1LE 8 9 0 R 111 11111 1 -3
1LE 74 2 2 L 0 00000000 11 4
1LE 77 9 0 R 111 111111 1 -4
1LE 79 9 0 R 111 11111 1 -3
1LE 135 142 3 L 00000000 0001111001110111 - 4
1LE 229 1016 1 R 0000000000 000011111 0000000000000011111 -9
1LE 453 9 0 R 111 1111 1 -2
1LE 528 22 2 L 0 0000 00001 2
1LE 558 12 1 R 1 0101 0111 -1
1LE 559 12 1 R 1 0101 0111 -1
1LE 562 2 2 L 0 0000 11 2
1LE 642 1 1 L 0 111111111111 1 8
1LE 656 1 1 L 0 111111 1 4
1LE 857 1 1 L 0 0000 1 3
1LE 859 15 2 L 0100 0000 001 3""".splitlines()
MACROS="""0LB 693 001213333 6
1LB 225 10123224324 6
1LB 261 10123224324 6
1LB 264 10123224324 6
1LB 305 10123224324 6
1LB 306 10123224324 6
1LB 310 10123224324 6
1LB 333 10123224324 6
1LB 469 00123224022 8
1LE 1118 00100 8
1LE 1234 00123224101 6""".splitlines()
CHUNK=240
B=7014

def late_hole(table, limit):
    """Untrusted simulation; the generated .last witness is checked by zipCheck."""
    raw=table.replace('_','')
    moves=[None if raw[i:i+3]=='---' else
           (int(raw[i]), raw[i+1]=='R', ord(raw[i+2])-65)
           for i in range(0,36,3)]
    if moves.count(None)!=1: return None
    q=a=l=r=0
    for n in range(limit):
        m=moves[2*q+a]
        if m is None: return n,2*q+a
        w,right,q=m
        if right:
            l=(l<<1)|w; a=r&1; r>>=1
        else:
            r=(r<<1)|w; a=l&1; l>>=1
    return None

def generate(raw,upgrade=False):
    B=(4200000 if raw=='0LB' else 70000 if raw=='0LA' else 7014) if upgrade else 7014
    folder=ROOT/(('upgrade_' if upgrade else 'partial_')+raw);folder.mkdir(exist_ok=True)
    parent=f'1RB{raw}_1RC---_0RD---_1LD1RE_---1LA_------'
    subprocess.run(['g++','-std=c++17','-O3',str(ROOT.parent/'agent2-tnf-raw99/enumerate.cpp'),'-o',str(folder/'enumerate')],check=True)
    subprocess.run([str(folder/'enumerate'),parent],cwd=folder,check=True)
    data=(folder/'open.txt').read_bytes();assert hashlib.sha256(data).hexdigest()==SHA[raw]
    opens=data.decode().splitlines();assert len(opens)==len(set(opens))
    if upgrade:
        from generate_lb1_four import main as block_generate, cases_for
        block_generate(raw,opens)
    certs={};pumps={};late={};imports=['Raw59Base','PartialAudit']
    for rle in opens:
        for a in BANK:
            try: masks(parse(rle),int(a[0]),[int(x,36) for x in a[1:]])
            except AssertionError: continue
            certs[rle]=a;break
    if upgrade and raw=='1LB':
        rle=opens[583]
        assert rle=='1RB1LB_1RC0RE_0RD0LC_1LD1RE_1RF1LA_0RB---'
        ns='BB6.Agent32Raw59LB1Sweep583'
        pumps[rle]=(ns+'.table',ns+'.never')
        imports.append('Raw59LB1Sweep583')
        rle=opens[1734]
        assert rle=='1RB1LB_1RC1RF_0RD0LE_1LD1RE_---1LA_0RA0RB'
        ns='BB6.Agent32Raw59LB1Sweep1734'
        pumps[rle]=(ns+'.table',ns+'.never')
        imports.append('Raw59LB1Sweep1734')
        rle=opens[189]
        assert rle=="1RB1LB_1RC0LB_0RD0RF_1LD1RE_1LA1LA_---1RA"
        pumps[rle]=("BB6.Agent32Raw59LB1RunGram.M189.table","BB6.Agent32Raw59LB1RunGram.M189.never")
        if "Raw59LB1RunGram" not in imports: imports.append("Raw59LB1RunGram")
        rle=opens[190]
        assert rle=="1RB1LB_1RC0LB_0RD0RF_1LD1RE_1LC1LA_---1RA"
        pumps[rle]=("BB6.Agent32Raw59LB1Block190.table","BB6.Agent32Raw59LB1Block190.never")
        if "Raw59LB1Block190" not in imports: imports.append("Raw59LB1Block190")
        rle=opens[191]
        assert rle=="1RB1LB_1RC0LB_0RD0RF_1LD1RE_1LD1LA_---1RA"
        pumps[rle]=("BB6.Agent32Raw59LB1RunGram.M191.table","BB6.Agent32Raw59LB1RunGram.M191.never")
        if "Raw59LB1RunGram" not in imports: imports.append("Raw59LB1RunGram")
        rle=opens[194]
        assert rle=="1RB1LB_1RC0LB_0RD0RF_1LD1RE_1RD1LA_---1RA"
        pumps[rle]=("BB6.Agent32Raw59LB1Block194.table","BB6.Agent32Raw59LB1Block194.never")
        if "Raw59LB1Block194" not in imports: imports.append("Raw59LB1Block194")
    if upgrade and raw!='1LB':
        for i,(table,*_) in cases_for(raw,opens).items():
            assert opens[i]==table
            module=f'Raw59{raw}Block{i}'
            ns='BB6.Agent32'+module
            pumps[table]=(ns+'.table',ns+'.never')
            imports.append(module)
    module='Raw59PartialSweep'+raw;ns='BB6Coverage.Agent31Pump.'+module
    pieces=['import SweepPumping','set_option maxRecDepth 100000','set_option maxHeartbeats 0','namespace '+ns,'open BB6Coverage']
    sweep_rows=SWEEPS
    if upgrade:
        import upgrade_data
        sweep_rows=SWEEPS+upgrade_data.SWEEPS
    for row in sweep_rows:
        b,i,t,q,side,pre,block,suf,delta=row.split()
        if b!=raw: continue
        i,t,q,delta=map(int,[i,t,q,delta]);rle=opens[i]
        if rle in certs or rle in pumps: continue
        if pre=='-':pre=''
        if suf=='-':suf=''
        p=sweeps.parse(rle)
        w=sweeps.W(pre,block,suf);v=sweeps.W(pre+block,block,suf);e=sweeps.W()
        st=sweeps.C(q,0,0,e,w) if side=='R' else sweeps.C(q,0,0,w,e)
        target=sweeps.C(q,delta,0,e,v) if side=='R' else sweeps.C(q,delta,0,v,e)
        ans=sweeps.pump(p,st,target,maxsteps=1000)
        if ans is None:
            print('retaining unsuccessful sweep',i,rle,flush=True);continue
        code,info=sweeps.generate(i,p,(t,None,st,target,ans))
        pieces.append(code);print('pump',rle,info)
        pumps[rle]=(ns+'.M'+str(i)+'.table',ns+'.M'+str(i)+'.never')
    if len(pieces)>6:
        pieces.append('end '+ns)
        (folder/(module+'.lean')).write_text('\n\n'.join(pieces)+'\n')
        imports.append(module)
    # Independently emitted macro certificates; the Lean checker replays all rules.
    macro_dir=ROOT.parent/'agent32-macro-far'
    sys.path.insert(0,str(macro_dir))
    from emit_source import emit as macro_emit
    module='Raw59PartialMacro'+raw;ns='BB6Coverage.Agent32MacroFAR.'+module
    pieces=['import MacroFARBridge','set_option maxRecDepth 100000','set_option maxHeartbeats 0','namespace '+ns]
    for row in MACROS:
        b,i,a,k=row.split()
        if b!=raw:continue
        rle=opens[int(i)]
        if rle in certs or rle in pumps:continue
        pieces.append(macro_emit(i,rle,a,k))
        pumps[rle]=(ns+'.M'+i+'.table',ns+'.M'+i+'.never')
    if len(pieces)>4:
        pieces.append('end '+ns);(folder/(module+'.lean')).write_text('\n\n'.join(pieces)+'\n')
        imports.append(module)
    # Search bounded local-window certificates. Large certificates remain explicit
    # residuals to keep the source kernel build practical.
    ng=ROOT.parent/'agent1-ngram'
    module='Raw59PartialNGram'+raw;ns='BB6.Agent32Raw59PartialNGram'+raw
    inputs=folder/'ngram-input.txt';outputs=folder/'ngram-output.txt'
    inputs.write_text(''.join(f'{i} {rle}\n' for i,rle in enumerate(opens) if rle not in certs and rle not in pumps))
    subprocess.run(['g++','-std=c++17','-O3',str(ng/'ngram.cpp'),'-o',str(folder/'ngram')],check=True)
    with inputs.open() as inp, outputs.open('w') as out:
        subprocess.run([str(folder/'ngram'),'9'],stdin=inp,stdout=out,check=True)
    chosen=[]
    for line in outputs.read_text().splitlines():
        i,k,n=map(int,line.split()[:3])
        if n>5000:continue
        chosen.append(line)
        pumps[opens[i]]=(ns+'.p'+str(i),ns+'.never'+str(i))
    outputs.write_text('\n'.join(chosen)+'\n')
    if chosen:
        subprocess.run([sys.executable,str(ng/'emit_ngram.py'),str(inputs),str(outputs),str(folder/(module+'.lean')),'--namespace',ns],check=True)
        imports.append(module)
    if upgrade:upgrade_data.add_ngrams(raw,folder,opens,certs,pumps,imports)
    special=None
    if upgrade and raw=='0LB':
        from generate_late190 import TABLE, STEPS, BOUND, generate as generate_late
        assert opens[190]==TABLE and B==BOUND
        assert TABLE not in certs and TABLE not in pumps
        generate_late()
        imports.append('Raw590LB190Data')
        late[TABLE]=(STEPS,5)
        special=TABLE
    if upgrade:
        # Leave ample allowance for the weighted initial blank-delay cost.
        # The source checker still proves the exact weighted inequality.
        for rle in opens:
            if rle in certs or rle in pumps or rle in late: continue
            hit=late_hole(rle,(70000 if raw=='0LA' else 7014)-100)
            if hit is not None: late[rle]=hit
        print(raw,'late final-hole witnesses',len(late),flush=True)
    unresolved=set(opens)-set(certs)-set(pumps)-set(late)
    (folder/'residual.txt').write_text(''.join(f'{i} {rle}\n' for i,rle in enumerate(opens) if rle in unresolved))
    print(raw,'FAR',len(certs),'semantic',len(pumps),'retained',len(unresolved),flush=True)
    used=set()
    tree=json.loads((folder/'tree.json').read_text());assert tree[0]=='split';first,root_slot=tree[1:3]
    prefix=f'Raw59Upgrade{raw}' if upgrade else f'Raw59Partial{raw}'; ns=f'BB6.Agent32{prefix}'
    header=f'''set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace {ns}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
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

theorem split_checked (p : PartialMachine) (n : Nat) (s : Slot) (kids : Move → PartialAudit)
    (hq : zipQueryOK {B} p n s = true)
    (hk : ∀ mv, partialCheck {B} (refine p s (some mv)) (kids mv) = true) :
    partialCheck {B} p (.split n s kids) = true := by
  change (zipQueryOK {B} p n s && allMoves (fun mv => partialCheck {B} (refine p s (some mv)) (kids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨hq, allMoves_of _ hk⟩
'''
    emit(prefix+'Base',imports,base)
    stats=Counter()
    def size(t):
        stats[t[0]]+=1
        return 1+sum(map(size,t[3])) if t[0]=='split' else 1
    size(tree)
    assert stats['open']==len(opens),stats
    def count(t):return 1+sum(map(count,t[3])) if t[0]=='split' else 1
    def render(t):
        tag,*v=t
        if tag=='cycle':
            e,k,r,b=v;return f'.closed (.cycle {e} {k} {str(r).lower()} ({b}))'
        if tag=='last':
            n,s=v;return f'.closed (.last {n} {slot(s)})'
        if tag=='open':
            code=v[0];assert code not in used;used.add(code)
            if code in unresolved:return '.unresolved'
            if code in late:
                n,s=late[code];return f'.closed (.last {n} {slot(s)})'
            if code in pumps:return '.closed (.proven '+ ' '.join(pumps[code])+')'
            a=certs[code]
            d,D,L,R,z=masks(parse(code),int(a[0]),[int(x,36) for x in a[1:]])
            return f'.closed (.far {str(a[0]=="1").lower()} {d} ⟨0,{D},{L},{R},{z}⟩)'
        assert tag=='split';n,s,kids=v;assert len(kids)==24
        return f'.split {n} {slot(s)} (byPartialMove [\n'+',\n'.join(map(render,kids))+'])'
    def contains_special(t):
        return special is not None and (t[0]=='open' and t[1]==special or
            t[0]=='split' and any(map(contains_special,t[3])))
    def compose(pname,name,t):
        if t[0]=='open' and t[1]==special:
            # Do not unfold four million primitive steps in partialCheck.
            code=render(t)
            return f'''def t_{name} : PartialAudit := {code}
theorem c_{name} : partialCheck {B} {pname} t_{name} = true := by
  change zipCheck {B} {pname} (.last 4136170 (2,true)) = true
  have he : {pname} = BB6.Agent32Raw590LB190.table :=
    tableOK_sound _ _ (by decide)
  rw [he]
  exact BB6.Agent32Raw590LB190.last_ok
'''
        if count(t)<=CHUNK and not contains_special(t):
            return f'def t_{name} : PartialAudit := {render(t)}\ntheorem c_{name} : partialCheck {B} {pname} t_{name} = true := by decide\n'
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
def k_{name} : Move → PartialAudit := byPartialMove [{','.join('t_'+x for x in names)}]
def t_{name} : PartialAudit := .split {n} {slot(s)} k_{name}
theorem q_{name} : zipQueryOK {B} {pname} {n} {slot(s)} = true := by decide
theorem kcheck_{name} (mv : Move) : partialCheck {B} (refine {pname} {slot(s)} (some mv)) (k_{name} mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{cases}
theorem c_{name} : partialCheck {B} {pname} t_{name} = true :=
  split_checked {pname} {n} {slot(s)} k_{name} q_{name} kcheck_{name}
'''
    mods=[];names=[]
    for i,kid in enumerate(tree[3]):
        a=f'kid{i:02}';names.append(a);name=f'{prefix}Kid{i:02}';mods.append(name)
        emit(name,[prefix+'Base'],f'abbrev p_{a} := refine {p} {slot(root_slot)} (some {move(MOVES[i])})\n'+compose(f'p_{a}',a,kid))
    body=combine(p,'root',first,root_slot,names)
    body+=f'''
def residuals : List (List Move × PartialMachine) := partialResiduals {p} t_root
theorem residual_sound : ∀ m, compatible {p} m → WeightedBound {B} m ∨
    ∃ e ∈ residuals, compatible e.2 m :=
  partialSound {B} {p} t_root {p}_root {p}_nohalt c_root
#print axioms residual_sound
'''
    if not unresolved:
        body+=f'''
theorem residuals_empty : residuals = [] := by
  have h : residuals.isEmpty = true := by decide
  exact List.isEmpty_iff.mp h
theorem bound : ∀ m, compatible {p} m → WeightedBound {B} m := by
  intro m hm
  rcases residual_sound m hm with h | ⟨e,he,_⟩
  · exact h
  · simp [residuals_empty] at he
#print axioms bound
'''
    assert used==set(opens)
    emit(prefix+'Data',mods,body)
    print(raw,stats,'partial audit emitted; retained',len(unresolved))
if __name__=='__main__':
    upgrade='--upgrade' in sys.argv[1:]
    for raw in [x for x in sys.argv[1:] if x!='--upgrade'] or SHA:generate(raw,upgrade)
