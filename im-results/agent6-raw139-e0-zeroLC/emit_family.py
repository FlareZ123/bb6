import json,pathlib,sys,subprocess
from collections import Counter
from search import far,tree,scan,generate

ROOT = pathlib.Path(__file__).resolve().parent
BLOCKFAR_ROOT = ROOT.parent / "agent13-block-far"
MASK_ROOT = ROOT.parent / "agent32-raw59"
sys.path.insert(0, str(BLOCKFAR_ROOT))
sys.path.insert(0, str(MASK_ROOT))
from generate_multi import generate as generate_offset
from emit_blockmask import emit as emit_offset

BLOCK_RECIPES = ("block", "phase", "mirror", "mirrorphase", "offset")
_OFFSET_BACKEND_READY = False

def pack(xs,b):return sum(v<<(b*i) for i,v in enumerate(xs))
def vec(xs,b,stride=16):return f'⟨{b},{stride},#['+','.join(hex(pack(xs[i:i+stride],b)) for i in range(0,len(xs),stride))+']⟩'
def rows(xs,b):
 k=max(1,max(map(len,xs)));return f'⟨{vec([pack([v+1 for v in x],b) for x in xs],b*k,8)},{b},{k}⟩'
def bl(x):return str(bool(x)).lower()
def slot(s):return f'({s//2},{bl(s%2)})'
def code_name(v):return ('One' if v&2 else 'Zero')+('R' if v&1 else 'L')+chr(65+v//4)
HEADER='''import BlockFAR2
import BlockFARBridge
import FastThreeHoleAudit
import FARBi
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
'''
def block_source(NS,i,t,c,flip=False):
 ns='BB6BlockFAR2' if c['width']==2 else 'BB6BlockFAR';d,n=c['left_states'],c['right_nodes'];b=max(d,n).bit_length();pb=(2**c['width']*d).bit_length()
 moves=', '.join('none' if m is None else f'some ⟨{bl(m[0])},{bl(m[1])},{m[2]}⟩' for m in c['moves'])
 source=f'''namespace {NS}.H{i}
def machine : BB6BlockFAR.Table := fun q b => ([{moves}] : List (Option BB6BlockFAR.Move))[2*q.val+b.toNat]?.getD none
def cert : {ns}.Data {d-1} {n-1} := {{
  start := 0
  pushCodes := {vec(c['push'],b)}
  controlCodes := {vec(c['ctrl'],b)}
  auxiliaryCodes := {vec(c['aux'],b)}
  predecessorCodes := {rows(c['pred'],pb)}
  edgeCodes := {rows(c['edges'],b)}
  zeroCodes := {sum(1<<x for x in c['zero_states'])}
  zeroNextCodes := {vec(c['zeroNext'],b)}
}}
'''
 if d>=10:
  source+='\n'.join(f'theorem row_{l} : cert.rowsAt machine ({l} : Fin {d}) = true := by decide +kernel' for l in range(d))
  source+=f'\ntheorem rows_valid : cert.rowsCheck machine = true := by\n  unfold {ns}.Data.rowsCheck\n  rw [show List.finRange {d} = ({list(range(d))} : List (Fin {d})) by decide]\n  simp ['+', '.join(f'row_{l}' for l in range(d))+']\n'
  source+='theorem valid : cert.Valid machine := ⟨by decide +kernel,by decide +kernel,rows_valid⟩\n'
 else:source+='theorem valid : cert.Valid machine := ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩\n'
 source+=f'''theorem forever : ∀ k, ∃ c, BB6BlockFAR.run machine k BB6BlockFAR.primBlank = some c :=
  cert.sound machine valid
def ctr : BB6Coverage.PartialMachine := BB6Coverage.FAR.fromCodes {t}
'''
 if flip:
  source+=f'''theorem same : BB6Coverage.FAR.reflectPartial ctr = BB6BlockFAR.partialTable machine :=
  BB6.Agent31ThreeHole.tableOK_sound _ _ (by decide)
theorem never (m : BB6Coverage.Machine) (hm : BB6Coverage.compatible ctr m) : BB6Coverage.NeverHalts m :=
  BB6Coverage.FAR.reflectNever m
    (BB6BlockFAR.transfer_never machine (BB6Coverage.reflectTable m)
      (by
        have h := BB6Coverage.FAR.reflectCompatible ctr m hm
        simpa only [← same] using h) forever)
'''
 else:
  source+=f'''theorem same : ctr = BB6BlockFAR.partialTable machine :=
  BB6.Agent31ThreeHole.tableOK_sound _ _ (by decide)
theorem never (m : BB6Coverage.Machine) (hm : BB6Coverage.compatible ctr m) : BB6Coverage.NeverHalts m :=
  BB6BlockFAR.transfer_never machine m (by simpa only [← same] using hm) forever
'''
 source+=f'#print axioms never\\nend {NS}.H{i}\\n'
 return source

def table_text(t):
 return '_'.join(
  '---' if v == 24 else
  f'{(v >> 1) & 1}{"R" if v & 1 else "L"}{chr(65 + v // 4)}'
  for v in t
 )

def ensure_offset_backend(width):
 global _OFFSET_BACKEND_READY
 if width == 4 and not _OFFSET_BACKEND_READY:
  subprocess.run([sys.executable, str(BLOCKFAR_ROOT / 'specialize.py'), '4'], check=True)
  _OFFSET_BACKEND_READY = True

def offset_block_source(NS,i,t,width,name):
 ns = 'BB6BlockFAR4' if width == 4 else 'BB6BlockFAR'
 return f'''namespace {NS}.H{i}
def ctr : BB6Coverage.PartialMachine := BB6Coverage.FAR.fromCodes {t}
theorem same : ctr = {ns}.partialTable {ns}.{name}.machine := by
  apply BB6.Agent31ThreeHole.tableOK_sound
  decide
theorem never (m : BB6Coverage.Machine) (hm : BB6Coverage.compatible ctr m) :
    BB6Coverage.NeverHalts m :=
  {ns}.transfer_never {ns}.{name}.machine m (by simpa only [← same] using hm) {ns}.{name}.never
#print axioms never
end {NS}.H{i}
'''

def emit(code,spec,out,blocks_only=False,tr=None):
 P=spec['parent'];NS=spec.get('namespace','BB6.Agent6E0ZeroLC.D0ZeroRC.C1'+code_name(code));prefix=spec.get('prefix','A6E0LCD0RCC1'+code_name(code))
 if tr is None:
  counts=Counter();opens=[];tr=tree(P,counts,opens,250,2);assert dict(counts)==spec['counts'] and opens==spec['open']
 else:
  counts=Counter(spec['counts']);opens=spec['open']
 rec={int(i):r for i,r in spec['recipes'].items()};assert set(rec)==set(range(len(opens)))
 idx={tuple(t):i for i,t in enumerate(opens)}
 blocks={i:r for i,r in rec.items() if r[0] in BLOCK_RECIPES};modules=[]
 for j in range(0,len(blocks),8):
  name=prefix+f'Block{j//8:02}';modules.append(name);body='';extra_imports=[]
  for i in sorted(blocks)[j:j+8]:
   r=blocks[i]
   if r[0]=='offset':
    width,cap,mod,runs,offset=map(int,r[1:])
    ensure_offset_backend(width)
    cert_name=prefix+f'OffsetH{i}'
    scratch=out.parent/(out.name+'-offset-generator')
    scratch.mkdir(parents=True,exist_ok=True)
    c=generate_offset(table_text(opens[i]),scratch,width=width,cap=cap,mod=mod,
      runs=runs,name=cert_name,minimize_left=True,offset=offset)
    emit_offset(out,cert_name,c,offset)
    bridge='BlockFARBridge4' if width==4 else 'BlockFARBridge'
    extra_imports += [f'import {cert_name}Proof',f'import {bridge}']
    body+=offset_block_source(NS,i,opens[i],width,cert_name)
   else:
    flip=r[0] in ('mirror','mirrorphase')
    phase=r[0] in ('phase','mirrorphase')
    c=generate(opens[i],*r[1:5],flip,60000,phase)
    assert c and (not r[5:] or [c['left_states'],c['right_nodes']]==r[5:])
    body+=block_source(NS,i,opens[i],c,flip)
  header=HEADER.replace('set_option maxRecDepth',
    ''.join(x+'\\n' for x in sorted(set(extra_imports)))+'set_option maxRecDepth')
  (out/(name+'.lean')).write_text(header+body)
 if blocks_only:return modules
 def node(t):
  k,*a=t
  if k=='cycle':e,s,r,x=a;return f'.cycle {e} {s} {bl(r)} ({x})'
  if k=='last':n,s=a;return f'.last {n} {slot(s)}'
  if k=='far':rev,d,dfa,t0,t1,z=a;return f'.far {bl(rev)} {d} ⟨0,{dfa},{t0},{t1},{z}⟩'
  if k=='split':n,s,children=a;return f'.split {n} {slot(s)} (byMove [\n'+',\n'.join(map(node,children))+'])'
  if k=='open':
   i=idx[tuple(a[0])];r=rec[i]
   if r[0] in BLOCK_RECIPES:return f'.proven {NS}.H{i}.ctr {NS}.H{i}.never'
   if r[0]=='cycle':return node(r)
   if r[0]=='late':
    assert a[0].count(24)==1 and scan(a[0],r[1])==('hole',r[1],r[2]);return node(('last',*r[1:]))
   if r[0]=='far':c=far(a[0],*r[1:]);assert c;return node(('far',*c))
  raise ValueError(t)
 B=max(counts['maxquery'],max((r[1] for r in rec.values() if r[0]=='late'),default=0))+6
 s='import FastThreeHoleAudit\n'+''.join(f'import {m}\n' for m in modules)+f'''set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace {NS}
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10FastAudit
def parent : PartialMachine := fromCodes {P}
def tree : Audit := {node(tr)}
theorem checked : fastCheck {B} parent tree = true := by decide +kernel
theorem root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt parent := by
  intro s
  unfold parent fromCodes
  cases h : ({P} : List Nat)[2 * s.1.val + s.2.toNat]? with
  | none => simp [h]
  | some n => by_cases hn : n < 24 <;> simp [h, hn]
noncomputable def certificate : WeightedTNFCertificate {B} parent 6 :=
  certifiedFast {B} parent tree root nohalt checked
theorem all_completions_weighted : ∀ m, compatible parent m → WeightedBound {B} m := certificate.sound
#print axioms checked
#print axioms all_completions_weighted
end {NS}
'''
 (out/(prefix+'Cover.lean')).write_text(s)
 print(code,code_name(code),B,len(modules),flush=True)
if __name__=='__main__':
 spec=json.load(open(sys.argv[1]));out=pathlib.Path(sys.argv[2]);out.mkdir(parents=True,exist_ok=True)
 for code,s in spec.items():emit(int(code),s,out)
