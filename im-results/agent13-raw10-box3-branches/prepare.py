"""Generate a source-audited C1 branch from the existing Box4 proof infrastructure."""
from pathlib import Path
import argparse,json,sys,subprocess,shutil
HERE=Path(__file__).resolve().parent
BASE=HERE.parent/'agent13-raw10-box4'
CORE_FRAGMENT="def literalDomain (i : Fin 12) : List (Fin 25) :=\n  match i.val with\n  | 0 => [8]\n  | 1 => [14]\n  | 2 => [11]\n  | 3 => [7]\n  | 4 => [17]\n  | 5 => [@C@]\n  | _ => List.finRange 25\n\ndef domain : Box Slot Transition := fun s => (literalDomain (index s)).map decode\n\ndef sourceDomain : Box Slot Transition := fun s =>\n  if index s = 5 then [decode @C@] else raw10Remainder[3]! s\n\ntheorem literalDomain_matches : ∀ i : Fin 12, literalDomain i =\n    if i = 5 then ([@C@] : List (Fin 25)) else BB6.Agent49BoxEncoded.boxes[3]! i := by decide\n\ntheorem index_source (s : Slot) : index s = BB6.Agent17Raw10BoxFar.slotIndex s := by\n  rcases s with ⟨q,b⟩\n  revert q b\n  decide\n\ntheorem decode_source (v : Fin 25) : decode v = BB6.Agent17Raw10BoxFar.decodeCode v := by\n  revert v\n  decide\n\ntheorem sourceDomainEq : domain = sourceDomain := by\n  funext s\n  have h := BB6.Agent17Raw10BoxFar.exact_box_at_index (3 : Fin 34) s\n  change raw10Remainder[3]! s =\n    (BB6.Agent49BoxEncoded.boxes[3]! (BB6.Agent17Raw10BoxFar.slotIndex s)).map BB6.Agent17Raw10BoxFar.decodeCode at h\n  unfold domain sourceDomain\n  rw [literalDomain_matches]\n  by_cases hi : index s = 5\n  · simp [hi]\n  · simp only [if_neg hi]\n    rw [h,index_source]\n    rw [show decode = BB6.Agent17Raw10BoxFar.decodeCode from funext decode_source]\n\ntheorem source_subset : ∀ s v, v ∈ sourceDomain s → v ∈ raw10Remainder[3]! s := by\n  intro s v hv\n  by_cases hi : index s = 5\n  · have hs : s = slot 5 := by rw [← slot_index s,hi]\n    subst s\n    have hm : decode @C@ ∈ raw10Remainder[3]! (slot 5) := by decide\n    simp [sourceDomain,index_slot] at hv\n    rw [hv]\n    exact hm\n  · simpa [sourceDomain,hi] using hv\n\n"
def generate(c):
    cfg=json.loads((HERE/'branches.json').read_text())[str(c)]
    name=f'Box3C{c}';bound=cfg['bound'];steps=cfg['steps'];delay=cfg['delay']
    for n in ('scan.cpp','classify.cpp','treegen.cpp','finish.py','greedy.py','emit_proof.py','Box4Core.lean','Box4Tree.lean'):
        s=(BASE/n).read_text()
        s=s.replace('8,14,11,7,17,4',f'8,14,11,7,17,{c}').replace('if(i!=6||v!=9)','').replace(' if i!=6 or v!=9','').replace('[ALL^(1<<9)]+[ALL]*5','[ALL]*6')
        if n.endswith('.lean') or n=='emit_proof.py':
            s=s.replace('Box4',name).replace('3640',str(bound))
            s=s.replace('raw10Remainder[4]!','sourceDomain')
        if n=='Box4Core.lean':
            a=s.index('def literalDomain')
            b=s.index('def sliceDomain',a)
            s=s[:a]+CORE_FRAGMENT.replace('@C@',str(c))+s[b:]
        if n=='greedy.py':
            s=s.replace('from lag_rle import run','from domain_lag_rle import run').replace('8000','20000')
        if n=='emit_proof.py':
            s=s.replace("'---' if v==0 else", "'---' if v<=0 else")
            s=s.replace('from greedy import HERE,cert,compress,safe_mask,mask_domain','from greedy import HERE,cert,compress,safe_mask,mask_domain,domain_mask,subset')
            a=s.index('    def parse(t):')
            b=s.index("        line=next(f)",a)
            s=s[:a]+'''    masks=[tuple(e['mask']) for e in json.load(open('greedyboxes.json'))['boxes']]
    def late_node(t):
        for i,b in enumerate(masks):
            if subset(domain_mask(t),b):return Node(t,'a',(i,))
        if t in block:return Node(t,'known',block[t])
        w=long[t]
        if w[0]=='halt':return Node(t,'h',(w[1],))
        if w[0] in ('cycle','side'):return Node(t,'c',tuple(w[1:]))
        if w[0]=='hole':
            s=w[1]
            return Node(t,'b',(s,),[(v,late_node(t[:s]+(v,)+t[s+1:])) for v in ds[s]])
        raise ValueError((t,w))
    def parse(t):
'''+s[b:]
            a=s.index("            if t in block:return Node")
            b=s.index("        return Node(t,k,a)",a)
            s=s[:a]+"            return late_node(t)\n"+s[b:]
        (HERE/n.replace('Box4',name)).write_text(s)
    lower=(BASE/'Box4Lower.lean').read_text().replace('Box4',name).replace('3640',str(bound)).replace('3639',str(steps)).replace('raw10Remainder[4]!','sourceDomain')
    t=cfg['witness']
    assert steps+1+delay==bound and t[5]==c
    def move(v):
        if v==0:return 'some none'
        return f'some (some ⟨{str((v-1)//2%2==1).lower()},{str((v-1)%2==1).lower()},{(v-1)//4}⟩)'
    a=lower.index('def late :');b=lower.index('def lateMachine',a)
    lower=lower[:a]+'def late : PartialMachine := fun s => match s with\n'+''.join(f'  | ({i//2},{str(i%2==1).lower()}) => {move(v)}\n' for i,v in enumerate(t))+'  | _ => none\n\n'+lower[b:]
    lower=lower.replace('lateDelayZero : 0 ∈',f'lateDelayZero : {delay} ∈').replace(f'{steps} 0 lateHalts',f'{steps} {delay} lateHalts')
    (HERE/f'{name}Lower.lean').write_text(lower)

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('c',type=int)
    p.add_argument('--prepare-only',action='store_true')
    p.add_argument('--target',type=int,choices=range(6,12))
    a=p.parse_args()
    generate(a.c)
    if not a.prepare_only:
        cmd=[sys.executable,str(HERE/'replay_branch.py'),str(a.c)]
        if a.target is not None:cmd+=['--target',str(a.target)]
        subprocess.run(cmd,check=True)
