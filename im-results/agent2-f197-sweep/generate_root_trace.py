"""Generate kernel-checkable blank-root trace, to be compiled after self trace."""
import json,sys,io,re,os
from pathlib import Path
import verify_nonhalt as v
from generate_packed_banks import write_op
root=Path(sys.argv[1]);root.mkdir(parents=True,exist_ok=True)

def seed_rows(target):
    v.clear();n,w=1,'TA';t=129;rows=[]
    while (n,w)!=(int(target['n']),target['w']):
        assert t<target['cost']
        try:
            a,b,r=v.local(n,w)
            cost=r['cost'] if r['type']=='direct' else 36*n+r['cost']+32*(n-r['k']-1+r['j'])+27
        except (RuntimeError,ValueError,AssertionError):
            L=v.enc(v.P*n+w)+'1';lp=rp=32
            while True:
                p,l,rr='B',L+'0'*lp,'001'+'0'*rp;cost=steps=0
                try:
                    while True:
                        c,p,l,rr=v.nextstep(p,l,rr);cost+=c;steps+=1
                        if p=='B' and rr.rstrip('0')=='001':break
                        assert steps<100000
                    break
                except ValueError:
                    lp*=2;rp*=2;assert lp<100000
            a,b=v.strip(v.word(l.rstrip('0')))
            r=dict(type='blank',lp=lp,rp=rp,lp2=len(l)-len(l.rstrip('0')),rp2=len(rr)-3,steps=steps,cost=cost)
        rows.append(dict(n=str(n),w=w,n2=str(a),w2=b,rule=r));n,w=a,b;t+=cost
    assert t==target['cost'];print('seed rows',len(rows),'cost',t,flush=True);return rows

def word_expr(w):
    pieces=[];start=0;i=0
    while i<len(w):
        found=False
        for u,name in [(v.LB,'LB'),('TA','enc "TA"'),(v.P,'P')]:
            if w.startswith(u*4,i):
                j=i
                while w.startswith(u,j):j+=len(u)
                if i>start:pieces.append('enc "'+w[start:i]+'"')
                pieces.append('flat ('+name+') '+str((j-i)//len(u)));i=start=j;found=True;break
        if not found:i+=1
    if start<len(w):pieces.append('enc "'+w[start:]+'"')
    return ' ++ '.join(pieces) if pieces else '[]'

def rope_expr(r):return '['+', '.join('('+word_expr(w)+', '+str(n)+')' for w,n in r)+']'
def op_key(r):return json.dumps(r,sort_keys=True)
D=v.root_trace()
GENERIC_CUT = os.getenv('F197_ROOT_CUT_GENERIC') == '1'
GENERIC_INFO = None
if GENERIC_CUT:
    candidates=[(i,x) for i,x in enumerate(D['trace']) if x.get('op',{}).get('kind')=='generic']
    assert len(candidates)==1, len(candidates)
    ix,x=candidates[0]
    assert not x['op']['family']['pure'], 'only the LB-output generic marker is supported'
    q=int(x['op']['q'])
    assert q>=45, q
    assert x['w'].startswith(v.M+v.GEN[1]['src']), (x['n'],x['w'][:80])
    assert int(x['n'])==2*(2*q+2)+1, (x['n'],q)
    GENERIC_INFO={'index':ix,'q':q,'Y':x['w'][len(v.M+v.GEN[1]['src']):]}
    D['trace']=D['trace'][:ix]
    D['end']={'n':x['n'],'w':x['w'],'rope':x['rope']}
    print('GENERIC SHORTCUT prefix rows',ix,'original rows',len(v.root_trace()['trace']),'q',q,flush=True)
seeds=seed_rows(D['seed']);rows=[];r=[]
for x in D['trace']:
    if x.get('kind')=='refill':
        y=dict(n=x['n'],w=x['before'],n2=x['n'],w2=x['after'],rope=r,rope2=x['rope2'],rule={'type':'refill'})
    else:
        assert x.get('rope',r)==r
        y=dict(n=x['n'],w=x['w'],n2=x['n2'],w2=x['w2'],rope=r,rope2=x.get('rope2',r),rule=x['op'].get('rule',{'type':x['op']['kind'],**x['op']}))
    r=y['rope2'];rows.append(y)
for x in seeds:x.update(rope=[],rope2=[])
rows=seeds+rows
for a,b in zip(rows,rows[1:]):assert (a['n2'],a['w2'],a['rope2'])==(b['n'],b['w'],b['rope'])
assert rows[-1]['w2']==D['end']['w'] and rows[-1]['rope2']==D['end']['rope']
normal=('core','direct','terminal')
# SelfTheorem's 658 operation banks are already source-checked. Reuse *identical*
# guarded rule certificates rather than reconstructing their packed proofs.
self_trace = v.self_trace(35)
self_rules = {op_key(x['rule']):x['rule'] for x in self_trace['trace']+self_trace['post']}
self_ids = {k:i for i,k in enumerate(self_rules)}
all_ops = {op_key(x['rule']):x['rule'] for x in rows if x['rule']['type'] in normal}
ops = [r for k,r in all_ops.items() if k not in self_ids]
opid = {op_key(r):i for i,r in enumerate(ops)}
def op_name(r):
    k=op_key(r)
    return f'op{self_ids[k]}' if k in self_ids else f'rootOp{opid[k]}'
for k in all_ops:
    if k in self_ids: assert (root/f'OpBank{self_ids[k]//80}.lean').exists()
for i in range(0,len(ops),80):
    name=f'RootBank{i//80}';buf=io.StringIO()
    for j,r in enumerate(ops[i:i+80],i):write_op(buf,j,r)
    body=re.sub(r'\bop(\d+)(OK)?\b',r'rootOp\1\2',buf.getvalue())
    (root/(name+'.lean')).write_text('import PackedCheck\nset_option linter.unusedSimpArgs false\nset_option maxRecDepth 100000\nset_option maxHeartbeats 20000000\nnamespace F197.Agent2Self\nopen Agent2Counter PackedCheck\n'+body+'end F197.Agent2Self\n')
print('root operations total/new/reused',len(all_ops),len(ops),len(all_ops)-len(ops),flush=True)
segments=[];i=0
while i<len(rows):
    r=rows[i];j=i+1
    if r['rule']['type'] in normal:
        while j<len(rows) and j-i<20 and rows[j]['rule']['type'] in normal and rows[j]['rope']==r['rope']:j+=1
    segments.append(rows[i:j]);i=j
ropes={};states=[]
for seg in segments:
    a=seg[0];states.append((a['n'],a['w'],a['rope']))
a=segments[-1][-1];states.append((a['n2'],a['w2'],a['rope2']))
for _,_,r in states:
    k=json.dumps(r)
    if k not in ropes:ropes[k]=len(ropes)
with (root/'RootStates.lean').open('w') as f:
    print('import RootCore\nset_option maxRecDepth 100000\nnamespace F197.Agent2Self\nopen Agent2Counter',file=f)
    for k,j in ropes.items():print(f'def rootR{j} : Rope := {rope_expr(json.loads(k))}',file=f)
    for i,(n,w,r) in enumerate(states):
        print(f'def rootN{i} : Nat := {n}\ndef rootW{i} : Word := {word_expr(w)}\ndef rootC{i} : Config := rstate rootN{i} rootW{i} rootR{ropes[json.dumps(r)]}',file=f)
    print('end F197.Agent2Self',file=f)

def emit_seg(f,i,seg):
    a,b=seg[0],seg[-1];w,w2=a['w'],b['w2'];rn='rootR'+str(ropes[json.dumps(a['rope'])]);rn2='rootR'+str(ropes[json.dumps(b['rope2'])]);tag=f'rootSeg{i}'
    typ=a['rule']['type']
    print(f'theorem {tag} : Reach rootC{i} rootC{i+1} := by',file=f)
    if typ in normal:
        suffix=w
        for x in seg:
            s=x['rule']['src'];s=v.M+s if x['rule']['type']=='terminal' else s
            nfree=len(x['w'])-len(s)
            if len(suffix)>nfree:suffix=suffix[-nfree:] if nfree else ''
            assert x['w'].endswith(suffix) and x['w2'].endswith(suffix)
        ws=w[:-len(suffix)] if suffix else w;wt=w2[:-len(suffix)] if suffix else w2
        names=[op_name(x['rule']) for x in seg]
        print('  let os : List Op := ['+', '.join(names)+']',file=f)
        for name,value in [('src',ws),('dst',wt),('tail',suffix)]:print(f'  let {name} : Word := {word_expr(value)}',file=f)
        print('  have hok : os.all opOK = true := by\n    simp only [os,List.all_cons,List.all_nil,Bool.true_and,'+','.join(name+'OK' for name in dict.fromkeys(names))+']',file=f)
        print(f'  have happ : applyOps os rootN{i} src = some (rootN{i+1},dst) := by decide +kernel\n  have ht : okHead tail = true := by decide +kernel\n  have hr : ropeOK {rn} = true := by decide +kernel',file=f)
        print(f'  have h := ops_sound os rootN{i} rootN{i+1} src dst (pre tail (ropeTape {rn})) (pre_first tail _ ht (rope_head {rn} hr)) hok happ',file=f)
        print(f'  have hs : src++tail = rootW{i} := by decide +kernel\n  have hd : dst++tail = rootW{i+1} := by decide +kernel\n  simp only [state, ← Agent2EpochMarker.pre_append] at h\n  rw [hs,hd] at h\n  exact h',file=f)
    elif typ=='blank':
        r=a['rule'];ns,nt=a['n'],a['n2'];lp,rp,lq,rq,k,c=(r[x] for x in ('lp','rp','lp2','rp2','steps','cost'))
        print(f'  exact blank_reset {ns} {nt} rootW{i} rootW{i+1} {lp} {rp} {lq} {rq} {k} {c} (by decide +kernel)',file=f)
    elif typ=='refill':
        assert w2.startswith(w);s=w2[len(w):];k=len(v.enc(s));fuel=len(a['rope'])+1
        print(f'  have h := refill rootN{i} rootW{i} ({word_expr(s)}) {rn} {rn2} {fuel} {k} (by decide +kernel)\n  have hw : rootW{i} ++ ({word_expr(s)}) = rootW{i+1} := by decide +kernel\n  rw [hw] at h\n  exact h',file=f)
    elif typ in ('marker','generic'):
        rr=a['rule'];isM=typ=='marker';prefix=v.M+('TATJ' if isM else rr['family']['src']);assert w.startswith(prefix);y=w[len(prefix):];k=rr['cycles'] if isM else rr['q'];tn='root_marker01' if isM else 'root_generic11';n0=f'2*(2*{k}+3)' if isM else f'2*(2*{k}+2)+1';src='M++enc "TATJ"' if isM else 'M++GS';dst='OUT01' if isM else 'OUT';insert='enc "T"' if isM else 'GT'
        print(f'  let y : Word := {word_expr(y)}\n  have h := {tn} {k} y {rn} (by decide +kernel) (by decide +kernel)\n  have hn : {n0} = rootN{i} := by decide +kernel\n  have hw : {src}++y = rootW{i} := by decide +kernel\n  have hd : {dst} = rootW{i+1} := by decide +kernel\n  have hr : ((LB,{k})::({insert}++y,1)::{rn}) = {rn2} := by decide +kernel\n  rw [hn,hw,hd,hr] at h\n  exact h',file=f)
    else:raise ValueError(typ)
    print(file=f)

names=[];size=4
for i in range(0,len(segments),size):
    name=f'RootPart{i//size}';names.append(name);segs=segments[i:i+size]
    keys={op_key(x['rule']) for seg in segs for x in seg if x['rule']['type'] in normal}
    root_banks=sorted({opid[k]//80 for k in keys if k in opid})
    self_banks=sorted({self_ids[k]//80 for k in keys if k in self_ids})
    with (root/(name+'.lean')).open('w') as f:
        print('import RootStates',file=f)
        for b in root_banks:print(f'import RootBank{b}',file=f)
        for b in self_banks:print(f'import OpBank{b}',file=f)
        print('set_option maxRecDepth 100000\nset_option maxHeartbeats 20000000\nnamespace F197.Agent2Self\nopen Agent2Counter PrefixCheck',file=f)
        for j,seg in enumerate(segs,i):emit_seg(f,j,seg)
        print(f'theorem rootPart{i//size} : Reach rootC{i} rootC{i+len(segs)} := by\n  have h0 := rootSeg{i}',file=f)
        for j in range(1,len(segs)):print(f'  have h{j} := reach_trans h{j-1} rootSeg{i+j}',file=f)
        print(f'  exact h{len(segs)-1}\nend F197.Agent2Self',file=f)
if GENERIC_CUT:
    with (root/'RootTheorem.lean').open('w') as f:
        print('import GenericBasin\n'+'\n'.join('import '+n for n in names),file=f)
        print('set_option maxRecDepth 100000\nset_option maxHeartbeats 20000000\nnamespace F197.Agent2Self\nopen Agent2Counter',file=f)
        print(f'theorem blank_to_generic : Reach blankStart rootC{len(segments)} := by\n  have h0 : Reach blankStart rootC0 := seed_first',file=f)
        for j in range(len(names)):
            print(f'  have h{j+1} := reach_trans h{j} rootPart{j}',file=f)
        print(f'  exact h{len(names)}\n',file=f)
        q=GENERIC_INFO['q']
        y=GENERIC_INFO['Y']
        r='rootR'+str(ropes[json.dumps(states[-1][2])])
        i=len(segments)
        print(f'theorem blank_nonhalt : ∀ t, run t blankStart ≠ none := by\n  let y : Word := {word_expr(y)}\n  have hq : 45 ≤ {q} := by decide +kernel\n  have hy : okHead y = true := by decide +kernel\n  have hr : ropeOK {r} = true := by decide +kernel',file=f)
        print(f'  have hstate : rstate (2*(2*{q}+2)+1) (M++GS++y) {r} = rootC{i} := by decide +kernel',file=f)
        print(f'  have hnon := generic_odd_basin_live {q} y {r} hq hr hy\n  rw [hstate] at hnon\n  exact nohalt_of_reach blank_to_generic hnon\n#print axioms blank_nonhalt\nend F197.Agent2Self',file=f)
else:
    with (root/'RootTheorem.lean').open('w') as f:
        print('import SelfTheorem\n'+'\n'.join('import '+n for n in names),file=f)
        print('set_option maxRecDepth 100000\nset_option maxHeartbeats 20000000\nnamespace F197.Agent2Self\nopen Agent2Counter\nopen Agent2EpochMarker (pre_append)',file=f)
        print(f'theorem blank_to_cylinder : ∃ l : Tape, l 0 = true ∧ Reach blankStart (state 72 START l) := by\n  have h0 : Reach blankStart rootC0 := seed_first',file=f)
        for j in range(len(names)):print(f'  have h{j+1} := reach_trans h{j} rootPart{j}',file=f)
        w=states[-1][1];assert w.startswith(v.HEAD+v.LB*35);suffix=w[len(v.HEAD+v.LB*35):];r='rootR'+str(ropes[json.dumps(states[-1][2])]);i=len(segments)
        print(f'  let tail : Word := {word_expr(suffix)}\n  let l := pre tail (ropeTape {r})\n  have hl : l 0 = true := pre_first tail _ (by decide +kernel) (rope_head {r} (by decide +kernel))\n  have hw : START++tail = rootW{i} := by decide +kernel\n  have h := h{len(names)}\n  have he : state 72 START l = rootC{i} := by\n    unfold l rootC{i} rstate state\n    rw [← pre_append,hw]\n    rfl\n  rw [← he] at h\n  exact ⟨l,hl,h⟩\n',file=f)
        print('theorem blank_nonhalt : ∀ t, run t blankStart ≠ none := by\n  obtain ⟨l,hl,k,hk⟩ := blank_to_cylinder\n  intro t ht\n  have hn := self_nonhalt l hl t\n  have hsum : run (k+t) blankStart ≠ none := by\n    rw [run_add,hk]\n    exact hn\n  rw [show k+t=t+k by omega,run_add,ht] at hsum\n  exact hsum rfl\n#print axioms blank_nonhalt\nend F197.Agent2Self',file=f)
print('root segments',len(segments),'modules',len(names),flush=True)
