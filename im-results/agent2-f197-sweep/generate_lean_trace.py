"""Generate finite kernel-checkable F197 self-embedding certificate modules.
Usage: python3 generate_lean_trace.py BUILD_DIRECTORY
No external dependencies besides verify_nonhalt.py in the same directory.
"""
import json,sys
from pathlib import Path
from verify_nonhalt import (check_families,clear,check_bulk,self_trace,enc as encode_bits,LB,E,W,R,BULK)
root=str(Path(sys.argv[1]).resolve());Path(root).mkdir(parents=True,exist_ok=True)
check_families();clear();bulk=check_bulk();D=self_trace(35)

def lean_rule(r):
    src=f'(enc "{r["src"]}")';dst=f'(enc "{r["dst"]}")'
    if r['type']=='core':return '.core '+src+' '+dst+' '+' '.join(str(r[k]) for k in ['k','j','add','steps','cost'])
    return '.direct '+src+' '+dst+' '+' '.join(str(r[k]) for k in ['n','n2','pad','steps','cost'])

with open(f'{root}/OrdinaryData.lean','w') as f:
    print('import OrdinaryCore\nset_option maxRecDepth 100000\nset_option maxHeartbeats 10000000\nnamespace F197.Agent2Self\nopen Agent2Counter\n',file=f)
    for p,(ent,cyc) in enumerate(bulk):
        _,u,d,n=BULK[p]
        for phase,rs,z0,z,base,n2 in [('ent',ent,E[p]+R*u,W[p],n,n+d),('cyc',cyc,W[p]+R*4,W[p],4,22)]:
            name=f'{phase}{p}'
            print('def '+name+' : List Rule := [\n  '+',\n  '.join(lean_rule(r) for r in rs)+'\n]',file=f)
            print(f'theorem {name}_ok : {name}.all ruleOK = true := by decide',file=f)
            print(f'theorem {name}_core : {name}.all coreOnly = true := by decide',file=f)
            print(f'theorem {name}_apply : applyRules {name} {base} (enc "{z0}") = some ({n2},enc "{z}") := by decide\n',file=f)
    print('end F197.Agent2Self',file=f)

def word_expr(w):
    n=0
    while w.endswith(LB):n+=1;w=w[:-len(LB)]
    pref="["+",".join("true" if c=="1" else "false" for c in encode_bits(w))+"]"
    return pref+(" ++ flat LB "+str(n) if n else "")
chunk=20;module_chunks=4

def lean_op(r):
    if r['type']=='terminal':return '.epoch ⟨(enc "'+r['src']+'"), (enc "'+r['dst']+'"), '+str(r['steps'])+', '+str(r['cost'])+'⟩'
    return '.loc ('+lean_rule(r)+')'

# Check every distinct finite macro certificate once, then use opaque proofs.
ops={}
for rr in D['trace']+D['post']:
    k=json.dumps(rr['rule'],sort_keys=True)
    if k not in ops:ops[k]=len(ops)
keys=list(ops);banks=[]
for i in range(0,len(keys),80):
    name='OpBank'+str(i//80);banks.append(name)
    with open(f'{root}/{name}.lean','w') as f:
        print('import TraceLogic\nset_option maxRecDepth 100000\nset_option maxHeartbeats 20000000\nnamespace F197.Agent2Self',file=f)
        for j,k in enumerate(keys[i:i+80],i):
            print(f'def op{j} : Op := '+lean_op(json.loads(k)),file=f)
            print(f'theorem op{j}OK : opOK op{j} = true := by decide',file=f)
        print('end F197.Agent2Self',file=f)
states=open(root+'/TraceStates.lean','w');print('import TraceLogic\nnamespace F197.Agent2Self',file=states)
def generate(kind,rows):
    allchunks=[rows[i:i+chunk] for i in range(0,len(rows),chunk)];modules=[]
    for i in range(0,len(allchunks),module_chunks):
        name=kind+str(i//module_chunks);prev='TraceStates';modules.append(name)
        with open(f'{root}/{name}.lean','w') as f:
            used=sorted({ops[json.dumps(r['rule'],sort_keys=True)]//80 for seg in allchunks[i:i+module_chunks] for r in seg})
            print('\n'.join('import '+banks[j] for j in used),file=f)
            print(f'import {prev}\nset_option maxRecDepth 100000\nset_option maxHeartbeats 20000000\nnamespace F197.Agent2Self\nopen Agent2Counter\n',file=f)
            for j,rs in enumerate(allchunks[i:i+module_chunks],i):
                tag=kind+f'Seg{j}'
                n,w=rs[0]['n'],rs[0]['w'];n2,w2=rs[-1]['n2'],rs[-1]['w2']
                if j==0:print(f'def {kind}W0 := {word_expr(w)}\ndef {kind}N0 : Nat := {n}',file=states)
                print(f'def {kind}W{j+1} := {word_expr(w2)}\ndef {kind}N{j+1} : Nat := {n2}',file=states)
                suffix=w
                for rr in rs:
                    src=rr['rule']['src']
                    if rr['rule']['type']=='terminal':src='JTAATAAA'+src
                    nfree=len(rr['w'])-len(src)
                    if len(suffix)>nfree:suffix=suffix[-nfree:] if nfree else ''
                    assert rr['w'].endswith(suffix) and rr['w2'].endswith(suffix)
                ws=w[:-len(suffix)] if suffix else w
                w2s=w2[:-len(suffix)] if suffix else w2
                print(f'def {tag}Src := {word_expr(ws)}\ndef {tag}Dst := {word_expr(w2s)}\ndef {tag}Tail := {word_expr(suffix)}',file=states)
                ids=[ops[json.dumps(r['rule'],sort_keys=True)] for r in rs]
                print(f'def {tag}Ops : List Op := ['+', '.join('op'+str(j) for j in ids)+']',file=f)
                print(f'theorem {tag}OK : {tag}Ops.all opOK = true := by\n  simp only [{tag}Ops,List.all_cons,List.all_nil,Bool.true_and,'+','.join('op'+str(j)+'OK' for j in dict.fromkeys(ids))+']',file=f)
                print(f'theorem {tag}Apply : applyOps {tag}Ops {kind}N{j} {tag}Src = some ({kind}N{j+1},{tag}Dst) := by rfl',file=f)
                print(f'theorem {tag} (l : Tape) (hl : l 0 = true) : '+('ReachPos' if j==0 else 'Reach')+f' (state {kind}N{j} {kind}W{j} l) (state {kind}N{j+1} {kind}W{j+1} l) := by',file=f)
                print(f'  have hhead : okHead {tag}Tail = true := by decide\n  have hh := pre_first {tag}Tail l hhead hl',file=f)
                print(f'  have h := '+('ops_pos' if j==0 else 'ops_sound')+f' {tag}Ops {kind}N{j} {kind}N{j+1} {tag}Src {tag}Dst (pre {tag}Tail l) hh '+('(by decide) ' if j==0 else '')+f'{tag}OK {tag}Apply',file=f)
                print(f'  have hs : {tag}Src ++ {tag}Tail = {kind}W{j} := by rfl\n  have hd : {tag}Dst ++ {tag}Tail = {kind}W{j+1} := by rfl',file=f)
                print('  simp only [state, ← Agent2EpochMarker.pre_append] at h\n  rw [hs,hd] at h\n  exact h\n',file=f)
            print('end F197.Agent2Self',file=f)
    return modules,len(allchunks)

pre,pn=generate('SelfPre',D['trace']);post,qn=generate('SelfPost',D['post']);print('end F197.Agent2Self',file=states);states.close()
with open(root+'/SelfTheorem.lean','w') as f:
    print('\n'.join('import '+m for m in pre+post),file=f)
    print(f'set_option maxRecDepth 100000\nset_option maxHeartbeats 2000000\nnamespace F197.Agent2Self\nopen Agent2Counter\nopen Agent2EpochMarker (pre_append)\n',file=f)
    for kind,N in [('SelfPre',pn),('SelfPost',qn)]:
        print(f'theorem {kind}Trace (l : Tape) (hl : l 0 = true) : ReachPos (state {kind}N0 {kind}W0 l) (state {kind}N{N} {kind}W{N} l) := by',file=f)
        print(f'  have h0 := {kind}Seg0 l hl',file=f)
        for i in range(1,N):print(f'  have h{i} := reach_pos_trans h{i-1} ({kind}Seg{i} l hl)',file=f)
        print(f'  exact h{N-1}\n',file=f)
    y=D['pre_marker']['Y'];k=int(D['pre_marker']['cycles']);extra=D['post_extra'];rem=D['post_suffix'];n=int(D['pre_marker']['n'])
    print(f'def markerY := {word_expr(y)}\ndef markerCount : Nat := {k}\ndef extraCount : Nat := {extra}\ndef newSuffix := enc "{rem}"\n',file=f)
    print(f'def grow (l : Tape) : Tape := pre newSuffix (rep LB (markerCount-extraCount) (pre (enc "T") (pre markerY l)))',file=f)
    print('theorem grow_head (l : Tape) (_hl : l 0 = true) : grow l 0 = true := by rfl\n',file=f)
    print('theorem self_embedding (l : Tape) (hl : l 0 = true) : ReachPos (state 72 START l) (state 72 START (grow l)) := by',file=f)
    print('  have hp := SelfPreTrace l hl',file=f)
    print('  have hstart : SelfPreW0 = START := by decide\n  have hnstart : SelfPreN0 = 72 := by decide',file=f)
    print(f'  have hpre : SelfPreW{pn} = M++enc "TATJ"++markerY := by decide\n  have hnpre : SelfPreN{pn} = 2*(2*markerCount+2)+1 := by decide',file=f)
    print('  rw [hstart,hnstart,hpre,hnpre] at hp',file=f)
    print('  let tailY := pre markerY l\n  have hy : tailY 0 = true := by rfl\n  have hmark := marker11 markerCount tailY hy',file=f)
    print('  have heq : state (2*(2*markerCount+2)+1) (M++enc "TATJ") tailY = state (2*(2*markerCount+2)+1) (M++enc "TATJ"++markerY) l := by simp only [state,pre_append,tailY]\n  rw [heq] at hmark\n  have hmiddle := reach_pos_trans hp hmark',file=f)
    print('  let tailL := rep LB (markerCount-extraCount) (pre (enc "T") tailY)\n  have ht : tailL 0 = true := rep_first LB (by decide) _ _ (by rfl)\n  have hpost := SelfPostTrace tailL ht',file=f)
    print('  have hpostStart : SelfPostW0 = OUT++flat LB extraCount := by decide\n  have hpostN : SelfPostN0 = 0 := by decide',file=f)
    print(f'  have hpostEnd : SelfPostW{qn} = START++newSuffix := by decide\n  have hpostNend : SelfPostN{qn} = 72 := by decide',file=f)
    print('  rw [hpostStart,hpostN,hpostEnd,hpostNend] at hpost',file=f)
    print('  have hsplit : extraCount+(markerCount-extraCount) = markerCount := by decide',file=f)
    print('  have hjoin : state 0 (OUT++flat LB extraCount) tailL = state 0 OUT (rep LB markerCount (pre (enc "T") tailY)) := by\n    simp only [state,pre_append,flat_pre,tailL,← rep_add,hsplit]',file=f)
    print('  have hfinal : state 72 (START++newSuffix) tailL = state 72 START (grow l) := by\n    simp only [state,pre_append,grow,tailL,tailY]',file=f)
    print('  rw [hjoin,hfinal] at hpost\n  exact reach_pos_trans hmiddle (reach_of_pos hpost)\n',file=f)
    print('theorem self_nonhalt (l : Tape) (hl : l 0 = true) : ∀ t, run t (state 72 START l) ≠ none :=\n  cylinder_live 72 START grow grow_head self_embedding l hl\n\n#print axioms self_embedding\n#print axioms self_nonhalt\nend F197.Agent2Self',file=f)
print(pre,post,pn,qn)
