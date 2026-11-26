"""Emit a sparse-map bitmask certificate for finite-width block-FAR.
Input: exact finite automaton returned by agent13-block-far/generate_multi.py.
The generator is untrusted: Lean checks every local closure and blank entry.
"""
from pathlib import Path
import json,sys,re

def tree(items):
    items=list(items)
    if not items:return '.empty'
    if len(items)==1 and items[0][0]==0:return f'(.leaf {items[0][1]})'
    return '(.branch '+tree((i//2,v) for i,v in items if i%2==0)+' '+tree((i//2,v) for i,v in items if i%2==1)+')'

def emit(root,name,data,offset=0):
    width=data['width'];assert width in (2,3,4)
    assert offset==0 or width==4
    k=2**width;suffix='' if width==3 else str(width)
    checker='MaskBlockFAR'+suffix
    if width!=4:
        template=(Path(__file__).resolve().parent/'MaskBlockFAR4.lean').read_text()
        template=template.replace('BlockFAR4','BlockFAR'+suffix)
        template=template.replace('⟨a,b,c,d⟩','⟨'+','.join('abcd'[:width])+'⟩')
        template=template.replace('cases a <;> cases b <;> cases c <;> cases d',' <;> '.join('cases '+c for c in 'abcd'[:width]))
        template=re.sub(r'\b96\b',str(6*k),template)
        template=re.sub(r'\b16\b',str(k),template)
        if width==2:template=template.replace(',run_add',',BB6BlockFAR.run_add')
        (root/(checker+'.lean')).write_text(template,encoding='utf8')
    D,C=data['left_states'],data['right_nodes'];dead=C-1
    ns='BB6BlockFAR'+suffix+'.'+name
    bo=lambda b:str(bool(b)).lower()
    lst=lambda xs:'['+','.join(map(str,xs))+']'
    def machine(moves):
        return 'def machine : Table := fun q b =>\n  (['+','.join('none' if mv is None else f'some ⟨{bo(mv[0])},{bo(mv[1])},{mv[2]}⟩' for mv in moves)+'] : List (Option Move))[2*q.val+b.toNat]?.getD none'
    s=[f'import {checker}','set_option maxRecDepth 100000','set_option maxHeartbeats 0','set_option Elab.async false',f'namespace {ns}','open BB6.Agent32MaskBiDFA (Map Cell)',machine(data['moves'])]
    maps={}
    maps['pushRows']=('Map (Map Nat)',tree((l,tree((a,str(data['push'][k*l+a]-1)) for a in range(k) if data['push'][k*l+a])) for l in range(D) if any(data['push'][k*l:k*l+k])))
    for nm,key in [('controlCodes','ctrl'),('auxiliaryCodes','aux'),('zeroNextCodes','zeroNext')]:maps[nm]=('Map Nat',tree((i,str(v)) for i,v in enumerate(data[key]) if v!=dead))
    maps['predecessorCodes']=('Map (List Nat)',tree((i,lst(v)) for i,v in enumerate(data['pred']) if v))
    def cell(v):return '⟨'+str(sum(1<<i for i in v))+','+lst(v)+'⟩'
    maps['edgeRows']=('Map (Map Cell)',tree((v,tree((a,cell(data['edges'][k*v+a])) for a in range(k) if data['edges'][k*v+a])) for v in range(C) if any(data['edges'][k*v:k*v+k])))
    for nm,(ty,val) in maps.items():s.append(f'def {nm} : {ty} := {val}')
    s.append(f'def zeroCodes : Nat := {sum(1<<i for i in data["zero_states"])}')
    s.append(f'def cert : MaskData {D-1} {C-1} := {{\n  start := 0\n'+''.join(f'  {nm} := {nm}\n' for nm in [*maps,'zeroCodes'])+'}')
    s.append(f'end {ns}')
    (root/(name+'MaskData.lean')).write_text('\n'.join(s)+'\n',encoding='utf8')
    s=[f'import {name}MaskData','import RangeCheck'+suffix,'set_option maxRecDepth 100000','set_option maxHeartbeats 0','set_option Elab.async false',f'namespace {ns}','theorem base_ok : cert.coreCheck = true := by decide +kernel']
    for kind,f in [('pred','cert.predCheckAt'),('rows','(cert.rowsAt machine)')]:
        chunk=10 if D<=200 else 5
        for i in range(0,D,chunk):s.append(f'theorem {kind}_{i} : rangeCheck {D-1} {f} {i} {min(chunk,D-i)} = true := by decide +kernel')
        expr=f'{kind}_0'
        for i in range(chunk,D,chunk):expr=f'(rangeCheck_join {D-1} {f} 0 {i} {min(chunk,D-i)} {expr} {kind}_{i})'
        s.append(f'theorem {kind}_full : rangeCheck {D-1} {f} 0 {D} = true := {expr}')
    s += ['theorem pred_ok : cert.predCheck = true := rangeCheck_full _ _ pred_full','theorem rows_ok : cert.rowsCheck machine = true := rangeCheck_full _ _ rows_full','theorem valid : cert.CoreValid machine := ⟨base_ok,pred_ok,rows_ok⟩']
    if not offset:
        s += ['theorem entry_ok : cert.entryCheck blockBlank = true := by decide +kernel','theorem never : ∀ k, ∃ c, run machine k primBlank = some c := cert.sound machine valid entry_ok']
    else:
        # Compute the exact finite initial exit; the resulting proof checks it.
        q,h,a,steps=0,offset,0,0
        seen=set()
        while 0<=h<4:
            key=(q,h,a);assert key not in seen;seen.add(key)
            mv=data['moves'][2*q+(a>>h&1)];assert mv is not None
            w,d,q=mv;a=(a&~(1<<h))|(w<<h);h+=1 if d else -1;steps+=1
        direction=bo(d);left=f'[Sym.ofCode {a}]' if d else '[]';right='[]' if d else f'[Sym.zero,Sym.ofCode {a}]'
        s += [f'def firstExit : Exit := ⟨{steps},{q},{direction},Sym.ofCode {a}⟩',f'def entry : BlockConfig := ⟨{q},{direction},{left},{right}⟩',f'theorem initial_exit : macroRun machine 385 0 .p{offset} Sym.zero = some firstExit := by decide +kernel',f'theorem initial_run : run machine {steps} primBlank = some entry.render := by',f'  have H := (macroRun_sound machine 385 0 .p{offset} Sym.zero [] [] firstExit initial_exit).2',f'  have hb : render 0 .p{offset} Sym.zero [] [] = primBlank := by simp [render,primBlank,Sym.zero,leftRay,rightRay,blank_cons]','  simpa [hb,entry,firstExit,BlockConfig.render,EntryPos] using H','theorem entry_ok : cert.entryCheck entry = true := by decide +kernel',f'theorem never : ∀ k, ∃ c, run machine k primBlank = some c := cert.soundFrom machine valid entry entry_ok {steps} initial_run']
    s += ['#print axioms never',f'end {ns}']
    (root/(name+'Proof.lean')).write_text('\n'.join(s)+'\n',encoding='utf8')

if __name__=='__main__':emit(Path('.'),sys.argv[1],json.loads(Path(sys.argv[2]).read_text()),int(sys.argv[3]) if len(sys.argv)>3 else 0)
