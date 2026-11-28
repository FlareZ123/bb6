"""Replace generated operation banks with bounded, packed kernel certificates."""
import sys,json
from pathlib import Path
from verify_nonhalt import enc, nextstep,U,S,X,J,P,check_families,clear,check_bulk,self_trace

def bits(w):return '['+','.join('true' if c=='1' else 'false' for c in enc(w))+']'
def packed(p,l,r):return f'⟨.{p},{int("1"+l[::-1],2)},{int("1"+r[::-1],2)}⟩'

def write_op(f,i,r):
    typ=r['type'];a,b=bits(r['src']),bits(r['dst']);k=r['steps'];cost=r['cost'];n=f'op{i}'
    if typ=='core':
        j,h,ad=r['k'],r['j'],r['add']
        d=f'.loc (.core {a} {b} {j} {h} {ad} {k} {cost})'
        src=f'guard {a} (u ++ flat s {j})';dst=f'guard (J ++ (flat P {ad} ++ {b})) (x ++ flat s {h})'
        L=enc(r['src'])+'1';R='00'+U+S*j+'1';L2=enc('J'+P*ad+r['dst'])+'1';R2='00'+X+S*h+'1'
    elif typ=='direct':
        j,h,pad=r['n'],r['n2'],r['pad']
        d=f'.loc (.direct {a} {b} {j} {h} {pad} {k} {cost})'
        src=f'guardBlank (flat P {j} ++ {a}) ([true] ++ List.replicate {pad} false)';dst=f'guardBlank (flat P {h} ++ {b}) [true]'
        L=enc(P*j+r['src'])+'1';R='001'+'0'*pad;L2=enc(P*h+r['dst'])+'1';R2='001'
    elif typ=='terminal':
        d=f'.epoch ⟨{a},{b},{k},{cost}⟩'
        src=f'guard {a} []';dst=f'guard (J++{b}) XC'
        L=enc(r['src'])+'1';R='001';L2=enc('J'+r['dst'])+'1';R2='00101101'
    else:raise ValueError(typ)
    initial=packed('B',L,R);final=packed('B',L2,R2)
    print(f'def {n} : Op := {d}',file=f)
    print(f'theorem {n}OK : opOK {n} = true := by\n  apply fastOpOK_sound\n  simp only [{n},fastOpOK,fastRuleOK,fastTerminalOK]\n  have hs : packC ({src}) = {initial} := by decide +kernel\n  have ht : packC ({dst}) = {final} := by decide +kernel',file=f)
    p='B';chunks=[];t=0
    for start in range(0,k,1500):
        c0=packed(p,L,R);u=0;steps=min(1500,k-start)
        for _ in range(steps):
            cc,p,L,R=nextstep(p,L,R);u+=cc
        c1=packed(p,L,R);t+=u;chunks.append((steps,c0,c1,u))
    assert p=='B' and L==L2 and R==R2 and t==cost,(i,p,L[:50],L2[:50],R[:50],R2[:50],t,cost)
    for j,(steps,c0,c1,u) in enumerate(chunks):
        print(f'  have hc{j} : pexecFast {steps} {c0} = some ({u},{c1}) := by decide +kernel',file=f)
        if j:print(f'  have hchain{j} := pexecFast_compose _ _ _ _ _ _ _ '+('hc0' if j==1 else f'hchain{j-1}')+f' hc{j}',file=f)
    he='hc0' if len(chunks)==1 else f'hchain{len(chunks)-1}'
    print(f'  have he : pexecFast {k} {initial} = some ({cost},{final}) := {he}\n  rw [hs,ht,he]\n  decide +kernel\n',file=f)

if __name__=='__main__':
    root=Path(sys.argv[1]);check_families();clear();check_bulk();D=self_trace(35)
    rs=list({json.dumps(x['rule'],sort_keys=True):x['rule'] for x in D['trace']+D['post']}.values())
    for i in range(0,len(rs),80):
        with open(root/f'OpBank{i//80}.lean','w') as f:
            print('import PackedCheck\nset_option linter.unusedSimpArgs false\nset_option maxRecDepth 100000\nset_option maxHeartbeats 20000000\nnamespace F197.Agent2Self\nopen Agent2Counter PackedCheck\n',file=f)
            for j,r in enumerate(rs[i:i+80],i):write_op(f,j,r)
            print('end F197.Agent2Self',file=f)
    print('generated',len(rs))
