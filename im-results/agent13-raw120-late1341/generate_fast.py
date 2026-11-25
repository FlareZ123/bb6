"""Generate exact checked action lists for the 1341 trace, after generate.py."""
from pathlib import Path
from collections import Counter
import sys
TABLE='1RB---_1RC0LF_0RD0RF_1LD1RE_1LB1LE_0RA0LE'
N=224705
s=TABLE.replace('_',''); rows=[s[i:i+3] for i in range(0,36,3)]
q=l=r=0; steps=[]; states=[]
for i in range(N):
    states.append((q,l,r)); ins=rows[2*q+l%2]; assert ins!='---',i
    steps.append(2*q+l%2); w,d,n=ins;q=ord(n)-65;w=int(w)
    if d=='R': l,r=r%2+2*(w+2*(l//2)),r//2
    else:l,r=l//2,w+2*r
states.append((q,l,r));assert q==0 and l%2==1 and l.bit_count()+r.bit_count()==521
motif=[2*(ord(x[0])-65)+int(x[1]) for x in 'A0 B1 F1 E0 B0 C1 F0 A0 B0 C1 F1 E0 B1 F1 E0 B0 C1 F0'.split()]

def actions():
    i=0
    while i<N:
        start=i
        while steps[i:i+18]==motif:i+=18
        if i>start:
            k=(i-start)//18; q,l,r=states[start];q1,l1,r1=states[i]
            L,R=l//8,r//4**(k+1); scale=4**k
            assert (q,l,r)==(0,8*L,4*(scale*(R+1)-1)+1)
            assert (q1,l1,r1)==(0,8*(scale*(L+1)-1),4*R+1)
            yield ('sweep18',k,i-start);continue
        while i<N and steps[i]==9:i+=1
        if i>start:
            k=i-start;q,l,r=states[start];q1,l1,r1=states[i];L=l//2**k
            assert (q,l)==(4,2**k*(L+1)-1)
            assert (q1,l1,r1)==(4,L,2**k*(r+1)-1)
            yield ('sweepE',k,k);continue
        i+=1
        while i<N and steps[i]!=9 and steps[i:i+18]!=motif:i+=1
        yield ('plain',i-start,i-start)

A=list(actions()); assert sum(x[2] for x in A)==N
print('actions',len(A),'counts',Counter(x[0] for x in A),'steps by kind',{k:sum(x[2] for x in A if x[0]==k) for k in ('plain','sweep18','sweepE')})

def write(out,name,imports,body):
    text=''.join(f'import {m}\n' for m in imports)
    text+='set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nset_option exponentiation.threshold 1024\nnamespace BB6.Agent13Raw120Late1341\nopen BB6Coverage BB6Coverage.Agent13PackedZipper BB6Coverage.Agent10ZipAudit\n'
    (out/(name+'.lean')).write_text(text+body+'\nend BB6.Agent13Raw120Late1341\n')

out=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_name('generated')
out.mkdir(parents=True,exist_ok=True)
CHUNK=40
base=[]; parts=[];time=0
for i in range(0,len(A),CHUNK):
    a=A[i:i+CHUNK]; j=i//CHUNK; start=time; end=start+sum(x[2] for x in a); time=end
    q,l,r=states[start];q1,l1,r1=states[end]
    if i==0:base.append('abbrev s0 : P := startP')
    base.append(f'def s{j+1} : P := ⟨{q1},{l1},{r1}⟩')
    name=f'Late1341FastPart{j:03}'
    acts=', '.join(f'.{kind} {k}' for kind,k,_ in a)
    body=f'private def script : List Action := [{acts}]\nprivate theorem ok : runActions script s{j} = some s{j+1} := by decide\ntheorem fastPart{j} : runP table {end-start} s{j} = some s{j+1} := runActions_sound ok'
    write(out,name,['Late1341FastBase'],body);parts.append((j,start,end,name))
assert time==N
write(out,'Late1341FastBase',['Late1341Action'],'\n'.join(base))
body=['private theorem fp0 : runP table 0 startP = some s0 := rfl']
for j,start,end,name in parts:
    body.append(f'private theorem fp{j+1} : runP table {end} startP = some s{j+1} := @joinP table {start} {end-start} startP s{j} s{j+1} fp{j} fastPart{j}')
body += [f'theorem fastTrace : runP table {N} startP = some s{len(parts)} := fp{len(parts)}',f'theorem fastQuery : zipRead table {N} = some (0,true) := by\n  rw [← readRunP_eq]\n  exact congrArg (fun x => x.map readP) fastTrace','#print axioms fastQuery']
write(out,'Late1341FastTrace',[p[3] for p in parts],'\n'.join(body));print('shards',len(parts))
# Preserve the semantic consumer's existing interface. The primitive generator remains a fallback.
write(out,'Late1341Trace',['Late1341FastTrace'],
      'theorem query : zipRead table 224705 = some (0,true) := fastQuery\n#print axioms query')
