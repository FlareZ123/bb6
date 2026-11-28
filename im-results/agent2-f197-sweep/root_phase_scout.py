"""Explore earlier *exact suffix-parametric* crossover from the authentic
F197 blank root trace into a state on the accepted positive self-return.
This is a scouting diagnostic, not a Lean theorem. A hit must be transported
through the separately source-certified self-phase suffix theorem.
"""
import itertools
from collections import defaultdict, Counter
from verify_nonhalt import root_trace, self_trace

D = root_trace()
S = self_trace(35)
phases = []
for phase, rowlist in [('pre', S['trace']), ('post', S['post'])]:
    for j,x in enumerate(rowlist):
        if 'n' in x and 'w' in x:
            phases.append(dict(phase=phase,j=j,n=int(x['n']),w=x['w']))
    if rowlist:
        x=rowlist[-1]
        phases.append(dict(phase=phase,j=len(rowlist),n=int(x['n2']),w=x['w2']))
by_n=defaultdict(list)
for s in phases: by_n[s['n']].append(s)

def rope_prefix(rope, n):
    out=[]
    for w,k in rope:
        if n<=0: break
        k=int(k)
        if not w or k<=0: continue
        q=min(k,(n+len(w)-1)//len(w))
        piece=(w*q)[:n]
        out.append(piece)
        n-=len(piece)
    return ''.join(out)

r=[]
rope=[]
for i,x in enumerate(D['trace']):
    if 'rope' in x: assert x['rope']==rope
    w=x.get('w',x.get('before'))
    if w is not None:
        r.append(dict(i=i,n=int(x['n']),w=w,rope=rope))
    if 'rope2' in x: rope=x['rope2']
    if 'n2' in x and 'w2' in x:
        r.append(dict(i=i,n=int(x['n2']),w=x['w2'],rope=rope))
    elif 'after' in x:
        r.append(dict(i=i,n=int(x['n']),w=x['after'],rope=rope))
r.append(dict(i=len(D['trace']),n=int(D['end']['n']),w=D['end']['w'],rope=D['end']['rope']))

hit=[]
near=[]
for row in r:
    candidates=by_n.get(row['n'],[])
    if not candidates:continue
    w=row['w'];rp=row['rope'];mx=max(len(s['w']) for s in candidates)
    whole=w+rope_prefix(rp,max(0,mx-len(w))+1)
    for s in candidates:
        u=s['w'];c=0
        for x,y in zip(whole,u):
            if x!=y:break
            c+=1
        if c==len(u):
            hit.append(dict(root_i=row['i'],self_phase=s['phase'],self_j=s['j'],match=len(u),n=row['n'],suffix=whole[len(u):len(u)+30]))
        elif c>=8:
            near.append(dict(root_i=row['i'],self_phase=s['phase'],self_j=s['j'],matched=c,total=len(u),n=row['n']))
print('PHASE SCOUT self phases',len(phases),'unique n',len(by_n),'authentic candidate rows',len(r))
print('PHASE SCOUT phase hits',len(hit))
for x in hit[:40]: print('PHASE SCOUT HIT',x)
print('PHASE SCOUT earliest',min(hit,key=lambda a:a['root_i']) if hit else 'NONE')
print('PHASE SCOUT close partial matches',sorted(near,key=lambda a:(a['matched'],-a['root_i']),reverse=True)[:20])
