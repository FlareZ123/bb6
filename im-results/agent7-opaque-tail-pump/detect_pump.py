#!/usr/bin/env python3
"""Source-faithful two-stack exact opaque-tail drift discovery for 6x2 partial TMs.

Diagnostic: a candidate is only accepted if *every* step of the abstract
continuation avoids reading the `?` marker and returns with the marker in
exactly the corresponding place. A later Lean proof must establish the
literal entry and macro law with the original semantics.
"""
from collections import deque, defaultdict
from dataclasses import dataclass
import sys, json

@dataclass(frozen=True)
class Snapshot:
    t:int
    q:int
    left:str
    right:str


def parse(table):
    s=table.replace('_','')
    assert len(s)==36
    return [s[i:i+3] for i in range(0,36,3)]

def next_step(q,left,right,moves,opaque=False):
    a=left[0] if left else '0'
    if a not in ('0','1'): return None
    mv=moves[2*q+int(a)]
    if mv=='---': return None
    write,direction,q2=mv
    assert write in '01' and direction in 'LR' and q2 in 'ABCDEF'
    if direction=='L':
        if left:left.popleft()
        right.appendleft(write)
    else:
        first=right.popleft() if right else '0'
        if first not in '01':return None
        if left:left.popleft()
        left.appendleft(write)
        left.appendleft(first)
    return ord(q2)-65

def symbolic(q,left,right,moves,steps,side='right'):
    L=deque(left+('?' if side=='left' else ''))
    R=deque(right+('?' if side=='right' else ''))
    for t in range(steps):
        q=next_step(q,L,R,moves,opaque=True)
        if q is None:return None
    return q,''.join(L),''.join(R)

def find_insertion(a,b):
    # Return P,W for b=P+W+T and a=P+T, preferring a short P.
    if len(b)<=len(a):return []
    wlen=len(b)-len(a)
    pre=0
    while pre<len(a) and a[pre]==b[pre]:pre+=1
    out=[]
    for k in range(pre+1):
        if b[k+wlen:]==a[k:]:out.append((a[:k],b[k:k+wlen]))
    return out

def search(table,max_steps=100000,max_macro_steps=5000,max_snapshots=60000,
           max_tape_len=2500,max_pre=64,max_insert=128,max_fixed=24,side='both'):
    moves=parse(table);q=0;L=deque();R=deque(); buckets=defaultdict(list)
    scans=0;possible=0
    for t in range(max_steps+1):
        if len(L)+len(R)>0:
            l=''.join(L) if len(L)<=max_tape_len else ''
            r=''.join(R) if len(R)<=max_tape_len else ''
            for target in ('right','left'):
                if side!='both' and side!=target:continue
                if target=='right':
                    if len(L)>max_fixed or len(R)<5 or len(R)>max_tape_len:continue
                    fixed=l; changing=r
                else:
                    if len(R)>max_fixed or len(L)<5 or len(L)>max_tape_len:continue
                    fixed=r; changing=l
                k=(target,q,fixed,changing[-8:] if len(changing)>=8 else changing)
                for s in reversed(buckets[k][-1024:]):
                    dt=t-s.t
                    if dt>max_macro_steps:break
                    old=s.right if target=='right' else s.left
                    for pre,block in find_insertion(old,changing):
                        if len(pre)>max_pre or len(block)>max_insert:continue
                        possible+=1
                        if target=='right':
                            probe=symbolic(q,fixed,pre,moves,dt,side=target)
                            goal=(q,fixed,pre+block+'?')
                        else:
                            probe=symbolic(q,pre,fixed,moves,dt,side=target)
                            goal=(q,pre+block+'?',fixed)
                        if probe and probe==goal:
                            return dict(table=table,entry=s.t,macro=dt,state=q,
                                side=target,fixed=fixed,pre=pre,block=block,
                                tail=old[len(pre):],second_time=t,
                                snapshots=scans,candidates=possible)
                buckets[k].append(Snapshot(t,q,l,r))
                scans+=1
                if scans>max_snapshots:break
        if scans>max_snapshots or t==max_steps:break
        q=next_step(q,L,R,moves)
        if q is None:break
    return dict(table=table,checked_steps=t,snapshots=scans,candidates=possible,found=False)

if __name__=='__main__':
    print(json.dumps(search(sys.argv[1],*(map(int,sys.argv[2:]))),indent=2))
