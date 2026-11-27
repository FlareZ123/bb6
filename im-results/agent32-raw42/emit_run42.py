#!/usr/bin/env python3
"""Regenerate independently checked BiDFA certificates from run42 parameters."""
from pathlib import Path
from run42 import discover
import sys

def b(x):return str(bool(x)).lower()
def emit(i,s,kind,p):
    d,n,e,states=discover(s,kind,p)
    print('import BiDFA\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace BB6.Agent32Raw42RA.Run\nopen BB6Coverage BB6Coverage.Agent16BiDFA')
    print(f'namespace Leaf{i}\n-- {s}\ndef table : PartialMachine := fun s => match s with')
    for j in range(12):
        v=s[3*j:3*j+3]
        if v!='---':print(f'  | ({j//2}, {b(j%2)}) => some (some ⟨{b(v[0]=="1")}, {b(v[1]=="R")}, {ord(v[2])-65}⟩)')
    print('  | _ => none')
    print('def cert : Cert := ⟨'+str(d[0])+','+str(d[1])+',')
    for es in e:print('  ['+','.join(f'⟨{dst},{b(a)},{src}⟩' for dst,a,src in es)+'],')
    print('  ['+','.join(f'⟨{q},{b(a)},{l},{r}⟩' for q,a,l,r in states)+']⟩')
    print('theorem checked : check table cert = true := by decide')
    print('theorem live (m : Machine) (hm : compatible table m) : NeverHalts m := never table cert checked m hm')
    print(f'#print axioms live\nend Leaf{i}\nend BB6.Agent32Raw42RA.Run')

if __name__=='__main__':
    i,s,kind,*p=sys.stdin.read().split();emit(int(i),s,kind,tuple(map(int,p)))
