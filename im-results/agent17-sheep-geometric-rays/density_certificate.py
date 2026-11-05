"""Exact modular inclusion-exclusion certificate for Sheep E indegree-zero density.

Every legal first-even E source ending at a multiple of six has h=0, so the
generic predecessor congruence classes below are complete up to a zero-density
family of exceptional (u=3) source outputs and source-size conditions.
"""
from fractions import Fraction
from math import gcd, lcm

CUTOFF=18
classes=[]
for b in range(1,CUTOFF+1):
    M=(1<<(b+1))+1
    g=gcd(M,12)
    if (2*b-1)%g: continue
    m=M//g
    r=((2*b-1)//g * pow(12//g,-1,m))%m
    classes.append((b,m,r))
print('classes',classes)
N=len(classes)
S=Fraction()
accepted=0
for mask in range(1,1<<N):
    members=[x for i,x in enumerate(classes) if (mask>>i)&1]
    if any((ri-rj)%gcd(mi,mj) for i,(bi,mi,ri) in enumerate(members) for bj,mj,rj in members[:i]):
        continue
    accepted+=1
    modulus=lcm(*(m for b,m,r in members))
    S += Fraction(1 if len(members)%2 else -1,modulus)
# The infinite union's parented density lies between S and S+tail.
# Each b>CUTOFF contributes at most gcd(M_b,12)/M_b <= 3*2^{-(b+1)}.
tail=Fraction(3,2**(CUTOFF+1))
L=1-S-tail
U=1-S
print('terms',accepted)
print('parent density finite',S,float(S))
print('zero density within multiples of6 lower',L,float(L),'upper',U,float(U),'width',float(tail))
print('lower density among all even integers at least', L/3)
print('lower density among all integers at least', L/6)
# Strict upper-bound witness: the b=19 progression has an element outside
# every b<=18 progression, hence adds positive asymptotic parent density.
t=1660250
assert t%1048577 == 611673
assert (12*t-37)%1048577 == 0
assert all(t%m != r for _,m,r in classes)
assert (12*t-37)//1048577 == 19
print('PASS strict upper interval: E(2^19*19)=6*1660250; all earlier congruences fail')
assert L>Fraction(317,840)
assert S == Fraction(336766596987601117645591,654227323046073897192215)
assert len(classes)==12 and accepted==287
print('PASS: exact rational inclusion-exclusion; positive zero-indegree density')
