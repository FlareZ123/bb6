"""Periodic run-of-runs stack abstraction; search only, checked by Lean."""
import rlelearn

def pushfun(a0,a1,cap,mod,depth,gcap,gmod):
    def push(x,b):
        bit,runs=x
        n=runs[0]
        groups=tuple(zip(runs[1::2],runs[2::2]))
        if bit==b:
            nn=0 if n==0 else n+1 if n<cap+mod-1 else cap
            return b,(nn,)+runs[1:]
        if n:
            token=0 if n==(a1 if bit else a0) else 1+2*n+bit
            if groups and groups[0][0]==token:
                k=groups[0][1]
                groups=((token,k+1 if k<gcap+gmod-1 else gcap),)+groups[1:]
            else:
                groups=((token,1),)+groups[:depth-1]
        return b,(1,)+tuple(x for g in groups for x in g)
    return push

def check(p,paramsL,paramsR,limit=150000):
    # Reuse the exact original finite closure engine, replacing only the
    # discovery abstraction. No proof relies on this substitution.
    old=rlelearn.pushfun
    try:
        rlelearn.pushfun=pushfun
        return rlelearn.check(p,paramsL,paramsR,limit)
    finally:
        rlelearn.pushfun=old
