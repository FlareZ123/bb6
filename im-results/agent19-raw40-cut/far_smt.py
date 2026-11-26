#!/usr/bin/env python3
"""Synthesize a FAR automaton by QF_BV constraints; check by independent saturation.
Requires libz3 (set Z3_LIBRARY on Windows or alternative installations).
Search failure is never a verdict. The original Lean FAR audit checks witnesses."""
import ctypes as C,os,sys,re,time

def solve_smt(query):
    z=C.CDLL(os.environ.get('Z3_LIBRARY','libz3.so.4'))
    z.Z3_mk_config.restype=C.c_void_p
    z.Z3_mk_context.argtypes=[C.c_void_p];z.Z3_mk_context.restype=C.c_void_p
    z.Z3_eval_smtlib2_string.argtypes=[C.c_void_p,C.c_char_p];z.Z3_eval_smtlib2_string.restype=C.c_char_p
    z.Z3_del_context.argtypes=[C.c_void_p];z.Z3_del_config.argtypes=[C.c_void_p]
    handler_type=C.CFUNCTYPE(None,C.c_void_p,C.c_int)
    handler=handler_type(lambda ctx,code:None)
    z.Z3_set_error_handler.argtypes=[C.c_void_p,handler_type]
    cfg=z.Z3_mk_config();ctx=z.Z3_mk_context(cfg);z.Z3_del_config(cfg);z.Z3_set_error_handler(ctx,handler)
    try:return z.Z3_eval_smtlib2_string(ctx,query.encode()).decode()
    finally:z.Z3_del_context(ctx)

def encode(p,n,rev,ms):
    N=6*n+1;H=N-1;w=max(1,(n-1).bit_length())
    out=['(set-logic QF_BV)',f'(set-option :timeout {ms})']
    def add(s):out.append('(assert '+s+')')
    def bv(x,width=N):return f'(_ bv{x} {width})'
    def name(a,l,q):return f'r{a}_{6*l+q}'
    def bit(x,k):return f'(= ((_ extract {k} {k}) {x}) #b1)'
    def subset(x,y):return f'(= (bvand {x} {y}) {x})'
    def sel(d,vals):
        v=vals[-1]
        for i in reversed(range(len(vals)-1)):v=f'(ite (= {d} {bv(i,w)}) {vals[i]} {v})'
        return v
    for l in range(n):
        for a in range(2):
            d=f'd{2*l+a}';out.append(f'(declare-const {d} (_ BitVec {w}))')
            if n<2**w:add(f'(bvult {d} {bv(n,w)})')
    add(f'(= d0 {bv(0,w)})')
    for i in range(1,2*n):
        for k in range(2,n):
            add(f'(=> (= d{i} {bv(k,w)}) (or '+ ' '.join(f'(= d{j} {bv(k-1,w)})' for j in range(i))+'))')
    for a in range(2):
        for k in range(N):out.append(f'(declare-const r{a}_{k} (_ BitVec {N}))')
        add(f'(= r{a}_{H} {bv(1<<H)})')
    out.append(f'(declare-const z (_ BitVec {N}))');add(bit('z',H));add(f'(not {bit("z",0)})')
    for k in range(N):add(f'(=> (not (= (bvand r0_{k} z) {bv(0)})) {bit("z",k)})')
    for q in range(6):
        for a in range(2):
            v=p[3*(2*q+a):3*(2*q+a)+3]
            if v=='---':
                for l in range(n):add(bit(name(a,l,q),H))
                continue
            write=int(v[0]);right=int(v[1]=='R');nxt=ord(v[2])-65
            if right!=rev:
                for l in range(n):
                    dst=sel(f'd{2*l+write}',[bv(1<<(6*j+nxt)) for j in range(n)])
                    add(subset(dst,name(a,l,q)))
            else:
                for j in range(n):
                    for b in range(2):
                        dst=f's{a}_{q}_{j}_{b}'
                        out.append(f'(define-fun {dst} () (_ BitVec {N}) {sel(f"d{2*j+b}",[name(a,l,q) for l in range(n)])})')
                        for k in range(N):add(f'(=> {bit(name(b,j,nxt),k)} {subset(f"r{write}_{k}",dst)})')
    out+=['(check-sat)','(get-value ('+' '.join(f'd{i}' for i in range(2*n))+'))']
    return '\n'.join(out)

def verify(p,D,rev):
    n=len(D)//2;N=6*n+1;H=N-1;T=[0]*(2*N);T[H]=T[N+H]=1<<H;rules=[]
    for l in range(n):
      for q in range(6):
       for a in range(2):
        v=p[3*(2*q+a):3*(2*q+a)+3];dst=a*N+6*l+q
        if v=='---':T[dst]=1<<H;continue
        w=int(v[0]);r=int(v[1]=='R');k=ord(v[2])-65
        if r!=rev:T[dst]=1<<(6*D[2*l+w]+k)
        else:
         for j in range(n):
          for b in range(2):
           if D[2*j+b]==l:rules.append((dst,b*N+6*j+k,w*N))
    while True:
      z=1<<H
      while True:
       old=z
       for j in range(N):
        if T[j]&z:z|=1<<j
       if z&1:return False
       if z==old:break
      changed=False
      for dst,src,off in rules:
       v=T[dst];bits=T[src]
       while bits:
        k=(bits&-bits).bit_length()-1;v|=T[off+k];bits&=bits-1
       if v!=T[dst]:T[dst]=v;changed=True
      if not changed:return True

def find(p,n,ms=2000):
    assert 1<=n<=10 and len(p)==36
    for rev in range(2):
        ans=solve_smt(encode(p,n,rev,ms))
        if not ans.startswith('sat'):continue
        d={int(i):int(v[2:],2 if v.startswith('#b') else 16) for i,v in re.findall(r'\(d(\d+) (#[bx][0-9a-f]+)\)',ans)}
        if len(d)!=2*n:raise ValueError(ans)
        D=[d[i] for i in range(2*n)]
        assert verify(p,D,rev),(p,D,rev)
        return str(rev)+''.join(map(str,D))
    return None

if __name__=='__main__':
    n=int(sys.argv[1]);ms=int(sys.argv[2]) if len(sys.argv)>2 else 2000
    for line in sys.stdin:
        i,p=line.split();p=p.replace('_','');t=time.monotonic();r=find(p,n,ms)
        if r:print(i,r,flush=True)
        print(i,r,round(time.monotonic()-t,2),file=sys.stderr,flush=True)
