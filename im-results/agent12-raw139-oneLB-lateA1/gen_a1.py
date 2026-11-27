#!/usr/bin/env python3
"""Independent packed trajectory producer; every output is checked by Lean."""
import sys
sys.set_int_max_str_digits(0)
def scan(u):
    ops=[]; cert=[]
    a=b=0
    while True:
        if u%4==0:
            w=5+8*(u//4); e=0; break
        if u%16==6:
            w=25+32*(u//16); e=4; break
        if u%16==14:
            return None,3+3*a+3*b,3+7*a+3*b,cert
        t=u%2==0
        x=7*u+2 if t else u+1
        k=((x^(x-1)).bit_length()-1)//(3 if t else 1)
        p=(8 if t else 2)**k
        g=(p-1)//(7 if t else 1)
        assert k>0 and u%p==(2 if t else 1)*g
        ops.append((p,g if t else 0));cert.append((t,k));u//=p
        if t:a+=k
        else:b+=k
    for p,d in reversed(ops):w=d+p*w
    return w,6+8*a+4*b+e,6+12*a+4*b+e,cert

def next(u):
    assert u%2==1
    w,a,b,c=scan(u//2)
    if w is None:return None,2+a,2+b,c
    return 1+4*w,6+a,6+b,c

def main():
    u,a,b=3,2,2
    states=[(u,a,b)]; certs=[]
    for i in range(7656):
        u,da,db,c=next(u); certs.append(c); assert u is not None
        a+=da;b+=db;states.append((u,a,b))
    w,da,db,c=next(u);certs.append(c);assert w is None
    assert (a+da,b+db)==(125150404,187672020)
    return states,certs
def lean_cert(c):
    return '['+','.join(f'({str(t).lower()},{k})' for t,k in c)+']'
def lean_certs(cs):
    return '['+','.join(map(lean_cert,cs))+']'
def emit(path,blocksize=256):
    states,certs=main()
    with open(path,'w') as f:
        f.write('import LateCert\nnamespace BB6.Agent12LateA1\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n')
        u,a,b=states[0]
        f.write(f'theorem reached0 (v : Bool) : run v (choose v {a} {b}) blankC = some (frontier {u}) := by cases v <;> exact seed _\n')
        for start in range(0,7656,blocksize):
            end=min(start+blocksize,7656)
            u,a,b=states[start];w,x,y=states[end]
            f.write(f'def u{end} : Nat := {w}\n')
            prev=str(u) if start==0 else f'u{start}'
            cs=lean_certs(certs[start:end])
            f.write(f'def cert{end} : List (List (Bool × Nat)) := {cs}\n')
            f.write(f'theorem checked{end} : advance cert{end} {prev} {a} {b} = some (u{end},{x},{y}) := by decide +kernel\n')
            f.write(f'''theorem reached{end} (v : Bool) : run v (choose v {x} {y}) blankC = some (frontier u{end}) := by
  have h := (advance_sound v cert{end} {prev} {a} {b} u{end} {x} {y} checked{end}).1
  rw [show choose v {x} {y} = choose v {a} {b} + (choose v {x} {y} - choose v {a} {b}) by cases v <;> decide +kernel]
  rw [run_add,reached{start},Option.bind_some,h]
''')
        u,a,b=states[-1]; _,da,db,c=next(u)
        f.write(f'''def lastCert : List (Bool × Nat) := {lean_cert(c)}
theorem last_checked : next lastCert u7656 = some (.hit {da} {db}) := by decide +kernel
theorem exact_query (v : Bool) : ∃ d, run v (choose v {a+da} {b+db}) blankC = some d ∧ d.q=0 ∧ d.r 0=true := by
  obtain ⟨d,hd,hq,hb⟩ := next_sound v lastCert u7656 (.hit {da} {db}) last_checked
  refine ⟨d,?_,hq,hb⟩
  rw [show choose v {a+da} {b+db} = choose v {a} {b} + choose v {da} {db} by cases v <;> decide +kernel]
  rw [run_add,reached7656,Option.bind_some,hd]
theorem weighted (v : Bool) (B : Nat) (hb : choose v {a+da} {b+db}+6≤B) :
    ∀ m, BB6Coverage.compatible (ctr v) m → BB6.Agent13BlankDelay.WeightedBound B m :=
  query_weighted v _ B hb (exact_query v)
#print axioms exact_query
#print axioms weighted
end BB6.Agent12LateA1
''')
    print(f'Generated {path}, {len(certs)} returns including terminal, {sum(map(len,certs))} runs')
if __name__=='__main__':
    emit(sys.argv[1] if len(sys.argv)>1 else 'LateA1Checked.lean')
