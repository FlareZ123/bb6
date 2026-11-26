import json,pathlib,collections
from box17 import ROOT,DOM,trace
from emit_all import partial

def cycle_witness(t,entry,period):
    L=R=q=h=0;hs=[]
    for n in range(entry+period+1):
        hs.append(h)
        if n==entry+period:break
        v=t[2*q+(R&1)]-1;assert v>=0;w=v//2%2
        if v%2:L=(L<<1)|w;R>>=1;h+=1
        else:R=(((R>>1)<<1)|w)<<1|(L&1);L>>=1;h-=1
        q=v//4
    right=hs[-1]>=hs[entry];boundary=(min if right else max)(hs[entry:]);return f'.cycle {entry} {period} {str(right).lower()} ({boundary})'

def main():
    certs=json.load(open('compressed.json'));known={tuple(t):i for i,(t,c) in enumerate(certs)};r1=(8,9,11,6,17,13,11,-1,2,23,3,23)
    late={(5,21,3,-1):(11,323),(9,-1,3,10):(7,7011),(9,-1,3,21):(7,3209),(4,-1,19,5):(7,538)}
    dst=pathlib.Path('directlean');dst.mkdir(exist_ok=True)
    pre='set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace BB6.Agent13.Box17\nopen BB6Coverage BB6.Agent13BlankDelay BB6Coverage.Agent10ZipAudit\n'
    post='\nend BB6.Agent13.Box17\n'
    counts=collections.Counter(); deps={}
    def write(mod,imports,src):
        deps[mod]=sorted(set(imports));(dst/(mod+'.lean')).write_text(''.join(f'import {m}\n' for m in deps[mod])+pre+''.join(src)+post)
    def split(t,s,name,src,children):
        p='p'+name;ok='ok'+name
        for v,nm in children:
            src.append(f'theorem eq{nm} : refine {p} (slot {s}) (decode {v}) = p{nm} := tableEq_sound _ _ (by decide)\n')
        src.append(f'theorem {ok} : Good {p} := by\n  apply good_split {p} {s}\n  intro v hv\n  change v ∈ {DOM[s]} at hv\n  simp only [List.mem_cons,List.not_mem_nil,or_false] at hv\n  rcases hv with '+ '|'.join('rfl' for v,nm in children)+'\n')
        for v,nm in children:src.append(f'  · rw [eq{nm}]; exact ok{nm}\n')
    def build(t,name,src,imports):
        r=trace(t,256);typ=r[0];p='p'+name;ok='ok'+name
        src.append(f'def {p} : PartialMachine := {partial(t)}\n')
        if typ=='hole' and not (t.count(-1)==1 and all(v!=0 for v in t)):
            counts['branch']+=1;s=r[2];children=[]
            for v in DOM[s]:
                nm=f'{name}_{v}';child=t[:s]+(v,)+t[s+1:];build(child,nm,src,imports);children.append((v,nm))
            split(t,s,name,src,children)
        else:
            counts[typ]+=1
            if typ=='halt':src.append(f'theorem {ok} : Good {p} := good_halt {p} {r[1]} (by decide)\n')
            elif typ in ('side','cycle'):
                w=f'.cycle {r[1]} {r[2]} {str(r[3]).lower()} ({r[4]})' if typ=='side' else cycle_witness(t,*r[1:]);_,e,n,dr,bd=w.split()
                src.append(f'theorem {ok} : Good {p} := good_cycle {p} {e} {n} {dr} {bd} (by decide) (by decide)\n')
            elif typ=='open' and (t in known or t==r1):
                if t==r1:src.append(f'theorem {ok} : Good {p} := by\n  rw [tableEq_sound {p} r1Table (by decide)]\n  exact good_r1\n')
                else:
                    i=known[t];mod=f'Box17Cert{i:03}';imports.append(mod);target=f'Cert{i}.p'
                    src.append(f'theorem {ok} : Good {p} := by\n  rw [tableEq_sound {p} {target} (by decide)]\n  exact good_never _ Cert{i}.nonhalt\n')
            else:
                if typ=='hole':sl,n=r[2],r[1]
                elif typ=='open':sl,n=late[tuple(t[i] for i in (1,7,10,11))]
                else:raise ValueError((t,r))
                halted=t[:sl]+(0,)+t[sl+1:]
                src.append(f'def h{p} : PartialMachine := {partial(halted)}\n')
                src.append(f'theorem eh{p} : refine {p} (slot {sl}) none = h{p} := tableEq_sound _ _ (by decide)\n')
                if n==7011:
                    src.append(f'theorem {ok} : Good {p} := by\n  apply good_last {p} (slot {sl}) {n} (by decide)\n  rw [eh{p}]\n  exact lateBound\n')
                else:
                    src.append(f'theorem {ok} : Good {p} := by\n  apply good_last {p} (slot {sl}) {n} (by decide)\n  rw [eh{p}]\n  decide\n')
    rootS=trace(ROOT,256)[2];children=[];modules=[]
    for v in DOM[rootS]:
        t=ROOT[:rootS]+(v,)+ROOT[rootS+1:];r=trace(t,256);name=f'B{v}';p='p'+name;mod=f'Box17D{v:02}';imports=['Box17DirectCore'];src=[]
        if r[0]=='hole' and not(t.count(-1)==1 and all(v!=0 for v in t)):
            counts['branch']+=1;s=r[2];kids=[]
            for u in DOM[s]:
                sub=t[:s]+(u,)+t[s+1:];nm=f'{name}_{u}';submod=f'{mod}_{u:02}';su=[];im=['Box17DirectCore'];build(sub,nm,su,im);write(submod,im,su);imports.append(submod);kids.append((u,nm))
            src=[f'def {p} : PartialMachine := {partial(t)}\n'];split(t,s,name,src,kids)
        else:build(t,name,src,imports)
        write(mod,imports,src);modules.append(mod);children.append((v,name))
    src=[f'def pRoot : PartialMachine := root\n'];split(ROOT,rootS,'Root',src,children)
    src.append('''theorem weighted_of_r1 (hr1 : NeverHalts r1Machine) (m : Machine) (hm : BB6.Agent49Box.Fits domain m) : WeightedBound 7014 m :=
  okRoot hr1 m hm (root_compatible m hm)

theorem exactWeighted_of_r1 (hr1 : NeverHalts r1Machine) (B : Nat) :
    (∀ m, BB6.Agent49Box.Fits domain m → WeightedBound B m) ↔ 7014 ≤ B := by
  constructor
  · exact lowerBound B
  · intro hb m hm k d hk hd
    exact Nat.le_trans (weighted_of_r1 hr1 m hm k d hk hd) hb
#print axioms exactWeighted_of_r1
''')
    write('Box17Direct',modules,src)
    (dst/'deps.json').write_text(json.dumps(deps));print(counts)
if __name__=='__main__':main()
