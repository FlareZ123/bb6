import json,pathlib,collections,sys
from compress import compress,convert
from emit_bitpacked import emit
from emit_all import partial
from box16 import ROOT,DOM,trace
from emit_direct import cycle_witness

def generate():
    ng=json.load(open('ngram16.json'));f=json.load(open('finish16.json'));assert not f['fail'] and not f['pending']
    cs=[(t,compress(t,c)) for t,c in f['certs']]+[(t,compress(t,convert(t,c))) for t,c in ng['certs']]
    json.dump(cs,open('compressed16.json','w'));print('compressed',len(cs),sum(len(c['states']) for t,c in cs),max(len(c['states']) for t,c in cs),flush=True)
    dst=pathlib.Path('box16lean');dst.mkdir(exist_ok=True)
    deps={};known={};group=[];size=0;g=0
    def flush():
        nonlocal group,size,g
        if not group:return
        mod=f'Box16CertGroup{g:03}';g+=1
        chunks=['import BitPackedStack\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n']
        for i,t,c in group:
            known[tuple(t)]=(i,mod)
            src=emit(i,t,c).replace('Box17.Cert','Box16.Cert')
            src=src[src.index('namespace '):]
            if len(c['states'])<200:
                a=src.index('theorem valid0');b=src.index('theorem nonhalt');src=src[:a]+'theorem checked : check p c = true := by decide\n'+src[b:]
            chunks.append(src)
        (dst/(mod+'.lean')).write_text(''.join(chunks));deps[mod]=['BitPackedStack'];group=[];size=0
    for i,(t,c) in enumerate(cs):
        n=len(c['states'])
        if size+n>1000 or len(group)>=32:flush()
        group.append((i,t,c));size+=n
    flush();print('cert groups',g,flush=True)
    late={tuple(t):(r[2],r[1]) for t,r in f['leaves']};pre='set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace BB6.Agent13.Box16\nopen BB6Coverage BB6.Agent13BlankDelay BB6Coverage.Agent10ZipAudit\nopen BB6.Agent13.Box17 (slot decode tableEq_sound)\n';post='\nend BB6.Agent13.Box16\n';counts=collections.Counter()
    def write(mod,imports,src):
        deps[mod]=sorted(set(imports));(dst/(mod+'.lean')).write_text(''.join(f'import {m}\n' for m in deps[mod])+pre+''.join(src)+post)
    def split(t,s,name,src,children):
        p='p'+name;ok='ok'+name
        for v,nm in children:src.append(f'theorem eq{nm} : refine {p} (slot {s}) (decode {v}) = p{nm} := tableEq_sound _ _ (by decide)\n')
        src.append(f'theorem {ok} : Good {p} := by\n  apply good_split {p} {s}\n  intro v hv\n  change v ∈ {DOM[s]} at hv\n  simp only [List.mem_cons,List.not_mem_nil,or_false] at hv\n  rcases hv with '+'|'.join('rfl' for _ in children)+'\n')
        for _,nm in children:src.append(f'  · rw [eq{nm}]; exact ok{nm}\n')
    def build(t,name,src,imports,depth=0):
        r=trace(t,256);typ=r[0];p='p'+name;ok='ok'+name
        src.append(f'def {p} : PartialMachine := {partial(t)}\n')
        if typ=='hole' and not (t.count(-1)==1 and all(v!=0 for v in t)):
            counts['branch']+=1;s=r[2];children=[]
            for v in DOM[s]:
                nm=f'{name}_{v}';child=t[:s]+(v,)+t[s+1:];build(child,nm,src,imports,depth+1);children.append((v,nm))
            split(t,s,name,src,children)
        else:
            counts[typ]+=1
            if typ=='halt':src.append(f'theorem {ok} : Good {p} := good_halt {p} {r[1]} (by decide)\n')
            elif typ in ('side','cycle'):
                w=f'.cycle {r[1]} {r[2]} {str(r[3]).lower()} ({r[4]})' if typ=='side' else cycle_witness(t,*r[1:]);_,e,n,dr,bd=w.split();src.append(f'theorem {ok} : Good {p} := good_cycle {p} {e} {n} {dr} {bd} (by decide) (by decide)\n')
            elif typ=='open' and t in known:
                i,mod=known[t];imports.append(mod);src.append(f'theorem {ok} : Good {p} := by\n  rw [tableEq_sound {p} Cert{i}.p (by decide)]\n  exact good_never _ Cert{i}.nonhalt\n')
            else:
                if typ=='hole':sl,n=r[2],r[1]
                elif typ=='open':sl,n=late[t]
                else:raise ValueError((t,r))
                halted=t[:sl]+(0,)+t[sl+1:];src.append(f'def h{p} : PartialMachine := {partial(halted)}\n');src.append(f'theorem eh{p} : refine {p} (slot {sl}) none = h{p} := tableEq_sound _ _ (by decide)\n')
                if n==7373:src.append(f'theorem {ok} : Good {p} := by\n  apply good_last {p} (slot {sl}) {n} (by decide)\n  rw [eh{p}]\n  exact lateBound\n')
                else:src.append(f'theorem {ok} : Good {p} := by\n  apply good_last {p} (slot {sl}) {n} (by decide)\n  rw [eh{p}]\n  decide\n')
    def modular(t,name,mod,depth=0):
        r=trace(t,256);typ=r[0];src=[];imports=['Box16Lower']
        if typ=='hole' and not(t.count(-1)==1 and all(v!=0 for v in t)) and depth<3:
            counts['branch']+=1;s=r[2];children=[];src.append(f'def p{name} : PartialMachine := {partial(t)}\n')
            for v in DOM[s]:
                nm=f'{name}_{v}';child=t[:s]+(v,)+t[s+1:];rr=trace(child,256)
                if rr[0]=='hole' and child.count(-1)>1:
                    submod=f'{mod}_{v:02}';modular(child,nm,submod,depth+1);imports.append(submod)
                else:build(child,nm,src,imports)
                children.append((v,nm))
            split(t,s,name,src,children)
        else:build(t,name,src,imports)
        write(mod,imports,src)
    modular(ROOT,'Root','Box16Root')
    src=['''theorem weighted (m : Machine) (hm : BB6.Agent49Box.Fits domain m) : WeightedBound 7376 m :=
  okRoot m hm (root_compatible m hm)

theorem exactWeighted (B : Nat) :
    (∀ m, BB6.Agent49Box.Fits domain m → WeightedBound B m) ↔ 7376 ≤ B := by
  constructor
  · exact lowerBound B
  · intro hb m hm k d hk hd
    exact Nat.le_trans (weighted m hm k d hk hd) hb
#print axioms exactWeighted
'''];write('Box16Direct',['Box16Root'],src)
    (dst/'deps.json').write_text(json.dumps(deps));print(counts,'modules',len(deps),flush=True)
if __name__=='__main__':generate()
