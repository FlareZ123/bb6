"""Direct all-completion first-hole audit. Discovery is untrusted; Lean checks
every split, last-row reduction, simulation witness and abstract certificate."""
from pathlib import Path
import json, os, shutil, sys
from replay_cylinder import HERE,BASE,BRANCH,call,HARD_D14V17,HARD_D14V18

SCAN_MAIN=r'''
uint64_t counts[5]={},mass[5]={};int maxhalt=0;
ofstream out("directtree.txt"),openout("open-1.txt");
uint64_t weight(const T&t){uint64_t m=1;for(int v:t)if(v<0)m*=25;return m;}
void visit(T t){
 int holes=0,last=-1;bool halt=false;
 for(int i=0;i<12;i++){if(t[i]<0){holes++;last=i;}if(t[i]==0)halt=true;}
 if(holes==1&&!halt){out<<"l "<<last<<'\n';counts[4]++;t[last]=0;visit(t);mass[4]+=24;return;}
 auto z=trace(t);
 switch(z.kind){
  case HOLE:
    out<<"b "<<z.s<<'\n';counts[3]++;
    for(int v=0;v<=24;v++){auto c=t;c[z.s]=v;visit(c);}break;
  case HALT:
    out<<"h "<<z.n<<'\n';counts[0]++;mass[0]+=weight(t);maxhalt=max(maxhalt,z.n);break;
  case CYCLE: case SIDE:
    out<<"c "<<z.n<<' '<<z.period<<' '<<z.right<<' '<<z.edge<<'\n';
    counts[1]++;mass[1]+=weight(t);break;
  case OPEN:
    out<<"o";for(int v:t){out<<' '<<v;openout<<v<<' ';}
    out<<'\n';openout<<'\n';counts[2]++;mass[2]+=weight(t);break;
 }
}
int main(int argc,char**argv){
 assert(argc==4);int d=atoi(argv[1]),slot=atoi(argv[2]),v=atoi(argv[3]);
 T root{8,-1,11,-1,1,13,d,-1,-1,-1,-1,-1};root[slot]=v;
 visit(root);uint64_t sum=0;
 for(int i=0;i<5;i++){sum+=mass[i];cerr<<i<<":"<<counts[i]<<"/"<<mass[i]<<" ";}
 cerr<<"total "<<sum<<" max live "<<maxhalt<<'\n';assert(sum==weight(root));
}
'''

def run_direct(args):
    d,v,B=args.d0,args.second,args.bound
    slot={2:3,3:3,4:3,12:1,14:7,16:7,17:8,18:8,19:8,20:8}[d]
    fixed=[8,-1,11,-1,1,13,d,-1,-1,-1,-1,-1];fixed[slot]=v;root=tuple(fixed)
    family=f'Box33D{d}V{v}';ns=f'BB6.Agent13.{family}'
    out=HERE/'generated'/family
    work=Path(args.work or f'/tmp/direct-{family}').resolve()
    work.mkdir(parents=True,exist_ok=True)
    os.chdir(work)
    for p in work.glob('long*.json'):p.unlink()
    sources={
        'scan':(BASE/'scan.cpp').read_text().split('int main(',1)[0]+SCAN_MAIN,
        'classify':(BASE/'classify.cpp').read_text().replace('if(i!=6||v!=9)','').replace('if(x.s==target)','if(t[x.s]<=0)'),
        'rle_scan':(BRANCH/'rle_scan.cpp').read_text().replace('s==target||t[s]==0','t[s]<=0').replace('if(lo==0)','if(t[x.s]<=0)'),
    }
    for name,src in sources.items():
        p=work/(name+'.cpp');p.write_text(src)
        call('g++','-O3','-std=c++17',p,'-o',work/name)
    call(work/'scan',d,slot,v);call(work/'classify',-1)
    sys.path[:0]=[str(BASE),str(BRANCH)]
    import finish,greedy
    from domain_lag_rle import run
    pending=[tuple(map(int,l.split())) for l in open('hard-1.txt') if l.strip()]
    late={};opens=[]
    def replace(t,i,a):return t[:i]+(a,)+t[i+1:]
    while pending:
        t=pending.pop()
        if t.count(-1)==1 and 0 not in t:
            i=t.index(-1);late[t]=('last',i);pending.append(replace(t,i,0));continue
        z=finish.trace_long(t,limit=16384,cycle_limit=2048)
        if z[0]=='hole':
            s=z[2];late[t]=('hole',s);pending.extend(replace(t,s,a) for a in range(25));continue
        if z[0]=='halt':assert z[1]+6<=B,(t,z)
        if z[0]=='open':opens.append(t)
        late[t]=z
    Path('rlestart-1.txt').write_text(''.join(' '.join(map(str,t))+'\n' for t in opens))
    call(work/'rle_scan',-1)
    known,source={(14,17):(HARD_D14V17,'Box33D14Source'),(14,18):(HARD_D14V18,'Box33D14V18Source')}.get((d,v),({},None))
    cycles={}
    known_specs={}
    if (d,v)==(17,22):
        hard=json.loads((HERE/'d17v22-hard.json').read_text())['machines']
        specs=[
            ([7],'Box33D17V22Counter','single'),
            ([1,2,3,4,5,6,8,10,16,19,20,23,24,32],'Box33D17V22CarryFamily','enum'),
            ([14],'Box33D17V22Unary','single'),
            ([0],'Box33D17V22M0','single'),
            ([9,17,18,21,22,25,26,27,28,31],'Box33D17V22PrefixFamily','nested'),
            ([29,30],'Box33D17V22PrefixExtra','nested'),
            ([12,15],'Box33D17V22RunSummary','nested'),
            ([11,34],'Box33D17V22RunExtra','nested'),
            ([13],'Box33D17V22Cycle','single'),
            ([33],'Box33D17V22M33','single'),
        ]
        for ids,mod,style in specs:
            for i in ids:
                nm=f'm{i}'
                known[tuple(hard[i])]=nm
                qual=f'BB6.Agent13.{mod}'+(f'.M{i}' if style=='nested' else '')
                arg=f' .m{i}' if style=='enum' else ''
                known_specs[nm]=(mod,qual,arg)
    if (d,v)==(17,23):
        hard=json.loads((HERE/'d17v23-hard.json').read_text())['machines']
        specs=[[[5,6,8,9,12,13,15,16],"Box33D17V23Block5"],[[7,10,14,17],"Box33D17V23Block7"],[[19],"Box33D17V23Block19"],[[24],"Box33D17V23Block24"],[[25],"Box33D17V23Block25"],[[1,2,3],"Box33D17V23Exact"],[[0,4,11],"Box33D17V23Anchored"]]
        for i in [18,22,23]:
            nm=f'm{i}';known[tuple(hard[i])]=nm
            known_specs[nm]=('Box33D17V23Carry','BB6.Agent13.Box33D17V23Carry',f' .{nm}')
        known[tuple(hard[20])]='m20'
        known_specs['m20']=('Box33D17V23M20','BB6.Agent13.Box33D17V23M20','')
        known[tuple(hard[21])]='m21'
        known_specs['m21']=('Box33D17V23M21','BB6.Agent13.Box33D17V23M21','')
        for ids,mod in specs:
            for i in ids:
                nm=f'm{i}';known[tuple(hard[i])]=nm
                known_specs[nm]=(mod,f'BB6.Agent13.{mod}.M{i}','')
    if (d,v)==(17,24):
        bank=json.loads((HERE/'d17v24-pair-blocks.json').read_text())
        for i,record in bank.items():
            nm=f'pair{i}';known[tuple(record['machine'])]=nm
            known_specs[nm]=('Box33D17V24PairBlocks',f'BB6.Agent13.Box33D17V24PairBlocks.M{i}','')
    if (d,v)==(17,21):
        known={
            (8,18,11,0,1,13,17,10,21,14,24,4):'m0',
            (8,6,11,14,1,13,17,10,21,0,24,4):'m1',
            (8,9,11,0,1,13,17,17,21,23,24,2):'m6',
            (8,4,11,6,1,13,17,7,21,0,24,4):'m2',
            (8,4,11,6,1,13,17,7,21,0,24,3):'m4',
            (8,6,11,2,1,13,17,19,21,3,4,0):'m8',
        }
        source='Box33D17V21Source'
        cycles={
            (8,6,11,2,1,13,17,0,21,17,24,3):('side',2130,89,0,-33),
            (8,2,11,12,1,13,17,0,21,17,24,3):('side',2482,103,0,-17),
            (8,14,11,0,1,13,17,22,21,11,24,2):('side',2092,1630,1,26),
        }
    if known and not known_specs and source:
        for nm in set(known.values()):known_specs[nm]=(source,f'BB6.Agent13.{source}',f' .{nm}')
    unresolved=[]
    for l in open('rlehard-1.txt'):
        t=tuple(map(int,l.split()))
        if t in cycles:
            late[t]=cycles[t]
        elif t in known:
            late[t]=('known',known[t])
        else:
            unresolved.append(t)
    auto_files={}
    if unresolved:
        # Discover proof-carrying candidate leaves; never treat success as a
        # trusted verdict. The generated exact source modules are imported
        # by DirectKnown and the tree audit checks partial-table equality.
        adir=work/'auto-run-summary'
        shutil.rmtree(adir,ignore_errors=True);adir.mkdir()
        inp=adir/'input.json';inp.write_text(json.dumps(unresolved))
        call('node',HERE/'auto_run_summary.js',inp,adir,family)
        manifest=json.loads((adir/'auto-run-manifest.json').read_text())
        for i,record in enumerate(manifest['found']):
            t=tuple(record['table']);nm=f'auto{i}';mod=record['module']
            known[t]=nm;known_specs[nm]=(mod,record['namespace'],'')
            late[t]=('known',nm)
        for f in adir.iterdir():
            if f.suffix in {'.lean','.json'}:auto_files[f.name]=f.read_text()
        unresolved=[tuple(t) for t in manifest['missing']]
    if unresolved:
        out.mkdir(parents=True,exist_ok=True)
        for name,body in auto_files.items():(out/name).write_text(body)
        (out/'UNACCEPTED-unresolved.json').write_text(json.dumps({
            'd0':d,'second':v,'proposed_bound':B,
            'remaining':unresolved},indent=2)+'\n')
        print('unresolved leaves:',len(unresolved),flush=True)
        for t in unresolved[:100]:
            print('UNACCEPTED',list(t),flush=True)
        raise RuntimeError('incomplete discovery; no weighted bound certified')
    stack=[]
    for l in open('rle-1.txt'):
        a=list(map(int,l.split()));assert len(a)==21;stack.append([a[:12],a[12:16],a[16:20]])
    json.dump({'stack':stack,'block':[]},open('survivors.json','w'))
    greedy.BASE=[1<<a if a>=0 else (1<<25)-1 for a in fixed]
    greedy.domain_mask=lambda t:tuple(1<<a if a>=0 else greedy.BASE[i] for i,a in enumerate(t))
    def direct_run(t,params,limit):
        c=run(t,params,limit)
        if c is not None and any(t[s]<=0 for s,_,_ in c['states']):return None
        return c
    greedy.run=direct_run;greedy.HERE=work
    argv=sys.argv;sys.argv=['greedy.py'];greedy.main()
    sys.argv=['emit_proof.py',str(out)]
    import emit_proof as em
    sys.argv=argv;em.HERE=work;em.OUT=out
    shutil.rmtree(out,ignore_errors=True);out.mkdir(parents=True,exist_ok=True)
    for name,body in auto_files.items():(out/name).write_text(body)
    oldwrite=em.write
    def write(name,imports,body):
        oldwrite(name.replace('Box4',family),[i.replace('Box4',family) for i in imports],body.replace('Box4',family))
    em.write=write
    (out/(family+'Tree.lean')).write_text(f'import Box33DirectTree\nnamespace {ns}\nabbrev SafeBox := BB6.Agent13.Box33Direct.SafeBox\nend {ns}\n')
    if known:
        if known_specs:
            imports=''.join('import '+mod+'\n' for mod in sorted({v[0] for v in known_specs.values()}))
            txt=f'import {family}Tree\n'+imports+f'namespace {ns}\nopen BB6Coverage BB6.Agent13.Box33Direct\n'
            for nm in sorted(set(known.values())):
                _,qual,arg=known_specs[nm]
                txt+=f'def {nm} : Known {B} := ⟨{qual}.partialTable{arg}, good_never _ _ ({qual}.compatible_never{arg})⟩\n'
        else:
            txt=f'import {family}Tree\nimport {source}\nnamespace {ns}\nopen BB6Coverage BB6.Agent13.Box33Direct\n'
            for nm in sorted(set(known.values())):
                txt+=f'def {nm} : Known {B} := ⟨{source}.partialTable .{nm}, good_never _ _ ({source}.compatible_never .{nm})⟩\n'
        (out/(family+'DirectKnown.lean')).write_text(txt+f'end {ns}\n')
    boxes=em.bank_modules('B')
    masks=[tuple(e['mask']) for e in json.load(open('greedyboxes.json'))['boxes']]
    idx={(i,a):sum(1<<k for k,b in enumerate(masks) if (greedy.BASE[i] if a<0 else 1<<a)&~b[i]==0) for i in range(12) for a in range(-1,25)}
    def safe(t):
        bits=(1<<len(masks))-1
        for i,a in enumerate(t):
            bits&=idx[i,a]
            if not bits:return None
        return (bits&-bits).bit_length()-1
    Node=em.Node
    def late_node(t):
        b=safe(t)
        if b is not None:return Node(t,'a',(b,))
        z=late[t]
        if z[0]=='known':return Node(t,'known',(family+'DirectKnown',ns+'.'+z[1]))
        if z[0]=='halt':return Node(t,'h',(z[1],))
        if z[0] in ('cycle','side'):return Node(t,'c',tuple(z[1:]))
        if z[0]=='last':
            i=z[1];return Node(t,'l',(i,),[(0,late_node(replace(t,i,0)))])
        if z[0]=='hole':
            i=z[1];return Node(t,'b',(i,),[(a,late_node(replace(t,i,a))) for a in range(25)])
        raise ValueError((t,z))
    f=iter(open('directtree.txt'))
    def parse(t):
        line=next(f).split();k=line[0];a=tuple(map(int,line[1:]))
        if k=='b':kids=[(x,parse(replace(t,a[0],x))) for x in range(25)]
        elif k=='l':kids=[(0,parse(replace(t,a[0],0)))]
        else:kids=[]
        b=safe(t)
        if b is not None:return Node(t,'a',(b,))
        if k=='o':
            assert a==t
            return late_node(t)
        return Node(t,k,a,kids)
    tree=parse(root);assert next(f,None) is None
    # Split independent subtrees into small kernel-checked modules. The last-row
    # constructor participates in the same sharding rule as a 25-way branch.
    group=serial=size=0;body=[];imports=set()
    def flush():
        nonlocal group,size,body,imports
        if body:
            write(f'{family}DG{group:04d}',imports|{family+'Tree'},f'namespace {ns}\n'+em.OPEN+'open BB6.Agent13.Box33Direct\n'+'\n'.join(body)+f'\nend {ns}\n')
            group+=1;size=0;body=[];imports=set()
    def materialize(node):
        nonlocal serial,size,body,imports
        if node.size>384:
            kids=list(node.kids);sz=node.size
            for j,(_,u) in sorted(enumerate(kids),key=lambda x:-x[1][1].size):
                if sz<=384:break
                x,u=kids[j];ref=materialize(u);kids[j]=(x,Node(u.t,'known',ref));sz-=u.size-1
            node=Node(node.t,node.kind,node.args,kids)
        if size+node.size>3000 or len(body)>=32:flush()
        name=f'DN{serial:06d}';serial+=1;mod=f'{family}DG{group:04d}'
        ks={};bs={}
        def render(n):
            if n.kind=='b':return f'.branch {n.args[0]} ['+','.join(f'({a},{render(c)})' for a,c in n.kids)+']'
            if n.kind=='l':return f'.last {n.args[0]} ({render(n.kids[0][1])})'
            if n.kind=='h':
                assert n.args[0]+6<=B
                return f'.leaf (.short {n.args[0]})'
            if n.kind=='c':
                e,k,d,b=n.args;return f'.leaf (.cycle {e} {k} {em.bools(d)} ({b}))'
            if n.kind=='a':return f'.leaf (.box {bs.setdefault(n.args[0],len(bs))})'
            if n.kind=='known':return f'.leaf (.known {ks.setdefault(tuple(n.args),len(ks))})'
            raise ValueError(n.kind)
        t=render(node);banks=[boxes[i] for i in bs];refs=list(ks)
        imports.update(m for m,_ in banks+refs if m!=mod)
        body.append(f'def p{name} : PartialMachine := {em.partial(node.t)}\ndef b{name} : Bank {B} := ⟨#[{",".join(r for _,r in refs)}],#[{",".join(r for _,r in banks)}]⟩\ndef t{name} : Tree := {t}\ntheorem ok{name} : audit b{name} 12 p{name} t{name} = true := by decide\ndef {name} : Known {B} := certified b{name} p{name} t{name} ok{name}\n')
        size+=node.size;return mod,ns+'.'+name
    mod,ref=materialize(tree);flush()
    write(f'{family}Closure',[mod,family+'Tree'],f'''namespace {ns}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent13.Box33Direct
open BB6.Agent13.Box17 (tableEq tableEq_sound)
theorem sourceBound : ∀ m, compatible (Box33D0.child {d} {v}) m → WeightedBound {B} m := by
  have he : {ref}.p = Box33D0.child {d} {v} := tableEq_sound _ _ (by decide)
  exact he ▸ {ref}.good
#print axioms sourceBound
end {ns}
''')
    print('direct tree nodes',tree.size,'shards',serial,'modules',group,'source proof still required',flush=True)
