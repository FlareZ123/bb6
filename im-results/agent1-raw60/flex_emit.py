"""Emit independent Lean certificates from flex-families.json."""
import json
from pathlib import Path
from itertools import groupby
import flexfill as f
from recursive_fill import C,norm,word,parse,table,num,bits

ROOT=Path(__file__).resolve().parent

def W(w):
    if not w:return '([] : List Bool)'
    x,a,b=w[0]
    if x in [2,3]:
        assert a==0 and b==1 and len(w)==1
        return 'L' if x==2 else 'R'
    if x==4:
        assert a==0 and b==1
        return '(b::'+W(w[1:])+')'
    return '(List.replicate '+num(a,b)+' '+bits(x)+' ++ '+W(w[1:])+')'

def cfg(c):return f'⟨{c.q},{W(c.l)},{W(c.r)}⟩'
def bool_expr(x):return 'b' if x==4 else bits(x)

def solve_eq(raw,canonical):
    assert norm(raw)==canonical,(raw,canonical)
    if raw==canonical:return 'by rfl'
    eqs=[]
    for x,g in groupby(raw,key=lambda x:x[0]):
        group=list(g)
        if len(group)>1:
            assert x in (0,1)
            parts=[num(a,b) for x,a,b in group];expr=parts[-1]
            for part in reversed(parts[:-1]):expr=f'({part}+{expr})'
            canon=num(sum(a for x,a,b in group),sum(b for x,a,b in group))
            if expr!=canon:eqs.append(f'show {expr}={canon} by omega')
    return 'by simp only [merge,List.replicate_append_replicate,List.append_nil]'+(' <;> simp only ['+','.join(eqs)+']' if eqs else '')

def eqs(c,raw_l,raw_r,tag,indent='    '):
    assert c.l==norm(raw_l) and c.r==norm(raw_r),(c,raw_l,raw_r)
    return [f'{indent}have {tag}L : {W(raw_l)} = {W(c.l)} := {solve_eq(raw_l,c.l)}',
            f'{indent}have {tag}R : {W(raw_r)} = {W(c.r)} := {solve_eq(raw_r,c.r)}']

def segments(hist):
    out=[];j=0
    while j<len(hist):
        typ,c,d,info=hist[j]
        if typ=='step':
            k=j+1
            while k<len(hist) and hist[k][0]=='step':k+=1
            out.append(('fixed',c,hist[k-1][2],k-j));j=k
        else:out.append(hist[j]);j+=1
    return out

def phases(hist,s,r,lp,fillname='fillRun'):
    out=[];costs=[];seg=segments(hist)
    for j,(typ,c,d,info) in enumerate(seg):
        name=f'h{j}'
        if typ=='fixed':
            cost=str(info)
            out.append(f'  have {name} : run0 table {cost} {cfg(c)} = some {cfg(d)} := by rfl')
            costs.append(cost);continue
        if typ in ('ih','fill'):
            if typ=='ih':
                bit,L,R=info;k,b=1,0;m='n';cost='T n'
                h=f'ih {bool_expr(bit)} {W(L)} {W(R)}'
            else:
                k,b,bit,L,R=info;m=num(k,b);cost=f'T {m}'
                h=f'{fillname} {m} {bool_expr(bit)} {W(L)} {W(R)}'
            length=(1,s*k,s*b+r)
            l0=(*lp,*L);r0=(length,(bit,0,1),*R)
            l1=((bit,0,1),length,*lp,*L);r1=R
            lines=[f'    have H := {h}']
            if typ=='fill':lines.append(f'    rw [show {s}*{m}+{r}={num(s*k,s*b+r)} by omega] at H')
        elif typ in ('left','right'):
            if typ=='left':
                a,x,y,L,R=info;cost=f'{a}*n'
                l0=((x,a,0),*L);r0=R;l1=L;r1=((y,a,0),*R)
                lines=[f'    have hlocal : ∀ L R : List Bool, run0 table {a} (Q {c.q} (List.replicate {a} {bits(x)}++L) R) = some (Q {c.q} L (List.replicate {a} {bits(y)}++R)) := by intro L R; rfl',
                       f'    have H := manyL table {c.q} {a} {bits(x)} {bits(y)} hlocal n {W(L)} {W(R)}']
            else:
                a,bit,x,y,L,R=info;cost=f'{a}*n'
                l0=((bit,0,1),*L);r0=((x,a,0),*R)
                l1=((bit,0,1),(y,a,0),*L);r1=R
                lines=[f'    have hlocal : ∀ L R : List Bool, run0 table {a} (Q {c.q} ({bits(bit)}::L) (List.replicate {a} {bits(x)}++R)) = some (Q {c.q} ({bits(bit)}::(List.replicate {a} {bits(y)}++L)) R) := by intro L R; rfl',
                       f'    have H := manyR table {c.q} {a} {bits(bit)} {bits(x)} {bits(y)} hlocal n {W(L)} {W(R)}']
        else:raise ValueError(typ)
        lines.append(f'    change run0 table ({cost}) ⟨{c.q},{W(l0)},{W(r0)}⟩ = some ⟨{d.q},{W(l1)},{W(r1)}⟩ at H')
        lines+=eqs(c,l0,r0,'src')+eqs(d,l1,r1,'dst')+['    simpa only [srcL,srcR,dstL,dstR] using H']
        out.append(f'  have {name} : run0 table ({cost}) {cfg(c)} = some {cfg(d)} := by\n'+'\n'.join(lines))
        costs.append(cost)
    join='h0'
    for j in range(1,len(seg)):join=f'(join0 {join} h{j})'
    out.append('  have H := '+join)
    return out,costs

def emit(idx,code,lp0,s,r,base,t,st,tg,oq=0,q0=5):
    p=parse(code);lp=word(lp0)
    src=C(q0,(*lp,*f.L),norm(((1,s,r+s),*f.B,*f.R)))
    dst=C(oq,norm((*f.B,(1,s,r+s),*lp,*f.L)),f.R)
    hist=f.path(p,src,dst,q0,s,r,lp,oq);assert hist,idx
    g=f.grow_path(p,st,tg,q0,s,r,lp,oq,200);assert g,idx
    seg=segments(hist)
    N=sum(v[0]=='ih' for v in seg)
    a=sum(v[3][0] for v in seg if v[0] in ('left','right'))
    b=sum(v[3] for v in seg if v[0]=='fixed')
    assert N>0
    lpL=W((*lp,*f.L));targetL=W((*f.B,(1,s,r),*lp,*f.L))
    startR=W(((1,s,r),*f.B,*f.R))
    statement=f'∀ (b : Bool) (L R : List Bool), run0 table (T n) (Q {q0} {lpL} {startR}) = some (Q {oq} {targetL} R)'
    out=[f'namespace M{idx}',f'-- {code}',table(p),
         f'def T : Nat → Nat | 0 => {base} | n+1 => {N}*T n+{a}*n+{b}',
         f'def Fill (n : Nat) : Prop := {statement}',
         'theorem fillStep (n : Nat) (ih : Fill n) : Fill (n+1) := by',
         '  intro b L R','  unfold Fill at ih',
         f'  change run0 table (T (n+1)) (Q {q0} '+lpL+' '+startR.replace(f'({s}*n+{r})',f'({s}*(n+1)+{r})')+f') = some (Q {oq} '+targetL.replace(f'({s}*n+{r})',f'({s}*(n+1)+{r})')+' R)',
         f'  rw [show {s}*(n+1)+{r}={s}*n+{r+s} by omega]']
    lines,costs=phases(hist,s,r,lp);out+=lines
    out += [f"  rw [show {'+'.join('('+x+')' for x in costs)}=T (n+1) by simp only [T]; omega] at H",
            '  exact H','theorem fill (n : Nat) : Fill n := by',
            '  induction n with','  | zero => intro b L R; rfl','  | succ n ih => exact fillStep n ih',
            f'def family (n : Nat) : Z0 := {cfg(st)}',
            f'theorem entry : run0 table {t} ⟨0,[],[]⟩ = some (family 0) := by rfl',
            f'theorem fillRun (n : Nat) (b : Bool) (L R : List Bool) : run0 table (T n) (Q {q0} {lpL} {startR}) = some (Q {oq} {targetL} R) := fill n b L R']
    glines,gcost=phases(g,s,r,lp)
    out.append('def cost (n : Nat) : Nat := '+' + '.join('('+c+')' for c in gcost))
    out.append('theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by')
    out+=glines
    varA,varB=next((a,b) for x,a,b in (*st.l,*st.r) if a)
    out.extend(['  unfold cost family',
                f'  rw [show {varA}*(n+1)+{varB}={varA}*n+{varB+varA} by omega]',
                '  exact H',
                'theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=',
                f'  never_of_growth table family {t} cost entry (by intro n; unfold cost; omega) growth m hm',
                '#print axioms never',f'end M{idx}'])
    return '\n'.join(out)+'\n'

def main():
    mods=[]
    for row in json.loads((ROOT/'flex-families.json').read_text()):
        idx,code,lp,s,r,base,t,q,L,R,*states=row
        oq,q0=states or [0,5]
        st=C(q,tuple(map(tuple,L)),tuple(map(tuple,R)))
        def grow(w):return tuple((x,a,b+a) for x,a,b in w)
        tg=C(q,grow(st.l),grow(st.r))
        mod=f'Raw60LFFlex{idx}';ns='BB6.Agent1Raw60LFFlex'
        head=f'import RecursiveFill\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nset_option linter.unusedSimpArgs false\nset_option linter.unusedVariables false\nnamespace {ns}\nopen BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1RecursiveFill\n'
        (ROOT/(mod+'.lean')).write_text(head+emit(idx,code,lp,s,r,base,t,st,tg,oq,q0)+f'\nend {ns}\n')
        mods.append(mod)
    (ROOT/'Raw60LFFlex.lean').write_text(''.join(f'import {m}\n' for m in mods))
    print(len(mods),'recursive transfer certificates')

if __name__=='__main__':main()
