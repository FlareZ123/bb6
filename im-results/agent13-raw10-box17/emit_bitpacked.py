import json,pathlib,sys
from emit_all import partial

def packstack(E,P):
    size=len(E);width=max(1,(2*size).bit_length());degree=max(1,max(map(len,E)))
    inv=sum((1+2*j+b)<<(width*(degree*i+k)) for i,es in enumerate(E) for k,(b,j) in enumerate(es))
    push=sum(j<<(width*(2*i+w)) for i,ab in enumerate(P) for w,j in enumerate(ab))
    return f'⟨{size},{width},{degree},{hex(inv)},{hex(push)}⟩'

def emit(i,t,c):
    r=len(c['edges'][1]);ss=[set() for _ in range(12)]
    for q,l,j in c['states']:ss[q].add(j+r*l)
    src=f'''import BitPackedStack
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent13.Box17.Cert{i}
open BB6Coverage BB6.Agent13BitPacked
def p : PartialMachine := {partial(t)}
'''
    rows=[]
    for j,s in enumerate(ss):
        xs=sorted(s); chunks=[xs[k:k+64] for k in range(0,len(xs),64)]
        for k,ch in enumerate(chunks):src+=f'def x{j}_{k} : List Nat := {ch}\n'
        src+=f'def row{j} : Row := ⟨[{",".join(f"x{j}_{k}" for k in range(len(chunks)))}],{hex(sum(1<<k for k in s))}⟩\n'
        rows.append(chunks)
    src+=f'def c : Cert := ⟨{packstack(c["edges"][0],c["pushes"][0])}, {packstack(c["edges"][1],c["pushes"][1])}, #[{",".join(f"row{j}" for j in range(12))}]⟩\n'
    for j,chunks in enumerate(rows):
        q=j//2;a=str(j%2==1).lower();names=[]
        src+=f'theorem valid{j} : (row c {q} {a}).valid = true := by decide\n'
        for k,ch in enumerate(chunks):
            nm=f'chunk{j}_{k}';names.append(nm)
            src+=f'theorem {nm} : indicesCheck p c {q} {a} x{j}_{k} = true := by decide\n'
        src+=f'theorem checked{j} : rowCheck p c {q} {a} = true := by\n  change (row c {q} {a}).valid && ([{",".join(f"x{j}_{k}" for k in range(len(chunks)))}] : List (List Nat)).all (indicesCheck p c {q} {a}) = true\n  rw [valid{j}]\n  simp only [List.all_cons,List.all_nil,Bool.and_self{"," if names else ""}{",".join(names)}] <;> rfl\n'
    src+='''theorem checked : check p c = true := by
  unfold check
  have h : (decide (0 < c.left.size) && decide (0 < c.right.size) && (c.left.pop 0).contains (false,0) && (c.right.pop 0).contains (false,0) && stateOK c 0 false 0 0) = true := by decide
  rw [h]
  have ha : ∀ (q : Fin 6) (a : Bool), rowCheck p c q a = true := by
    intro q a
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
    rcases hq with h|h|h|h|h|h <;> subst q <;> cases a
'''
    src+=''.join(f'    · exact checked{j}\n' for j in range(12))
    src+='''  simp [ha]
theorem nonhalt (m : Machine) (h : compatible p m) : NeverHalts m := never p c checked m h
#print axioms nonhalt
'''+f'end BB6.Agent13.Box17.Cert{i}\n'
    return src

def main():
    ts=json.load(open('compressed.json'));dst=pathlib.Path('packedlean');dst.mkdir(exist_ok=True)
    for i in map(int,sys.argv[1:]) if len(sys.argv)>1 else range(len(ts)):
        t,c=ts[i];(dst/f'Box17Cert{i:03}.lean').write_text(emit(i,t,c))
if __name__=='__main__':main()
