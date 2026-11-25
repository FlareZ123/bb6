from pathlib import Path
import argparse
from macrofar import check
from emit_macrofar import tree, arr

def emit(i, original, code, k):
    dfa = [int(x,36) for x in code[1:]]
    cert = check(original, dfa, int(code[0]), int(k), certificate=True)
    assert cert, (i, original, code, k)
    _, dfa, T, H, zero, trees = cert
    d,n = len(dfa)//2,len(T)
    p = original.replace('_','')
    lines = [f'namespace M{i}',f'-- {original} {code} {k}',
      'def table : PartialMachine := fun s =>','  match s.1.val,s.2 with']
    for j in range(12):
        a=p[3*j:3*j+3]
        if a != '---':
            lines.append(f'  | {j//2},{str(bool(j%2)).lower()} => some (some ⟨{str(a[0]=="1").lower()},{str(a[1]=="R").lower()},{ord(a[2])-65}⟩)')
    lines += ['  | _,_ => none',
      'abbrev oriented : PartialMachine := '+ ('FAR.reflectPartial table' if code[0]=='1' else 'table'),
      f'def data : MacroFAR.Data {d} {n} := ⟨0,{arr(dfa)},{arr(range(6*d))},{H},{arr(row[0] for row in T)},{arr(row[1] for row in T)},{zero}⟩',
      'def trees (q : Fin 6) : MacroFAR.Tree (Fin 6) :=','  match q.val with']
    for q,t in enumerate(trees):
        lines.append(f'  | {q} => {tree(t)}')
    lines += ['  | _ => .reject',
      'theorem base_ok : data.baseOK = true := by decide',
      'theorem blank_ok : data.zero (data.node data.start 0) = false := by decide']
    for q in range(6):
        lines.append(f'theorem check{q} : data.treeCheck (MacroFARBridge.project oriented) {q} [] [] (trees {q}) = true := by decide')
    lines += ['theorem checked : data.check (MacroFARBridge.project oriented) trees = true := by',
      '  unfold MacroFAR.Data.check','  rw [base_ok,blank_ok]',
      '  simp only [Bool.not_false,Bool.and_self,Bool.true_and]',
      '  apply List.all_eq_true.mpr','  intro q _',
      '  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega',
      '  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl',
      *[f'  · exact check{q}' for q in range(6)],
      'theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=']
    if code[0]=='1':
        lines.append('  FAR.reflectNever m (MacroFARBridge.never oriented data trees checked (reflectTable m) (FAR.reflectCompatible table m hm))')
    else:
        lines.append('  MacroFARBridge.never table data trees checked m hm')
    lines += ['#print axioms never',f'end M{i}']
    return '\n'.join(lines)

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('input',type=Path);ap.add_argument('output',type=Path)
    a=ap.parse_args()
    blocks=['import MacroFARBridge','set_option maxRecDepth 100000','set_option maxHeartbeats 0','namespace BB6Coverage.Agent32MacroFAR']
    for line in a.input.read_text().splitlines():
        i,p,code,k,*_=line.split();blocks.append(emit(i,p,code,k))
    blocks.append('end BB6Coverage.Agent32MacroFAR')
    a.output.write_text('\n\n'.join(blocks)+'\n')
