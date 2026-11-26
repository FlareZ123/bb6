"""Emit the eight-phase nonhalting proof for 0LF miss 12."""
import re
from la_multivar import C, Machine, cfg, gen, make_table
from generate_rf_growth import replay
def emit_phase12(rows,out):
    i=12
    M=Machine(rows[i])
    p,q="01110","00111"
    ps=(p*3,q)
    base=[37,41,65,55,81,65,69,99]
    coef=[42,42,56,42,56,42,42,56]
    params=[(2,"000",0),(2,"0011",0),(2,"01111",0),(3,"",1),(3,"011111",0),(4,"0",1),(4,"0011111",0),(4,"01111111",0),(5,"000",1)]
    ph=[C("A","00",p*k+"A"+s+q*j+"B"+"0011",ps) for k,s,j in params]
    lines=["import SweepPumping","set_option maxRecDepth 100000","set_option maxHeartbeats 0","namespace BB6.Agent8Raw54.ZeroLF.M12","open BB6Coverage BB6Coverage.Agent31Pump",make_table(M),f"def family (n : Nat) : Z0 := {cfg(ph[0])}","theorem entry : run0 table 140 ⟨0,[],[]⟩ = some (family 0) := by rfl"]
    for j in range(8):
        a,b=ph[j:j+2]
        ans=replay(M,a,b,coef[j],base[j])
        assert ans and ans[1]==(coef[j],base[j]),j
        s=gen(i,M,a,b,140,ans)
        body=s.split("theorem epoch (n : Nat)")[1].split("  have htarget")[0]
        body=body.replace("(family n)",cfg(a)).replace("(family (n+1))",cfg(b))
        last=re.search(r" at (\w+)\s*$",body)[1]
        lines.append(f"theorem phase{j} (n : Nat)"+body+"  exact "+last)
    lines.append(f"theorem epoch (n : Nat) : run0 table ({sum(coef)}*n+{sum(base)}) (family n) = some (family (n+1)) := by")
    for j in range(8):lines.append(f"  have h{j} := phase{j} n")
    cur="h0"
    for j in range(1,8):
        lines.append(f"  have g{j} := join0 {cur} h{j}")
        cur=f"g{j}"
    lines.append(f'  rw [show {"+".join(f"({a}*n+{b})" for a,b in zip(coef,base))}={sum(coef)}*n+{sum(base)} by omega] at {cur}')
    lines.append(f"  have ht : ({cfg(ph[-1])} : Z0) = family (n+1) := by simp only [family,rep,List.append_assoc,List.append_nil,List.nil_append,List.cons_append] <;> rfl")
    lines.append(f"  rw [ht] at {cur}\n  exact {cur}")
    lines.append(f"theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=\n  never_of_growth table family 140 (fun n => {sum(coef)}*n+{sum(base)}) entry (by intro n; omega) epoch m hm\n#print axioms never\nend BB6.Agent8Raw54.ZeroLF.M12")
    (out/"Raw54ZeroLF12.lean").write_text("\n".join(lines)+"\n")
