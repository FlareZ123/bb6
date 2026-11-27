"""Emit exact guarded sweep lemmas from the saved 69-stage 1352 trace.
All joins, transition rules, seed and positive growth are kernel checked."""
import json
import pathlib
import sys

def bs(s):
    return "["+",".join("true" if b=="1" else "false" for b in s)+"]"
def ls(w):
    return "["+",".join(".rep "+bs(a["s"])+" "+("false" if a["v"]=="x" else "true") if a["v"] else ".lit "+bs(a["s"]) for a in w)+"]"
def state(z):
    return f'⟨{z["q"]},{ls(z["l"])},{ls(z["r"])}⟩'
def ev(w):
    return f"(ev {ls(w)} (env x y))"
def cost(a):
    return str(a["k"]) if a["kind"]=="F" else str(a["k"])+"*"+a["v"]
def generate(out):
    out.mkdir(parents=True,exist_ok=True)
    d=json.loads(pathlib.Path(__file__).with_name("sweep1352.json").read_text())
    ns="BB6.Agent6OneLF1352"
    head=f"""set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace {ns}
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent6ListSym BB6.Agent6SymWord
"""
    def put(n,s):
        (out/(n+".lean")).write_text(s)
    qcode="\n".join(f'  | {i//2},{str(bool(i&1)).lower()} => some (some ⟨{str(bool(v&2)).lower()},{str(bool(v&1)).lower()},{v//4}⟩)' for i,v in enumerate(d["table"]) if v!=24)
    put("Sweep1352Base",f"""import ListSym
{head}
def p : PartialMachine := fun s => match s.1.val,s.2 with
{qcode}
  | _,_ => none
def widths : Widths := ⟨24,20⟩
def initial : State := {state(d['init'])}
def shifted : State := {state(d['goal'])}
end {ns}
""")
    parts=[]
    for start in range(0,len(d["stages"]),10):
        end=min(start+10,len(d["stages"]))
        idx=len(parts)
        name=f"Sweep1352Part{idx}"
        s=f"import Sweep1352Base\n{head}"
        for i in range(start,end):
            a=d["stages"][i]
            s+=f"def s{i} : State := {state(a['src'])}\ndef d{i} : State := {state(a['dst'])}\n"
            f=a["kind"]=="F"
            l=bool(a["L"]) if f else True
            r=bool(a["R"]) if f else True
            lp,rp=bs(a["lp"]),bs(a["rp"])
            tl,tr="++L" if l else "","++R" if r else ""
            args=(" (L : List Bool)" if l else "")+(" (R : List Bool)" if r else "")
            if f:
                sl,sr,dl,dr=lp+tl,rp+tr,bs(a["ol"])+tl,bs(a["or"])+tr
            elif a["kind"]=="L":
                sl,sr,dl,dr=lp+"++"+bs(a["I"])+"++L",rp+"++R",lp+"++L",rp+"++"+bs(a["O"])+"++R"
            else:
                sl,sr,dl,dr=lp+"++L",rp+"++"+bs(a["I"])+"++R",lp+"++"+bs(a["O"])+"++L",rp+"++R"
            s+=f"""theorem rule{i}{args} :
    run0 p {a['k']} ⟨{a['src']['q']},{sl},{sr}⟩ =
      some ⟨{a['dst']['q']},{dl},{dr}⟩ := rfl
"""
            if f:
                expr=f"rule{i}"+(" "+ev(a["L"]) if l else "")+(" "+ev(a["R"]) if r else "")
            else:
                expr=f"sweep{a['kind']} p {a['src']['q']} {lp} {rp} {bs(a['I'])} {bs(a['O'])} {a['k']} rule{i} {a['v']} {ev(a['L'])} {ev(a['R'])}"
            s+=f"""theorem h{i} (x y : Nat) : run0 p ({cost(a)}) (s{i}.eval x y)=some (d{i}.eval x y) := by
  simpa only [s{i},d{i},State.eval,ev,env,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.append_nil,List.nil_append] using {expr}
"""
        c="+".join(cost(a) for a in d["stages"][start:end])
        h=f"H{start}"
        s+=f"""theorem part{idx} (x y : Nat) : run0 p ({c}) (s{start}.eval x y)=some (d{end-1}.eval x y) := by
  have H{start} := h{start} x y
"""
        for i in range(start+1,end):
            s+=f"  have H{i} := h{i} x y\n  rw [← State.same_sound widths d{i-1} s{i} (by decide +kernel) x y] at H{i}\n"
            h=f"join0 ({h}) H{i}"
        s+=f"  exact {h}\n#print axioms part{idx}\nend {ns}\n"
        put(name,s)
        parts.append((name,idx,start,end,c))
    s="\n".join("import "+a[0] for a in parts)+"\n"+head+"""theorem period (x y : Nat) : run0 p (1288*x+1080*y+7114) (initial.eval x y)=some (shifted.eval x y) := by
"""
    h="P0"
    for name,idx,start,end,c in parts:
        prev="initial" if idx==0 else "d"+str(start-1)
        s+=f"  have P{idx} := part{idx} x y\n  rw [← State.same_sound widths {prev} s{start} (by decide +kernel) x y] at P{idx}\n"
        if idx>0:h=f"join0 ({h}) P{idx}"
    c="+".join("("+a[4]+")" for a in parts)
    s+=f"""  have H := {h}
  rw [State.same_sound widths d{len(d['stages'])-1} shifted (by decide +kernel) x y] at H
  rw [show {c}=1288*x+1080*y+7114 by omega] at H
  exact H
def family (k : Nat) := initial.eval k k
theorem shift_eq (k : Nat) : shifted.eval k k=family (k+1) := by
  unfold family shifted initial State.eval
  simp only [ev,env,Bool.false_eq_true,ite_false,ite_true,rep,List.append_assoc,List.cons_append,List.nil_append]
theorem seed : run0 p 6678 ⟨0,[],[]⟩=some (family 0) := by decide +kernel
theorem growth (k : Nat) : run0 p (2368*k+7114) (family k)=some (family (k+1)) := by
  have h:=period k k
  rw [shift_eq,show 1288*k+1080*k+7114=2368*k+7114 by omega] at h
  exact h
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  never_of_growth p family 6678 (fun k => 2368*k+7114) seed (by intro k; omega) growth m hm
#print axioms period
#print axioms never
end {ns}
"""
    put("Sweep1352",s)
if __name__=="__main__":
    generate(pathlib.Path(sys.argv[1]))
