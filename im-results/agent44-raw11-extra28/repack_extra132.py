#!/usr/bin/env python3
"""Repack the exact Extra132 giant TwoSidedAutomata witness into proof-sized bit-packed modules.

SOURCE_DIR is the frozen/transformed Extra132 parent-source directory.
OUT_DIR receives generated modules. The script patches the one parent subtree
source so it imports the packed proof. Generated source is untrusted: every
Boolean obligation is still discharged by Lean's kernel.
"""
from __future__ import annotations
import ast
import re
import sys
from pathlib import Path

CHUNK = 256
GROUP = 8
PAIRS = {"(": ")", "[": "]", "{": "}", "⟨": "⟩"}
CLOSERS = {v: k for k, v in PAIRS.items()}
ROW_COUNTS = [9510,811,1696,11030,1834,13603,11465,12024,9152,0,5153,7161]
TARGET = "Agent5Raw11Extra132Sub_root_12_root_19_root_21.lean"

def split_top(text):
    out=[]; stack=[]; start=0
    for i,ch in enumerate(text):
        if ch in PAIRS: stack.append(ch)
        elif ch in CLOSERS:
            if not stack or stack[-1] != CLOSERS[ch]:
                raise ValueError(f"unbalanced delimiter at {i}: {ch!r}")
            stack.pop()
        elif ch == "," and not stack:
            out.append(text[start:i].strip()); start=i+1
    if stack: raise ValueError("unterminated delimiter")
    out.append(text[start:].strip())
    return out

def parse_stack(src,name):
    text=(src/f"Agent44Extra132Giant{name}.lean").read_text(encoding="utf-8")
    m=re.search(rf"def {name.lower()} : .*? := (⟨.*⟩)\n#print",text,re.S)
    if not m: raise ValueError(f"missing {name} stack")
    parts=split_top(m.group(1)[1:-1])
    if len(parts)!=2: raise ValueError(f"{name}: expected two fields")
    def conv(x):
        return ast.literal_eval(x.replace("#[","[").replace("false","False").replace("true","True"))
    return conv(parts[0]),conv(parts[1])

class TrieParser:
    def __init__(self,text,env):
        self.text=text; self.i=0; self.env=env
    def ws(self):
        while self.i<len(self.text) and self.text[self.i].isspace(): self.i+=1
    def eat(self,tok):
        self.ws()
        if not self.text.startswith(tok,self.i):
            raise ValueError((self.i,tok,self.text[self.i:self.i+60]))
        self.i+=len(tok)
    def expr(self):
        self.ws()
        if self.text.startswith(".empty",self.i): self.i+=6; return ("e",)
        if self.text.startswith(".leaf",self.i): self.i+=5; return ("l",)
        if self.text.startswith("(.branch",self.i):
            self.i+=len("(.branch"); a=self.expr(); b=self.expr(); self.eat(")"); return ("b",a,b)
        full="(BB6.Agent1NGram.Trie.branch"
        if self.text.startswith(full,self.i):
            self.i+=len(full); a=self.expr(); b=self.expr(); self.eat(")"); return ("b",a,b)
        m=re.match(r"[A-Za-z0-9_.]+",self.text[self.i:])
        if m:
            name=m.group(0); self.i+=len(name)
            if name not in self.env: raise KeyError(name)
            return self.env[name]
        raise ValueError((self.i,self.text[self.i:self.i+80]))

def def_expr(path,name):
    text=path.read_text(encoding="utf-8")
    m=re.search(rf"^def {re.escape(name)}\s*:.*?:=\s*(.*)$",text,re.M)
    if not m: raise ValueError(f"missing {name} in {path.name}")
    return m.group(1).strip()

def parse_rows(src):
    env={}
    for path in sorted(src.glob("Agent44Extra132GiantRow*SplitData*.lean")):
        text=path.read_text(encoding="utf-8")
        ns=re.search(r"^namespace\s+(\S+)",text,re.M)
        item=re.search(r"^def\s+(chunk\d+)\s*:.*?:=\s*(.*)$",text,re.M)
        if not ns or not item: continue
        p=TrieParser(item.group(2).strip(),env); tree=p.expr(); p.ws()
        if p.i!=len(p.text): raise ValueError(f"trailing trie syntax in {path.name}")
        env[ns.group(1)+"."+item.group(1)]=tree
    rows=[]
    for j in range(12):
        path=src/f"Agent44Extra132GiantRowData{j:02d}.lean"
        expr=def_expr(path,f"row{j:02d}")
        p=TrieParser(expr,env); tree=p.expr(); p.ws()
        if p.i!=len(expr): raise ValueError(f"trailing row syntax in {path.name}")
        vals=[]
        def walk(node,prefix=0,bit=0):
            if node[0]=="e": return
            if node[0]=="l": vals.append(prefix); return
            walk(node[1],prefix,bit+1); walk(node[2],prefix+(1<<bit),bit+1)
        walk(tree); rows.append(sorted(vals))
    counts=[len(x) for x in rows]
    if counts!=ROW_COUNTS: raise ValueError(f"unexpected Extra132 row census: {counts}")
    if sum(counts)!=83439: raise ValueError("Extra132 state census changed")
    return rows

def pack_stack(edges,pushes):
    size=len(edges); width=max(1,(2*size).bit_length()); degree=max(1,max(map(len,edges)))
    inv=sum((1+2*pred+int(bit))<<(width*(degree*i+k))
            for i,es in enumerate(edges) for k,(bit,pred) in enumerate(es))
    push=sum(dst<<(width*(2*i+bit)) for i,pair in enumerate(pushes) for bit,dst in enumerate(pair))
    return f"⟨{size},{width},{degree},{hex(inv)},{hex(push)}⟩"

def write(path,text): path.write_text(text,encoding="utf-8")

def emit(src,out):
    out.mkdir(parents=True,exist_ok=True)
    le,lp=parse_stack(src,"Left"); re_,rp=parse_stack(src,"Right")
    if (len(le),len(lp),max(map(len,le)))!=(2097,2097,13): raise ValueError("unexpected left stack")
    if (len(re_),len(rp),max(map(len,re_)))!=(133,133,104): raise ValueError("unexpected right stack")
    rows=parse_rows(src)
    pre="set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nset_option Elab.async false\n"
    ns="namespace BB6.Agent44Extra132Packed\nopen BB6.Agent13BitPacked\n"
    write(out/"Extra132PackedLeft.lean","import BitPackedStack\n"+pre+ns+
          "def left : Stack := "+pack_stack(le,lp)+"\n#print axioms left\nend BB6.Agent44Extra132Packed\n")
    write(out/"Extra132PackedRight.lean","import BitPackedStack\n"+pre+ns+
          "def right : Stack := "+pack_stack(re_,rp)+"\n#print axioms right\nend BB6.Agent44Extra132Packed\n")
    row_groups=[]
    for j,vals in enumerate(rows):
        chunks=[vals[k:k+CHUNK] for k in range(0,len(vals),CHUNK)]
        names=[f"x{j}_{k}" for k in range(len(chunks))]
        groups=[names[k:k+GROUP] for k in range(0,len(names),GROUP)]
        row_groups.append(groups)
        body="import BitPackedStack\n"+pre+ns
        for k,ch in enumerate(chunks): body+=f"def x{j}_{k} : List Nat := {ch}\n"
        for gi,g in enumerate(groups): body+=f"def g{j}_{gi} : List (List Nat) := [{','.join(g)}]\n"
        body+=f"def chunks{j} : List (List Nat) := "+(" ++ ".join(f"g{j}_{gi}" for gi in range(len(groups))) if groups else "[]")+"\n"
        body+=f"def mask{j} : Nat := {hex(sum(1<<k for k in vals))}\n"
        body+=f"def row{j} : Row := ⟨chunks{j},mask{j}⟩\n#print axioms row{j}\nend BB6.Agent44Extra132Packed\n"
        write(out/f"Extra132PackedRow{j:02d}.lean",body)
    imports="import Extra132PackedLeft\nimport Extra132PackedRight\n"+"".join(f"import Extra132PackedRow{j:02d}\n" for j in range(12))
    table="""def p : PartialMachine := fun s => match s.1.val, s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,false,3⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,2⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨false,true,4⟩)
  | _,_ => none
"""
    write(out/"Extra132PackedCert.lean",imports+pre+"namespace BB6.Agent44Extra132Packed\nopen BB6Coverage BB6.Agent13BitPacked\n"+table+
          "def c : Cert := ⟨left,right,#[row0,row1,row2,row3,row4,row5,row6,row7,row8,row9,row10,row11]⟩\n#print axioms c\nend BB6.Agent44Extra132Packed\n")
    for j,groups in enumerate(row_groups):
        q,abit=divmod(j,2); a="true" if abit else "false"
        write(out/f"Extra132PackedValid{j:02d}.lean","import Extra132PackedCert\n"+pre+ns+
              f"theorem valid{j} : row{j}.valid = true := by decide +kernel\n#print axioms valid{j}\nend BB6.Agent44Extra132Packed\n")
        for gi,g in enumerate(groups):
            body="import Extra132PackedCert\n"+pre+ns; lems=[]
            for xname in g:
                k=xname.split("_")[1]; lm=f"chunk{j}_{k}"; lems.append(lm)
                body+=f"theorem {lm} : indicesCheck p c ({q} : Fin 6) {a} {xname} = true := by decide +kernel\n#print axioms {lm}\n"
            alts=" | ".join("rfl" for _ in g)
            body+=f"""theorem groupmember{j}_{gi} {{xs : List Nat}} (h : xs ∈ g{j}_{gi}) :
    indicesCheck p c ({q} : Fin 6) {a} xs = true := by
  simp only [g{j}_{gi}, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with {alts} <;> simp only [{','.join(lems)}]
#print axioms groupmember{j}_{gi}
end BB6.Agent44Extra132Packed
"""
            write(out/f"Extra132PackedChunk{j:02d}G{gi:02d}.lean",body)
        mi="".join(f"import Extra132PackedChunk{j:02d}G{gi:02d}\n" for gi in range(len(groups)))
        if not groups: mi="import Extra132PackedCert\n"
        body=mi+"set_option maxRecDepth 100000\n"+ns
        body+=f"theorem member{j} {{xs : List Nat}} (h : xs ∈ chunks{j}) :\n    indicesCheck p c ({q} : Fin 6) {a} xs = true := by\n"
        if not groups:
            body+=f"  simp only [chunks{j}, List.not_mem_nil] at h\n"
        elif len(groups)==1:
            body+=f"  rw [chunks{j}] at h\n  exact groupmember{j}_0 h\n"
        else:
            body+=f"  rw [chunks{j}] at h\n"
            def dispatch(n,indent="  "):
                if n==1:
                    return indent+"rcases List.mem_append.mp h with h0 | h1\n"+indent+f"· exact groupmember{j}_0 h0\n"+indent+f"· exact groupmember{j}_1 h1\n"
                return indent+"rcases List.mem_append.mp h with h | hr\n"+indent+"· "+dispatch(n-1,indent+"  ").lstrip()+indent+f"· exact groupmember{j}_{n} hr\n"
            body+=dispatch(len(groups)-1)
        body+=f"#print axioms member{j}\nend BB6.Agent44Extra132Packed\n"
        write(out/f"Extra132PackedMember{j:02d}.lean",body)
    pi="import BitPackedSplit\nimport WeightedTNF\nimport Extra132PackedCert\n"+"".join(f"import Extra132PackedValid{j:02d}\n" for j in range(12))+"".join(f"import Extra132PackedMember{j:02d}\n" for j in range(12))
    proof=pi+pre+"""namespace BB6.Agent44Extra132Packed
open BB6Coverage BB6.Agent13BitPacked BB6.Agent13BlankDelay
private theorem state_cases (q : Fin 6) :
    q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
theorem allValid (q : Fin 6) (a : Bool) : (row c q a).valid = true := by
  rcases state_cases q with rfl | rfl | rfl | rfl | rfl | rfl <;> cases a
"""
    for j in range(12): proof+=f"  · exact valid{j}\n"
    proof+="""theorem allChunks (q : Fin 6) (a : Bool) (xs : List Nat)
    (h : xs ∈ (row c q a).chunks) : indicesCheck p c q a xs = true := by
  rcases state_cases q with rfl | rfl | rfl | rfl | rfl | rfl <;> cases a
"""
    for j in range(12): proof+=f"  · exact member{j} h\n"
    proof+="""theorem splitChecked : BB6.Agent44BitPackedSplit.SplitCheck p c := by
  refine ⟨?_, ?_, ?_, ?_, ?_, allValid, allChunks⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
theorem nonhalt (m : Machine) (hm : compatible p m) : NeverHalts m :=
  BB6.Agent44BitPackedSplit.never p c splitChecked m hm
theorem weighted (B : Nat) : Cover (WeightedBound B) p :=
  .leaf _ fun m hm => weighted_never B m (nonhalt m hm)
#print axioms allValid
#print axioms allChunks
#print axioms splitChecked
#print axioms nonhalt
#print axioms weighted
end BB6.Agent44Extra132Packed
"""
    write(out/"Extra132PackedSplitProof.lean",proof)
    target=src/TARGET; text=target.read_text(encoding="utf-8")
    if "import Agent44Extra132GiantProof" in text:
        text=text.replace("import Agent44Extra132GiantProof","import Extra132PackedSplitProof",1)
    elif "import Extra132PackedSplitProof" not in text:
        raise ValueError("unexpected target proof import")
    text=text.replace("BB6.Agent44Extra132Giant.table","BB6.Agent44Extra132Packed.p")
    text=text.replace("BB6.Agent44Extra132Giant.weighted","BB6.Agent44Extra132Packed.weighted")
    target.write_text(text,encoding="utf-8")
    print("left",len(le),"right",len(re_),"rows",[len(x) for x in rows])
    print("generated",len(list(out.glob("*.lean"))),"modules; patched",target.name)

def main():
    if len(sys.argv)!=3: raise SystemExit("usage: repack_extra132.py SOURCE_DIR OUT_DIR")
    emit(Path(sys.argv[1]).resolve(),Path(sys.argv[2]).resolve())
if __name__=="__main__": main()
