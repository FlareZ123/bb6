#!/usr/bin/env python3
"""Split a generated sparse n-gram row checker at low-bit trie prefixes.

The original certificate, table and final never theorem are unchanged.
Every chunk is checked by Lean; the joining theorem proves exact coverage.
"""
import argparse
from functools import lru_cache
from pathlib import Path
import re

BASE = "BB6.Agent47SparseNGram"
HEADER = """set_option maxRecDepth 100000
set_option maxHeartbeats 0
"""

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("directory", type=Path)
    ap.add_argument("--name", default="Raw115Sparse7")
    ap.add_argument("--chunk", type=int, default=64)
    args = ap.parse_args()
    assert args.chunk > 0
    root, name = args.directory, args.name
    ns = f"{BASE}.{name}"
    data = (root / f"{name}Data.lean").read_text()
    defs = dict((a, (b, c)) for a,b,c in re.findall(
        r"^def (t\d+) : Trie := \.branch (\S+) (\S+)$", data, re.M))
    rows = re.search(r"^def cert : .*#\[([^\]]+)\]", data, re.M)
    assert rows, "missing generated cert row array"
    rows = [s.strip() for s in rows.group(1).split(",")]
    assert len(rows) == 12
    @lru_cache(None)
    def size(node):
        if node == ".empty": return 0
        if node == ".leaf": return 1
        e,o = defs[node]
        return size(e)+size(o)

    def term(node):
        return f"({node} : Trie)" if node.startswith(".") else node

    def write(mod, imports, body):
        (root / f"{mod}.lean").write_text(
            "".join(f"import {x}\n" for x in imports) + HEADER
            + f"namespace {ns}\nopen BB6Coverage BB6.Agent1NGram\n"
            + body + f"\nend {ns}\n")

    join = name + "Join"
    helper = """theorem trie_all_join (f : Nat → Bool) (e o : Trie) (m p : Nat)
    (he : e.all (fun i => f ((2*m)*i+p))=true)
    (ho : o.all (fun i => f ((2*m)*i+(p+m)))=true) :
    (Trie.branch e o).all (fun i => f (m*i+p))=true := by
  have h1 : (fun i : Nat => f (m*(2*i)+p)) = (fun i : Nat => f ((2*m)*i+p)) := by
    funext i; congr 1; ac_rfl
  have h2 : (fun i : Nat => f (m*(2*i+1)+p)) = (fun i : Nat => f ((2*m)*i+(p+m))) := by
    funext i; congr 1; simp only [Nat.mul_add,Nat.mul_one]; ac_rfl
  simp only [Trie.all,h1,h2,he,ho,Bool.and_self]
"""
    for j in range(12):
        q,a=j//2,str(bool(j%2)).lower()
        helper += (f"def rowStep{j:02} (i : Nat) : Bool :=\n"
                   f"  {BASE}.stateStepOK table cert {q} {a} (i/2^(cert.n+1)) (i%2^(cert.n+1))\n")
    write(join,[name+"Data"],helper)
    total_chunks = 0
    for j,node in enumerate(rows):
        q,a=j//2,str(bool(j%2)).lower()
        f=f"rowStep{j:02}"
        imports, assembly = [join], []
        idx=0
        def emit(t,m,p):
            nonlocal idx,total_chunks
            k=idx; idx+=1
            theorem=f"splitRow{j:02}_{k:04}"
            ty=f"{term(t)}.all (fun i => {f} ({m}*i+{p})) = true"
            if size(t)<=args.chunk:
                if size(t)==0:
                    assembly.append(f"theorem {theorem} : {ty} := by rfl")
                else:
                    mod=f"{name}Chunk{j:02}_{k:04}"
                    write(mod,[join],f"theorem {theorem} : {ty} := by decide +kernel\n")
                    imports.append(mod);total_chunks+=1
            else:
                e,o=defs[t]
                he=emit(e,2*m,p)
                ho=emit(o,2*m,p+m)
                assembly.append(f"theorem {theorem} : {ty} :=\n"
                    f"  trie_all_join {f} {term(e)} {term(o)} {m} {p} {he} {ho}")
            return theorem
        result=emit(node,1,0)
        assembly.append(f"theorem row{j:02} : ({BASE}.row cert {q} {a}).all (fun i =>\n"
            f"    {BASE}.stateStepOK table cert {q} {a} (i/2^(cert.n+1)) (i%2^(cert.n+1))) = true := by\n"
            f"  simpa only [Nat.one_mul,Nat.add_zero,{f}] using {result}")
        write(f"{name}Row{j:02}",imports,"\n\n".join(assembly)+"\n")
        print(f"row {j:02}: {size(node)} states, {len(imports)-1} chunks",flush=True)
    print(f"{sum(map(size,rows))} states, {total_chunks} chunks",flush=True)

if __name__ == "__main__":
    main()
