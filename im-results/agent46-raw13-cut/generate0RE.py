#!/usr/bin/env python3
"""Generate a standalone, complete, mixed-bound D1=0RE parent certificate."""
from collections import Counter
from itertools import product
from pathlib import Path
import subprocess
import tempfile
import json
from generate import D, MOVES, DECODE, tally, emit, move, write

RAW = "1RB1LC1RC0LD1LA0RB1LB0RE------------"
NS = "BB6.Agent46Raw13ZeroRE"
GRAM = NS + "Gram"
HEADER = """set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13ZeroRE
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent46CanonicalCut
"""
def output(name, imports, body):
    (D/(name+".lean")).write_text("".join(f"import {i}\n" for i in imports)+HEADER+body+"\nend "+NS+"\n",encoding="utf-8")
def main():
    ng = D.parent/"agent1-ngram"
    with tempfile.TemporaryDirectory() as temp:
        temp = Path(temp)
        exe = temp/"selected"
        subprocess.run(["g++","-std=c++17","-O3",str(D/"select_complete.cpp"),"-o",str(exe)],check=True)
        r = subprocess.check_output([str(exe)],input=RAW+" 5 4\n",text=True)
        raw,data = r.strip().split(" ",1)
        assert raw == RAW
        tree = json.loads(data)
        c,m = Counter(),Counter()
        tally(tree,4,5,c,m)
        assert tree[:3] == ["split",22,8]
        assert c == Counter(split=60,halt=60,cycle=609,state=80,last=339,ngram=347,pump0RE=5,late0RE=1),c
        assert sum(m.values()) == 25**4,m
        grams=[]
        def collect(t):
            if t[0]=="ngram": grams.append(t[1])
            elif t[0]=="split":
                for ch in t[3]:
                    if ch is not None: collect(ch)
        collect(tree)
        assert len(set(grams))==len(grams)==347
        data=temp/"tables.txt"
        ids={raw:i for i,raw in enumerate(grams)}
        data.write_text("".join(f"{i} {raw}\n" for raw,i in ids.items()))
        exe=temp/"ngram"
        subprocess.run(["g++","-std=c++17","-O3",str(ng/"ngram.cpp"),"-o",str(exe)],check=True)
        certs=temp/"certs.txt"
        with data.open() as inp,certs.open("w") as out:
            subprocess.run([str(exe),"7"],stdin=inp,stdout=out,check=True)
        lines=certs.read_text().splitlines()
        assert len(lines)==347
        modules=[]
        for i in range(0,len(lines),16):
            name=f"Agent46Raw13ZeroREGram{i//16}"
            modules.append(name)
            shard=temp/"shard.txt"
            shard.write_text("\n".join(lines[i:i+16])+"\n")
            subprocess.run(["python",str(ng/"emit_ngram.py"),str(data),str(shard),str(D/(name+".lean")),"--namespace",GRAM],check=True)
        def norm(t):
            if t is None: return None
            if t[0]=="ngram": return ("selectedgram",ids[t[1]])
            if t[0]=="split": return ("split",t[1],t[2],[norm(ch) for ch in t[3]])
            return t
        kids=[]
        for i,t in enumerate(tree[3]):
            name=f"Agent46Raw13ZeroREKid{i:02}"
            kids.append(name)
            body=emit(norm(t)).replace("BB6.Agent46Raw13SelectedGram",GRAM)
            mv=move(MOVES[i])
            output(name,["Agent46Raw13ZeroREBase","Agent46Raw13Pump0RE","Agent46Raw13Late0RE"]+modules,f"""
def kid{i:02} : Cut := {body}
theorem checked{i:02} : check 21269 (next {mv}) (nextCut 5 {mv}) kid{i:02} = true := by decide
""")
        terms=",".join(f"kid{i:02}" for i in range(24))
        cases="\n".join(f"  · exact checked{12*w+6*r+q:02}" for q,w,r in product(range(6),range(2),range(2)))
        output("Agent46Raw13ZeroRE",kids,f"""
def kids : Move → Cut := byCutMove [{terms}]
theorem kids_checked (mv : Move) :
    check 21269 (next mv) (nextCut 5 mv) (kids mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{cases}

def parentCut : Cut := .split 22 (4,false) kids
theorem parent_checked : check 21269 parent 5 parentCut = true := by
  change (BB6.Agent10ZipAudit.zipQueryOK 21269 parent 22 (4,false) &&
    BB6.Agent31ThreeHole.allMoves (fun mv =>
      if mv.next.val ≤ 5 then check 21269 (next mv) (nextCut 5 mv) (kids mv)
      else true)) = true
  simp only [Bool.and_eq_true]
  refine ⟨by decide, BB6.Agent31ThreeHole.allMoves_of _ ?_⟩
  intro mv
  have h : mv.next.val ≤ 5 := by omega
  simp [h,kids_checked mv]

theorem empty_complement : residuals parent 5 parentCut = [] := by decide

theorem bound (m : Machine) (hm : compatible parent m) : WeightedBound 21269 m := by
  rcases sound 21269 parent 5 parentCut (by decide) parent_support (by decide)
      parent_nohalt parent_checked m (compatible_quotient m hm) with hb | ⟨e,he,hq⟩
  · exact hb
  · rw [empty_complement] at he
    simp at he

#print axioms parent_checked
#print axioms empty_complement
#print axioms bound
""")
        print("0RE complete candidate census",dict(c),"mass",dict(m))
if __name__=="__main__":
    main()
