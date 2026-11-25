#!/usr/bin/env python3
"""Generate a standalone, complete, mixed-bound D1=0RE parent certificate."""
from collections import Counter
from itertools import product
from pathlib import Path
import subprocess
import tempfile
import json
from generate import D, MOVES, tally, emit, move
import sys

SPEC = {
    "1RC": ("1RB1LC1RC0LD1LA0RB1RC---------------",4,5,12,7,7014,
            Counter(split=225,halt=225,cycle=3426,state=336,last=1189,ngram=173,oneRCHard=48),
            ["Agent46Raw13Auto1RC"]),
    "1RE": ("1RB1LC1RC0LD1LA0RB1RE---------------",5,5,7,8,7014,
            Counter(split=1900,halt=1900,cycle=30642,state=1320,last=10274,ngram=1430,oneREHard=35),
            ["Agent46Raw13OneREPumps","Agent46Raw13OneREBinary"]),
    "0RB": ("1RB1LC1RC0LD1LA0RB0RB---------------",4,5,17,7,7014,
            Counter(split=232,halt=232,cycle=2435,state=336,last=1226,ngram=1318,zeroRBHard=18),
            ["Agent46Raw13ZeroRBNested","Agent46Raw13ZeroRBPump009"]),
    "1LC": ("1RB1LC1RC0LD1LA0RB1LC---------------",4,5,10,7,7014,
            Counter(split=222,halt=222,cycle=3657,state=296,last=1003,ngram=129,oneLCHard=18),
            ["Agent46Raw13OneLCPumps","Agent46Raw13OneLCBinary","Agent46Raw13OneLCTernary","Agent46Raw13OneLCNested"]),
    "1LA": ("1RB1LC1RC0LD1LA0RB1LA---------------",4,5,9,7,7014,
            Counter(split=233,halt=233,cycle=3777,state=276,last=1108,ngram=185,oneLAHard=10),
            ["Agent46Raw13OneLAPump","Agent46Raw13OneLAFAR"]),
    "1RA": ("1RB1LC1RC0LD1LA0RB1RA---------------",4,5,9,7,7014,
            Counter(split=374,halt=374,cycle=5988,state=676,last=1848,ngram=79,oneRAHard=8),
            ["Agent46Raw13OneRAPumps","Agent46Raw13OneRAPump303","Agent46Raw13OneRAFAR"]),
    "0RA": ("1RB1LC1RC0LD1LA0RB0RA---------------",4,5,9,7,7014,
            Counter(split=147,halt=147,cycle=2671,state=136,last=495,ngram=67,zeroRAHard=9),
            ["Agent46Raw13ZeroRAPump","Agent46Raw13ZeroRAFAR"]),
    "1RD": ("1RB1LC1RC0LD1LA0RB1RD---------------",4,5,8,7,7014,
            Counter(split=392,halt=392,cycle=6027,state=716,last=2183,ngram=72,auto1RD=15),
            ["Agent46Raw13Auto1RD"]),
    "0RE": ("1RB1LC1RC0LD1LA0RB1LB0RE------------",5,4,22,8,21269,
            Counter(split=60,halt=60,cycle=609,state=80,last=339,ngram=347,pump0RE=5,late0RE=1),
            ["Agent46Raw13Pump0RE","Agent46Raw13Late0RE"]),
    "0RC": ("1RB1LC1RC0LD1LA0RB0RC---------------",4,5,10,7,7014,
            Counter(split=287,halt=287,cycle=4670,state=396,last=1340,ngram=191,pump0RC=1),
            ["Agent46Raw13Pump0RC"]),
    "0LB": ("1RB1LC1RC0LD1LA0RB0LB---------------",4,5,13,7,7014,
            Counter(split=244,halt=244,cycle=3846,state=356,last=1352,ngram=46,pump0LB=9),
            ["Agent46Raw13Pump0LB"]),
    "0LC": ("1RB1LC1RC0LD1LA0RB0LC---------------",4,5,10,7,7014,
            Counter(split=261,halt=261,cycle=4118,state=336,last=1314,ngram=227,pump0LC=5),
            ["Agent46Raw13Pump0LC"]),
    "0RD": ("1RB1LC1RC0LD1LA0RB0RD---------------",4,5,8,7,7014,
            Counter(split=158,halt=158,cycle=2800,state=176,last=630,ngram=20,pump0RD=5),
            ["Agent46Raw13Pump0RD"])
}
BRANCH = sys.argv[1] if len(sys.argv)>1 else "0RE"
RAW,CUT,HOLES,QUERY,QSLOT,BOUND,CENSUS,PROOFS=SPEC[BRANCH]
PREFIX="Agent46Raw13"+("One" if BRANCH[0]=="1" else "Zero")+BRANCH[1:]
NS="BB6."+PREFIX
GRAM=NS+"Gram"
HEADER = f"""set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace {NS}
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
        r = subprocess.check_output([str(exe)],input=f"{RAW} {CUT} {HOLES}\n",text=True)
        raw,data = r.strip().split(" ",1)
        assert raw == RAW
        tree = json.loads(data)
        c,m = Counter(),Counter()
        tally(tree,HOLES,CUT,c,m)
        assert tree[:3] == ["split",QUERY,QSLOT]
        assert c == CENSUS,c
        assert sum(m.values()) == 25**HOLES,m
        grams=[]
        def collect(t):
            if t[0]=="ngram": grams.append(t[1])
            elif t[0]=="split":
                for ch in t[3]:
                    if ch is not None: collect(ch)
        collect(tree)
        assert len(set(grams))==len(grams)==CENSUS['ngram']
        data=temp/"tables.txt"
        far = {}
        far_modules=[]
        if BRANCH in ("0RB","1LC","1RE","1RC"):
            from generatePackedFAR import generate
            far,far_modules=generate(BRANCH,grams)
            assert len(set(grams) & far.keys()) == {"0RB":1313,"1LC":124,"1RE":1424,"1RC":173}[BRANCH]
        if BRANCH == "0RA":
            from generateZeroRAFAR import generate
            far = generate()
            assert len(set(grams) & far.keys()) == 60
        if BRANCH in ("1LA","1RA"):
            from generateOneFAR import generate
            far = generate(BRANCH)
            assert len(set(grams) & far.keys()) == {"1LA":179,"1RA":78}[BRANCH]
        ids={raw:i for i,raw in enumerate(grams) if raw not in far}
        data.write_text("".join(f"{i} {raw}\n" for raw,i in ids.items()))
        exe=temp/"ngram"
        subprocess.run(["g++","-std=c++17","-O3",str(ng/"ngram.cpp"),"-o",str(exe)],check=True)
        certs=temp/"certs.txt"
        with data.open() as inp,certs.open("w") as out:
            subprocess.run([str(exe),"7"],stdin=inp,stdout=out,check=True)
        lines=certs.read_text().splitlines()
        assert len(lines)==len(ids)
        modules=[]
        for i in range(0,len(lines),16):
            name=f"{PREFIX}Gram{i//16}"
            modules.append(name)
            shard=temp/"shard.txt"
            shard.write_text("\n".join(lines[i:i+16])+"\n")
            subprocess.run(["python",str(ng/"emit_ngram.py"),str(data),str(shard),str(D/(name+".lean")),"--namespace",GRAM],check=True)
        def norm(t):
            if t is None: return None
            if t[0]=="ngram":
                if t[1] in far: return ({"0RA":"zeroRAFar","1LA":"oneLAFar","1RA":"oneRAFar","0RB":"zeroRBFar","1LC":"oneLCFar","1RE":"oneREFar","1RC":"oneRCFar"}[BRANCH],far[t[1]])
                return ("selectedgram",ids[t[1]])
            if t[0]=="split": return ("split",t[1],t[2],[norm(ch) for ch in t[3]])
            return t
        kids=[]
        for i,t in enumerate(tree[3]):
            if t is None: continue
            name=f"{PREFIX}Kid{i:02}"
            kids.append(name)
            body=emit(norm(t)).replace("BB6.Agent46Raw13SelectedGram",GRAM)
            mv=move(MOVES[i])
            if BRANCH in ("0RB","1LC","1RE","1RC") or (BRANCH == "1RA" and i in (4,16)):
                from shard_cut import checked_subtree
                tag=f"{i:02}"
                prefix=checked_subtree(t,tag,f"next {mv}",max(CUT,i%6+1),BOUND,
                    lambda tree: emit(norm(tree)).replace("BB6.Agent46Raw13SelectedGram",GRAM))
                output(name,[PREFIX+"Base"]+PROOFS+far_modules+modules,prefix+f"""
def kid{tag} : Cut := c{tag}
theorem checked{tag} : check {BOUND} (next {mv}) (nextCut {CUT} {mv}) kid{tag} = true := ok{tag}
""")
                continue
            output(name,[PREFIX+"Base"]+PROOFS+far_modules+modules,f"""
def kid{i:02} : Cut := {body}
theorem checked{i:02} : check {BOUND} (next {mv}) (nextCut {CUT} {mv}) kid{i:02} = true := by decide
""")
        terms=",".join(f"kid{i:02}" if tree[3][i] is not None else ".unresolved" for i in range(24))
        cases="\n".join(f"  · exact checked{12*w+6*r+q:02}" for q,w,r in product(range(CUT+1),range(2),range(2)))
        hq=" ∨ ".join(f"q = {i}" for i in range(CUT+1))
        alternatives="|".join("rfl" for _ in range(CUT+1))
        from generate import slot
        output(PREFIX,kids,f"""
def kids : Move → Cut := byCutMove [{terms}]
theorem kids_checked (mv : Move) (hv : mv.next.val ≤ {CUT}) :
    check {BOUND} (next mv) (nextCut {CUT} mv) (kids mv) = true := by
  rcases mv with ⟨w,r,q⟩
  change q.val ≤ {CUT} at hv
  have hq : {hq} := by omega
  rcases hq with {alternatives}
  all_goals cases w <;> cases r
{cases}

def parentCut : Cut := .split {QUERY} {slot(QSLOT)} kids
theorem parent_checked : check {BOUND} parent {CUT} parentCut = true := by
  change (BB6.Agent10ZipAudit.zipQueryOK {BOUND} parent {QUERY} {slot(QSLOT)} &&
    BB6.Agent31ThreeHole.allMoves (fun mv =>
      if mv.next.val ≤ {CUT} then check {BOUND} (next mv) (nextCut {CUT} mv) (kids mv)
      else true)) = true
  simp only [Bool.and_eq_true]
  refine ⟨by decide, BB6.Agent31ThreeHole.allMoves_of _ ?_⟩
  intro mv
  by_cases h : mv.next.val ≤ {CUT}
  · simp [h,kids_checked mv h]
  · simp [h]

theorem empty_complement : residuals parent {CUT} parentCut = [] := by decide

theorem bound (m : Machine) (hm : compatible parent m) : WeightedBound {BOUND} m := by
  rcases sound {BOUND} parent {CUT} parentCut (by decide) parent_support (by decide)
      parent_nohalt parent_checked m (compatible_quotient m hm) with hb | ⟨e,he,hq⟩
  · exact hb
  · rw [empty_complement] at he
    simp at he

#print axioms parent_checked
#print axioms empty_complement
#print axioms bound
""")
        print(BRANCH+" complete candidate census",dict(c),"mass",dict(m))
if __name__=="__main__":
    main()
