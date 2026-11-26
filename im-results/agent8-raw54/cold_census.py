#!/usr/bin/env python3
"""Regenerate exact cold-child census and the 0LF sparse proof modules.
Run from the repository root. No search result is trusted by Lean."""
import hashlib
import subprocess as sp
import sys
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OUT = HERE / "cold-generated"
OUT.mkdir(exist_ok=True)
NGRAM = ROOT / "im-results/agent47-raw111-cut"
sys.path.insert(0, str(NGRAM))
from emit_sparse import emit
ENUM = ROOT / "im-results/agent47-raw112-cut/enumerate_fast.cpp"
BANK = ROOT / "im-results/agent8-tnf-six/bank.cpp"
BANK_DATA = HERE / "bank.txt"
def build(src, target):
    sp.run(["g++", "-std=c++17", "-O3", str(src), "-o", str(target)], check=True)
def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    build(ENUM, OUT/"enumerate")
    build(BANK, OUT/"bank")
    build(NGRAM/"ngram_sparse.cpp", OUT/"ngram")
    for mv, expected in {
        "0LF": ("375c5f5cc4ce825594a94feea4e9bac832eeaab851168d0fa8821c68e939910d","d013ba549e3284f18092fd34491eb5e1cfc3cd262ea0a8d36c9ea9e6e823771b"),
        "0RB": ("831a2c2f191c3161d3dd0956622384013f0c6b18ab0cd7f096bc73b4bbb9e616","92711eb390829f5984a729938926d5b07f3285e6a43a8c96bf933cf37dfa2e60"),
        "0RF": ("de819b98d929ce3b47ba67b55da83fe362f64dc1ae549e3ff1f41a345f84e40f","88cd217d844add1424fa01a25c4404a48cd0ead2e077084bc24a6e4d2c7a45e6"),
        "1RA": ("7a5b361c09d3f0f8be56947baa6390bd1f0617bac39a26bddc8495e3badb9b99","5b92ebb47de7e0e1edc4eb3acb2fbcc5b0956856b283a87dd93f0a928511e0da"),
    }.items():
        d = OUT/mv
        d.mkdir(exist_ok=True)
        machine = "1RB---_1RC---_0RD---_1LD0LE_"+mv+"0LE_------"
        with (d/"census.txt").open("w") as f:
            sp.run([str(OUT/"enumerate"), machine],cwd=d,stdout=f,check=True)
        assert digest(d/"open.txt")==expected[0]
        with (d/"far.txt").open("w") as f:
            sp.run([str(OUT/"bank"),str(BANK_DATA),str(d/"open.txt")],stdout=f,check=True)
        found={int(l.split(":")[0]) for l in (d/"far.txt").read_text().splitlines()}
        rows=(d/"open.txt").read_text().splitlines()
        misses=[m for i,m in enumerate(rows) if i not in found]
        (d/"miss.txt").write_text("".join(m+"\n" for m in misses))
        assert digest(d/"miss.txt")==expected[1], (mv,digest(d/"miss.txt"))
        print(mv,len(rows),len(found),len(misses),flush=True)
    rows=(OUT/"0LF/miss.txt").read_text().splitlines()
    for line in (HERE/"zeroLF-ngram.txt").read_text().splitlines():
        i,k,n,l,r=map(int,line.split())
        result=sp.check_output([str(OUT/"ngram"),str(k)],input=f"{i} {rows[i]}\n",text=True)
        ident,data=result.split(maxsplit=1)
        assert int(ident)==i
        emit(OUT,i,rows[i],data,width=k,module_name=f"Raw54ZeroLFSparse{i}",expected=(n,l,r))
if __name__=="__main__":
    main()
