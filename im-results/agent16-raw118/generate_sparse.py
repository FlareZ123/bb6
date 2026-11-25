"""Generate sparse n-gram proof modules from stable candidate widths."""
from pathlib import Path
from collections import defaultdict
import sys,subprocess,tempfile
ROOT=Path(__file__).resolve().parent
IM=ROOT.parent
sys.path.insert(0,str(IM/"agent47-raw111-cut"))
from emit_sparse import emit
def generate(rows,ng,work):
    exe=work/"ngram_sparse_dump"
    subprocess.run(["g++","-O3","-std=c++17",str(IM/"agent47-raw111-cut/ngram_sparse.cpp"),"-o",str(exe)],check=True)
    groups=defaultdict(list)
    for i,(k,n) in ng.items():groups[k].append((i,n))
    mods=[];claims=[];parts=[];weight=0;group=0
    def flush():
        nonlocal parts,weight,group
        if not parts:return
        name=f"Raw118SparseGroup{group:03}"
        (ROOT/(name+".lean")).write_text("import SparseNGram\n"+"\n".join(parts))
        mods.append(name);parts=[];weight=0;group+=1
    with tempfile.TemporaryDirectory() as tmp:
        temp=Path(tmp)
        for k,group_rows in sorted(groups.items()):
            inp="".join(f"{i} {rows[i]}\n" for i,n in group_rows)
            output=subprocess.check_output([str(exe),str(k)],input=inp,text=True)
            expected=dict(group_rows)
            for line in output.splitlines():
                i,data=line.split(maxsplit=1);i=int(i)
                _,n,L,R,S=data.split();n=int(n);assert n==expected[i]
                def edges(s):return sum(int(v).bit_count() for _,v in (a.split(":") for a in s.rstrip(",").split(",")))
                name,ns=emit(temp,i,rows[i],data,width=k,module_name=f"Raw118Sparse{i}",expected=(n,edges(L),edges(R)))
                claims.append((i,ns))
                files=[name+"Data",*[name+f"Row{j:02}" for j in range(12)],name]
                if n>5000:
                    flush()
                    for f in files:(temp/(f+".lean")).replace(ROOT/(f+".lean"))
                    mods.append(name)
                else:
                    if weight+n>7000:flush()
                    for f in files:
                        text=(temp/(f+".lean")).read_text()
                        parts.append("\n".join(l for l in text.splitlines() if not l.startswith("import "))+"\n")
                    weight+=n
        flush()
    return mods,claims
