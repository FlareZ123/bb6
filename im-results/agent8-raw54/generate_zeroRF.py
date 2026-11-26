"""Generate the complete exact-threshold proof for the Raw54 E0=0RF child."""
from collections import Counter
from pathlib import Path
import argparse, hashlib, json, subprocess, tempfile, sys
from generate_rf_witnesses import ROOT, masks, parse
from generate_ra import Node, zrun, table, refine, all_moves, slot, move, MOVES, fuse_sparse
from generate_rf_run_quotients import run_search, edge_count
from emit_mask import emit_data
sys.path.insert(0,str(ROOT.parent/"agent47-raw111-cut"))
from emit_sparse import emit
PARENT="1RB---_1RC---_0RD---_1LD0LE_0RF0LE_------"
BOUND=402
NS="BB6.Agent8Raw54.ZeroRF"
HEADER="""set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace BB6.Agent8Raw54.ZeroRF
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
open BB6Coverage.Agent50Zipper BB6Coverage.Agent31Pump BB6.Agent48PrefixAudit
"""
def write(name, imports, body):
    (ROOT/(name+".lean")).write_text("".join("import "+m+"\n" for m in sorted(set(imports)))+HEADER+body+"\nend "+NS+"\n")

def emit_tree(node,p,expr,name,t,threshold):
    mod="Raw54ZeroRFShard"+name.removeprefix("zeroRFShard").replace("_","X")
    imports={"Raw54ZeroRFBase"}
    body=[]
    def local(n,c,p2,e2,prefix):
        imports.update(c.deps)
        body.extend([
            f"def {n} : Audit := {c.term()}",
            f"def {n}Table : PartialMachine := {table(p2)}",
            f"theorem {n}Table_eq : {n}Table = ({e2}) := tableOK_sound _ _ (by decide)",
            f"def {n}Prefix : Z := {zrun(p2,prefix)}",
            f"theorem {n}_checked : zipCheck {BOUND} ({e2}) {n} = true := by",
            f"  rw [← {n}Table_eq, ← checkAt_eq {BOUND} {n}Table {n} {prefix} {n}Prefix (by rfl)]",
            "  decide"])
    if node.size<=threshold or not node.children:
        local(name,node,p,expr,t)
    else:
        names=[]
        for j,c in enumerate(node.children):
            cn=f"{name}_{j:02d}"
            p2=refine(p,node.s,MOVES[j])
            e2=f"refine ({expr}) {slot(node.s)} (some {move(MOVES[j])})"
            if c.size>threshold:
                imports.add(emit_tree(c,p2,e2,cn,node.n,threshold))
            else:local(cn,c,p2,e2,node.n)
            names.append(cn)
        kids="byMove ["+", ".join(names)+"]"
        body.extend([
            f"def {name} : Audit := .split {node.n} {slot(node.s)} ({kids})",
            f"theorem {name}_checked : zipCheck {BOUND} ({expr}) {name} = true := by",
            f"  change (zipQueryOK {BOUND} ({expr}) {node.n} {slot(node.s)} && allMoves (fun mv => zipCheck {BOUND} (refine ({expr}) {slot(node.s)} (some mv)) ({kids} mv))) = true",
            "  simp only [Bool.and_eq_true]",
            "  refine ⟨by decide, allMoves_of _ ?_⟩",
            all_moves([n+"_checked" for n in names])])
    write(mod,imports,"\n".join(body))
    return mod


# Frozen miss indices grouped by accepting DFA code; search is untrusted.
FAR_GROUPS="""00102334101 74 83 133 256
00102340130 29 33 37 148 169 198
00102340133 147 168
0010234014555 15 27 31 35 56 70 100 104 117 125 140 159 175 178 186 193 196
0010301450123 55 57 76 77 85 86 126 128 207 208 260 261
00105c946663264a84761473101 18 19 46 48 50 51 59 63 78 79 87 88 221 222 225 228 262 264 275 276 290 291 295 298 313
00105c946663264a8476b473101 246 253 316 318
001230120 335
00123014001 54 336 337 338 339 340 341 342 343
0012301450123 333
0012322422521 26 30 34 115 136 155 174 177 192 195
0012322452102 143 162
0013203345555 129
0013501334324 188
00145c946663264a84762473101 22 40 61 73 82 110 123 180 215 223 226 236 255 257 309 311 315 321 323 327
00185c946663264a84760473101 58 62 75 81 84 90 206 211 216 217 218 220 224 227 258 263 266 267 272 273 279 280 287 288 294 299 301 306 308 310 312 322 328 329 330 332
002356533818166664737 8
00414570213666612 121 199
005052524130422 127
005252216132422 137 152 156
005492139366843262736 303
005962722258124332527 334
006040232441345 324
00606060044170523 134 135 144 145 151 154 163 166 172 325
00606062344170526 94 99 103 116 120 139 142 149 158 161 164 165 170
00606462045171723 344 346 347 348
006c3280a7a28518888417889b6 184 296
0070752140787555387 52 53
008525576197555526438 21 23 24 39 41 42 108 109 111 112 122 181 209 212 214 231 233 235 238 240 241 242 243 244 245 247 250 251 269 271 277 282 284 286 292 304 317 320
008525578197555526438 95 97 203 205
00a02557619755552603804 191
00a02557619755552693804 102 105 132 187 189 213
00a51b8dbef5751fg8451032828f946eeg1 101
00a52557619755552603824 201 202 305
00f8244ebec27e4cc215d8d4ac63a6649 93 98 190
00f8244ece827e4c4213a5b0ac6ca6649 326
00f8244ece827e4c4213a5d0ac6ca6649 14 16 20 25 38 43 44 45 47 49 60 64 68 71 80 89 107 113 114 124 131 173 182 210 219 229 230 232 234 237 248 249 252 254 259 265 268 270 274 278 281 283 285 289 293 297 300 302 307 314 319 331
00f8244ece827e4cc215dbd4ac6ca6649 0 1
00f8244ecec27e4c9215d8d4ac63a6649 17 28 32 36 69 72 106 118 119 138 141 146 150 153 157 160 167 171 176 179 194 197
00f8b44ecec27e4cc215d8d4ac6ca6649 2
1084773322887712365 6"""
NGRAM="""3 7 420 34 46
4 4 392 20 22
5 6 130 22 26
7 9 895 161 34
11 14 367 44 48
65 8 171 21 28
66 5 214 23 21
92 5 172 20 17
96 5 172 20 17
183 8 154 16 26
239 6 142 14 18"""
RUN="""9 4 4 6 4 6 4 4 6 4 6 656 37 65 116
10 4 4 6 4 6 4 4 6 4 6 656 37 65 116
12 4 4 6 4 6 4 4 6 4 6 663 37 63 114
67 3 4 2 4 2 3 4 2 4 2 375 14 63 101
91 3 4 3 4 3 3 4 3 4 3 182 14 28 50
130 3 4 2 4 2 3 4 2 4 2 645 11 83 142
185 3 4 2 4 2 3 4 2 4 2 368 12 58 94
200 2 4 2 4 2 2 4 2 4 2 217 10 26 48
204 3 4 2 4 2 3 4 2 4 2 444 14 57 95
345 5 4 4 4 4 5 4 4 4 4 722 18 175 224"""
def collect(work):
    for folder,src,name in [
        ("agent47-raw112-cut","enumerate_fast.cpp","enumerate"),
        ("agent8-tnf-six","bank.cpp","bank"),
        ("agent47-raw111-cut","ngram_sparse.cpp","ngram")]:
        subprocess.run(["g++","-O3","-std=c++17",str(ROOT.parent/folder/src),"-o",str(work/name)],check=True)
    subprocess.run([str(work/"enumerate"),PARENT],cwd=work,check=True)
    raw=(work/"open.txt").read_bytes()
    assert hashlib.sha256(raw).hexdigest()=="de819b98d929ce3b47ba67b55da83fe362f64dc1ae549e3ff1f41a345f84e40f"
    rows=raw.decode().splitlines()
    assert len(rows)==len(set(rows))==1994
    found=dict((int(i),c) for i,c in (l.split(":") for l in subprocess.check_output(
        [str(work/"bank"),str(ROOT/"bank.txt"),str(work/"open.txt")],text=True).splitlines()))
    assert len(found)==1645
    misses=[row for j,row in enumerate(rows) if j not in found]
    assert hashlib.sha256(("\n".join(misses)+"\n").encode()).hexdigest()=="88cd217d844add1424fa01a25c4404a48cd0ead2e077084bc24a6e4d2c7a45e6"
    certs,deps={},{}
    def put(row,proof,mod=None):
        assert row not in certs,("duplicate",row)
        certs[row]=proof
        if mod:deps[row]=mod
    def proved(i,mod,ns,arg=""):
        put(misses[i],f".proven ({ns}.table{arg}) ({ns}.never{arg})",mod)
    far={rows[j]:c for j,c in found.items()}
    for line in FAR_GROUPS.splitlines():
        code,*indices=line.split()
        for i in map(int,indices):
            assert misses[i] not in far
            far[misses[i]]=code
    assert len(far)==1972
    for row,code in far.items():
        d,D,L,R,z=masks(parse(row),int(code[0]),[int(c,36) for c in code[1:]])
        put(row,f".far {str(code[0]=='1').lower()} {d} ⟨0,{D},{L},{R},{z}⟩")
    for line in NGRAM.splitlines():
        i,k,n,l,r=map(int,line.split())
        res=subprocess.check_output([str(work/"ngram"),str(k)],input=f"{i} {misses[i]}\n",text=True)
        ident,data=res.split(maxsplit=1)
        assert int(ident)==i
        mod,ns=emit(ROOT,i,misses[i],data,width=k,module_name=f"Raw54ZeroRFSparse{i}",expected=(n,l,r))
        fuse_sparse(ROOT,mod)
        proved(i,mod,ns)
    for line in RUN.splitlines():
        i,*tail=map(int,line.split())
        params=tuple(tail[:10]);n,l,r,e=tail[10:]
        D,N,info=run_search(misses[i],params)
        assert D is not None,(i,N,info)
        E,S=info
        assert (N,len(D[0])//2,len(D[1])//2,edge_count(E))==(n,l,r,e),i
        mod=f"Raw54ZeroRFRun{i}"
        emit_data(ROOT,mod,misses[i],D,E,S)
        proved(i,mod,"BB6.Agent32AsymNGram."+mod)
    assert misses[13]=="1RB0RB_1RC1RE_0RD1RA_1LD0LE_0RF0LE_1LB---"
    proved(13,"Raw54ZeroRF13","BB6.Agent8Raw54.ZeroRF13")
    assert set(certs)==set(rows),[i for i,row in enumerate(misses) if row not in certs]
    assert len(deps)==22
    return json.loads((work/"tree.json").read_text()),certs,deps
def assemble(tree,certs,deps,threshold):
    stats=Counter()
    root=Node(tree,certs,deps,stats)
    assert stats==Counter(split=1837,cycle=31881,last=8377,open=1994),stats
    write("Raw54ZeroRFBase",["Raw54ZeroRFLate"],"""abbrev parent : PartialMachine := BB6.Agent8Raw54.ZeroRFLate.parent
theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := BB6.Agent8Raw54.ZeroRFLate.parent_root
theorem parent_nohalt : weightedTNFNoAssignedHalt parent := BB6.Agent8Raw54.ZeroRFLate.parent_nohalt""")
    mod=emit_tree(root,parse(PARENT),"parent","zeroRFShardRoot",0,threshold)
    write("Raw54ZeroRFCut",[mod,"Raw54ZeroRFLate"],f"""theorem checked : zipCheck {BOUND} parent zeroRFShardRoot = true := zeroRFShardRoot_checked
theorem cover : ∀ m, compatible parent m → WeightedBound {BOUND} m :=
  (certifiedZip {BOUND} parent zeroRFShardRoot parent_root parent_nohalt checked).sound
theorem lower_bound402 (B : Nat) (h : ∀ m, compatible parent m → WeightedBound B m) : {BOUND} ≤ B := by
  obtain ⟨m, hm, hh, hd⟩ := BB6.Agent8Raw54.ZeroRFLate.M402.attained
  have hb := h m hm 401 0 hh hd
  omega
theorem exact_threshold (B : Nat) : (∀ m, compatible parent m → WeightedBound B m) ↔ {BOUND} ≤ B := by
  constructor
  · exact lower_bound402 B
  · intro h m hm k d hk hd
    exact Nat.le_trans (cover m hm k d hk hd) h
#print axioms cover
#print axioms exact_threshold""")
    print(stats,"root module",mod,"shards",len(list(ROOT.glob("Raw54ZeroRFShard*.lean"))),flush=True)
def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--threshold",type=int,default=50)
    a=ap.parse_args()
    assert a.threshold>0
    with tempfile.TemporaryDirectory() as d:
        tree,certs,deps=collect(Path(d))
        assemble(tree,certs,deps,a.threshold)
if __name__=="__main__":main()
