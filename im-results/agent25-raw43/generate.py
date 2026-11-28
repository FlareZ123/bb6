"""Produce the Raw43 B1=0RE E1=0LE five-hole audit using existing exact checkers."""
from pathlib import Path
from collections import Counter
from itertools import product
import hashlib, json, os, re, subprocess, sys, tempfile

ROOT = Path(__file__).resolve().parent
IM = ROOT.parent
VARIANT = sys.argv[1] if len(sys.argv) > 1 else "default"
B1C1 = re.fullmatch(r"b([01][lr][a-f])_([ac]|e1?)([01][lr][a-f])", VARIANT)
assert VARIANT == "default" or re.fullmatch(r"[01][lr][a-f]", VARIANT) or B1C1
OUT = ROOT / ("generated" if VARIANT == "default" else "generated_"+VARIANT)
OUT.mkdir(exist_ok=True)
sys.path[:0] = [str(IM/x) for x in (
    "agent31-three-hole-tnf", "agent10-tnf-multipump", "agent1-ngram",
    "agent32-raw59")]
from generate_four_hole import masks, move, slot
from emit_ngram import emit as emit_ngram
from emit_rungram import emit as emit_bidfa

S = json.loads((ROOT/("spec.json" if VARIANT == "default" else f"spec_{VARIANT}.json")).read_text())
B = S.get("bound", 75)
MOVES = [w+d+q for w,d,q in product("01","LR","ABCDEF")]
SUFFIX = VARIANT.upper() if B1C1 else {"default":"", "0rd":"RD", "1rd":"RD1"}.get(VARIANT, "E"+VARIANT.upper())
NS = "BB6.Agent25Raw43" + SUFFIX
PREFIX = "Raw43" + SUFFIX
CHUNK = 240
SHARD = 5000
BIDFA_BATCH = max(1, int(os.environ.get("RAW43_BIDFA_BATCH", "1")))

# Exact local-window replacement for the dominant B1RE/E1=1LE BiDFA outlier.
# The candidate search is untrusted: emit_ngram produces a certificate that Lean
# rechecks through NGramCertificate.check.  Width 12 is the first successful
# symmetric local-window closure for residual 3 (4416 abstract states), replacing
# the previous 47353-state BiDFA certificate.
MACRO_OVERRIDES = {
    "b1le_e0ra": {
        192: (
            "1RB1LF_1RC1LE_0RD0RC_1LD0RB_0RA---_0LA1LB",
            "Raw43B1LEE0RAMacro",
            "BB6.Agent38Raw43B1LEE0RA.table",
            "BB6.Agent38Raw43B1LEE0RA.never",
        ),
    },
}

NGRAM_OVERRIDES = {
    "b1re_e11le": {3: 12},
    # Seven exact local-window closures in B1LE/E1=1RB.  Residual 175 is the
    # material one: width 1 replaces a 3643-state BiDFA.  The remaining six
    # are small but strictly cheaper and use the same already-accepted checker.
    "b1le_e1rb": {175: 1, 475: 1, 679: 6, 685: 1, 725: 1, 775: 1, 885: 1},
    # Seven E0LF leaves save 7144 BiDFA states in total.  All are exact
    # first-success widths from the same NGram checker.
    "b1le_e0lf": {385: 1, 395: 1, 785: 1, 795: 1, 845: 1, 895: 1, 1151: 1},
}

def emit(name, imports, body, namespace=NS, opens=None):
    if opens is None:
        opens = ("BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath "
                 "BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit")
    (OUT/(name+".lean")).write_text(
        "".join("import "+x+"\n" for x in imports)
        + "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n"
        + f"namespace {namespace}\nopen {opens}\n"
        + body + f"\nend {namespace}\n")

def emit_bidfa_batch(name, entries, symmetry_entries=()):
    opens = "BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1NGram BB6.Agent32FastBiDFA"
    imports = ["FastBiDFA"]
    if symmetry_entries:
        imports += ["WeightedSymmetry", "WeightedTNF"]
    parts = ["".join("import "+x+"\\n" for x in imports)
             + "set_option maxRecDepth 100000\\nset_option maxHeartbeats 0\\n"]
    for namespace, body in entries:
        parts.append(f"namespace {namespace}\\nopen {opens}\\n{body}\\nend {namespace}\\n")
    sym_opens = opens + " BB6.Agent13BlankDelay BB6.Agent16WeightedSymmetry"
    for namespace, body in symmetry_entries:
        parts.append(f"namespace {namespace}\\nopen {sym_opens}\\n{body}\\nend {namespace}\\n")
    (OUT/(name+".lean")).write_text("".join(parts))

def swap_ef_table(table):
    """Rename states E and F in both source rows and transition targets."""
    flat = table.replace("_", "")
    assert len(flat) == 36
    perm = [0, 1, 2, 3, 5, 4]
    old = [flat[3*i:3*i+3] for i in range(12)]
    new = ["---"] * 12
    for q in range(6):
        for a in range(2):
            tr = old[2*q+a]
            if tr != "---":
                tr = tr[:2] + chr(ord("A") + perm[ord(tr[2])-ord("A")])
            new[2*perm[q]+a] = tr
    return "_".join("".join(new[2*q:2*q+2]) for q in range(6))

def partial_table_source(table):
    flat = table.replace("_", "")
    rows = [flat[3*i:3*i+3] for i in range(12)]
    out = ["def table : PartialMachine := fun s =>", "  match s.1.val,s.2 with"]
    for j,tr in enumerate(rows):
        if tr == "---":
            continue
        write = str(tr[0] == "1").lower()
        right = str(tr[1] == "R").lower()
        nxt = ord(tr[2]) - ord("A")
        out.append(f"  | {j//2},{str(bool(j%2)).lower()} => some (some ⟨{write},{right},{nxt}⟩)")
    out.append("  | _,_ => none")
    return "\\n".join(out)

def symmetry_never_body(i, table, rep_i, rep_namespace):
    return f"""namespace M{i}
{partial_table_source(table)}
private abbrev ef : StatePerm := swapStates (4 : Fin 6) 5
theorem renamed_table :
    renamePartial ef table = {rep_namespace}.M{rep_i}.table := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide +kernel
private theorem rename_never_back (e : StatePerm) (hroot : e.forward (0 : Fin 6) = 0)
    (m : Machine) (h : NeverHalts (renameTable e m)) : NeverHalts m := by
  intro n
  have hrun : run (renameTable e m) n blank =
      (run m n blank).map (renameConfig e) := by
    simpa [renameConfig,blank,hroot] using rename_run e m blank n
  have hn := h n
  rw [hrun] at hn
  cases hr : run m n blank with
  | none => simp [hr] at hn
  | some d => simp [hr]
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  have hc := rename_compatible ef hm
  rw [renamed_table] at hc
  have hn := {rep_namespace}.M{rep_i}.never (renameTable ef m) hc
  exact rename_never_back ef (by decide +kernel) m hn
#print axioms renamed_table
#print axioms never
end M{i}"""

def compile_cpp(src, out):
    subprocess.run(["g++","-std=c++20","-O3",str(src),"-o",str(out)],check=True)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def generate():
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        compile_cpp(IM/"agent2-tnf-raw124/fast_partition.cpp",work/"enumerate")
        prefix=work/"tree"
        subprocess.run([str(work/"enumerate"),S["table"],str(S["cap"]),str(S["lookback"]),str(prefix)],check=True)
        raw=prefix.with_suffix(".open").read_bytes()
        treebytes=prefix.with_suffix(".json").read_bytes()
        if "openSHA256" in S:
            assert digest(raw)==S["openSHA256"]
        if "treeSHA256" in S:
            assert digest(treebytes)==S["treeSHA256"]
        rows=raw.decode().splitlines()
        assert len(rows)==len(set(rows))==S.get("stats", {"open":52})["open"]
        if "openRows" in S:
            assert rows == S["openRows"]
        tree=json.loads(treebytes)
        assert tree[:3]==S.get("rootQuery", ["split",8,8])
        index={row:i for i,row in enumerate(rows)}
        cert={}
        modules={}
        for key,code in S["witnesses"].items():
            i=int(key)
            p=tuple(rows[i].replace("_","")[j:j+3] for j in range(0,36,3))
            d,D,L,R,z=masks(p,int(code[0]),[int(c,36) for c in code[1:]])
            cert[i]=f".far {str(code[0]=='1').lower()} {d} ⟨0,{D},{L},{R},{z}⟩"
        for key,table in S["growth"].items():
            i=int(key)
            if isinstance(table,dict):
                assert rows[i]==table["table"]
                cert[i]=f'.proven {table["partial"]} {table["never"]}'
                modules[i]=table["module"]
            else:
                assert rows[i]==table
                cert[i]=".proven BB6.Agent25Raw43M29.table BB6.Agent25Raw43M29.never"
                modules[i]="Raw43M29"

        macro_overrides = MACRO_OVERRIDES.get(VARIANT, {})
        for i,(expected,module,partial,never) in sorted(macro_overrides.items()):
            assert rows[i] == expected
            cert[i] = f".proven {partial} {never}"
            modules[i] = module
            print(
                f"macro override {VARIANT} residual {i}: {module}",
                flush=True,
            )

        ngram_overrides = NGRAM_OVERRIDES.get(VARIANT, {})
        if ngram_overrides:
            ngram_bin = work/"ngram"
            compile_cpp(IM/"agent1-ngram/ngram.cpp", ngram_bin)
            for i,width in sorted(ngram_overrides.items()):
                proc = subprocess.run(
                    [str(ngram_bin), str(width)],
                    input=f"{i} {rows[i]}\n",
                    text=True,
                    capture_output=True,
                    check=True,
                )
                line = proc.stdout.strip()
                found_i, ngram_cert = line.split(maxsplit=1)
                assert int(found_i) == i
                found_width = int(ngram_cert.split()[0])
                assert found_width == width
                name = PREFIX+"NGram"+str(i)
                namespace = NS+"NGram"+str(i)
                body = emit_ngram(str(i), rows[i], ngram_cert)
                emit(
                    name, ["NGramCertificate"], body, namespace,
                    "BB6Coverage BB6.Agent1NGram",
                )
                cert[i] = f".proven {namespace}.p{i} {namespace}.never{i}"
                modules[i] = name
                print(
                    f"ngram override {VARIANT} residual {i}: width {width}",
                    flush=True,
                )

        bidfa_pending=[]
        bidfa = {int(key): leaf for key,leaf in S.get("bidfa",{}).items()}
        symmetry_mate = {}
        if VARIANT == "b1la_a0la":
            by_table = {leaf["table"]: i for i,leaf in bidfa.items()}
            for i,leaf in bidfa.items():
                mate = by_table.get(swap_ef_table(leaf["table"]))
                assert mate is not None and mate != i
                assert swap_ef_table(bidfa[mate]["table"]) == leaf["table"]
                symmetry_mate[i] = mate
            reps = [i for i in bidfa if i < symmetry_mate[i]]
            assert len(bidfa) == 88 and len(reps) == 44
            print("B1LA A0LA E/F symmetry: 88 BiDFA leaves -> 44 representatives", flush=True)

        done_bidfa=set()
        for i in sorted(bidfa):
            if i in done_bidfa or i in ngram_overrides or i in macro_overrides:
                continue
            leaf=bidfa[i]
            assert rows[i]==leaf["table"]
            mate = symmetry_mate.get(i)
            if mate is not None:
                rep=min(i,mate)
                partner=max(i,mate)
                if i != rep:
                    continue
                assert rows[partner] == bidfa[partner]["table"]
            else:
                rep=i
                partner=None

            name=PREFIX+"BiDFA"+str(rep)
            namespace=NS+"BiDFA"+str(rep)
            body=emit_bidfa(rep,rows[rep],*leaf["dfa"],[leaf["states"],leaf["edges"]])
            cert[rep]=f".proven {namespace}.M{rep}.table {namespace}.M{rep}.never"
            sym_entry=None
            if partner is not None:
                partner_namespace=NS+"BiDFA"+str(partner)
                partner_body=symmetry_never_body(partner, rows[partner], rep, namespace)
                cert[partner]=f".proven {partner_namespace}.M{partner}.table {partner_namespace}.M{partner}.never"
                sym_entry=(partner_namespace,partner_body)
                done_bidfa.add(partner)
            done_bidfa.add(rep)

            if BIDFA_BATCH == 1:
                emit_bidfa_batch(name,[(namespace,body)],[] if sym_entry is None else [sym_entry])
                modules[rep]=name
                if partner is not None:
                    modules[partner]=name
            else:
                bidfa_pending.append((rep,namespace,body,partner,sym_entry))

        if BIDFA_BATCH > 1:
            for off in range(0,len(bidfa_pending),BIDFA_BATCH):
                chunk=bidfa_pending[off:off+BIDFA_BATCH]
                name=PREFIX+"BiDFABatch"+str(off//BIDFA_BATCH)
                emit_bidfa_batch(
                    name,
                    [(namespace,body) for _,namespace,body,_,_ in chunk],
                    [sym for *_,sym in chunk if sym is not None],
                )
                for i,_,_,partner,_ in chunk:
                    modules[i]=name
                    if partner is not None:
                        modules[partner]=name
        for key,leaf in S.get("lateLast",{}).items():
            i=int(key)
            assert rows[i]==leaf["table"]
            cert[i]=f'.last {leaf["n"]} {slot(leaf["s"])}'
        for key,leaf in S.get("lateCycle",{}).items():
            i=int(key)
            assert rows[i]==leaf["table"]
            e,k,r,b=leaf["cycle"]
            cert[i]=f".cycle {e} {k} {str(bool(r)).lower()} ({b})"
        assert set(cert)==set(range(len(rows)))
        stats=Counter()
        sizes={}
        def inspect(t):
            tag=t[0];stats[tag]+=1
            n=1+sum(inspect(k) for k in t[3]) if tag=="split" else 1
            sizes[id(t)]=n
            return n
        inspect(tree)
        assert stats==Counter(S.get("stats", dict(cycle=5371,last=995,open=52,split=279)))
        used=set()
        def render(t):
            tag,*v=t
            if tag=="cycle":
                e,k,r,b=v;return f".cycle {e} {k} {str(bool(r)).lower()} ({b})"
            if tag=="last":
                n,s=v;return f".last {n} {slot(s)}"
            if tag=="open":
                i=index[v[0]];assert i not in used;used.add(i)
                return cert[i]
            assert tag=="split"
            n,s,kids=v;assert len(kids)==24
            return f".split {n} {slot(s)} (byMove [\n"+",\n".join(map(render,kids))+"])"
        def deps(t):
            if t[0]=="open":
                return {modules[index[t[1]]]} if index[t[1]] in modules else set()
            if t[0]=="split":
                return set().union(*(deps(k) for k in t[3]))
            return set()
        p0 = "(refine (pathEnd root 2 (path.take 3)).1 (3,true) (some ⟨false,true,1⟩))"
        if B1C1:
            b1, slot_name, c1 = (x.upper() for x in B1C1.groups())
            pos = {"A":1,"C":5,"E":8,"E1":9}[slot_name]
            tab = list("1RB---1RC"+b1+"0RD---1LD0RB------------")
            tab[3*pos:3*pos+3] = c1
            assert S["table"].replace("_","") == "".join(tab)
            target = slot(pos)
            base_expr = f"refine (refine {p0} (1,true) (some {move(b1)})) {target} (some {move(c1)})"
        else:
            base_expr = f"refine (refine {p0} (1,true) (some ⟨false,true,4⟩)) (4,true) (some {move(S.get('e1','0LE'))})"
        emit(PREFIX+"Base",["ZipPrefixAudit"],f"""
abbrev p43child : PartialMachine :=
  {base_expr}
theorem p43child_root : p43child initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p43child_nohalt : weightedTNFNoAssignedHalt p43child :=
  weightedTNFNoAssignedHalt_refine _ _ _ (weightedTNFNoAssignedHalt_refine _ _ _ (weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 3) firstOneCylinder_no_assigned_halt)))
theorem split_checked (p : PartialMachine) (n : Nat) (s : Slot) (kids : Move → Audit)
    (hq : zipQueryOK {B} p n s = true)
    (hk : ∀ mv, zipCheck {B} (refine p s (some mv)) (kids mv) = true) :
    zipCheck {B} p (.split n s kids) = true := by
  change (zipQueryOK {B} p n s && allMoves (fun mv => zipCheck {B} (refine p s (some mv)) (kids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨hq, allMoves_of _ hk⟩
""")
        def combine(p,name,n,s,names):
            cases="\n".join(f"  · exact c_{names[12*w+6*r+q]}" for q,w,r in product(range(6),range(2),range(2)))
            return f"""
def k_{name} : Move → Audit := byMove [{','.join('t_'+x for x in names)}]
def t_{name} : Audit := .split {n} {slot(s)} k_{name}
theorem q_{name} : zipQueryOK {B} {p} {n} {slot(s)} = true := by decide
theorem kcheck_{name} (mv : Move) : zipCheck {B} (refine {p} {slot(s)} (some mv)) (k_{name} mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{cases}
theorem c_{name} : zipCheck {B} {p} t_{name} = true :=
  split_checked {p} {n} {slot(s)} k_{name} q_{name} kcheck_{name}
"""
        def local(t,p,name):
            if sizes[id(t)]<=CHUNK:
                return f"""def t_{name} : Audit := {render(t)}
theorem c_{name} : zipCheck {B} {p} t_{name} = true := by
  rw [← BB6.Agent48PrefixAudit.prefixCheck_eq]
  decide
"""
            assert t[0]=="split"
            _,n,s,kids=t;out=[];names=[]
            for i,k in enumerate(kids):
                a=f"{name}_{i:02}";names.append(a)
                out.append(f"abbrev p_{a} := refine {p} {slot(s)} (some {move(MOVES[i])})\n")
                out.append(local(k,f"p_{a}",a))
            out.append(combine(p,name,n,s,names))
            return "".join(out)
        def shard(t,p,name):
            mod=f"{PREFIX}Shard_{name}"
            if sizes[id(t)]<=SHARD:
                emit(mod,[PREFIX+"Base",*sorted(deps(t))],
                     f"abbrev p_{name} := {p}\n"+local(t,f"p_{name}",name))
                return mod
            assert t[0]=="split"
            _,n,s,kids=t;names=[];imports=[]
            for i,k in enumerate(kids):
                a=f"{name}_{i:02}";names.append(a)
                imports.append(shard(k,f"(refine {p} {slot(s)} (some {move(MOVES[i])}))",a))
            emit(mod,imports,f"abbrev p_{name} := {p}\n"+combine(f"p_{name}",name,n,s,names))
            return mod
        mod=shard(tree,"p43child","root")
        assert used==set(range(len(rows)))
        emit(PREFIX+"Data",[mod],f"""
noncomputable def certificate43child : WeightedTNFCertificate {B} p43child 6 :=
  certifiedZip {B} p43child t_root p43child_root p43child_nohalt c_root
theorem all43child : ∀ m, compatible p43child m → WeightedBound {B} m :=
  certificate43child.sound
#print axioms all43child
""")
        print("raw43:",stats,"complete candidate audit; bound",B,flush=True)

if __name__=="__main__":
    generate()
