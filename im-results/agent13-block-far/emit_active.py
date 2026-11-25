"""Emit a support-complete, compact block-FAR certificate.

Input is the exact dictionary returned by generate_multi.generate. Packed
rows are merely data: Lean proves every omitted symbol vacuous through
ActiveData.valid_of_checks, and checks all supplied transitions in the kernel.
"""
from pathlib import Path
from collections import defaultdict
import re

def specialize_active(block, width):
    if width == 3:
        return
    s = (block / "ActiveSparseFAR.lean").read_text()
    s = re.sub(r"\b8\b", str(2**width), s)
    s = s.replace("import SparseBlockFAR", f"import SparseBlockFAR{width}")
    s = s.replace("namespace BB6BlockFAR", f"namespace BB6BlockFAR{width}").replace(
        "end BB6BlockFAR", f"end BB6BlockFAR{width}")
    if width >= 8:
        # The specialized BlockMacro already proves the code bijection
        # symbolically. Reuse it rather than splitting 2**width cases.
        s = re.sub(r"private theorem code_lt \(a : Sym\) : a.code < \d+ := by\n.*?\n\n",
                   f"private theorem active_code_lt (a : Sym) : a.code < {2**width} := code_lt a\n\n",
                   s, flags=re.S)
        s = re.sub(r"private theorem code_roundtrip \(a : Sym\) : Sym.ofCode a.code = a := by\n.*?\n\n",
                   "private theorem code_roundtrip (a : Sym) : Sym.ofCode a.code = a := ofCode_code a\n\n",
                   s, flags=re.S)
        s = s.replace("have h := code_lt a", "have h := active_code_lt a")
    else:
        fields = [f"x{i}" for i in range(width)]
        s = s.replace("⟨a,b,c⟩", "⟨" + ",".join(fields) + "⟩")
        s = s.replace("cases a <;> cases b <;> cases c <;> decide",
                      " <;> ".join("cases " + v for v in fields) + " <;> decide")
    (block / f"ActiveSparseFAR{width}.lean").write_text(s)

def pack(xs, bits):
    assert all(0 <= x < (1 << bits) for x in xs)
    return sum(x << (bits*i) for i, x in enumerate(xs))

def emit_lookup(name, mapping, default=0):
    # A small decision tree of variable-width packed groups. Kernel checking
    # needs neither native_decide nor a large unfolded array literal.
    stride = 16
    groups = defaultdict(dict)
    for key, val in mapping.items():
        if val != default:
            groups[key//stride][key%stride] = val
    values = []
    for key, vs in sorted(groups.items()):
        bits = max(1, default.bit_length(), *(v.bit_length() for v in vs.values()))
        code = pack([vs.get(j, default) for j in range(stride)], bits)
        values.append((key, f"({bits},{hex(code)})"))
    db = max(1, default.bit_length())
    fallback = f"({db},{hex(pack([default]*stride, db))})"
    def tree(xs):
        if not xs:
            return fallback
        if len(xs) == 1:
            k,v = xs[0]
            return f"if i = {k} then {v} else {fallback}"
        k = len(xs)//2
        return f"if i < {xs[k][0]} then ({tree(xs[:k])}) else ({tree(xs[k:])})"
    return (f"def {name}Chunks (i : Nat) : Nat × Nat := " + tree(values) +
            f"\ndef {name} (i : Nat) : Nat := let p := {name}Chunks (i/{stride}); "
            f"(p.2 >>> (p.1*(i%{stride}))) % (2^p.1)\n")

def emit_active(data, out, name):
    width = data["width"]
    A = 2**width
    D,C = data["left_states"],data["right_nodes"]
    dead = C-1
    suffix = "" if width == 3 else str(width)
    ns = "BB6BlockFAR" + suffix + "." + name
    K = max(A,16)
    push,ctrl,aux,edge = (defaultdict(list) for _ in range(4))
    for i,v in enumerate(data["push"]):
        if v:
            push[i//A].append((i%A,v))
    for i,v in enumerate(data["ctrl"]):
        if v != dead:
            ctrl[i//12].append((i%12,v+1))
    for i,v in enumerate(data["aux"]):
        if v != dead:
            aux[i//A].append((i%A,v+1))
    for i,ts in enumerate(data["edges"]):
        if ts:
            edge[i//A].append((i%A,ts))
    zero = set(data["zero_states"])
    zn = {i:data["zeroNext"][i] for i in zero}
    pairbits = K.bit_length()-1 + max(D,C+1).bit_length() + 1
    tbits = C.bit_length()
    max_t = max(1,max((len(ts) for vs in edge.values() for _,ts in vs),default=0))
    ebits = width + tbits*max_t + 1
    pbits = (A*D).bit_length()
    pfuel = max(1,max(map(len,data["pred"])))
    def kv(m):
        return {i:pack([key+K*v+1 for key,v in vs],pairbits) for i,vs in m.items()}
    em = {i:pack([1+a+A*pack([t+1 for t in ts],tbits) for a,ts in vs],ebits)
          for i,vs in edge.items()}
    pm = {i:pack([v+1 for v in vs],pbits) for i,vs in enumerate(data["pred"]) if vs}
    s = f"import ActiveSparseFAR{suffix}\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace {ns}\n"
    s += "def machine : Table := fun q b => ([" + ",".join(
        "none" if v is None else f"some ⟨{str(bool(v[0])).lower()},{str(bool(v[1])).lower()},{v[2]}⟩"
        for v in data["moves"]) + "] : List (Option Move))[2*q.val+b.toNat]?.getD none\n"
    s += f"""def unpack : Nat → Nat → Nat → List Nat
  | 0,_,_ => []
  | k+1,b,x =>
    let y := x % (2^b)
    if y=0 then [] else (y-1)::unpack k b (x >>> b)
def pairs (fuel bits code : Nat) : List (Nat × Nat) :=
  (unpack fuel bits code).map fun x => (x%{K},x/{K})
"""
    for field,mapping,default in [("pushData",kv(push),0),("ctrlData",kv(ctrl),0),
        ("auxData",kv(aux),0),("predData",pm,0),("edgeData",em,0),("zeroNextCodes",zn,dead)]:
        s += emit_lookup(field,mapping,default)
    s += f"""def pushRows (l : Nat) : List (Nat × Nat) := pairs {A} {pairbits} (pushData l)
def controlCodes (i : Nat) : Nat := ((activeLookup (i%12) (pairs 12 {pairbits} (ctrlData (i/12)))).getD {dead+1}).pred
def auxiliaryCodes (i : Nat) : Nat := ((activeLookup (i%{A}) (pairs {A} {pairbits} (auxData (i/{A})))).getD {dead+1}).pred
def predecessorCodes (l : Nat) : List Nat := unpack {pfuel} {pbits} (predData l)
def edgeRows (v : Nat) : List (Nat × List Nat) := (unpack {A} {ebits} (edgeData v)).map fun x => (x%{A},unpack {max_t} {tbits} (x/{A}))
def cert : ActiveData {D-1} {C-1} := {{
  start := 0
  pushRows := pushRows
  controlCodes := controlCodes
  auxiliaryCodes := auxiliaryCodes
  predecessorCodes := predecessorCodes
  edgeRows := edgeRows
  zeroCodes := {hex(sum(1<<v for v in zero))}
  zeroNextCodes := zeroNextCodes
}}
end {ns}
"""
    out = Path(out)
    (out / (name+"Packed.lean")).write_text(s)
    # Chunk proof computation and combine in a balanced tree. All check
    # results are kernel reductions, with no external completeness claims.
    s = f"import {name}Packed\nimport RangeCheck{suffix}\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace {ns}\n"
    s += "theorem base_ok : cert.sparse.baseCheck = true := by decide +kernel\n"
    for kind,f in [("pred","cert.fastPredAt"),("rows","(cert.fastRowsAt machine)")]:
        def combine(lo,length):
            if length <= 16:
                tag=f"{kind}_{lo}_{length}"
                return (f"theorem {tag} : rangeCheck {D-1} {f} {lo} {length} = true := by decide +kernel\n",tag)
            left=length//2
            ls,ln=combine(lo,left);rs,rn=combine(lo+left,length-left)
            tag=f"{kind}_{lo}_{length}"
            return (ls+rs+f"theorem {tag} : rangeCheck {D-1} {f} {lo} {length} = true := "
                f"rangeCheck_join {D-1} {f} {lo} {left} {length-left} {ln} {rn}\n",tag)
        proof,tag=combine(0,D)
        s+=proof+f"theorem {kind}_full : (List.finRange {D}).all {f} = true := rangeCheck_full _ _ {tag}\n"
    s += f"""theorem valid : cert.sparse.Valid machine := cert.valid_of_checks machine base_ok pred_full rows_full
theorem never : ∀ k, ∃ c, run machine k primBlank = some c := cert.sparse.sound machine valid
#print axioms never
end {ns}
"""
    (out/(name+"Proof.lean")).write_text(s)
