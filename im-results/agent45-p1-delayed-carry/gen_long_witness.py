#!/usr/bin/env python3
"""Generate kernel-checkable packed/sparse long reverse-witness certificates.

This script is untrusted: every transition cover and recovery equality is checked
by Lean.  It is deliberately independent of the earlier C++ prefix search.
"""
from argparse import ArgumentParser
from functools import lru_cache
from pathlib import Path

MASKS = (0xAAAAAAAAAAAAAAAA, 0xCCCCCCCCCCCCCCCC, 0xF0F0F0F0F0F0F0F0,
         0xFF00FF00FF00FF00, 0xFFFF0000FFFF0000, 0xFFFFFFFF00000000)


def small_weight(b):
    return sum((b & mask) << j for j, mask in enumerate(MASKS))


@lru_cache(None)
def index_masks(L):
    capacity = 1 << L
    masks = []
    for j in range(L):
        p = 1 << j
        mask = ((1 << p) - 1) << p
        width = 2*p
        while width < capacity:
            mask |= mask << width
            width *= 2
        masks.append(mask)
    return tuple(masks)


def weight(B, L):
    return sum((B & mask) << j for j, mask in enumerate(index_masks(L)))


def witness(F, k, Y, z):
    """Greedy word, accelerating legal subblocks by the fitted quotient rule."""
    q = F - k
    c, word, rem = z, 0, k
    while rem:
        f = q + rem
        j = min(rem, 63, max(1, f.bit_length()-2))
        start = rem-j
        y = (Y >> start) & ((1 << j)-1)
        X = (c << j) + y
        B0 = X//f
        found = False
        for B in (B0, B0+1):
            if B >= 1 << j:
                continue
            w = (f-j)*B + small_weight(B)
            if 0 <= X-w < f-j:
                c = X-w
                word |= B << start
                rem = start
                found = True
                break
        if found:
            continue
        # If a guard fails, finish the saturated binary greedy word.  The
        # exact neighbouring-word inequality is independently checked below.
        for i in range(rem-1, start-1, -1):
            m = q+i
            c = 2*c + ((Y >> i)&1)
            if c >= m:
                c -= m
                word |= 1 << i
            if c >= m:
                word |= (1 << i)-1
                rem = 0
                c = q
                break
        else:
            rem = start
    L = (k-1).bit_length() if k else 0
    X = (z << k) + Y
    W = q*word + weight(word,L)
    assert 0 <= word < 1 << k and W <= X
    if c < q:
        assert X-W == c
    else:
        assert X-W >= q and (word+1 == 1 << k or
                             X < q*(word+1) + weight(word+1,L))
    return z,word,c


def target_digits(n, s, B, k):
    return ((7*B << n) >> s) & ((1 << k)-1)


@lru_cache(None)
def spread_plan(L):
    plan = []
    for k in range(L-1,-1,-1):
        b = 1 << k
        mask = (1 << b)-1
        for r in range(L-k):
            mask |= mask << (2*b*(1 << r))
        plan.append((b,mask))
    return plan


def packed_back(plan, q, y, bits):
    for shift,mask in plan:
        bits = (bits | (bits << shift)) & mask
    u = bits << y
    return (u | (u >> q)) & ((1 << q)-1)



def packed_jump(q, k, Y):
    """Exact modular support, removing half-period weights before expansion."""
    weights = [(q+j) << j for j in range(k-1,-1,-1)]
    exponent = k
    while exponent:
        M = 1 << exponent
        idx = next((i for i,w in enumerate(weights) if w%M==M//2),None)
        if idx is None:
            break
        weights.pop(idx)
        exponent -= 1
    M = 1 << exponent
    mask = (1 << M)-1
    def rot(b,s):
        s %= M
        return ((b << s) | (b >> (M-s))) & mask
    b = 1
    for w in reversed(weights):
        b |= rot(b,-w)
    b = rot(b,Y)
    for t in range((q//M).bit_length()+1):
        if M << t >= q:
            break
        b |= b << (M << t)
    return b & ((1 << q)-1)

def bit_members(x):
    ans = []
    # bytes avoid repeatedly clearing bits of a huge integer
    for i,b in enumerate(x.to_bytes((x.bit_length()+7)//8, "little")):
        while b:
            low = b & -b
            ans.append(8*i + low.bit_length()-1)
            b ^= low
    return ans


def lean_num(n):
    return str(n) if n < 1000000 else hex(n)


def lean_list(items):
    return "[" + ",".join(map(str,items)) + "]"


def lean_rows(rows):
    return lean_list(f"({z},{lean_num(B)},{c})" for z,B,c in rows)


def lean_prefixes(ps):
    return lean_list(f"({lean_num(B)},{a})" for B,a in ps)


class Writer:
    def __init__(self, root):
        self.root = Path(root)
        self.root.mkdir(parents=True,exist_ok=True)
        self.modules = []

    def emit(self, body, imports=None):
        name = f"LW{len(self.modules):04}"
        if imports is None:
            imports = [self.modules[-1]] if self.modules else ["LongBlockHalf","PackedJump","LongConeSource"]
        hdr = "\n".join("import "+x for x in imports)
        hdr += "\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n"
        hdr += "open BB6.Agent45ReverseBlock BB6.Agent45LongBlock BB6.Agent45.DelayedCarry BB6.Agent43P1Complement BB6.Agent45PackedJump\n"
        (self.root/(name+".lean")).write_text(hdr+body+"\n")
        self.modules.append(name)
        return name

    def finish(self):
        (self.root/"modules.txt").write_text("\n".join(self.modules)+"\n")


def generate(args):
    n,h = args.n,args.h
    assert n >= 8000 and n%2 == 0 and 0 < h < n
    assert 0 < args.chunk <= args.initial and args.long >= 0
    assert 0 <= args.jump <= min(args.initial,30)
    cover_type = "HalfCovered" if args.half else "Covered"
    recover = "recoverHalfRows" if args.half else "recoverRows"
    next_lemma = "half_covered_next_rows" if args.half else "covered_next_rows"
    w = Writer(args.out)
    s = 1
    ps = [(1,(n+2)//2)]
    w.emit(f"def ps0 : List Prefix := {lean_prefixes(ps)}\n"
           f"theorem cover0 : {cover_type} {n} 1 ps0 := {'half_covered_first' if args.half else 'covered_first'} {n}")
    for stage in range(args.stages):
        suffix = n-h
        F = 2*n+s+3
        L = (F-1).bit_length()
        next_ps = []
        branch = []
        for i,(B,a) in enumerate(ps):
            tag = f"w{stage}_{i}"
            b = tag+"_B"
            w.emit(f"def {b} : Nat := {lean_num(B)}")
            prev = tag+"_init"
            d = min(args.jump,suffix)
            if d:
                start = s+n-d
                bits = packed_jump(F-d,d,target_digits(n,start,B,d))
                w.emit(f"def {prev}_bits : Nat := {lean_num(bits)}\n"
                       f"theorem {prev}_cover : LiveBits {n} {b} {start} {d} {prev}_bits := by\n"
                       f"  have he : packedReducedJump {F-d} {d} (targetDigits {n} {start} {b} {d}) = {prev}_bits := by decide +kernel\n"
                       f"  rw [←he]\n"
                       f"  exact live_bits_jump {n} {b} {start} {d}")
            else:
                bits = (1 << F)-1
                w.emit(f"def {prev}_bits : Nat := 2^{F}-1\n"
                       f"theorem {prev}_cover : LiveBits {n} {b} {s+n} 0 {prev}_bits := "
                       f"live_bits_init {n} {b} {s+n}")
            while d < min(args.initial,suffix):
                j = min(args.chunk,min(args.initial,suffix)-d)
                start = s+n-d-j
                y = target_digits(n,start,B,j)
                for k in range(j-1,-1,-1):
                    bits = packed_back(spread_plan(L),n+start+k+3,(y >> k)&1,bits)
                cur = tag+f"_b{d+j}"
                w.emit(f"def {cur}_bits : Nat := {lean_num(bits)}\n"
                       f"theorem {cur}_cover : LiveBits {n} {b} {start} {d+j} {cur}_bits := by\n"
                       f"  exact live_bits_extend {L} {n} {b} {start} {j} {d} "
                       f"{prev}_bits {cur}_bits (by decide) {prev}_cover (by decide +kernel)")
                prev = cur
                d += j
            xs = bit_members(bits)
            cur = tag+f"_s{d}"
            w.emit(f"def {cur}_xs : List Nat := {lean_list(xs)}\n"
                   f"theorem {cur}_cover : LiveList {n} {b} {s+n-d} {d} {cur}_xs := by\n"
                   f"  exact live_bits_to_list {n} {b} {s+n-d} {d} {prev}_bits "
                   f"{cur}_xs {prev}_cover (by decide +kernel)")
            prev = cur
            print("PACK",stage,i,F,d,len(xs),flush=True)
            while d < suffix and xs:
                j = min(args.long or max(1,d),suffix-d)
                start = s+n-d-j
                y = target_digits(n,start,B,j)
                f = n+start+j+3
                rows = [witness(f,j,y,z) for z in xs]
                new = sorted({c for z,R,c in rows if c<f-j})
                cur = tag+f"_s{d+j}"
                w.emit(f"def {cur}_rows : List WitnessRow := {lean_rows(rows)}\n"
                       f"def {cur}_xs : List Nat := {lean_list(new)}\n"
                       f"theorem {cur}_cover : LiveList {n} {b} {start} {d+j} {cur}_xs := by\n"
                       f"  exact live_list_extend {(j-1).bit_length()} {n} {b} {start} {j} {d} "
                       f"{prev}_xs {cur}_xs {cur}_rows (by decide) {prev}_cover "
                       f"(by decide +kernel) (by decide +kernel) (by decide +kernel)")
                print("LONG",stage,i,f,j,len(xs),len(new),flush=True)
                prev, xs = cur,new
                d += j
            if d < suffix:
                # Empty covers propagate. No numerical row generation needed.
                j = suffix-d
                start = s+h
                cur = tag+f"_s{suffix}"
                w.emit(f"def {cur}_xs : List Nat := []\n"
                       f"theorem {cur}_cover : LiveList {n} {b} {start} {suffix} {cur}_xs := by\n"
                       f"  exact live_list_extend {(j-1).bit_length()} {n} {b} {start} {j} {d} "
                       f"{prev}_xs {cur}_xs [] (by decide) {prev}_cover "
                       f"(by decide +kernel) (by decide +kernel) (by decide +kernel)")
                prev = cur
                d = suffix
            y = target_digits(n,s,B,h)
            f = n+s+h+3
            mids = [witness(f,h,y,z) for z in xs]
            out = [(B+(R << s),z) for z,R,c in mids if c==a and (not args.half or (B+(R << s))%4==1)]
            next_ps.extend(out)
            w.emit(f"def {tag}_mid : List WitnessRow := {lean_rows(mids)}\n"
                   f"theorem {tag}_ends : {tag}_mid.map Prod.fst = {prev}_xs := by decide +kernel\n"
                   f"theorem {tag}_check : {tag}_mid.all (rowCheck {(h-1).bit_length()} "
                   f"{f} {h} (targetDigits {n} {s} {b} {h})) = true := by decide +kernel")
            branch.append((tag,b,prev))
            print("MID",stage,i,len(xs),len(out),flush=True)
        rows_name = f"rows{stage}"
        row_expr = "[]"
        for tag,b,prev in reversed(branch):
            row_expr = f"if B = {b} then {tag}_mid else "+row_expr
        body = f"def {rows_name} (B : Nat) : List WitnessRow := {row_expr}\n"
        for tag,b,prev in branch:
            body += f"theorem {tag}_lookup : {rows_name} {b} = {tag}_mid := by decide +kernel\n"
        mname = f"midcover{stage}"
        body += f"theorem {mname} : MidpointRows {(h-1).bit_length()} {n} {s} {h} ps{stage} {rows_name} := by\n"
        body += "  constructor\n"
        cases = " | ".join("⟨rfl,rfl⟩" for _ in branch)
        # A single previous ps equality can also be decomposed with rcases.
        for islive in [True,False]:
            body += "  · intro B a hp" + (" z c hw\n" if islive else "\n")
            body += f"    simp only [ps{stage},List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hp\n"
            body += f"    rcases hp with {cases}\n"
            for tag,b,prev in branch:
                if islive:
                    body += f"    · change c ∈ ({rows_name} {b}).map Prod.fst\n"
                    body += f"      rw [{tag}_lookup,{tag}_ends]\n"
                    body += f"      exact {prev}_cover z c hw\n"
                else:
                    body += f"    · change ({rows_name} {b}).all (rowCheck {(h-1).bit_length()} {n+s+h+3} {h} (targetDigits {n} {s} {b} {h})) = true\n"
                    body += f"      rw [{tag}_lookup]\n      exact {tag}_check\n"
        body += f"def ps{stage+1} : List Prefix := {lean_prefixes(next_ps)}\n"
        body += f"theorem rec{stage} : {recover} {s} ps{stage} {rows_name} = ps{stage+1} := by decide +kernel\n"
        if next_ps:
            body += f"theorem cover{stage+1} : {cover_type} {n} {s+h} ps{stage+1} := by\n"
            body += f"  exact {next_lemma} {(h-1).bit_length()} {n} {s} {h} ps{stage} ps{stage+1} {rows_name} "
            body += f"(by decide) (by decide) (by decide) cover{stage} {mname} rec{stage}\n"
        else:
            final_s = s
            if args.half:
                if s >= 2:
                    body += f"theorem emptyHalf : HalfCovered {n} {s} [] := by\n"
                    body += f"  exact half_covered_empty_rows {(h-1).bit_length()} {n} {s} {h} ps{stage} {rows_name} "
                    body += f"(by decide) (by decide) (by decide) cover{stage} {mname} rec{stage}\n"
                else:
                    final_s = s+h
                    body += f"theorem emptyHalf : HalfCovered {n} {final_s} [] := by\n"
                    body += f"  exact half_covered_next_rows {(h-1).bit_length()} {n} {s} {h} ps{stage} [] {rows_name} "
                    body += f"(by decide) (by decide) (by decide) cover{stage} {mname} rec{stage}\n"
                body += f"theorem emptyCover : Covered {n} {final_s} [] := half_empty_to_full {n} {final_s} (by decide) (by decide) (by decide) emptyHalf\n"
            else:
                body += f"theorem emptyCover : Covered {n} {s} [] := by\n"
                body += f"  exact covered_empty_rows {(h-1).bit_length()} {n} {s} {h} ps{stage} {rows_name} "
                body += f"(by decide) (by decide) cover{stage} {mname} rec{stage}\n"
            body += f"theorem p1_excluded_{n} : ¬ BB6.Agent1.Reach 2 (14*2^{n}-2*{n}-10) := by\n"
            body += f"  exact BB6.Agent43LongCone.critical_reset_no_reach_of_short_lag {n} {final_s} "
            body += "(by decide) (by decide) (by decide) (by decide +kernel) emptyCover\n"
            body += f"#print axioms p1_excluded_{n}\n"
            body += f'#eval "P1_LONG_CERTIFIED n={n} s={final_s}"\n'
        w.emit(body)
        print("STAGE",stage,s,len(ps),len(next_ps),flush=True)
        if not next_ps:
            w.finish()
            return
        ps = next_ps
        s += h
    w.finish()
    raise SystemExit("No empty cover within stage limit")


if __name__ == "__main__":
    parser = ArgumentParser()
    parser.add_argument("out")
    parser.add_argument("--n",type=int,default=124834)
    parser.add_argument("--h",type=int,default=62417)
    parser.add_argument("--stages",type=int,default=4)
    parser.add_argument("--initial",type=int,default=512)
    parser.add_argument("--chunk",type=int,default=256)
    parser.add_argument("--long",type=int,default=8192)
    parser.add_argument("--jump",type=int,default=0)
    parser.add_argument("--half",action="store_true")
    generate(parser.parse_args())
