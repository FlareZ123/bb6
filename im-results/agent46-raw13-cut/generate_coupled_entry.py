"""Generate kernel-checkable blank-to-guard path from check_coupled_entry.

The Python generator is untrusted: every emitted edge has to typecheck as a
positive path of the literal Raw13 machine. No large primitive replay occurs.
"""
from pathlib import Path
from check_coupled_entry import certificate, config


def bits_value(bits):
    return sum(b << i for i, b in enumerate(bits))


def word(bits):
    return f"(bits {len(bits)} {bits_value(bits)})"


def left(n):
    return f"(bits {n.bit_length()} {n})"


def state(l, w):
    q, l, r = config(l, w)
    return f"(⟨{q},{l},{r}⟩ : NConf)"


def generate():
    trace, _ = certificate()
    lines = ["""import Raw13CoupledJump
import Raw13TapeValue

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13CoupledEntry
open BB6Coverage.Agent31Pump
open BB6.Agent46Raw13Frames (A main mixed11 special special0)
open BB6.Agent46Raw13TapeValue
open BB6.Agent46Raw13RightCounter (Triple add encode word)
open BB6.Agent46Raw13CoupledJump (jump)
open BB6.Agent46Raw13Detour (blank0)

def bits : Nat → Nat → List Bool
  | 0, _ => []
  | n+1, x => (x%2 == 1)::bits n (x/2)

def triples : List Bool → List Triple
  | a::b::c::R => ⟨a,b,c⟩::triples R
  | _ => []
"""]
    _, count, l, w = trace[0]
    lines.append(f"theorem s0 : Reach (nv blank0) {state(l,w)} := ⟨{count},by decide,by rfl⟩\n")
    for i, (tag, d, new_l, new_w) in enumerate(trace[1:], 1):
        lines.append(f"theorem s{i} : Reach {state(l,w)} {state(new_l,new_w)} := by")
        if tag == 'jump':
            u, x, m = l, 0, 0
            while u and (u&15)<=1:
                x |= (u&1)<<m
                u >>= 4
                m += 1
            if not u:
                m = max(m, (x+2*d).bit_length())
            n = len(w)//3
            assert x+2*d < 2**m
            assert w[3*n:] == new_w[3*n:]
            ts = f"(triples {word(w[:3*n])})"
            us = f"(triples {word(new_w[:3*n])})"
            lines.append(f"  have h := path_reach (jump {m} {x} {d} {left(u)} {word(w[3*n:])} {ts} {us} (by decide) (by decide) (by rfl))")
        elif tag == 'primitive':
            lines.append(f"  exact ⟨{d},by decide,by rfl⟩\n")
            l,w = new_l,new_w
            continue
        else:
            k,n,u = 0,0,l
            while u&3==3:
                k += 1
                u >>= 2
            while u&15==1:
                n += 1
                u >>= 4
            if tag == 'main':
                args=f"{k} {n} {left(u>>1)} {word(w)}"
            elif tag == 'mixed11':
                args=f"{k} {n-1} {left(u>>3)} {word(w)}"
            elif tag == 'special':
                args=f"{k} {n-1} {left(u>>4)} {word(w)}"
            elif tag == 'special0':
                args=f"{k} {left(u>>4)} {word(w)}"
            else:
                raise ValueError(tag)
            lines.append(f"  have h := path_reach ({tag} {args})")
        lines.append(f"  change Reach {state(l,w)} {state(new_l,new_w)} at h")
        lines.append("  exact h\n")
        l,w = new_l,new_w
    # Balanced composition prevents deep expression trees.
    def chain(lo,hi):
        if lo == hi:
            return f"s{lo}"
        mid=(lo+hi)//2
        return f"(reach_trans {chain(lo,mid)} {chain(mid+1,hi)})"
    lines.append(f"def guardWord : List Bool := {word(w)}\n")
    lines.append("theorem entry : Reach (nv blank0) (F [true] guardWord) := by")
    lines.append(f"  have h := {chain(0,len(trace)-1)}")
    lines.append(f"  change Reach (nv blank0) (F [true] guardWord) at h")
    lines.append("  exact h\n")
    lines.append("theorem guard_shape : ∃ U : List Bool, guardWord = [true,true,true] ++ U ++ List.replicate 9 false ++ [true] := by")
    lines.append(f"  exact ⟨{word(w[3:-10])},rfl⟩\n")
    lines.append("#print axioms entry\n#print axioms guard_shape\nend BB6.Agent46Raw13CoupledEntry\n")
    dest=Path(__file__).with_name('Raw13CoupledEntry.lean')
    dest.write_text('\n'.join(lines),encoding='utf-8')
    print(f"wrote {dest.name}: {dest.stat().st_size} bytes")


if __name__ == '__main__':
    generate()
