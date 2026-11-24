"""Untrusted generator of compact Lean first-reset path certificates for #746."""
import argparse
from pathlib import Path
import sys
sys.set_int_max_str_digits(0)

def fatal(n):
    return 4 * (1 << n) - n - 4

def step(h):
    k = max(0, h.bit_length() - 3)
    while h + k + 5 >= 8 << k:
        k += 1
    if h == fatal(k):
        raise ValueError(f"fatal height reached at index {k}")
    p = 1 << k
    if (h+k) % 2 == 0:
        return 4*p+(h+k)//2, k, 0
    q = 4*p+(h+k)//2+3
    t = (q & -q).bit_length()-1
    return (3**(t+1)*(q>>t)-5)//2,k,t

def generate(bound, chunk_size, output):
    if bound < 1 or chunk_size < 1:
        raise ValueError("bound and chunk size must be positive")
    h=2
    cap=fatal(bound)
    blocks=[]
    transitions=0
    while h<=cap:
        start=h
        witnesses=[]
        while len(witnesses)<chunk_size and h<=cap:
            u,k,t=step(h)
            assert h<u
            witnesses.append((k,t))
            h=u
            transitions+=1
        blocks.append((start,h,witnesses))
    lines=['import ResetBlockCore','set_option maxHeartbeats 0','set_option maxRecDepth 100000','set_option exponentiation.threshold 1000000','namespace CascadeResetShield']
    for i,(start,end,w) in enumerate(blocks):
        lines += [f'private def h{i} : Nat := {start}', f'private def w{i} : List (Nat × Nat) := [']
        for j in range(0,len(w),12):
            lines.append('  '+', '.join(f'({k},{t})' for k,t in w[j:j+12])+(',' if j+12<len(w) else ''))
        lines += [']']
    lines += [f'private def h{len(blocks)} : Nat := {h}']
    for i in range(len(blocks)):
        lines += [f'private theorem block{i} : runBlock h{i} w{i} = some h{i+1} := by decide',f'private theorem path{i} : Path Edge h{i} h{i+1} := runBlock_sound (fun _ _ e => e) _ _ _ block{i}']
    lines += ['private theorem prefix0 : Path Edge 2 h0 := Path.refl 2']
    for i in range(len(blocks)):
        lines += [f'private theorem prefix{i+1} : Path Edge 2 h{i+1} := path_trans prefix{i} path{i}']
    lines += [f'theorem certified_prefix_{bound} : ∃ z, Path Edge 2 z ∧ fatal {bound} < z :=',f'  ⟨h{len(blocks)}, prefix{len(blocks)}, by decide⟩',f'#print axioms certified_prefix_{bound}','end CascadeResetShield']
    output.write_text('\n'.join(lines)+'\n')
    print(f'bound={bound} resets={transitions} blocks={len(blocks)} endpoint_bits={h.bit_length()} source_bytes={output.stat().st_size}')

if __name__=='__main__':
    p=argparse.ArgumentParser(); p.add_argument('--bound',type=int,required=True); p.add_argument('--chunk',type=int,default=64); p.add_argument('--output',type=Path,required=True); a=p.parse_args(); generate(a.bound,a.chunk,a.output)
