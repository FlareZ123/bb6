"""Untrusted generator for exact #746 batched reset certificates.

Each record is (source level, length of even run, optional odd t+1).
The Lean checker proves the resulting path using only integer equations.
"""
import argparse
from pathlib import Path


def fatal(n: int) -> int:
    return (4 << n) - n - 4


def macro(h: int) -> tuple[int, tuple[int, int, int]]:
    k = max(0, h.bit_length() - 3)
    while h + k + 5 >= 8 << k:
        k += 1
    if h == fatal(k):
        raise ValueError(f"fatal height reached at index {k}")
    w = (8 << k) + k
    delta = w - h
    c = 2*k + 5
    assert delta > c
    v2 = (delta & -delta).bit_length() - 1
    cross = (delta // (c+1)).bit_length()
    r = min(v2, cross)
    v = w - (delta >> r)
    if r == cross:
        return v, (k, r, 0)
    assert (v + k) % 2 == 1 and v < fatal(k+1)
    q = (8 << k) - ((w-v-c)//2)
    t = (q & -q).bit_length() - 1
    u = (3**(t+1)*(q>>t)-5)//2
    return u, (k, r, t+1)


def generate(bound: int, chunk_size: int, output: Path) -> None:
    if bound < 1 or chunk_size < 1:
        raise ValueError("bound and chunk size must be positive")
    h = 2
    cap = fatal(bound)
    blocks = []
    resets = macros = 0
    while h <= cap:
        start = h
        witnesses = []
        while len(witnesses) < chunk_size and h <= cap:
            u, witness = macro(h)
            assert h < u
            k, r, tcode = witness
            resets += r + (tcode != 0)
            macros += 1
            witnesses.append(witness)
            h = u
        blocks.append((start, h, witnesses))
    lines = ['import EvenBatch', 'set_option maxHeartbeats 0', 'set_option maxRecDepth 100000',
             'set_option exponentiation.threshold 10000000', 'namespace CascadeResetShield']
    for i,(start,end,w) in enumerate(blocks):
        lines += [f'private def h{i} : Nat := {hex(start)}', f'private def w{i} : List (Nat × Nat × Nat) := [']
        for j in range(0,len(w),12):
            lines.append('  '+', '.join(f'({k},{r},{t})' for k,r,t in w[j:j+12])+(',' if j+12<len(w) else ''))
        lines += [']']
    lines += [f'private def h{len(blocks)} : Nat := {hex(h)}']
    for i in range(len(blocks)):
        lines += [f'private theorem block{i} : runMacroBlock h{i} w{i} = some h{i+1} := by decide',
                  f'private theorem path{i} : Path Edge h{i} h{i+1} := runMacroBlock_sound _ _ _ block{i}']
    # Balanced composition of paths: logarithmic proof depth, linear size.
    def join(lo, hi):
        if hi-lo == 1:
            return f'path{lo}'
        mid = (lo+hi)//2
        a,b = join(lo,mid),join(mid,hi)
        name = f'prefix_{lo}_{hi}'
        lines.append(f'private theorem {name} : Path Edge h{lo} h{hi} := path_trans {a} {b}')
        return name
    proof = join(0,len(blocks))
    lines += [f'theorem certified_macro_prefix_{bound} : ∃ z, Path Edge 2 z ∧ fatal {bound} < z :=',
              f'  ⟨h{len(blocks)}, {proof}, by decide⟩',
              f'theorem no_fatal_through_macro_{bound} (n : Nat) (hn : n≤{bound}) : ¬ Path Edge 2 (fatal n) := by',
              f'  obtain ⟨z,hp,hz⟩ := certified_macro_prefix_{bound}',
              f'  exact bounded_fatal_exclusion edge_deterministic edge_strict (fun _ _ h => h) {bound} z hp hz n hn',
              f'#print axioms certified_macro_prefix_{bound}', f'#print axioms no_fatal_through_macro_{bound}',
              'end CascadeResetShield']
    output.write_text('\n'.join(lines)+'\n')
    print(f'bound={bound} resets={resets} macros={macros} blocks={len(blocks)} endpoint_bits={h.bit_length()} source_bytes={output.stat().st_size}')


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--bound',type=int,required=True)
    p.add_argument('--chunk',type=int,default=128)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    generate(a.bound,a.chunk,a.output)
