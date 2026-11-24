"""Generate independent, kernel-checkable #746 reset path shards.

The generator is untrusted: the Lean statements contain exact boundary heights
and every proposed macro is checked by EvenBatch.lean.
"""
import argparse
from pathlib import Path
from generate_macro_blocks import fatal, macro

HEADER = ['import EvenBatch', 'set_option maxHeartbeats 0', 'set_option maxRecDepth 100000',
          'set_option exponentiation.threshold 10000000', 'namespace CascadeResetShield']


def join(lines, paths, heights):
    def go(lo, hi):
        if hi - lo == 1:
            return paths[lo]
        mid = (lo + hi) // 2
        a, b = go(lo, mid), go(mid, hi)
        name = f'join_{lo}_{hi}'
        lines.append(f'private theorem {name} : Path Edge {heights[lo]} {heights[hi]} := path_trans {a} {b}')
        return name
    return go(0, len(paths))


def generate(bound: int, chunk: int, shard: int, out: Path):
    if min(bound, chunk, shard) < 1:
        raise ValueError('bound, chunk and shard must be positive')
    out.mkdir(parents=True, exist_ok=True)
    h, cap = 2, fatal(bound)
    resets = macros = 0
    boundaries = [h]
    modules = []
    while h <= cap:
        i = len(modules)
        module = f'Macro{bound}Shard{i:04d}'
        lines = HEADER.copy()
        heights, paths = [], []
        for block in range(shard):
            if h > cap:
                break
            heights.append(f'h{block}')
            lines.append(f'private def h{block} : Nat := {hex(h)}')
            w = []
            for _ in range(chunk):
                if h > cap:
                    break
                u, witness = macro(h)
                assert u > h
                k, r, t = witness
                resets += r + (t != 0)
                macros += 1
                w.append(f'({k},{r},{t})')
                h = u
            lines.append(f'private def w{block} : List (Nat × Nat × Nat) := [' + ','.join(w) + ']')
            paths.append(f'p{block}')
        end = len(paths)
        heights.append(f'h{end}')
        lines.append(f'private def h{end} : Nat := {hex(h)}')
        for j in range(end):
            lines.append(f'private theorem c{j} : runMacroBlockFast h{j} w{j} = some h{j+1} := by decide')
            lines.append(f'private theorem p{j} : Path Edge h{j} h{j+1} := runMacroBlockFast_sound _ _ _ c{j}')
        proof = join(lines, paths, heights)
        lines.extend([f'theorem macro_{bound}_shard_{i} : Path Edge {hex(boundaries[-1])} {hex(h)} := {proof}', 'end CascadeResetShield'])
        (out / f'{module}.lean').write_text('\n'.join(lines)+'\n')
        boundaries.append(h)
        modules.append(module)
    lines = [f'import {m}' for m in modules] + HEADER[1:]
    paths = [f'macro_{bound}_shard_{i}' for i in range(len(modules))]
    proof = join(lines, paths, [hex(h) for h in boundaries])
    lines += [f'theorem certified_macro_prefix_{bound} : ∃ z, Path Edge 2 z ∧ fatal {bound} < z :=',
              f'  ⟨{hex(h)}, {proof}, by decide⟩',
              f'theorem no_fatal_through_macro_{bound} (n : Nat) (hn : n≤{bound}) : ¬ Path Edge 2 (fatal n) := by',
              f'  obtain ⟨z,hp,hz⟩ := certified_macro_prefix_{bound}',
              f'  exact bounded_fatal_exclusion edge_deterministic edge_strict (fun _ _ h => h) {bound} z hp hz n hn',
              f'#print axioms certified_macro_prefix_{bound}', f'#print axioms no_fatal_through_macro_{bound}',
              'end CascadeResetShield']
    final = f'MacroBound{bound}'
    (out / f'{final}.lean').write_text('\n'.join(lines)+'\n')
    (out / 'modules.txt').write_text('\n'.join(modules+[final])+'\n')
    print(f'bound={bound} resets={resets} macros={macros} shards={len(modules)} endpoint_bits={h.bit_length()}')


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--bound', type=int, required=True)
    p.add_argument('--chunk', type=int, default=64)
    p.add_argument('--shard', type=int, default=32)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    generate(a.bound, a.chunk, a.shard, a.output)
