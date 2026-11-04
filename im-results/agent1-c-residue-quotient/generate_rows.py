"""Deterministic standard-kernel finite-closure proof sharder (192 residues)."""
from __future__ import annotations
import re
import os
from pathlib import Path
from filelock import FileLock
from make_bits import emit

N = 192
PHASES = (0, 1, 3, 4)
ROWS = [(p, x) for p in PHASES for x in range(N)]


def atomic_write(path: Path, data: str) -> None:
    temp = path.with_suffix(path.suffix + '.tmp')
    temp.write_text(data, encoding='utf-8')
    os.replace(temp, path)


def main() -> None:
    target = Path(__file__).resolve().parent
    with FileLock(str(target / '.generator.lock')):
        stats = emit(N, target / 'Bits192.lean')
        source = (target / 'Bits192.lean').read_text(encoding='utf-8')
        match = re.search(r'def masks : Array Nat := #\[\n(.*?)\n\]', source, re.S)
        if match is None:
            raise ValueError('Missing generated masks')
        values = [int(v) for v in re.findall(r'\d+', match.group(1))]
        if len(values) != 4 * N:
            raise ValueError(f'Expected 768 masks, received {len(values)}')
        maskfn = ('def mask (i : Nat) : Nat :=\n  match i with\n'
                  + ''.join(f'  | {i} => {v}\n' for i, v in enumerate(values))
                  + '  | _ => 0')
        defs = source[:match.start()] + maskfn + source[match.end():]
        for offset in (0, N, 2*N, 3*N):
            defs = defs.replace(f'masks[{offset}+a]!', f'mask ({offset}+a)')
        defs = defs.replace('masks[a]!', 'mask a')
        defs = defs.split('theorem finite_closed :')[0] + '\nend CQuotient192\n'
        atomic_write(target / 'BitDefs.lean', defs)
        for p, x in ROWS:
            text = ('import BitDefs\n'
                    'set_option maxRecDepth 65536\n'
                    'set_option maxHeartbeats 0\n'
                    'namespace CQuotient192\n'
                    f'theorem row_{p}_{x} : ∀ y : Fin {N}, '
                    f'closedAt {p} {x} y.val = true := by decide\n'
                    'end CQuotient192\n')
            atomic_write(target / f'Row{p}_{x}.lean', text)
        imports = ''.join(f'import Row{p}_{x}\n' for p, x in ROWS)
        s = (imports + 'import Lean.Elab.Tactic.Omega\n'
             'set_option maxRecDepth 65536\n'
             'set_option maxHeartbeats 0\n'
             'namespace CQuotient192\n'
             'theorem all_closed (p : Fin 5) (x y : Fin 192) : '
             'closedAt p.val x.val y.val = true := by\n'
             '  rcases p with ⟨p,hp⟩\n'
             '  rcases x with ⟨x,hx⟩\n'
             '  change closedAt p x y.val = true\n'
             '  match p with\n')
        for p in range(5):
            s += f'  | {p} =>\n'
            if p == 2:
                s += '    simp [closedAt, succs]\n'
                continue
            s += '    match x with\n'
            for x in range(N):
                s += f'    | {x} => exact row_{p}_{x} y\n'
            s += '    | x+192 => omega\n'
        s += ('  | p+5 => omega\n'
              '#print axioms all_closed\n'
              'end CQuotient192\n')
        atomic_write(target / 'AllRows.lean', s)
        print(f"Rows={len(ROWS)}; shards=64; quotient vertices={stats['seen']}; "
              f"SHA256={stats['sha256']}")


if __name__ == '__main__':
    main()
