"""Reproduce the 19 Raw58 incidence quotient reductions.

Run from any directory. The exact candidate enumerator produces the ordered
open leaf lists under a temporary directory. Optional --emit-le203 emits the
compressed literal-table proof using the current row-sharded generator.
"""
import argparse
import json
import subprocess
import tempfile
from pathlib import Path
from rlelearn import check
from quotient import compress

HERE = Path(__file__).resolve().parent


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--emit-le203', type=Path)
    args = ap.parse_args()
    params = json.loads((HERE / 'rle-params.json').read_text())
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        exe = root / 'enumerate'
        subprocess.run(['g++', '-std=c++17', '-O3',
                        str(HERE.parent / 'agent2-tnf-raw99' / 'enumerate.cpp'),
                        '-o', str(exe)], check=True)
        for child, items in params.items():
            subprocess.run([str(exe), '1RB'+child+'_1RC---_0RD---_1LD1RE_---0RA_------'],
                           cwd=root, check=True, stdout=subprocess.DEVNULL)
            lines = (root / 'open.txt').read_text().splitlines()
            for idx, pms in items.items():
                i = int(idx)
                raw = lines[i]
                s = raw.replace('_','')
                p = tuple(s[j:j+3] for j in range(0,len(s),3))
                cert = check(p,pms,pms)
                reduced = compress(p,cert)
                print(child,i,raw,cert[1],*[len(x) for x in cert[-1]],
                      '->',reduced[1],*[len(x) for x in reduced[-1]],flush=True)
                if child == '0LE' and i == 203 and args.emit_le203:
                    # Import the emitter via AST extraction: no tree generator
                    # or unrelated witness dependencies are needed.
                    import ast
                    from emit_automata import emit
                    tree = ast.parse((HERE.parent/'agent4-raw58'/'generate_more.py').read_text())
                    node = next(n for n in tree.body if isinstance(n,ast.FunctionDef)
                                and n.name == 'emit_automata_sharded')
                    scope = {'emit_automata': emit}
                    exec(compile(ast.Module(body=[node],type_ignores=[]),'emitter','exec'),scope)
                    body = scope['emit_automata_sharded'](i,p,reduced)
                    args.emit_le203.write_text('import TwoSidedAutomata\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace BB6.Agent4Raw58LE\nopen BB6Coverage\n'+body+'\nend BB6.Agent4Raw58LE\n')


if __name__ == '__main__':
    main()
