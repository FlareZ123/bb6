"""Split large block-FAR row checks into kernel-checked finite ranges.

Only generated proof declarations change; automaton data and semantics are unchanged.
Pass a bank source and a minimum left-state count (default 64).
"""
import re
import sys
from pathlib import Path

NS = 'BB6.Agent6D1RangeCheck'

def split(text, threshold=64, chunk=2):
    if chunk < 1:
        raise ValueError('chunk must be positive')
    def rewrite(m):
        body = m.group(0)
        match = re.search(r'^def cert : (BB6BlockFAR\d*)\.Data (\d+) (\d+) := ', body, re.M)
        if match is None:
            return body
        block, d, n = match.group(1), int(match.group(2)), int(match.group(3))
        if d + 1 < threshold:
            return body
        statements = []
        def ranges(name, size, f):
            items = []
            for start in range(0, size, chunk):
                length = min(chunk, size - start)
                label = f'{name}_{start}_{length}'
                statements.append(f'private theorem {label} : {NS}.check {size-1} ({f}) {start} {length} = true := by decide +kernel')
                items.append((start, length, label))
            while len(items) > 1:
                merged = []
                for i in range(0, len(items), 2):
                    a, length, x = items[i]
                    if i+1 == len(items):
                        merged.append(items[i]); continue
                    b, k, y = items[i+1]
                    assert a + length == b
                    label = f'{name}_{a}_{length+k}'
                    statements.append(f'private theorem {label} : {NS}.check {size-1} ({f}) {a} {length+k} = true := {NS}.join {size-1} ({f}) {a} {length} {k} {x} {y}')
                    merged.append((a, length+k, label))
                items = merged
            return items[0][2]
        label = ranges('rows', d+1, 'cert.rowsAt machine')
        statements.append(f'theorem valid : cert.Valid machine := ⟨by decide +kernel, by decide +kernel, {NS}.full {d} (cert.rowsAt machine) {label}⟩')
        old = 'theorem valid : cert.Valid machine := ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩'
        return body.replace(old, '\n'.join(statements))
    text2 = re.sub(r'^namespace H(\d+)\n.*?^end H\1$', rewrite, text, flags=re.M|re.S)
    if text2 != text and 'import D1RangeCheck\n' not in text2:
        text2 = 'import D1RangeCheck\n' + text2
    return text2

if __name__ == '__main__':
    path = Path(sys.argv[1])
    path.write_text(split(path.read_text(), int(sys.argv[2]) if len(sys.argv)>2 else 64, int(sys.argv[3]) if len(sys.argv)>3 else 2))
