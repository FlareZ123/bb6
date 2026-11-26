"""Regenerate the three hard Raw39 1LE gap-list BiDFA certificates.

The search is untrusted; FastBiDFA.never checks every abstract configuration.
Run from any directory; pass the directory for the generated Lean modules.
"""
from collections import defaultdict
from pathlib import Path
import sys
from rungram_regen import discover
from minimize_bi import minimize, reach

SPECS = {
    5777: ("0RC", 15, 17, 17074, 640, 853),
    5779: ("0RE", 16, 15, 12533, 555, 592),
    5787: ("1RC", 16, 15, 12476, 554, 592),
}

def arr(xs):
    return '#[' + ','.join(xs) + ']'

def bs(b):
    return str(bool(b)).lower()

def generate(out, indices=None):
    out = Path(out)
    out.mkdir(parents=True, exist_ok=True)
    for i in SPECS if indices is None else indices:
        f, kl, kr, n, nl, nr = SPECS[i]
        table = '1RB1LE_1RC0LE_0RD---_1LD0RA_0LB0RF_1RE' + f
        dl, dr, _, _ = discover(table, (kl,12,12,1,1), (kr,12,12,1,1))
        dl, dr, count, _ = minimize(table, [dl,dr])
        S, es = reach(table, [dl,dr])
        assert (len(S), len(dl)//2, len(dr)//2) == (n,nl,nr)
        assert count == n
        module = f'Raw39LE{i}'
        ns = f'BB6.Agent11{module}'
        lines = ['import FastBiDFA','set_option maxRecDepth 100000',
                 'set_option maxHeartbeats 0',f'namespace {ns}',
                 'open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1NGram BB6.Agent32FastBiDFA',
                 'def table : PartialMachine := fun s =>','  match s.1.val,s.2 with']
        p = table.replace('_','')
        for j in range(12):
            m = p[3*j:3*j+3]
            if m != '---':
                lines.append(f'  | {j//2},{bs(j%2)} => some (some ⟨{bs(m[0]=="1")},{bs(m[1]=="R")},{ord(m[2])-65}⟩)')
        lines.append('  | _,_ => none')
        for name,d,e in zip(['leftGraph','rightGraph'],[dl,dr],es):
            pred = arr('['+','.join(f'({bs(b)},{y})' for b,y in sorted(e[x]))+']'
                       for x in range(len(d)//2))
            lines.append(f'def {name} : Graph := ⟨{arr(map(str,d))},{pred}⟩')
        rs = defaultdict(set)
        for q,a,l,r in S:
            rs[q*2+a,l].add(r)
        cache = {frozenset():'.empty',frozenset({0}):'.leaf'}
        def trie(xs):
            xs = frozenset(xs)
            if xs in cache:
                return cache[xs]
            a = trie(x//2 for x in xs if x%2==0)
            b = trie(x//2 for x in xs if x%2)
            name = f't{len(cache)}'
            cache[xs] = name
            lines.append(f'def {name} : Trie := .branch {a} {b}')
            return name
        rows = [[trie(rs[s,l]) for l in range(nl)] for s in range(12)]
        for s,row in enumerate(rows):
            lines.append(f'def row{s} : Array Trie := '+arr(row))
        lines.append('def cert : BB6.Agent32FastBiDFA.Cert := ⟨leftGraph,rightGraph,'+
                     arr(f'row{s}' for s in range(12))+'⟩')
        for s in range(12):
            lines.append(f'theorem row_checked{s} : rowCheck table cert {s//2} {bs(s%2)} = true := by decide')
        lines.extend(['theorem checked : check table cert = true := by',
            '  apply check_of_rows','  · decide','  · decide','  · decide',
            '  · intro q a',
            '    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega',
            '    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases a',
            *[f'    · exact row_checked{s}' for s in range(12)],
            'theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6.Agent32FastBiDFA.never table cert checked m hm',
            '#print axioms never',f'end {ns}'])
        (out/(module+'.lean')).write_text('\n'.join(lines)+'\n')
        print(i, n, nl, nr, len(cache))

if __name__ == '__main__':
    generate(sys.argv[1], list(map(int,sys.argv[2:])) or None)
