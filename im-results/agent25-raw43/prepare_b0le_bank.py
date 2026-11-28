"""Merge the pinned deep-search bank with exact nonhalting/late certificates.
The downstream generator re-enumerates and Lean checks every branch.
"""
import json
import sys
from pathlib import Path

KINDS = ('witnesses', 'bidfa', 'growth', 'lateLast', 'lateCycle')

def validate(s):
    rows = s['openRows']
    assert len(rows) == len(set(rows)) == s['stats']['open']
    seen = set()
    for kind in KINDS:
        for key, item in s[kind].items():
            i = int(key)
            assert str(i) == key and 0 <= i < len(rows) and i not in seen
            if kind != 'witnesses':
                assert rows[i] == item['table']
            seen.add(i)
    unresolved = set()
    for item in s['unresolved']:
        i = item['i']
        assert 0 <= i < len(rows) and rows[i] == item['table']
        assert i not in seen and i not in unresolved
        unresolved.add(i)
    assert seen | unresolved == set(range(len(rows)))

def prepare(variant, s):
    validate(s)
    rows = s['openRows']
    def add(kind, i, table, **fields):
        key = str(i)
        assert rows[i] == table
        for old_kind in KINDS:
            if key in s[old_kind]:
                # Only replace equivalent nonhalting certificates by a growth proof.
                assert old_kind == kind or (kind == 'growth' and old_kind == 'bidfa')
                if old_kind == kind:
                    assert s[kind][key] == dict(table=table, **fields)
                else:
                    del s[old_kind][key]
        s[kind][key] = dict(table=table, **fields)
        s['unresolved'] = [e for e in s['unresolved'] if e['i'] != i]

    def growth(i, table, module, ns, arg=''):
        partial, never = ns + '.table', ns + '.never'
        if arg:
            partial, never = f'({partial} {arg})', f'({never} {arg})'
        add('growth', i, table, module=module, partial=partial, never=never)

    def last(i, table, n, slot):
        add('lateLast', i, table, n=n, s=slot)
        s['bound'] = max(s['bound'], n + 6)

    if variant == '1la':
        for i, table in {
            44: '1RB0LA_1RC0LE_0RD1RA_1LD0RB_1LA1LF_---0LD',
            59: '1RB0LA_1RC0LE_0RD1RF_1LD0RB_1LA0RD_0LD---',
            61: '1RB0LA_1RC0LE_0RD1RF_1LD0RB_1LA1LB_0RE---',
            62: '1RB0LA_1RC0LE_0RD1RF_1LD0RB_1LA1RA_0RE---',
            176: '1RB0LF_1RC0LE_0RD1RF_1LD0RB_1LA1LB_0RE---',
            413: '1RB1LA_1RC0LE_0RD1RF_1LD0RB_1LA1LB_0RE---',
            558: '1RB1LC_1RC0LE_0RD1RF_1LD0RB_1LA1LB_0RE---',
            627: '1RB1RA_1RC0LE_0RD1RF_1LD0RB_1LA1LB_1RC---',
            711: '1RB1RC_1RC0LE_0RD1RF_1LD0RB_1LA1LD_0RD---',
            905: '1RB1RF_1RC0LE_0RD---_1LD0RB_1LA1LD_0RD1RF',
        }.items():
            growth(i, table, f'M{i}Proof', f'BB6.Agent38M{i}')
        last(9, '1RB0LA_1RC0LE_0RD0RA_1LD0RB_1LA0LF_1RB---', 1135, 11)
        last(10, '1RB0LA_1RC0LE_0RD0RA_1LD0RB_1LA1LF_0RA---', 1211, 11)
        last(60, '1RB0LA_1RC0LE_0RD1RF_1LD0RB_1LA0RF_0RA---', 2963, 11)
        add('lateCycle', 31, '1RB0LA_1RC0LE_0RD0RE_1LD0RB_1LA1RF_1RD---', cycle=[25134,57,1,51])
    elif variant == '1lb':
        module = 'Raw43B0LEE1LBI746'
        growth(746, '1RB1RA_1RC0LE_0RD1RF_1LD0RB_1LB1LD_0RA---', module, 'BB6.Agent25'+module)
        last(841, '1RB0LE_1RC0LE_0RD1RF_1LD0RB_1LB0LA_0RE---', 1569, 11)
    elif variant == '1lf':
        module = 'Raw43B0LEE1LFTriple'
        for v, (i, table) in enumerate([
            (330, '1RB1LF_1RC0LE_0RD0RB_1LD0RB_1LF---_0LA0LB'),
            (331, '1RB1RD_1RC0LE_0RD0RB_1LD0RB_1LF---_0LA0LB'),
            (396, '1RB1RD_1RC0LE_0RD1LA_1LD0RB_1LF---_0LA0LB'),
        ]):
            growth(i, table, module, 'BB6.Agent25'+module, f'({v} : Fin 3)')
        module = 'Raw43B0LEE1LFI746'
        growth(746, '1RB---_1RC0LE_0RD1RE_1LD0RB_1LF1RA_0RA0LF', module, 'BB6.Agent25'+module)
    elif variant == '1rf':
        growth(81, '1RB1LF_1RC0LE_0RD0RB_1LD0RB_1RF---_0LA0LB', 'M81Proof', 'BB6.Agent25M81')
    else:
        raise ValueError(variant)
    validate(s)
    assert not s['unresolved']
    print(variant, 'bound', s['bound'], {k: len(s[k]) for k in KINDS}, flush=True)
    return s

if __name__ == '__main__':
    variant, source, dest = sys.argv[1:]
    result = prepare(variant, json.loads(Path(source).read_text()))
    Path(dest).write_text(json.dumps(result, separators=(',', ':'))+'\n')
