#!/usr/bin/env python3
"""Generate the exact FastBiDFA certificate for Raw56 E0=0LF leaf 3613.

Discovery uses the periodic stack word 111110 with a 3->6 repetition fold.
That search is untrusted: the emitted certificate is independently quotient-
minimized, re-saturated, and finally checked by the unchanged Lean FastBiDFA
kernel checker against the literal partial machine.
"""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
BIDFA = ROOT / 'im-results/agent32-raw59'
ID = 3613
TABLE = '1RB---_1RC0RE_0RD0RF_1LD1LE_0LF0LE_1RA0LB'
PARAM = {'k': 30, 'groups': [['111110', 3, 3]]}
RAW_EXPECTED = (45865, 2426)
QUOTIENT_EXPECTED = (9210, 785)


def main():
    out = Path(sys.argv[1]).resolve()
    out.mkdir(parents=True, exist_ok=True)
    payload = [dict(id=ID, table=TABLE, params=[PARAM, PARAM],
                    states=RAW_EXPECTED[0], edges=RAW_EXPECTED[1])]
    replay = subprocess.check_output(
        ['node', str(HERE / 'motif_replay.cjs')],
        input=json.dumps(payload).encode())
    witness = json.loads(replay)[0]
    assert (witness['states'], witness['edges']) == RAW_EXPECTED

    sys.path.insert(0, str(BIDFA))
    from emit_rungram import emit
    from motif_quotient import minimize
    d, P, S = minimize(TABLE, witness['dfa'])
    n = len(S)
    e = sum(map(len, P)) + 2
    assert (n, e) == QUOTIENT_EXPECTED, (n, e)

    module = 'Raw56LE0LFMotif3613'
    text = '\n'.join([
        'import FastBiDFA',
        'set_option maxRecDepth 100000',
        'set_option maxHeartbeats 0',
        'namespace BB6.Agent1Raw56.LE0LFMotif3613',
        'open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1NGram BB6.Agent32FastBiDFA',
        emit(ID, TABLE, *d, [n, e]),
        'end BB6.Agent1Raw56.LE0LFMotif3613',
        ''
    ])
    (out / (module + '.lean')).write_text(text)
    record = dict(
        id=ID, table=TABLE, params=[PARAM, PARAM],
        pre_quotient=dict(states=RAW_EXPECTED[0], edges=RAW_EXPECTED[1]),
        quotient=dict(states=n, edges=e),
        theorem='BB6.Agent1Raw56.LE0LFMotif3613.M3613.never',
        source_sha256=hashlib.sha256(text.encode()).hexdigest(),
        method='periodic-stack discovery; independent quotient re-saturation; unchanged FastBiDFA Lean check')
    (out / '3613-manifest.json').write_text(
        json.dumps(record, indent=2, sort_keys=True) + '\n')
    print(json.dumps(record, sort_keys=True), flush=True)


if __name__ == '__main__':
    main()
