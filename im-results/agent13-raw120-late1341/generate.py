"""Emit independently kernel-checked chunks for the exact raw120/1LB index 1341 trace."""
from pathlib import Path
import sys

TABLE = '1RB---_1RC0LF_0RD0RF_1LD1RE_1LB1LE_0RA0LE'
N, CHUNK, SHARD = 224705, 1000, 15
code = TABLE.replace('_', '')
rows = [code[i:i+3] for i in range(0, 36, 3)]
q, l, r = 0, 0, 0
points = [(q,l,r)]
for n in range(N):
    inst = rows[2*q+l%2]
    assert inst != '---', n
    w,d,s = inst
    q, w = ord(s)-65, int(w)
    if d == 'R':
        l,r = r%2+2*(w+2*(l//2)),r//2
    else:
        l,r = l//2,w+2*r
    if (n+1)%CHUNK == 0 or n+1 == N:
        points.append((q,l,r))
assert q == 0 and l%2 == 1 and l.bit_count()+r.bit_count() == 521

# Independently replay primitive tape semantics; also catch endpoint mistakes.
q, h, lo, hi = 0, 0, 0, 0
ones = set()
for n in range(N):
    inst = rows[2*q+int(h in ones)]
    assert inst != '---', n
    w,d,s = inst
    if w == '1': ones.add(h)
    else: ones.discard(h)
    h += 1 if d == 'R' else -1
    q = ord(s)-65
    lo, hi = min(lo,h), max(hi,h)
assert (q,h,lo,hi,len(ones),h in ones) == (0,147,-382,151,521,True)
assert rows[2*q+int(h in ones)] == '---'

def time(i): return min(i*CHUNK,N)

def write(out, name, imports, body):
    text = ''.join(f'import {m}\n' for m in imports)
    text += ('set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
             'namespace BB6.Agent13Raw120Late1341\n'
             'open BB6Coverage BB6Coverage.Agent13PackedZipper BB6Coverage.Agent10ZipAudit\n')
    (out / (name+'.lean')).write_text(text+body+'\nend BB6.Agent13Raw120Late1341\n', encoding='utf-8')

def generate(out, core='PackedZipper'):
    out.mkdir(parents=True, exist_ok=True)
    base = ['def table : PartialMachine := fun s => match s.1.val, s.2 with']
    for i,inst in enumerate(rows):
        q,a=divmod(i,2)
        key=f'  | {q}, {str(bool(a)).lower()} => '
        if inst=='---': base.append(key+'none')
        else:
            w,d,s=inst
            base.append(key+f'some (some ⟨{str(bool(int(w))).lower()},{str(d=="R").lower()},{ord(s)-65}⟩)')
    base += ['  | _, _ => none','abbrev z0 : P := startP']
    for i,(q,l,r) in enumerate(points[1:],1):
        base.append(f'def z{i} : P := ⟨{q},{l},{r}⟩')
    write(out,'Late1341Base',[core],'\n'.join(base))
    parts=[]
    for a in range(0,len(points)-1,SHARD):
        b=min(a+SHARD,len(points)-1)
        name=f'Late1341Part{a//SHARD:02}'
        body=[f'private theorem prefix{a} : runP table 0 z{a} = some z{a} := rfl']
        for i in range(a+1,b+1):
            body += [f'private theorem segment{i} : runP table {time(i)-time(i-1)} z{i-1} = some z{i} := by decide',
                     f'private theorem prefix{i} : runP table {time(i)-time(a)} z{a} = some z{i} := joinP prefix{i-1} segment{i}']
        body.append(f'theorem part{a} : runP table {time(b)-time(a)} z{a} = some z{b} := prefix{b}')
        write(out,name,['Late1341Base'],'\n'.join(body))
        parts.append((a,b,name))
    body=['private theorem whole0 : runP table 0 startP = some z0 := rfl']
    for a,b,_ in parts:
        body.append(f'private theorem whole{b} : runP table {time(b)} startP = some z{b} := joinP whole{a} part{a}')
    last=len(points)-1
    body += [f'theorem trace : runP table {N} startP = some z{last} := whole{last}',
             f'theorem query : zipRead table {N} = some (0,true) := by\n  rw [← readRunP_eq,readRunP,trace]\n  rfl',
             '#print axioms query']
    write(out,'Late1341Trace',[name for _,_,name in parts],'\n'.join(body))
    print(f'{len(points)-1} checked segments proposed in {len(parts)} shards; {N} live steps')

if __name__ == '__main__':
    generate(Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_name('generated'),
             sys.argv[2] if len(sys.argv)>2 else 'PackedZipper')
