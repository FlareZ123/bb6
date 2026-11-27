"""Close the corrected Raw36 B1=0LA cut with exact-table keyed evidence.

The original search generates the actual 24-way tree with explicit OPEN
leaves; only those leaves are replaced. No obsolete census is trusted. FAR
masks are reconstructed on the literal table and sweep proofs enter through
Audit.proven, whose zipCheck checks equality of all twelve slots. The output
is untrusted until the original Lean checker accepts every root.
"""
import argparse, base64, gzip, hashlib, json, subprocess, sys
from collections import Counter
from itertools import product
from pathlib import Path

ROOT = Path(__file__).resolve().parent
TRANSFER = ROOT.parent / 'agent7-raw36-transfer'
sys.path.insert(0, str(ROOT.parent / 'agent31-three-hole-tnf'))
from generate_four_hole import masks, slot, move, refine, parse
sys.path.insert(0, str(ROOT.parent / 'agent10-tnf-multipump'))
from chunk_checks import partition

MOVES = [w+d+q for w,d,q in product('01','LR','ABCDEF')]
REPS = tuple(i for i in range(24) if i % 6 != 5)
BOUND = 1022
EXPECTED_OPEN = {4:5,10:38,16:8,18:134,19:94,20:82,22:32}
RECOVERY_CODES = ('101230333','101023202')
NS = 'BB6.Agent7Raw36Sweeps'
HEADER = '''import Raw36Cut
import Raw36TransferSweeps
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent29Raw36
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
'''
NODE = '''
const {makeSearch}=require('./search.cjs');
const spec=require('./candidate.json');
const i=Number(process.argv[1]);
const s=makeSearch(spec.codes,spec.options);
const p=s.parse(spec.parent);p[spec.query[2]]=i;
process.stdout.write(JSON.stringify(s.run(p,true)));
'''

def evidence():
    raw = gzip.decompress(base64.b64decode((TRANSFER/'fixture.tsv.gz.b64').read_text()))
    assert hashlib.sha256(raw).hexdigest() == '3bf03c9c90c64837cdd930d4af71e0d30b67ee7c4f86b479f9a67308a2eac089'
    rows = [line.split() for line in raw.decode().splitlines()]
    far = {parse(table):code for table,code in rows}
    recs = [json.loads(line) for line in (TRANSFER/'sweep_recipes.jsonl').read_text().splitlines() if line.strip()]
    sweep = {parse(r[1]):r[0] for r in recs}
    assert len(rows)==len(far)==350
    assert len(recs)==len(sweep)==len(set(sweep.values()))==16
    assert not set(far)&set(sweep)
    assert sweep[parse('1RB1LF_1RC0LA_0RD1RE_0LD1LB_1RB0LB_---0LE')]==360
    return far,sweep

def far_term(p,code):
    rev=int(code[0]); dfa=[int(x,36) for x in code[1:]]
    assert rev in (0,1) and len(dfa)%2==0 and all(0<=x<len(dfa)//2 for x in dfa)
    d,D,L,R,z=masks(p,rev,dfa)
    return f'.far {str(bool(rev)).lower()} {d} ⟨0,{D},{L},{R},{z}⟩'

def term(p,t,far,sweep,used):
    tag,*a=t
    if tag=='cycle':
        e,k,r,b=a
        return f'.cycle {e} {k} {str(r).lower()} ({b})'
    if tag=='last':
        n,s=a
        return f'.last {n} {slot(s)}'
    if tag=='far':
        return far_term(p,a[0])
    if tag=='open':
        assert p==parse(a[0]) and p not in used, (p,a)
        if p in far:
            used[p]='transfer-far'
            return far_term(p,far[p])
        if p in sweep:
            used[p]='sweep'
            ns=f'{NS}.M{sweep[p]}'
            return f'.proven {ns}.table {ns}.never'
        for code in RECOVERY_CODES:
            try:
                cert=far_term(p,code)
            except AssertionError:
                continue
            used[p]='recovered-far'
            return cert
        raise ValueError(('uncovered exact OPEN leaf',a[0]))
    if tag=='split':
        n,s,kids=a
        assert len(kids)==24 and p[s]=='---'
        return f'.split {n} {slot(s)} (byMove [\n'+',\n'.join(term(refine(p,s,mv),kid,far,sweep,used) for mv,kid in zip(MOVES,kids))+'])'
    raise ValueError(t)

def generate(i,limit,far,sweep,out):
    got=json.loads(subprocess.check_output(['node','-e',NODE,str(i)],cwd=ROOT))
    p=parse(got['parent']);used={}
    assert got['stats']['open']==EXPECTED_OPEN.get(i,0), (i,got['stats'])
    assert got['stats']['score']<=BOUND, (i,got['stats'])
    nm=f'kid{i:02d}';pexpr=f'(child {move(MOVES[i])})'
    body=HEADER+f'\ndef {nm} : Audit := {term(p,got["tree"],far,sweep,used)}\n\ntheorem {nm}_checked : zipCheck {BOUND} {pexpr} {nm} = true := by rfl\n'
    assert set(used)=={parse(t) for t in got['opens']}
    body,n=partition(body,limit)
    body+=f'''
theorem {nm}_bound : ∀ m, compatible {pexpr} m → WeightedBound {BOUND} m :=
  (certifiedZip {BOUND} {pexpr} {nm} (child_root {move(MOVES[i])}) (child_nohalt {move(MOVES[i])}) {nm}_checked).sound
#print axioms {nm}_bound
end BB6.Agent29Raw36
'''
    (out/f'Raw36Kid{i:02d}.lean').write_text(body)
    print(f'{nm}: {got["stats"]["nodes"]} nodes, score≤{got["stats"]["score"]}, {dict(Counter(used.values()))}, {n} chunks',flush=True)
    return used

def assemble(out):
    head=HEADER.replace('import Raw36Cut\nimport Raw36TransferSweeps\n','import Raw36SymmetryCut\n'+''.join(f'import Raw36Kid{i:02d}\n' for i in REPS))
    body=head+f'''
theorem children_bound : ∀ mv ∈ representatives, ∀ m,
    compatible (child mv) m → WeightedBound {BOUND} m := by
  intro mv hmv m hm
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
'''
    for q,w,r in product(range(6),range(2),range(2)):
        if q==5:
            body+=f'  · exact False.elim ((by decide : (⟨{str(bool(w)).lower()},{str(bool(r)).lower()},5⟩ : Move) ∉ representatives) hmv)\n'
        else:
            body+=f'  · exact kid{12*w+6*r+q:02d}_bound m hm\n'
    body+=f'''
theorem branch_bound (m : Machine) (hm : compatible branch m) : WeightedBound {BOUND} m :=
  branch_bound_from_twenty {BOUND} (by decide) children_bound m hm

theorem branch_cover : Cover (WeightedBound {BOUND}) branch :=
  Cover.leaf branch_bound
#print axioms children_bound
#print axioms branch_bound
#print axioms branch_cover
end BB6.Agent29Raw36
'''
    (out/'Raw36Branch.lean').write_text(body)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('children',nargs='*',type=int)
    ap.add_argument('--limit',type=int,default=300)
    ap.add_argument('--out',type=Path,default=ROOT)
    ap.add_argument('--assemble-only',action='store_true')
    a=ap.parse_args();a.out.mkdir(parents=True,exist_ok=True)
    if a.assemble_only:
        assert not a.children
        assemble(a.out);return
    selected=a.children or list(REPS)
    assert len(selected)==len(set(selected)) and set(selected)<=set(REPS)
    far,sweep=evidence()
    subprocess.run([sys.executable,str(ROOT.parent/'agent7-raw49'/'emit_sweep_recipes.py'),str(TRANSFER/'sweep_recipes.jsonl'),NS,str(a.out/'Raw36TransferSweeps.lean')],check=True)
    used={}
    for i in selected:
        found=generate(i,a.limit,far,sweep,a.out)
        assert not set(used)&set(found)
        used.update(found)
    if set(selected)==set(REPS):
        assert {p for p,v in used.items() if v=='transfer-far'}==set(far)
        assert {p for p,v in used.items() if v=='sweep'}==set(sweep)
        assert Counter(used.values())=={'transfer-far':350,'recovered-far':27,'sweep':16}
        assemble(a.out)
    print('EXACT OPEN MATCHES:',dict(Counter(used.values())),flush=True)

if __name__=='__main__':
    main()
