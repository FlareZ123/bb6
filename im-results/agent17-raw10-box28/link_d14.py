#!/usr/bin/env python3
"""Link six accepted D0=14 source cuts without rerunning their discovery.
Lean checks each exact source-domain identity and bound inequality.
"""
from pathlib import Path
import argparse, json, re, hashlib

CODES=(3,4,17,18,19,20)

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--inputs',type=Path,required=True)
    p.add_argument('--out',type=Path,required=True)
    a=p.parse_args()
    a.out.mkdir(parents=True,exist_ok=True)
    bounds={}
    hashes={}
    for d in CODES:
        matches=list(a.inputs.rglob(f'Box28D{d}Closure.lean'))
        assert len(matches)==1,(d,matches)
        root=matches[0]
        match=re.search(r'theorem sourceBound\s*:\s*∀ m, Fits sourceDomain m → WeightedBound (\d+) m',root.read_text())
        assert match,(d,root)
        bounds[d]=int(match.group(1))
        for path in root.parent.glob('*.lean'):
            dest=a.out/path.name
            data=path.read_bytes()
            if dest.exists():
                assert dest.read_bytes()==data,('conflicting module',path.name)
            else:
                dest.write_bytes(data)
            hashes[path.name]=hashlib.sha256(data).hexdigest()
    B=max(11,*bounds.values())
    lines=['import Box28Orbit',*[f'import Box28D{d}Closure' for d in CODES],
           '', 'namespace BB6.Agent17.Box28D14Complete',
           'open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box BB6.Agent49BoxBridge',
           'open BB6.Agent13.Box17 (decode)',
           'open BB6.Agent17.Box28Orbit BB6.Agent17.Box28Symmetry',
           'set_option maxRecDepth 100000',
           'set_option maxHeartbeats 0',
           '',
           f'theorem cut_bounds : ∀ d ∈ hardCodes, ∀ m, Fits (sourceCutFor 14 d) m → WeightedBound {B} m := by',
           '  intro d hd m hm',
           '  have hc : '+ ' ∨ '.join(f'd = {d}' for d in CODES)+' := by',
           '    simpa [hardCodes] using hd',
           '  rcases hc with '+'|'.join('h' for _ in CODES)+' <;> subst d']
    for d in CODES:
        ns=f'BB6.Agent13.Box28D{d}'
        lines.extend([f'  · have h := {ns}.sourceBound m (show Fits {ns}.sourceDomain m from hm)',
                      '    intro k j hk hj',
                      '    exact Nat.le_trans (h k j hk hj) (by decide)'])
    lines.extend(['',f'theorem parent_bound : ∀ m, Fits raw10Remainder[28]! m → m (3,false) = decode 14 → WeightedBound {B} m :=',
                  f'  fun m hm h0 => d14_bound {B} (by decide) cut_bounds m hm h0',
                  '', '#print axioms cut_bounds','#print axioms parent_bound',
                  'end BB6.Agent17.Box28D14Complete',''])
    (a.out/'Box28D14Complete.lean').write_text('\n'.join(lines))
    (a.out/'link-inputs.json').write_text(json.dumps({'bounds':bounds,'common_bound':B,'source_sha256':hashes},indent=2)+'\n')
    print('D0=14 common weighted bound:',B,'cut bounds:',bounds,flush=True)
if __name__=='__main__':main()
