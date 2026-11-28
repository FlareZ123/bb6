"""Cross-parent FAR replay over exact source-indexed direct D1 OPEN leaves.

This is a candidate discovery/reuse stage. The original Lean FAR checker must
accept each literal witness before any theorem or weighted Cover is claimed.
Unlike another whole-tree search, only saved OPEN rows are evaluated here.
"""
import argparse,base64,gzip,json,lzma,subprocess,hashlib,tempfile
from collections import Counter
from pathlib import Path

ROOT=Path(__file__).resolve().parent
R29=ROOT.parent/'agent29-raw36'
R7=ROOT.parent/'agent7-raw36-b1le'
TRANSFER=ROOT.parent/'agent7-raw36-transfer'
def dec(p):
    raw=base64.b64decode(p.read_text())
    return json.loads(lzma.decompress(raw) if '.xz.' in p.name else gzip.decompress(raw))

def far_codes():
    codes=set(json.loads((R29/'candidate.json').read_text())['codes'])
    codes.update(('101230333','101023202'))
    for line in gzip.decompress(base64.b64decode((TRANSFER/'fixture.tsv.gz.b64').read_text())).decode().splitlines():
        z=line.split()
        if len(z)>1: codes.add(z[1])
    for p in sorted(R29.glob('d1-*-evidence.json.gz.b64')):
        d=dec(p)
        for _,c in d.get('far',[]):codes.add(c)
    for p in sorted(R29.glob('*-compact.json.xz.b64')):
        d=dec(p)
        for row in d.get('data',[]):
            if isinstance(row,str):codes.add(row)
    for p in sorted(R7.glob('evidence*.json.xz.b64')):
        d=dec(p)
        for row in d.get('data',[]):
            if isinstance(row,list) and row and row[0]=='f':codes.add(row[1])
    for f in (R29/'b1-9-recovered.tsv',):
        if f.exists():
            for line in f.read_text().splitlines():
                z=line.split()
                if len(z)>1 and z[1][0] in '01' and len(z[1])%2==1:codes.add(z[1])
    # Skip malformed historic encodings; C++ independently validates witness.
    codes={c for c in codes if isinstance(c,str) and len(c)>2 and len(c)%2==1 and c[0] in '01'
           and all(('0'<=v<='9') or ('a'<=v<='z') for v in c[1:])}
    return sorted(codes,key=lambda x:(len(x),x))

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--index',required=True,type=int)
    ap.add_argument('--census',required=True,type=Path);ap.add_argument('--out',required=True,type=Path)
    ap.add_argument('--maxd',type=int,default=3);a=ap.parse_args()
    a.out.mkdir(parents=True,exist_ok=True)
    inp=json.loads(gzip.decompress(a.census.read_bytes()))
    assert inp['parent']=='1RB---_1RC---_0RD---_0LD'+[w+d+q for w in '01' for d in 'LR' for q in 'ABCDEF'][a.index]+'_------_------'
    keys=inp['opens'];assert len(keys)==len(set(keys))==inp['stats']['open']
    bank=far_codes()
    (a.out/'tables.txt').write_text('\n'.join(keys)+'\n')
    (a.out/'codes.txt').write_text('\n'.join(bank)+'\n')
    subprocess.run(['g++','-std=c++17','-O3',str(R29/'far_recover.cpp'),'-o',str(a.out/'far_recover')],check=True)
    with (a.out/'found.tsv').open('w') as fo,(a.out/'search.log').open('w') as fe:
        subprocess.run([str(a.out/'far_recover'),str(a.out/'tables.txt'),str(a.out/'codes.txt'),str(a.maxd)],check=True,stdout=fo,stderr=fe)
    pairs=[l.split() for l in (a.out/'found.tsv').read_text().splitlines() if l]
    assert len(pairs)==len(set(k for k,c in pairs))
    found=dict(pairs);assert set(found)<=set(keys)
    remain=sorted(set(keys)-set(found))
    (a.out/'remaining.txt').write_text('\n'.join(remain)+'\n')
    (a.out/'candidate.json').write_text(json.dumps({'index':a.index,'bound':inp['stats']['score'],
      'parent':inp['parent'],'cut':inp['cut'],'digest':hashlib.sha256('\n'.join(sorted(t.replace('_','') for t in keys)).encode()).hexdigest(),
      'fars':pairs,'missing':remain},separators=(',',':')))
    summary={'index':a.index,'canonical_OPEN':len(keys),'far_seeds':len(bank),
      'cross_FAR_hits':len(found),'remaining':len(remain),'dmax':a.maxd,
      'distinct_winners':len(set(found.values())),
      'remaining_sha256':hashlib.sha256('\n'.join(remain).encode()).hexdigest()}
    (a.out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary),flush=True)

if __name__=='__main__':main()
