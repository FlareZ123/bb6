"""Accelerated reproducible canonical tree generation for complete Agent7 B1 banks."""
import argparse,base64,gzip,json,subprocess,tempfile
from pathlib import Path
from generate_cover import main, MOVES
ROOT=Path(__file__).resolve().parent
R29=ROOT.parent/'agent29-raw36'
def prepare(index,out,limit=300):
    spec=json.loads((R29/'candidate.json').read_text())
    assert spec['options']['short']==160 and spec['options']['long']==2000
    old=gzip.decompress(base64.b64decode((ROOT.parent/'agent7-raw36-transfer'/'fixture.tsv.gz.b64').read_text())).decode()
    bank=list(dict.fromkeys([*spec['codes'],'101230333','101023202',*(line.split()[1] for line in old.splitlines())]))
    parent='1RB---_1RC'+MOVES[index]+'_0RD---_0LD1LB_------_------'
    cut=max(4,index%6+1)
    with tempfile.TemporaryDirectory() as tmp:
        t=Path(tmp);(t/'seeds.txt').write_text('\n'.join(bank)+'\n')
        subprocess.run(['g++','-std=c++17','-O3',str(ROOT/'scan_tree.cpp'),'-o',str(t/'scan')],check=True)
        data=json.loads(subprocess.check_output([str(t/'scan'),parent,str(cut),str(t/'seeds.txt'),str(t/'tree.json')]))
        data['tree']=json.loads((t/'tree.json').read_text())
        print(data['stats'],flush=True)
        (t/'full.json').write_text(json.dumps(data,separators=(',',':')))
        main(t/'full.json',out,limit,index)
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('index',type=int);ap.add_argument('--out',type=Path,default=R29);ap.add_argument('--limit',type=int,default=300);a=ap.parse_args()
    prepare(a.index,a.out,a.limit)
