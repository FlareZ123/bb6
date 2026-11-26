"""Pinned candidate manifests on the SHA-checked raw59 source enumeration.

The gzip records are data, not proofs. Decode via python upgrade_data.py.
Each candidate is accepted only by kernel-checked source theorems.
"""
import base64,gzip,subprocess,json
from quotient_search import search
from emit_mask import emit as emit_quotient
from pathlib import Path
import generate_asym as asym
ROOT=Path(__file__).resolve().parent
def read(name):
    return gzip.decompress(base64.b64decode((ROOT/(name+'.b64')).read_text())).decode().splitlines()
SWEEPS=read('upgrade_sweeps')
NGRAMS=read('upgrade_ngrams')
assert len(SWEEPS)==214 and len(NGRAMS)==141

def add_ngrams(raw,folder,opens,certs,pumps,imports):
    rows=[x.split() for x in NGRAMS if x.split()[0]==raw]
    exe=folder/'ngram_asym'
    subprocess.run(['g++','-O3','-std=c++17',str(ROOT/'ngram_asym.cpp'),'-o',str(exe)],check=True)
    use_quotient=raw in ('0LA','0LB','0LF','1LB','1LE')
    records=[]
    for b,i,l,r,n,eL,eR in rows:
        table=opens[int(i)]
        if table in certs or table in pumps:continue
        # Keep exceptionally large proof obligations visible for later sharding.
        if int(n)>40000 and not use_quotient:continue
        data=subprocess.check_output([str(exe)],input=f'{i} {table} {l} {r}\n',text=True).strip().split(maxsplit=1)
        assert data[0]==i
        actual=data[1].split();assert actual[:3]==[l,r,n]
        assert len(actual[3].rstrip(',').split(','))==int(eL)
        assert len(actual[4].rstrip(',').split(','))==int(eR)
        if use_quotient:
            record=search(' '.join(data),table,verbose=False)
            record.update(branch=raw,index=int(i),original_states=int(n),widths=[int(l),int(r)])
            records.append(record)
            name=emit_quotient(folder,f'Raw59Upgrade{raw}NG{i}',record)
        else:
            name=asym.emit(folder,f'Raw59Upgrade{raw}NG{i}',table,data[1])
        ns=asym.BASE+'.'+name
        pumps[table]=(ns+'.table',ns+'.never')
        imports.append(name)
    if use_quotient:
        (folder/'quotient_witnesses.json').write_text(json.dumps(records,separators=(',',':'))+'\n')
if __name__=='__main__':
    print('SWEEPS (branch id entry q side prefix block suffix delta)')
    print('\n'.join(SWEEPS))
    print('NGRAMS (branch id L R configurations left-window-keys right-window-keys)')
    print('\n'.join(NGRAMS))
