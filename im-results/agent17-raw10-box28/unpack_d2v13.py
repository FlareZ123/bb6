#!/usr/bin/env python3
"""Restore saved discovery seeds; no repeat of ngram/RLE parameter search."""
import base64,gzip,hashlib,struct,sys,json
from pathlib import Path
D=Path(__file__).resolve().parent
from cuts import fixed_for,targets_for
out=Path(sys.argv[1]);out.mkdir(parents=True,exist_ok=True)
raw=base64.b64decode((D/'d2v13-seeds.b64').read_text())
assert hashlib.sha256(raw).hexdigest()=='0e33c7f851a56ff9566053d50dc27728ba277a3b3247a993283325ac34634377'
data=gzip.decompress(raw);pos=0
fixed=fixed_for(2,13)
open_rows=[[8,24,11,13,11,13,2,23,0,6,4,20],[8,24,11,13,11,13,2,23,0,10,4,20],[8,20,11,13,11,13,2,23,4,0,2,21],[8,20,11,13,11,13,2,19,4,24,0,6],[8,20,11,13,11,13,2,19,4,24,0,10],[8,24,11,13,11,13,2,19,2,17,4,0]]
summary={}
for t in targets_for(2):
    free=[i for i,v in enumerate(fixed) if v<0 and i!=t]
    for mode,n in [('ngram',1),('rle',8)]:
        count=struct.unpack_from('<H',data,pos)[0];pos+=2
        with (out/f'{mode}{t}.txt').open('w') as f:
            for j in range(count):
                a=struct.unpack_from('<I',data,pos)[0];pos+=4
                row=fixed[:];row[t]=0
                for i,k in enumerate(free):row[k]=((a>>(5*i))&31)-1
                params=list(data[pos:pos+n]);pos+=n
                f.write(' '.join(map(str,row+params+[0]))+'\n')
    (out/f'late{t}.json').write_text('[]\n')
    rr=[r for r in open_rows if r[t]==0]
    summary[t]={'open_rows':rr,'open_count':len(rr),'late_max_halt':[0,None]}
assert pos==len(data)
(out/'summary.json').write_text(json.dumps(summary,indent=2))
