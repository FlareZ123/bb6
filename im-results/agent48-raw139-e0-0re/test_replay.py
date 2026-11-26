"""Compare the C++ witness producer against the existing Python tree scanner."""
import collections
import json
import random
import subprocess
import sys
from scan import tree

def main(binary):
    rng=random.Random(480)
    for i in range(120):
        p=[rng.randrange(24) for _ in range(12)]
        p[0]=7
        for j in rng.sample(range(1,12),1+i%3):
            p[j]=24
        counts=collections.Counter()
        opens=[]
        limit=5+i%40
        t=tree(p,counts,opens,limit,2)
        result=json.loads(subprocess.check_output(
            [binary,str(limit),'2',*map(str,p)],stderr=subprocess.DEVNULL))
        assert result['tree']==json.loads(json.dumps(t)),(i,p)
        assert result['open']==opens
        assert all(result['counts'][k]==counts[k] for k in result['counts'])
    print('C++ exact tree equality on 120 fixtures')
if __name__=='__main__':
    main(sys.argv[1])
