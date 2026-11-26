#!/usr/bin/env python3
import subprocess
import re
rows = [
    (1,25000,20156,4844),
    (25001,50000,20210,4790),
    (50001,200000,121287,28713),
    (200001,300000,80812,19188),
    (300001,600000,242609,57391),
    (600001,1000000,323494,76506),
    (1000001,1661786,535129,126657),
]
end = 0
for lo, hi, sieve, sparse in rows:
    assert lo == end+1
    out = subprocess.check_output(["./needle11","11","1","0","1",str(lo),str(hi)],text=True)
    print(out,end="",flush=True)
    f = dict(re.findall(r"(\w+)=([^ ]*)",out.strip()))
    assert f["range"] == f"{lo}..{hi}" and int(f["cut"]) == 1661786
    assert int(f["sieve"]) == sieve and int(f["sparse"]) == sparse
    assert all(int(f[k]) == 0 for k in ("exact","extras","largeZero"))
    assert f["parents"] == "" and sieve+sparse == hi-lo+1
    end = hi
assert end == 1661786
print("COMPLETE: r=11 has no predecessor")
