"""Prepare the pinned packed-prefix source for safe larger-K resumption.

No changes to carry equations, endpoint sets, margin tests or branch selection.
Persist the last completed block, even when the *next* stage would exceed K.
A future invocation must choose K >= n+s and recheck the saved maximum gap.
"""
from pathlib import Path
import sys

src, dst = map(Path, sys.argv[1:])
s = src.read_text()

def once(old, new):
    global s
    if s.count(old) != 1:
        raise SystemExit(f"Expected exactly one match: {old!r}")
    s = s.replace(old, new, 1)

once(
    'if(get()!=0x50314331||get()!=n||get()!=K||get()!=h||get()!=half)throw std::runtime_error("checkpoint parameters");',
    'if(get()!=0x50314331||get()!=n)throw std::runtime_error("checkpoint parameters");int oldK=get();if(oldK>K||get()!=h||get()!=half)throw std::runtime_error("checkpoint parameters");'
)
once(
    'load(path,n,K,h,half,s,maxgap,gs);',
    'load(path,n,K,h,half,s,maxgap,gs);if(!safe(maxgap))throw std::runtime_error("checkpoint margin");'
)
once(
    'if(s+h+n>K)break;s+=h;gs=std::move(next);save(path,n,K,h,half,s,maxgap,gs);',
    's+=h;gs=std::move(next);save(path,n,K,h,half,s,maxgap,gs);'
)
dst.write_text(s)
