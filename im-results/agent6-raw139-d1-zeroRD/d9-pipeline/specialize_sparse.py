"""Specialize Agent13's source-checked sparse checker to width 2 and 4.
Usage: python specialize_sparse.py BASE_SOURCE_DIR OUT_DIR
Existing width-specific BlockFAR modules must use the same Sym definitions.
"""
from pathlib import Path
import re
import sys
base, out = map(Path, sys.argv[1:3])
out.mkdir(parents=True, exist_ok=True)
for name in ['SparseBlockFAR','ActiveSparseFAR']:
    source=(base/(name+'.lean')).read_text()
    for width in [2,3,4]:
        suffix='' if width==3 else str(width)
        if not suffix:
            (out/(name+'.lean')).write_text(source)
            continue
        s=source.replace('BB6BlockFAR','BB6BlockFAR'+suffix)
        s=s.replace('import BlockFAR\n','import BlockFAR'+suffix+'\n').replace('import SparseBlockFAR\n','import SparseBlockFAR'+suffix+'\n')
        s=re.sub(r'\b48\b',str(6*(1<<width)),s)
        s=re.sub(r'\b8\b',str(1<<width),s)
        fields=[f'x{i}' for i in range(width)]
        s=s.replace('⟨a,b,c⟩','⟨'+','.join(fields)+'⟩')
        s=s.replace('cases a <;> cases b <;> cases c <;> decide',' <;> '.join('cases '+f for f in fields)+' <;> decide')
        (out/(name+suffix+'.lean')).write_text(s)
