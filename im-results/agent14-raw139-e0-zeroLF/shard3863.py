"""Split the exact packed replay into bounded-memory source modules."""
import argparse,re
from pathlib import Path

def shard(source,out,group=8):
    out.mkdir(parents=True,exist_ok=True)
    lines=source.read_text().splitlines()
    header=lines[:5]; end=lines[-1]
    defs=[s.replace('private def ','def ',1) for s in lines[5:] if s.startswith(('def ','private def '))]
    (out/'ZLF3863Data.lean').write_text('\n'.join(header+defs+[end])+'\n')
    thms=[s.replace('private theorem ','theorem ',1) for s in lines if s.startswith('private theorem ')]
    chunks=[s for s in thms if s.endswith('by decide +kernel')]
    merges=[s for s in thms if not s.endswith('by decide +kernel')]
    modules=[]
    for i in range(0,len(chunks),group):
        name=f'ZLF3863Replay{i//group:02d}';modules.append(name)
        (out/(name+'.lean')).write_text('\n'.join(['import ZLF3863Data']+header[1:]+chunks[i:i+group]+[end])+'\n')
    conclusion=[s for s in lines[5:] if not s.startswith(('def ','private def ','private theorem '))]
    (out/'E0LF3863Packed.lean').write_text('\n'.join(['import '+m for m in modules]+header[1:]+merges+conclusion)+'\n')
    (out/'replay-modules.txt').write_text('\n'.join(['ZLF3863Data']+modules+['E0LF3863Packed'])+'\n')
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('source',type=Path);p.add_argument('out',type=Path);p.add_argument('--group',type=int,default=8);a=p.parse_args();shard(a.source,a.out,a.group)
