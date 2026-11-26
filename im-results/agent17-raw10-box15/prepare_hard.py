"""Emit the final literal box15 nonhalting certificate from the finite FAR search.
The generator is untrusted; Lean checks all resulting certificate rows."""
from pathlib import Path
import subprocess,sys
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
FAR=ROOT/'im-results'/'agent13-block-far'
sys.path.insert(0,str(FAR))
from generate_multi import generate
out=HERE/'generated'
out.mkdir(exist_ok=True)
subprocess.run([sys.executable,str(FAR/'specialize.py'),'4'],check=True)
mirror=(ROOT/'im-results'/'agent5-q0-held-blockfar'/'MirrorTransport.lean').read_text()
(out/'MirrorTransport4.lean').write_text(mirror.replace('import BlockMacro','import BlockMacro4').replace('BB6BlockFAR','BB6BlockFAR4'))
table='1RB0LF_1LC0RB_0LE0LD_1LC1LE_1LA0RA_1LD---'
generate(table,out,width=4,cap=1,mod=1,runs=6,flip=True,name='Box15Hard',left_mode='suffix',minimize_left=True)
