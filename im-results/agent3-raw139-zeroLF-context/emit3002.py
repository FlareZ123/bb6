"""Generate exact width-four block-FAR certificate for E0=0LF residual 3002."""
from pathlib import Path
import sys
base=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(base/'agent48-raw139-f1-oneLA'))
sys.path.insert(0,str(base/'agent48-raw139-f1-oneRA'))
from blockcert import generate
from package import block_source

TABLE=[7,23,11,13,14,1,24,16,20,11,3,6]

def key(xs,a):
    if not xs and a==0:
        return ()
    pref,tail,m,o=xs or ((),(),0,0)
    return ((pref+(a,))[:1],(tail+(a,))[-4:],(m+1)%2,(o+a.bit_count())%3)

def emit(out):
    c=generate(TABLE,width=4,flip=False,event_limit=100000,left_key=key)
    assert c is not None,"candidate synthesis failed"
    print("minimized",c['left_states'],c['right_nodes'],flush=True)
    src=block_source(3002,TABLE,c)
    src=src.replace('BB6BlockFAR','BB6BlockFAR4').replace(
        'BB6.Agent48F1OneRABlocks.H3002','BB6.Agent3E0LFResidual3002')
    header=('import BlockFAR4\nimport BlockFARBridge4\nimport FastThreeHoleAudit\n'
            'set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n')
    out.mkdir(parents=True,exist_ok=True)
    (out/'E0LFResidual3002.lean').write_text(header+src)

if __name__=='__main__':
    emit(Path(sys.argv[1]))
