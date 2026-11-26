"""Generate exact width-four block witness for residual 9015."""
import pathlib,sys
base=pathlib.Path(__file__).resolve().parent
sys.path.insert(0,str(base.parent/'agent48-raw139-f1-oneLA'))
sys.path.insert(0,str(base.parent/'agent48-raw139-f1-oneRA'))
from blockcert import generate
from package import block_source
table=[7,21,11,24,14,3,0,16,20,11,14,17]
c=generate(table,4,1,2,3,False,phase=False,event_limit=50000)
assert c is not None and c['left_states']==99 and c['right_nodes']==255
s=block_source(9015,table,c)
s=s.replace('BB6BlockFAR','BB6BlockFAR4').replace('BB6.Agent48F1OneRABlocks.H9015','BB6.Agent14E0LFResidual9015')
header='import BlockFAR4\nimport BlockFARBridge4\nimport FastThreeHoleAudit\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n'
out=pathlib.Path(sys.argv[1]);out.mkdir(parents=True,exist_ok=True)
(out/'E0LFResidual9015.lean').write_text(header+s)
