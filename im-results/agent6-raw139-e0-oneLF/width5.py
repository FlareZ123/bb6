"""Generate the exact width-five certificate sources, no search replay."""
import json, pathlib, sys
ROOT=pathlib.Path(__file__).resolve().parents[2]
sys.path[:0]=[str(ROOT/'im-results/agent48-raw139-f1-oneRA'),str(ROOT/'im-results/agent48-raw139-f1-oneLA')]
from blockcert import generate
from package import block_source as original_block_source
def emit(out, rec):
    i,t=rec['id'],rec['table']
    w,c,m,z,f,ph,*_=rec['block5']
    data=generate(t,w,c,m,z,f,event_limit=150000,phase=ph)
    assert data is not None,(i,rec)
    print('width5',i,'minimized',data['left_states'],data['right_nodes'],flush=True)
    s=original_block_source(i,t,data).replace('BB6.Agent48F1OneRABlocks','BB6.Agent6OneLFWidth5').replace('BB6BlockFAR.','BB6BlockFAR5.')
    if f:
        s=s.replace('theorem same : ctr =','theorem same : BB6Coverage.FAR.reflectPartial ctr =')
        s=s.replace('BB6BlockFAR5.transfer_never machine m (by simpa only [← same] using hm) forever','BB6Coverage.FAR.reflectNever m (BB6BlockFAR5.transfer_never machine _ (by simpa only [← same] using BB6Coverage.FAR.reflectCompatible ctr m hm) forever)')
    (out/f'OLFWidth{i}.lean').write_text('import BlockFARBridge5\nimport FastThreeHoleAudit\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n'+s)
if __name__=='__main__':
    out=pathlib.Path(sys.argv[1]);out.mkdir(parents=True,exist_ok=True)
    for r in json.loads(pathlib.Path(__file__).with_name('holdouts.json').read_text())['unresolved']:
        if 'block5' in r and (len(sys.argv)==2 or r['id']==int(sys.argv[2])):emit(out,r)
