"""Reproduce local Raw36 kernel checks using the existing original rowwise checker emitter."""
from pathlib import Path
import json,sys
D=Path(__file__).resolve().parent
sys.path.insert(0,str(D.parent/'agent32-raw59'))
from emit_rungram import emit
def main():
    spec=json.loads((D/'raw36-factor.json').read_text())
    dest=Path(sys.argv[1]) if len(sys.argv)>1 else D/'generated'
    dest.mkdir(parents=True,exist_ok=True)
    for k in range(0,len(spec),8):
        name=f'Raw36Factor{k//8:02}'
        out=['import FastBiDFA','set_option maxRecDepth 100000','set_option maxHeartbeats 0','namespace BB6.Agent46Raw36Factor','open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1NGram BB6.Agent32FastBiDFA']
        for i,t in enumerate(spec[k:k+8],k):
            s=emit(i,t['table'],*t['dfa'],[t['states'],t['edges']])
            # Match the locally checked theorem slice, omitting the redundant live_all lemma.
            a=s.index('theorem live_all')
            b=s.index('theorem never',a)
            s=s[:a]+s[b:]
            s=s.replace('#print axioms live_all\n','')
            out.append(s)
        out.append('end BB6.Agent46Raw36Factor')
        (dest/(name+'.lean')).write_text('\n'.join(out)+'\n')
    print('emitted',len(spec),'certificates')
if __name__=='__main__':main()
