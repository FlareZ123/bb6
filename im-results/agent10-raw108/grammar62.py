"""Generate arbitrary-word carry/drain proof for raw108/0RF #62."""
from countergen import macro,table,C,clean,lit,rep,opaque
from pathlib import Path
def main():
    ls=['import SweepPumping','namespace BB6.Agent10Raw108RF62','open BB6Coverage BB6Coverage.Agent31Pump','set_option maxRecDepth 100000','set_option maxHeartbeats 0',table('1RB1LA_1RC0RF_0RD---_1LD1RE_0LA1LB_1RA0LE')]
    R=opaque('R')
    def c(q,l,r):return C(q,clean(l),clean(r))
    for nm,st,tg in [
      ('finishRaw',c(0,lit('11111')+rep('11')+lit('01'),R),c(0,(),lit('10000111')+rep('11')+R)),
      ('entryRaw',c(0,(),lit('100001')+rep('11')+lit('00')+R),c(1,lit('11111')+rep('11')+lit('01'),lit('00')+R))]:
        s,a,b=macro(nm,st,tg);ls.append(s)
    ls.append(Path(__file__).with_name('RF62Grammar.txt').read_text())
    Path(__file__).with_name('Raw108RF62.lean').write_text('\n\n'.join(ls)+'\n')
if __name__=='__main__':main()
