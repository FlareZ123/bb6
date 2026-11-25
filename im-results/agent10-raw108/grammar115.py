"""Generate two-counter transfer invariant for raw108/0RF #115."""
from countergen import macro,table,C,clean,lit,rep,opaque
from pathlib import Path
def main():
    ls=['import SweepPumping','namespace BB6.Agent10Raw108RF115','open BB6Coverage BB6Coverage.Agent31Pump','set_option maxRecDepth 100000','set_option maxHeartbeats 0',table('1RB---_1RC0RF_0RD1LF_1LD1RE_0RA1LB_0LE0LF')]
    P='000100101';Q='000010001';M1='000100110001';M2='000001';R=opaque('R')
    def c(r):return C(4,(),clean(r))
    for nm,ss,tt in [('phaseA',M1,P+M2),('phaseB',M2,P),('phaseC',Q,M1),('phaseEnd','0001',P+'001')]:
        tail=() if nm=='phaseEnd' else R
        s,a,b=macro(nm,c(lit(P)+rep(P)+lit(ss)+tail),c(lit(P)+rep(P)+lit(tt)+tail));ls.append(s)
    s,a,b=macro('phaseReset',c(lit(P)+rep(P)+lit('001')),c(lit(M1)+rep(Q)+lit('0001')));ls.append(s)
    ls.append(Path(__file__).with_name('RF115Grammar.txt').read_text())
    Path(__file__).with_name('Raw108RF115.lean').write_text('\n\n'.join(ls)+'\n')
if __name__=='__main__':main()
