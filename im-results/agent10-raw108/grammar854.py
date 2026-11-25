"""Generate kernel-checked arbitrary-word invariant for raw108/0LF leaf854."""
from countergen import macro,table,C,clean,lit,rep,opaque
from pathlib import Path

def main():
    code='1RB0LF_1RC0LF_0RD---_1LD1RE_0RB1LB_0LA0RE'
    ls=['import SweepPumping','namespace BB6.Agent10Raw108LF854','open BB6Coverage BB6Coverage.Agent31Pump','set_option maxRecDepth 100000','set_option maxHeartbeats 0',table(code)]
    P='0101';Z='0000';Cb='1100';O='0010';T='0110';U='0100';R=opaque('R')
    def e(l,r):return C(4,clean(l),clean(r))
    for nm,rr,tt in [('scanZ',lit(Z)+R,lit(Cb)+rep(Z)+lit(T)+R),('scanC',lit(Cb)+R,lit(Cb)+rep(Z)+lit(U)+R),('scanEnd',lit('11'),lit(Cb)+rep(Z)+lit('01'))]:
        s,a,b=macro(nm,e(lit(P)+rep(P)+lit('00'),rr),e(lit('00'),tt))
        ls.append(s)
    for nm,rr,tt in [('markZ',lit('0'+Z)+R,lit(Z)+rep(Z)+lit(Cb)+R),('markT',lit('0'+T)+R,lit(Z)+rep(Z)+lit(O)+R),('markEnd',lit('001'),lit(Z+Z)+rep(Z)+lit('11'))]:
        s,a,b=macro(nm,e(lit('01')+rep(P)+lit('011'),rr),e(lit('00'),tt),e(rep(P)+lit('01011'),rr))
        ls.append(s)
    ls.append(Path(__file__).with_name('LF854Grammar.txt').read_text())
    Path(__file__).with_name('Raw108LF854.lean').write_text('\n\n'.join(ls)+'\n')
if __name__=='__main__':main()
