# Two counted RLE halters: first experimental checkpoint

Upstream cryptids revision d1d231afe3a5f6310ac9f956d5687b5a45d7a13d. The accepted upstream IsHalt witnesses are unweighted. This investigation adds the primitive-move clock to the shared RleStackEngine. It is not yet a Lean score theorem.

| Machine | Raw parent | Ordinary moves (candidate) | Score with halt query |
|---|---:|---:|---:|
| `1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RDHHH` | 9 | 111579188581812927653348117002306046024821208051411619955580898884568781 | 111579188581812927653348117002306046024821208051411619955580898884568782 |
| `1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LAHHH` | 23 | 932242535661307148726923126800831715518673957228 | 932242535661307148726923126800831715518673957229 |

An independent BigInt translation of the executable RleStackEngine definitions reproduced each exact upstream checkpoint (including all compressed segment fields and both stack items) and the halt flag. The raw9 replay used 18089 non-padding RLE steps out of 18500; raw23 used 9101 out of 9500. The last RLE transition is the three ordinary moves to the halt query. Both machine-specific rule families use exactly the same primitive counts, by their execute n witnesses.

The replay's cost formulas count concatenations of those witnesses, with the following notation: S = sum over clean segments (r,c) of c*(6r+26), T(q)=q(q-1)/2. All costs below count ordinary moves and exclude the halt query.

- rule_B_nil / BR_nil 1, B_zero 4, B_succ 2, BR_zero 2, BR_one 4, BR_add_two 5, DR0_nil 3, DR0_zero 4, DR0_succ 3, C_nil 1, C_zero_nil 3, C_zero_zero 5, C_zero_one 17, C_zero_add_two 4, C_one_nil 5, C_one_zero 7, C_one_succ 6, C_add_two_halt 3.
- B_succ_step = 4; C_one_prefix(c)=4c+6; C_r_add_three(r)=4r+11; C_blkL_pow(q,r)=q(4r+11); C_bot_four(r)=4r+12; DR0_bot(k)=6k+14; DR0_bot_zeros(q,k)=q(6k+9q+9); BR_blkR_one(r)=2r+15; BR_blkR_succ(k,r)=(k+1)(2r+15).
- clean_sweep_core(S,b)=S+6b+41; clean_DR0_one(c,S,b)=6c+S+6b+46; clean_DR0_zeros(q,c,S,b)=q(6c+S+6b+50+6(q-1))+18T(q).
- clean_RNIL_one(c,S,b)=6c+S+6b+57; clean_RNIL_zero_pow(q,S,b)=q(S+6b+57+6(q-1))+20T(q).
- clean_P1_pow(q,r,S,b)=q(10r+S+6b+75+6(q-1))+(6r+38)T(q).
- P2_one(0,S,b)=S+6b+73; P2_one(r,S,b), r>0, with x=r-1, equals (x+2)(S+6b)+165+116x+6x²+18T(x).
- P2_pow(q,r,S,b)=q*P2_one(r,S,b+(q-1)(r+1))+(r+1)(18r+38)T(q).

These formulas use the final bottom b argument of each upstream macro, not its input bottom; for q=0 the entire cost is zero. Pack/unpack has cost zero. The one ordinary move from blank to ckpt0 is added separately.

A complete weighted last-hole Cover would follow for either exact table from a formal HaltsAfter n theorem and champion bound n+6 <= B: every other completion of its one hole is an all-ordinary total machine, hence cannot halt. The current result is candidate arithmetic only. Do not consume either leaf in the accepted global roster yet.
