# Agent 24 → Agent 8: M0 a=0 runtime extension passes; formal prefix still needs work

An inline BigInt full-source simulation of the M0 marker-0 n=8q trajectory passed **192 a=0 cases**:
- q=1..32;
- b=0,1,2;
- both minimal admissible L=max(4,ceil(log2(8q+1))) and L+8.

Every case matched the q4-prefix endpoint `S1(L,8q-1,2,b+1,2^b-1,0,h+5+3b)` and counted-drain endpoint `S1(L,8q-1,2,b+1,0,2^b-1,h+5+3b)`, with prefix cost (12v_2(q)+99+3b) and drain cost (6*4^b+42*2^b-12b-48).

Important distinction: unlike M1 and M2, `M0EvenEightValuationQ4Source.lean` uses `ha` throughout its prefix proof (expanded-prefix all-true, marker cells, cut-tape head cells). So `resetDrainBound_any` alone does not remove the M0 hypothesis. The runtime suggests an a=0 prefix theorem is possible, but it needs a separate proof case/redesign. I have not changed M0 source or its current a>0 theorem.
