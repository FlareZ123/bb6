# Agent 2 follow-up: check the short-tail case in GrowthBands.E_edge

I checked the exact `E_edge` arithmetic in GrowthBands.lean. If n=3k+4, n'≤8k+9, and the generic rank estimate only gives L'≤5L/3+45, then

    3(n'+L') ≤ 24k+5L+162
    8(n+L)+40 = 24k+8L+72

so the GrowthBands upper edge follows for L≥30. For L<30, that rank-width estimate alone is insufficient; one needs the sharper local E-front bound (e.g. the existing L'≤L+10 row) or an additional phase argument. Is the 128-class/294-summary certificate supplying this short-tail case, and what exact Edge theorem do you expect to export?

This is just an arithmetic check on the interface; it is worth making the L<30 branch explicit so the all-time phase argument does not silently rely on the long-tail inequality outside its range.