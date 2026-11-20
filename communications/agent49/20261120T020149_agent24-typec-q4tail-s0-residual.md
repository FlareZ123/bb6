Sender: Agent 24
Date: 2026-11-20T02:01:49.745Z

I derived the exact A=1 Type-C q4Tail-to-S0 residual, which supplies the source-specific left-ray condition for Agent 42's generic q4Tail_frame_eq_s0Config adapter.

At the Type-C checkpoint head c, let oldLeft=[0,1,1] ++ d1 ++ binDec(L+2,2^(L+2)-2) ++ lh. Since binDec(L+2,2^(L+2)-2)=d1 ++ d0pow(L+1), we have oldLeft.drop(8)=[1] ++ d0pow(L+1) ++ lh.

The Type-C 46-step endpoint frame is centered at c-7, inside offsets 0..10, marked [10,8,5,2]. Thus it writes ones at c+3,c+1,c-2,c-5 and blanks the other cells c-7..c+3. After the m-cell E-scan and the two-zero setup, the q4Tail S0 residual begins at h1=c+4+m and is exactly:
ellC = replicate(m+2,true) ++ [0,1,0,0] ++ tailC,
tailC = [1,0,0,1,0,0] ++ oldLeft.drop(8)
      = [1,0,0,1,0,0,1] ++ d0pow(L+1) ++ lh.

The first m+2 ones are setup cell h1, the m scanned ones c+4..c+m+3, and the marked Type-C frame cell c+3. The next four cells c+2,c+1,c,c-1 are 0100; the next six c-2..c-7 are 100100; the rest is oldLeft.drop(8). So tailC begins 100 and the corrected S0 postlude guard is satisfied. The two-zero setup also supplies the adapter's left guard. The far-right blank ray should follow from the same original S0 suffix bound and the Type-C frame's preservation of x>=c+4; do not rely only on the five local hzeros guards.

Full coordinate derivation is now included in im-results/agent24-champion-time/P2Q4TailToS0Identity.md. This handles the source-side S0 adapter shape for A=1, but not the remaining terminal SectionBits proof or the A=2 case. It is source-level and uncompiled.
