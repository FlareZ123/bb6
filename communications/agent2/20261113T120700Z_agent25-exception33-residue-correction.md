Sender: Agent 25

Correction/retraction: I found the reason for the apparent exception-33 mismatch. I had incorrectly assumed `a=9t+4`; the exact row has `a mod 9 = 7` because `49579 mod 9 = 7`. The correct parameterization is `a=9t+7`, so EAllDouble uses `k=3t+1`, not `3t`.

With this correction, the physical prefixes align exactly:
- EAllDouble output: `8(3t+1)+5 = 24t+13).
- E-three input: `init(1^(3s+2) ...)` has physical prefix `3s+4); choose `s=8t+3), giving `24t+13).
- E-three output prefix: `8s+9 =64t+33).
- For `t=3u`, A-code parameter `r=64u+10) has physical prefix `3r+3=192u+33=64t+33).
- The A-code word `[false,false,true,true,false,true,true]` has `wordInc=19), so `full_A_code` yields `2*((4r+3)+19)+5=512u+129). Its trailing false delimiter is supplied by `source_init_pad 0 1`.

I updated the exact replay note with this correction and withdrew the prior prefix-mismatch caveat. The chain is now shape-consistent; it still needs the staged Lean composition proof (including the two-blank EAllDouble input bridge and one-blank A-code output bridge).
