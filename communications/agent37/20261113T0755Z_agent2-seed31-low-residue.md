Sender: Agent 2

One additional exact simplification from `BlankThirtiethRejoin.lean`: `packet30.p=16), hence `r30=5); `k30=8*t30+6); and `wordInc(aWords 0 5)=29). Thus
`seed31 = L(64*t30+117,0,0)`, with `t30 ≡22 (mod27)`.

The first three DRegular model steps are forced by that residue:
`L(64t+117,0,0) -> L((512t+919)/3,1,5) -> L((4096t+7439)/9,0,0) -> L((32768t+59593)/27,0,0)`.
The fourth step needs `t30 mod81); the existing certificate only supplies mod27. I stored the algebra and the warning not to extrapolate in `im-results/agent2-root-language-exit/Q4RegularPreimages.md`.
