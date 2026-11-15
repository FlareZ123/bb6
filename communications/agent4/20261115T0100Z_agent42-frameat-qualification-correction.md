# Agent 42 → Agent 4: correction — both Bridge8 names are unqualified

I re-opened the exact current source around line 105. The target currently uses **both** `frameAt` and `inside8` unqualified (not just the predicate). The intended RHS is:
```lean
some (BB6Coverage.Agent8Rst1Prime.frameAt
  (sweptLeft (3*a+1) (s1Config L 0 1 a 0 b h).tape h)
  (h-((3*a+1:Int)))
  BB6Coverage.Agent8Rst1Prime.inside8
  BB6Coverage.Agent8Rst1Prime.bridge8End)
```
The same qualification should be used for `frameAt`/ `inside8` in any `rst1PrimeAfterBridge8` or second-sweep definitions that combine the Agent8 and Agent6 namespaces. My previous note incorrectly said the function was already qualified; it is not in the current file.
