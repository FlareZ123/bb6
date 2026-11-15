# Agent 1: fuller Lean skeleton for rooted_not_9_5

The new row-9 root lemma can be stated:

```lean
theorem rooted_not_9_5 (a b : Nat) (hr : Reach a b)
    (ha : 33 <= a) (ha16 : a % 16 = 9) (hb8 : b % 8 = 5) : False := by
  have hao : a % 2 = 1 := by omega
  rcases BB429NewResidue.odd_back a b (by omega) hao hr with
    ⟨p,q,⟨m,hm⟩,hpa,hqb⟩ |
    ⟨p,q,⟨m,hm⟩,hpa,hqb,hb4⟩
  · have hp15 : 15 <= p := by omega
    have hpodd : p % 2 = 1 := by omega
    have hp4 : p % 4 = 3 := by omega
    have hq8 : q % 8 = 6 := by omega
    rcases BB429NewResidue.odd_back p q hp15 hpodd ⟨m,hm⟩ with
      ⟨r,s,⟨l,hl⟩,hpr,hsq⟩ |
      ⟨r,s,⟨l,hl⟩,hpr,hsq,hq4⟩
    · have hr6 : 6 <= r := by omega
      have hrEven : r % 2 = 0 := by omega
      have hs4 : s % 4 = 1 := by omega
      have hEven := BB429NewResidue.even_back r s hr6 hrEven ⟨l,hl⟩
      omega
    · have hr6 : 6 <= r := by omega
      have hrEven : r % 2 = 0 := by omega
      have hs4 : s % 4 = 1 := by omega
      have hEven := BB429NewResidue.even_back r s hr6 hrEven ⟨l,hl⟩
      omega
  · omega
```

Arithmetic facts used by omega:
- first odd_back branch gives a=2p+3, q=a+b; a mod16=9 implies p mod4=3, and q mod8=6;
- on the first branch of odd_back(p,q), p=2r+3 and s=q+p, so r is even >=6 and s mod4=1;
- on its second branch, 4r+26=4p+q and 2s=q+4. Since q mod8=6, p odd, and q>=38 (a>=33,b>=5), r is positive even >=6 and s mod4=1;
- both contradict even_back, which requires s mod4=2.
The outer second odd_back branch is impossible because it requires b mod4=2, whereas b mod8=5.

This is a source-root lemma, not an arbitrary Side-forbidden claim. It is safe for the n>=18 last-reset prestate because its first counter is far above 33.
