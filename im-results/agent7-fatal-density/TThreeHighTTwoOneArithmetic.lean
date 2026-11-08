import Lean
set_option maxHeartbeats 0
namespace CascadeHighTTwoArithmetic

theorem pow_two_mod_nine (k:Nat) :
  2^k%9 = (if k%6=0 then 1 else if k%6=1 then 2 else if k%6=2 then 4 else if k%6=3 then 8 else if k%6=4 then 7 else 5) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ, Nat.mul_mod]
    have hk : k%6=0 ∨ k%6=1 ∨ k%6=2 ∨ k%6=3 ∨ k%6=4 ∨ k%6=5 := by omega
    rcases hk with h|h|h|h|h|h
    · simp [h] at ih
      have hnext : (k+1)%6=1 := by omega
      rw [hnext, ih]
      decide
    · simp [h] at ih
      have hnext : (k+1)%6=2 := by omega
      rw [hnext, ih]
      decide
    · simp [h] at ih
      have hnext : (k+1)%6=3 := by omega
      rw [hnext, ih]
      decide
    · simp [h] at ih
      have hnext : (k+1)%6=4 := by omega
      rw [hnext, ih]
      decide
    · simp [h] at ih
      have hnext : (k+1)%6=5 := by omega
      rw [hnext, ih]
      decide
    · simp [h] at ih
      have hnext : (k+1)%6=0 := by omega
      rw [hnext, ih]
      decide

private theorem bad_4_17 (n k s d a b c:Nat)
 (hn20:20≤n) (hn:n%18=4∨n%18=17) (hk:k=n-8) (hs:s=2^k)
 (h0:8*d=8*s+a+k+5) (h1:2*a=8*s+b+k) (h2:2*b=8*s+c+k)
 (hd:d%9=7) : (2*a+5)%9≠0 ∧ (2*c+5)%9≠0 := by
 have hk18:k%18=14∨k%18=9:=by omega
 have hs9:s%9=4∨s%9=8:=by
  rcases hk18 with h|h
  · have hk6:k%6=2:=by omega
    rw [hs,pow_two_mod_nine]
    simp [hk6]
  · have hk6:k%6=3:=by omega
    rw [hs,pow_two_mod_nine]
    simp [hk6]
 omega

private theorem bad_5_10 (n k s d a b c:Nat)
 (hn20:20≤n) (hn:n%18=5∨n%18=10) (hk:k=n-8) (hs:s=2^k)
 (h0:8*d=8*s+a+k+5) (h1:2*a=8*s+b+k) (h2:2*b=8*s+c+k)
 (hd:d%9=1) : (2*a+5)%9≠0 ∧ (2*c+5)%9≠0 := by
 have hk18:k%18=15∨k%18=2:=by omega
 have hs9:s%9=8∨s%9=4:=by
  rcases hk18 with h|h
  · have hk6:k%6=3:=by omega
    rw [hs,pow_two_mod_nine]
    simp [hk6]
  · have hk6:k%6=2:=by omega
    rw [hs,pow_two_mod_nine]
    simp [hk6]
 omega

private theorem bad_11_16 (n k s d a b c:Nat)
 (hn20:20≤n) (hn:n%18=11∨n%18=16) (hk:k=n-8) (hs:s=2^k)
 (h0:8*d=8*s+a+k+5) (h1:2*a=8*s+b+k) (h2:2*b=8*s+c+k)
 (hd:d%9=4) : (2*a+5)%9≠0 ∧ (2*c+5)%9≠0 := by
 have hk18:k%18=3∨k%18=8:=by omega
 have hs9:s%9=8∨s%9=4:=by
  rcases hk18 with h|h
  · have hk6:k%6=3:=by omega
    rw [hs,pow_two_mod_nine]
    simp [hk6]
  · have hk6:k%6=2:=by omega
    rw [hs,pow_two_mod_nine]
    simp [hk6]
 omega

theorem one_gate_mod9_or_odd (n k s d a b c:Nat) (P:Prop)
 (hn20:20≤n)
 (hk:k=n-8) (hs:s=2^k) (h0:8*d=8*s+a+k+5)
 (h1:2*a=8*s+b+k) (h2:2*b=8*s+c+k) (hd:d%3=1)
 (hbranch:(2*a+5)%9=0 ∨ (2*c+5)%9=0 ∨ P) :
 ((n%18=4∨n%18=17) → d%9=1∨d%9=4∨P) ∧
 ((n%18=5∨n%18=10) → d%9=4∨d%9=7∨P) ∧
 ((n%18=11∨n%18=16) → d%9=1∨d%9=7∨P) := by
 have hd9:d%9=1∨d%9=4∨d%9=7:=by omega
 refine ⟨?_,?_,?_⟩
 · intro h
   rcases hd9 with h1d|h4d|h7d
   · exact Or.inl h1d
   · exact Or.inr (Or.inl h4d)
   · have hb := bad_4_17 n k s d a b c hn20 h hk hs h0 h1 h2 h7d
     rcases hbranch with ha|hc|hp
     · exact False.elim (hb.1 ha)
     · exact False.elim (hb.2 hc)
     · exact Or.inr (Or.inr hp)
 · intro h
   rcases hd9 with h1d|h4d|h7d
   · have hb := bad_5_10 n k s d a b c hn20 h hk hs h0 h1 h2 h1d
     rcases hbranch with ha|hc|hp
     · exact False.elim (hb.1 ha)
     · exact False.elim (hb.2 hc)
     · exact Or.inr (Or.inr hp)
   · exact Or.inl h4d
   · exact Or.inr (Or.inl h7d)
 · intro h
   rcases hd9 with h1d|h4d|h7d
   · exact Or.inl h1d
   · have hb := bad_11_16 n k s d a b c hn20 h hk hs h0 h1 h2 h4d
     rcases hbranch with ha|hc|hp
     · exact False.elim (hb.1 ha)
     · exact False.elim (hb.2 hc)
     · exact Or.inr (Or.inr hp)
   · exact Or.inr (Or.inl h7d)

end CascadeHighTTwoArithmetic
