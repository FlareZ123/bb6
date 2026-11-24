import CountedZipper

namespace BB6CountedZipper

def binDec : Nat → Nat → List Bool
  | 0,_ => []
  | L+1,n => (if n%2=0 then d1 else d0) ++ binDec L (n/2)

def v2 (n : Nat) : Nat :=
  if n=0 then 0 else if n%2=1 then 0 else 1+v2 (n/2)
termination_by n
decreasing_by omega

theorem bin_zero (L : Nat) : binDec L 0 = ones (3*L) := by
  induction L with
  | zero => rfl
  | succ L ih =>
    rw [binDec]
    simp only [Nat.zero_mod,if_true,Nat.zero_div,ih]
    rw [show 3*(L+1)=3+3*L by omega,ones_add];rfl

theorem bin_even (L n : Nat) : binDec (L+1) (2*n) = d1 ++ binDec L n := by
  rw [binDec,show 2*n%2=0 by omega,if_pos rfl,show 2*n/2=n by omega]

theorem bin_odd (L n : Nat) : binDec (L+1) (2*n+1) = d0 ++ binDec L n := by
  rw [binDec,show (2*n+1)%2=1 by omega,if_neg (by decide : ¬1=0),show (2*n+1)/2=n by omega]

theorem bin_carry (L n : Nat) (hpos : 0<n) (hlt : n<2^L) :
    ∃ l, binDec L n = ones (3*v2 n) ++ d0 ++ l ∧
      binDec L (n-1) = zeros3 (v2 n) ++ d1 ++ l := by
  induction L generalizing n with
  | zero => simp at hlt; omega
  | succ L ih =>
    have hp : 2^(L+1)=2*2^L := by rw [Nat.pow_succ]; ac_rfl
    rw [hp] at hlt
    by_cases ho : n%2=1
    · have hn : n=2*(n/2)+1 := by omega
      have hm : n-1=2*(n/2) := by omega
      have hv : v2 n=0 := by rw [v2,if_neg (by omega : n≠0),if_pos ho]
      refine ⟨binDec L (n/2),?_,?_⟩
      · have he : binDec (L+1) n = d0 ++ binDec L (n/2) := by rw [binDec,if_neg (by omega : n%2≠0)]
        rw [hv,he]; rfl
      · rw [hv,hm,bin_even]; rfl
    · have he : n%2=0 := by omega
      have hn : n=2*(n/2) := by omega
      have hm : n-1=2*(n/2-1)+1 := by omega
      have hv : v2 n=1+v2 (n/2) := by rw [v2,if_neg (by omega : n≠0),if_neg ho]
      obtain ⟨l,h₁,h₂⟩ := ih (n/2) (by omega) (by omega)
      refine ⟨l,?_,?_⟩
      · have h : binDec (L+1) n = d1 ++ binDec L (n/2) := by rw [binDec,if_pos he]
        rw [h,h₁,hv,show 3*(1+v2 (n/2))=3+3*v2 (n/2) by omega,ones_add]
        simp only [List.append_assoc];rfl
      · rw [hm,bin_odd,h₂,hv,show 1+v2 (n/2)=v2 (n/2)+1 by omega,zeros3]
        simp only [List.append_assoc]

theorem bin_all (a b : Nat) : binDec (a+b) (2^b-1) = zeros3 b ++ ones (3*a) := by
  induction b with
  | zero => simp [zeros3,bin_zero]
  | succ b ih =>
    have hp : 0<2^b := Nat.two_pow_pos b
    have hn : 2^(b+1)-1=2*(2^b-1)+1 := by rw [Nat.pow_succ];omega
    rw [show a+(b+1)=a+b+1 by omega,hn,bin_odd,ih,zeros3,List.append_assoc]

def expanded (L a : Nat) : Nat := (2^(L+2)-1)*2^a-1

theorem expanded_lt (L a : Nat) : expanded L a < 2^(L+a+2) := by
  have h₁ : (2^(L+2)-1)*2^a < 2^(L+2)*2^a :=
    Nat.mul_lt_mul_of_pos_right (by have := Nat.two_pow_pos (L+2);omega) (Nat.two_pow_pos a)
  rw [← Nat.pow_add,show L+2+a=L+a+2 by omega] at h₁
  unfold expanded
  omega

theorem bin_expanded (L a : Nat) :
    binDec (L+a+2) (expanded L a) = zeros3 a ++ d1 ++ zeros3 (L+1) := by
  induction a with
  | zero =>
    have hp : 0<2^(L+1) := Nat.two_pow_pos (L+1)
    have he : expanded L 0 = 2*(2^(L+1)-1) := by
      simp only [expanded,Nat.pow_zero,Nat.mul_one]
      rw [show L+2=L+1+1 by omega,Nat.pow_succ];omega
    rw [he,show L+0+2=L+1+1 by omega,bin_even]
    have h := bin_all 0 (L+1)
    simpa [zeros3,ones] using congrArg (fun x => d1++x) h
  | succ a ih =>
    have hp : 0<(2^(L+2)-1)*2^a := Nat.mul_pos (by have := Nat.two_pow_pos (L+1);rw [show L+2=L+1+1 by omega,Nat.pow_succ];omega) (Nat.two_pow_pos a)
    have he : expanded L (a+1)=2*expanded L a+1 := by
      unfold expanded
      rw [Nat.pow_succ 2 a,← Nat.mul_assoc]
      omega
    rw [show L+(a+1)+2=L+a+2+1 by omega,he,bin_odd,ih]
    change _ = (d0 ++ zeros3 a) ++ d1 ++ zeros3 (L+1)
    simp only [List.append_assoc]

def s0 (l : List Bool) (a z b : Nat) (h : Int) : Z := left 3 h (binDec a z ++ l) (rc b)
def s1 (L n m a z b : Nat) (h : Int) : Z := s0 (marker m ++ d0 ++ binDec L n ++ lh) a z b h

def incCost (n b : Nat) := 48+12*v2 n+12*b

theorem inc0 (l : List Bool) (a z b : Nat) (h : Int) (hz : 0<z) (hb : z<2^a) :
    run (incCost z b) (s0 l a z b h) = some (s0 l a (z-1) (b+1) h) := by
  obtain ⟨t,ht,ht'⟩ := bin_carry a z hz hb
  simpa only [incCost,s0,ht,ht',List.append_assoc] using inc0_carry (v2 z) b h (t++l)

def drainCost : Nat → Nat → Nat
  | 0,_ => 0
  | z+1,b => incCost (z+1) b + drainCost z (b+1)

theorem drain (l : List Bool) (a z b : Nat) (h : Int) (hb : z<2^a) :
    run (drainCost z b) (s0 l a z b h) = some (s0 l a 0 (b+z) h) := by
  induction z generalizing b with
  | zero => rfl
  | succ z ih =>
    have h₁ := inc0 l a (z+1) b h (by omega) hb
    have h₂ := ih (b+1) (by omega)
    have hh := join h₁ h₂
    simpa only [drainCost,show b+1+z=b+(z+1) by omega,Nat.add_sub_cancel] using hh

def prefixCost (m n a b : Nat) := 63+4*m+12*(a+v2 n)+3*b
def rstCost (m n a b : Nat) := prefixCost m n a b+drainCost (2^b-1) 0

theorem rst (L n m a b : Nat) (h : Int) (hn : 0<n) (hb : n<2^L) (hm : m<3) :
    run (rstCost m n a b) (s1 L n m a 0 b h) =
    some (s1 L (n-1) (nextM m) (nextA m a b) 0 (2^b-1) (h+5+3*(b:Int))) := by
  obtain ⟨t,ht,ht'⟩ := bin_carry L n hn hb
  have hp := reset_prefix m a (v2 n) b hm h (t++lh)
  have hbin : binDec (nextA m a b) (2^b-1) = zeros3 b ++ ones (3*(a+(if m=0 then 1 else 2))) := by
    rw [show nextA m a b = (a+(if m=0 then 1 else 2))+b by unfold nextA;omega,bin_all]
  have hpre : run (prefixCost m n a b) (s1 L n m a 0 b h) =
      some (s1 L (n-1) (nextM m) (nextA m a b) (2^b-1) 0 (h+5+3*(b:Int))) := by
    simpa only [prefixCost,s1,s0,ht,ht',bin_zero,hbin,List.append_assoc] using hp
  have hpow : 2^b ≤ 2^(nextA m a b) := Nat.pow_le_pow_right (by decide) (by unfold nextA;omega)
  have hd := drain (marker (nextM m) ++ d0 ++ binDec L (n-1) ++ lh) (nextA m a b) (2^b-1) 0 (h+5+3*(b:Int)) (by have := Nat.two_pow_pos b;omega)
  have hh := join hpre hd
  simpa only [rstCost,s1,Nat.zero_add] using hh

def primeCost (L a b : Nat) := 97+12*(L+a)+3*b+drainCost (2^b-1) 0

theorem rstPrime (L a b : Nat) (h : Int) :
    run (primeCost L a b) (s1 L 0 1 a 0 b h) =
    some (s1 (L+a+2) (expanded L a) 2 b 0 (2^b-1) (h+5+3*(b:Int))) := by
  have hp := reset_prime_prefix L a b h
  have hbin : binDec b (2^b-1) = zeros3 b := by
    have hh := bin_all 0 b
    simpa [ones] using hh
  have hp' : run (97+12*(L+a)+3*b) (s1 L 0 1 a 0 b h) =
      some (s1 (L+a+2) (expanded L a) 2 b (2^b-1) 0 (h+5+3*(b:Int))) := by
    simpa only [s1,s0,bin_zero,bin_expanded,hbin,List.append_assoc] using hp
  have hd := drain (marker 2 ++ d0 ++ binDec (L+a+2) (expanded L a) ++ lh) b (2^b-1) 0 (h+5+3*(b:Int)) (by have := Nat.two_pow_pos b;omega)
  simpa only [primeCost,s1,Nat.zero_add] using (join hp' hd)

theorem haltFinal (L a b : Nat) (h : Int) :
    ∃ z, run (59+12*(L+a)) (s1 L 0 0 a 0 b h) = some z ∧ step z=none := by
  simpa only [s1,s0,bin_zero,List.append_assoc] using terminal L a b h

#print axioms rst
#print axioms rstPrime
#print axioms haltFinal
end BB6CountedZipper
