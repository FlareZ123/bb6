import RayNoSeam
import EvenChainGap
set_option maxHeartbeats 0
namespace CascadeSeam
open CascadeEvenChainGap

private def cWalk (k B:Nat) : Nat → Nat
  | 0 => B
  | i+1 => 2*cWalk k B i+k

private theorem k_margin (k:Nat) : k+2≤4*2^k:=by
  induction k with
  | zero=>decide
  | succ k ih=>
    rw [Nat.pow_succ]
    omega

private theorem walk_complement (k q B r:Nat)
  (h0:q+B=8*2^k)
  (hband:∀i<r, 3≤cWalk k B i ∧ cWalk k B i≤2*2^k+1) :
  evenWalk k q r + cWalk k B r=8*2^k := by
  induction r with
  | zero => simpa [evenWalk,cWalk] using h0
  | succ r ih =>
    have hbefore:∀i<r, 3≤cWalk k B i ∧ cWalk k B i≤2*2^k+1:=
      fun i hi=>hband i (by omega)
    have hprev:=ih hbefore
    have hr:=hband r (by omega)
    have hm:=k_margin k
    simp only [evenWalk,cWalk]
    omega

/-- A no-skip gap certificate for the genuine evenWalk recurrence,
    given explicit bounds on its complementary deficit. -/
theorem walk_gap_from_deficit (k q B r:Nat)
  (h0:q+B=8*2^k)
  (hband:∀i<r, 3≤cWalk k B i ∧ cWalk k B i≤2*2^k+1)
  (hgap:2*2^k+1<cWalk k B r ∧ cWalk k B r<4*2^k+3) :
  (∀i<r, 6*2^k-1≤evenWalk k q i ∧ evenWalk k q i≤8*2^k-3) ∧
  (4*2^k-3<evenWalk k q r ∧ evenWalk k q r<6*2^k-1) := by
  constructor
  · intro i hi
    have hB:=hband i hi
    have hc:=walk_complement k q B i h0 (fun s hs=>hband s (by omega))
    omega
  · have hc:=walk_complement k q B r h0 hband
    omega

private theorem initial_complement (p q:Nat)
 (h:3≤8*p-q) : q+(8*p-q)=8*p := by omega

/-- Uniform genuine-source evenWalk exit after two to four inverse
    resets, subject to the exact source-algebra weak-margin premises. -/
theorem weak_margin_inverse_exit (n j q:Nat) (hn:20≤n)
  (hs:81*(8*2^(n-4)-q)+3=16*2^(n-4)+128*(2^j*(2*n+3))+169*n)
  (hm:32*(2^j*(2*n+3))+32*n+160≤16*2^(n-4))
  (hb:3≤8*2^(n-4)-q ∧ 8*2^(n-4)-q≤2*2^(n-4)+1) :
  ∃r, (r=2 ∨ r=3 ∨ r=4) ∧
    (∀i<r, 6*2^(n-4)-1≤evenWalk (n-4) q i ∧
       evenWalk (n-4) q i≤8*2^(n-4)-3) ∧
    (4*2^(n-4)-3<evenWalk (n-4) q r ∧
       evenWalk (n-4) q r<6*2^(n-4)-1) := by
  let k:=n-4
  let p:=2^k
  let B:=8*p-q
  have hpk:2^k=p:=rfl
  have hpn:2^(n-4)=p:=rfl
  have hkn:k=n-4:=rfl
  have hq:q+B=8*p:=initial_complement p q hb.1
  obtain ⟨r,hr,hcase⟩:=weak_margin_no_seam n j B hn hs hm hb
  clear hs hm hb
  rcases hr with rfl|rfl|rfl
  · simp only [if_pos rfl] at hcase
    rcases hcase with ⟨h0,h1,h2⟩
    have hi:∀i<2, 3≤cWalk k B i ∧ cWalk k B i≤2*p+1:=by
      intro i hi
      rcases (show i=0 ∨ i=1 by omega) with he|he
      · subst i
        simpa only [cWalk] using h0
      · subst i
        dsimp [cWalk]
        exact h1
    have hg:2*p+1<cWalk k B 2 ∧ cWalk k B 2<4*p+3:=by
      dsimp [cWalk]
      omega
    exact ⟨2,Or.inl rfl,(walk_gap_from_deficit k q B 2 hq hi hg)⟩
  · simp only [if_neg (show (3:Nat)≠2 by decide),if_pos rfl] at hcase
    rcases hcase with ⟨h0,h1,h2,h3⟩
    have hi:∀i<3, 3≤cWalk k B i ∧ cWalk k B i≤2*p+1:=by
      intro i hi
      rcases (show i=0 ∨ i=1 ∨ i=2 by omega) with he|he|he
      · subst i
        simpa only [cWalk] using h0
      · subst i
        dsimp [cWalk]
        exact h1
      · subst i
        dsimp [cWalk]
        omega
    have hg:2*p+1<cWalk k B 3 ∧ cWalk k B 3<4*p+3:=by
      dsimp [cWalk]
      omega
    exact ⟨3,Or.inr (Or.inl rfl),(walk_gap_from_deficit k q B 3 hq hi hg)⟩
  · simp only [if_neg (show (4:Nat)≠2 by decide),if_neg (show (4:Nat)≠3 by decide)] at hcase
    rcases hcase with ⟨h0,h1,h2,h3,h4⟩
    have hi:∀i<4, 3≤cWalk k B i ∧ cWalk k B i≤2*p+1:=by
      intro i hi
      rcases (show i=0 ∨ i=1 ∨ i=2 ∨ i=3 by omega) with he|he|he|he
      · subst i
        simpa only [cWalk] using h0
      · subst i
        dsimp [cWalk]
        exact h1
      · subst i
        dsimp [cWalk]
        omega
      · subst i
        dsimp [cWalk]
        omega
    have hg:2*p+1<cWalk k B 4 ∧ cWalk k B 4<4*p+3:=by
      dsimp [cWalk]
      omega
    exact ⟨4,Or.inr (Or.inr rfl),(walk_gap_from_deficit k q B 4 hq hi hg)⟩

#print axioms weak_margin_inverse_exit
#print axioms walk_gap_from_deficit
end CascadeSeam
