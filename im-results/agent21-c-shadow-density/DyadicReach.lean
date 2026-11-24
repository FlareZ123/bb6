import DyadicExtinction

namespace BB6.Agent21Dyadic

-- The source-independent interface is identical to Agent42's ParentLaw.
def pow (b : Nat) : Nat := 2^b
def Large (b y : Nat) : Prop := 3*pow b≤y+2
def Inverse (a k x y v : Nat) : Prop :=
  (y%2=0 ∧ a+2=x+y ∧ 2*k+2=y) ∨
  ∃ n, n+2≤v ∧ n%2=(x+1+(x+y)%2)%2 ∧
    x+y+(x+y)%2=pow (n+1)*(a+2+(x+y)%2) ∧
    2*k+a+7+3*n=x+2*y

def ParentLaw (reach : Nat→Nat→Prop) : Prop :=
  ∀ x y v, reach x y → 8≤y → (x+y+(x+y)%2)%pow (v+1)=pow v →
    pow v<x+y+(x+y)%2 → ∃ a k, reach a k ∧ Inverse a k x y v

private theorem pow_pos (b : Nat) : 0<pow b := Nat.two_pow_pos b
private theorem pow_split {b r : Nat} (h : r≤b) : pow b=pow (b-r)*pow r :=
  (Nat.pow_sub_mul_pow 2 h).symm
private theorem pow_le {b r : Nat} (h : r≤b) : pow r≤pow b :=
  Nat.pow_le_pow_right (by decide) h

private theorem large_direct {b y k : Nat} (hb : 1≤b) (hl : Large b y) (he : 2*k+2=y) : Large (b-1) k := by
  unfold Large at *
  rw [pow_split hb] at hl
  change 3*(pow (b-1)*2)≤y+2 at hl
  omega

private theorem exp_linear (n : Nat) : 3*n+4≤pow (n+2) := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h : pow (n+1+2)=pow (n+2)*2 := by unfold pow; rw [show n+1+2=n+2+1 by omega,Nat.pow_succ]
    rw [h]; omega

private theorem large_high {b n a k x y : Nat} (hb : n+2≤b) (hl : Large b y)
    (hq : x+y+(x+y)%2=pow (n+1)*(a+2+(x+y)%2))
    (hw : 2*k+a+7+3*n=x+2*y) : Large (b-(n+2)) k := by
  have hd : 2≤pow (n+1) := pow_le (by omega : 1≤n+1)
  have hp : pow (n+2)=pow (n+1)*2 := by simp [pow,Nat.pow_succ]
  have hm := Nat.mul_le_mul_right a hd
  have ho := Nat.mul_le_mul_right ((x+y)%2) hd
  rw [Nat.mul_add,Nat.mul_add] at hq
  have hh := exp_linear n
  have hxy : a+pow (n+2)≤x+y := by omega
  have hk : y+1≤2*(k+2) := by omega
  have h0 : 2≤pow (n+2) := by omega
  have h1 := Nat.mul_le_mul_right (k+2) h0
  have h2 : 4≤pow (n+2) := by omega
  have h3 := Nat.mul_le_mul_right (k+2) h2
  have hs : y+2≤pow (n+2)*(k+2) := by omega
  unfold Large at *
  rw [pow_split hb] at hl
  apply Nat.le_of_mul_le_mul_left (c:=pow (n+2)) _ (pow_pos _)
  rw [Nat.mul_comm (pow (n+2)) (3*pow (b-(n+2))),Nat.mul_assoc]
  exact Nat.le_trans hl hs

-- Signed normalized coordinates, U=-x and V=-y.
def S (x y : Nat) : Int := -(x:Int)-2*(y:Int)
def Z (x y : Nat) : Int := (-(x:Int)-2-parity (S x y))/2

theorem twice_Z (x y : Nat) : 2*Z x y=-(x:Int)-2-parity (S x y) := by
  unfold Z parity S
  omega

theorem one_numer (x y r : Nat) : Z x y+offset (S x y) r=-(x:Int)-(y:Int)-parity (S x y+shift r) := by
  have hz := twice_Z x y
  unfold offset
  have he : (S x y+parity (S x y))%2=0 := by unfold parity; omega
  unfold S at hz ⊢
  omega

theorem parity_cost (x y r : Nat) (h : r%2=(y+1)%2) :
    parity (S x y+shift r)=((x+y)%2:Nat) := by
  unfold parity S shift
  omega

theorem direct_edge (a k x y : Nat) (he : y%2=0) (ha : a+2=x+y) (hk : 2*k+2=y) :
    S a k=S x y+shift 1 ∧ P 1*Z a k=Z x y+offset (S x y) 1 := by
  have hs : S a k=S x y+shift 1 := by unfold S shift; omega
  refine ⟨hs,?_⟩
  rw [one_numer]
  change 2*Z a k=-(x:Int)-(y:Int)-parity (S x y+shift 1)
  rw [twice_Z,←hs]
  omega

theorem high_edge (a k x y n : Nat) (hpar : n%2=(x+1+(x+y)%2)%2)
    (hq : x+y+(x+y)%2=pow (n+1)*(a+2+(x+y)%2))
    (hw : 2*k+a+7+3*n=x+2*y) :
    S a k=S x y+shift (n+2) ∧ P (n+2)*Z a k=Z x y+offset (S x y) (n+2) := by
  have hs : S a k=S x y+shift (n+2) := by unfold S shift; omega
  refine ⟨hs,?_⟩
  rw [one_numer,parity_cost x y (n+2) (by omega)]
  have hz := twice_Z a k
  rw [hs,parity_cost x y (n+2) (by omega)] at hz
  have hq' := congrArg (fun t : Nat=>(t:Int)) hq
  simp only [Int.natCast_add,Int.natCast_mul] at hq'
  have hp : (pow (n+1):Int)=P (n+1) := by simp [pow,P]
  rw [hp] at hq'
  rw [show n+2=n+1+1 by omega,P_add]
  change P (n+1)*2*Z a k=-(x:Int)-(y:Int)-↑((x+y)%2)
  rw [Int.mul_assoc,hz,show -(a:Int)-2-↑((x+y)%2)=-((a:Int)+2+↑((x+y)%2)) by omega,Int.mul_neg]
  change (x:Int)+(y:Int)+↑((x+y)%2)=P (n+1)*((a:Int)+2+↑((x+y)%2)) at hq'
  omega

def OpenAt (s z : Int) (n : Nat) : Prop :=
  (∃ w : List Nat, Positive w ∧ cost w=n ∧ P n∣z+acc s w) ∨
  (∃ w : List Nat, ∃ r : Nat, 2≤r ∧ Positive (w++[r]) ∧ cost (w++[r])=n+1 ∧ P n∣z+acc s (w++[r]))

theorem open_zero (s z : Int) : OpenAt s z 0 :=
  Or.inl ⟨[],by simp [Positive],rfl,by simp [P]⟩

theorem open_prepend (s z s' z' : Int) (r n : Nat) (hr : 0<r)
    (hs : s'=s+shift r) (hz : P r*z'=z+offset s r)
    (ho : OpenAt s' z' n) : OpenAt s z (n+r) := by
  have hd (w : List Nat) (h : P n∣z'+acc s' w) : P (n+r)∣z+acc s (r::w) := by
    rw [show n+r=r+n by omega,P_add,acc,←hs,←Int.add_assoc,←hz,←Int.mul_add]
    exact (Int.mul_dvd_mul_iff_left (P_ne r)).mpr h
  rcases ho with ⟨w,hp,hc,h⟩|⟨w,k,hk,hp,hc,h⟩
  · left
    exact ⟨r::w,positive_append [r] w (by simp [Positive,hr]) hp,by rw [cost_cons,hc]; omega,hd w h⟩
  · right
    refine ⟨r::w,k,hk,?_,?_,?_⟩
    · exact positive_append [r] (w++[k]) (by simp [Positive,hr]) hp
    · change cost (r::(w++[k]))=n+r+1
      rw [cost_cons,hc]; omega
    · exact hd (w++[k]) h

theorem open_divisible (x y n : Nat) (hn : 0<n) (hq : pow n∣x+y+(x+y)%2) : OpenAt (S x y) (Z x y) n := by
  let Q := x+y+(x+y)%2
  have hq' : P n∣-(Q:Int) := by
    obtain ⟨w,hw⟩ := hq
    refine ⟨-(w:Int),?_⟩
    have he := congrArg (fun t:Nat=>(t:Int)) hw
    simp [pow,P] at he
    change -(Q:Int)=P n*(-(w:Int))
    rw [Int.mul_neg]; congr 1
  have hnum (r : Nat) (hr : r%2=(y+1)%2) : Z x y+acc (S x y) [r]=-(Q:Int) := by
    simp only [acc,Int.mul_zero,Int.add_zero]
    rw [one_numer,parity_cost x y r hr]
    unfold Q; omega
  by_cases hr : n%2=(y+1)%2
  · left
    refine ⟨[n],by simp [Positive,hn],by simp [cost],?_⟩
    rwa [hnum n hr]
  · right
    refine ⟨[],n+1,by omega,by simp [Positive],by simp [cost],?_⟩
    simp only [List.nil_append]
    rwa [hnum (n+1) (by omega)]

private theorem valuation_exists (Q n : Nat) (hn : ¬pow n∣Q) :
    ∃ v, v<n ∧ Q%pow (v+1)=pow v := by
  induction n with
  | zero => simp [pow] at hn
  | succ n ih =>
    by_cases h : pow n∣Q
    · obtain ⟨k,hk⟩ := h
      have he : pow (n+1)=pow n*2 := by simp [pow,Nat.pow_succ]
      have hkodd : k%2=1 := by
        by_cases hm : k%2=0
        · have hd : 2∣k := Nat.dvd_of_mod_eq_zero hm
          obtain ⟨l,hl⟩ := hd
          apply False.elim
          apply hn
          refine ⟨l,?_⟩
          rw [hk,hl,he,Nat.mul_assoc]
        · omega
      refine ⟨n,by omega,?_⟩
      rw [hk,he,Nat.mul_mod_mul_left,hkodd,Nat.mul_one]
    · obtain ⟨v,hv,hq⟩ := ih h
      exact ⟨v,by omega,hq⟩

/-- No finite precision can be exhausted at a reachable target with enough
    right-counter height.  This is a direct soundness theorem, independent of
    the older recursive residue checker's implementation. -/
theorem reach_open (reach : Nat→Nat→Prop) (parent : ParentLaw reach)
    (n x y : Nat) (hl : Large (n+2) y) (hr : reach x y) : OpenAt (S x y) (Z x y) n := by
  induction n using Nat.strongRecOn generalizing x y with
  | ind n ih =>
    by_cases hn : n=0
    · subst n; exact open_zero _ _
    by_cases hdiv : pow n∣x+y+(x+y)%2
    · exact open_divisible x y n (by omega) hdiv
    obtain ⟨v,hv,hmod⟩ := valuation_exists _ n hdiv
    have hy : 8≤y := by
      have h4 : 4≤pow (n+2) := pow_le (by omega : 2≤n+2)
      unfold Large at hl; omega
    have hgt : pow v<x+y+(x+y)%2 := by
      have hp := pow_le (show v≤n+2 by omega)
      unfold Large at hl
      omega
    obtain ⟨a,k,hreach,he⟩ := parent x y v hr hy hmod hgt
    rcases he with ⟨hye,ha,hk⟩|⟨r,hrv,hpar,hq,hw⟩
    · obtain ⟨hs,hz⟩ := direct_edge a k x y hye ha hk
      have hlarge := large_direct (by omega : 1≤n+2) hl hk
      have heq : n+2-1=n-1+2 := by omega
      rw [heq] at hlarge
      have hopen := ih (n-1) (by omega) a k hlarge hreach
      have hout := open_prepend _ _ _ _ 1 (n-1) (by decide) hs hz hopen
      rwa [show n-1+1=n by omega] at hout
    · obtain ⟨hs,hz⟩ := high_edge a k x y r hpar hq hw
      have hlarge := large_high (by omega : r+2≤n+2) hl hq hw
      have heq : n+2-(r+2)=n-(r+2)+2 := by omega
      rw [heq] at hlarge
      have hopen := ih (n-(r+2)) (by omega) a k hlarge hreach
      have hout := open_prepend _ _ _ _ (r+2) (n-(r+2)) (by omega) hs hz hopen
      rwa [show n-(r+2)+(r+2)=n by omega] at hout

#print axioms reach_open
end BB6.Agent21Dyadic
