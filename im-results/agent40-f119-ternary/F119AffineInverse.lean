import F119Inverse2

namespace F119AffineInverse
open F119Inverse2

-- Arithmetic inverse search for a target D*y+C = 3^N, with 3 ∤ D.
def generic (h r t : Nat) : Nat := (3*3^h+1)*t + 3^h*r + h+3 + (if r=2 then 1 else 0)

theorem high_excluded (D C h r t N : Nat)
    (hD : 0<D) (hD3 : D%3≠0) (hh : 2≤h) (hr : r=1 ∨ r=2)
    (hgap : 2*(C+D*(h+4))<3^h) : D*generic h r t+C ≠ 3^N := by
  intro he
  let p := 3^h
  let M := 3*p+1
  let q := D*r/3
  let u := D*r%3
  let H := h+3+(if r=2 then 1 else 0)
  let E := C+D*H
  have hqr : D*r=3*q+u := by dsimp [q,u]; omega
  have hq : q≤D := by rcases hr with rfl|rfl <;> dsimp [q] <;> omega
  have hu : u=1 ∨ u=2 := by
    dsimp [u]
    rw [Nat.mul_mod]
    rcases hr with rfl|rfl <;> omega
  have hH : h+3≤H ∧ H≤h+4 := by dsimp [H]; split <;> omega
  have hEup : E≤C+D*(h+4) := Nat.add_le_add_left (Nat.mul_le_mul_left D hH.2) C
  have hElo : D*(h+3)≤E := by
    have h1 := Nat.mul_le_mul_left D hH.1
    dsimp [E]; omega
  have hDmul : D*2≤D*(h+3) := Nat.mul_le_mul_left D (by omega)
  have hE : 1 < E-q := by
    have hDmul' : D*3≤D*(h+3) := Nat.mul_le_mul_left D (by omega)
    omega
  have hsmall : 2*(E-q)<p := by change 2*(C+D*(h+4))<p at hgap; omega
  have hp : 9≤p := Nat.pow_le_pow_right (n:=3) (by decide) hh
  have hEeq : E=q+(E-q) := by omega
  have hqr' : p*(D*r)=M*q+p*u-q := by
    rw [hqr,Nat.mul_add,← Nat.mul_assoc p 3 q,Nat.mul_comm p 3]
    dsimp [M]
    rw [Nat.add_mul]
    have hle : q≤3*p*q+q := by omega
    omega
  have hcalc : 3^N=M*(D*t+q)+(p*u+(E-q)) := by
    rw [← he]
    have hg : generic h r t = M*t+p*r+H := by unfold generic; dsimp [M,p,H]; omega
    rw [hg]
    rw [Nat.mul_add,Nat.mul_add,Nat.mul_left_comm D M t,Nat.mul_left_comm D p r,hqr']
    rw [Nat.mul_add M (D*t) q]
    have hle : q≤M*q := Nat.le_mul_of_pos_left q (by dsimp [M]; omega)
    dsimp [E] at hEeq
    omega
  have hres : 3^N%M=p*u+(E-q) := by
    rw [hcalc,Nat.mul_add_mod,Nat.mod_eq_of_lt]
    rcases hu with hu|hu <;> rw [hu] <;> dsimp [M] <;> omega
  obtain ⟨j,hj,hs⟩ := signed_residue h N (by omega)
  have hjp : 3^j≤p := Nat.pow_le_pow_right (n:=3) (by decide) hj
  change 3^N%M=3^j ∨ 3^N%M=M-3^j at hs
  rw [hres] at hs
  rcases hu with hu|hu
  · rw [hu] at hs
    dsimp [M] at hs
    omega
  · rw [hu] at hs
    have hjlt : j<h := by
      apply Nat.lt_of_not_ge
      intro hn
      have hjh : j=h := by omega
      subst j
      change p*2+(E-q)=p ∨ p*2+(E-q)=M-p at hs
      dsimp [M] at hs
      omega
    have hjp' : 3^j≤3^(h-1) := Nat.pow_le_pow_right (n:=3) (by decide) (show j≤h-1 by omega)
    have hpi : p=3*3^(h-1) := by
      have e : h=(h-1)+1 := by omega
      calc
        p = 3^h := rfl
        _ = 3^((h-1)+1) := congrArg (3^·) e
        _ = 3*3^(h-1) := by rw [Nat.pow_succ,Nat.mul_comm]
    dsimp [M] at hs
    omega

#print axioms high_excluded

-- A positive remainder smaller than 3^a is incompatible with a power of 3.
theorem no_small_remainder (A B a N : Nat) (hA : 0<A) (hB : 0<B)
    (hBsmall : B<3^a) : 3^N ≠ 3^a*A+B := by
  intro he
  have ha : a≤N := by
    apply Nat.le_of_not_gt
    intro hn
    have hlt := Nat.pow_lt_pow_right (a:=3) (by decide) hn
    have hle : 3^a≤3^a*A := Nat.le_mul_of_pos_right _ hA
    omega
  have hmod := Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 3 ha)
  rw [he,Nat.mul_add_mod,Nat.mod_eq_of_lt hBsmall] at hmod
  omega

theorem no_pure_power (D C a N : Nat) (hD : 0<D)
    (hgap : D*(a+3)+C<3^a) : D*(3^a+a+3)+C ≠ 3^N := by
  intro he
  have hB : 0<D*(a+3)+C := by
    have hp := Nat.mul_pos hD (show 0<a+3 by omega)
    omega
  apply no_small_remainder D (D*(a+3)+C) a N hD hB hgap
  rw [← he,show 3^a+a+3=3^a+(a+3) by omega,Nat.mul_add,Nat.mul_comm D (3^a)]
  omega

theorem tag_two_bound (a h t r : Nat) (ha : 2≤a) (hr : r=1 ∨ r=2)
    (hx : 3^a+a+1=3^h*(3*t+r)) : h≤a ∧ 3^h≤a+1 := by
  have hpos : 0<3*t+r := by omega
  have hp := Nat.le_mul_of_pos_right (3^h) hpos
  rw [← hx] at hp
  have hlt : 3^a+a+1<3^(a+1) := by
    have hl := linear_pow a
    have hp0 : 0<3^a := Nat.pow_pos (by decide)
    rw [Nat.pow_succ]
    omega
  have hha : h≤a := by
    apply Nat.le_of_not_gt
    intro hh
    have hb := Nat.pow_le_pow_right (n:=3) (by decide) (show a+1≤h by omega)
    omega
  have hdiv : 3^h ∣ 3^a := Nat.pow_dvd_pow 3 hha
  have hdiv2 : 3^h ∣ 3^a+(a+1) := by
    exact ⟨3*t+r,by omega⟩
  have hd : 3^h ∣ a+1 := by
    apply (Nat.dvd_add_iff_left hdiv).mpr
    simpa [Nat.add_comm] using hdiv2
  exact ⟨hha,Nat.le_of_dvd (by omega) hd⟩

theorem scaled_tag_two (p x y h t r : Nat)
    (hx : x=p*(3*t+r)) (hy : y=x+2+h+t+r+1) :
    3*p*y=(3*p+1)*x+p*(3*h+2*r+9) := by
  have h1 : 3*p*t+p*r=x := by
    rw [hx,Nat.mul_add,← Nat.mul_assoc p 3 t,Nat.mul_comm p 3]
  have h2 : (3*p)*(h+r+3)=p*r+p*(3*h+2*r+9) := by
    rw [Nat.mul_comm 3 p,Nat.mul_assoc,← Nat.mul_add]
    congr 1
    omega
  rw [show y=x+t+(h+r+3) by omega,Nat.mul_add,Nat.mul_add,h2,Nat.add_mul]
  omega

def budget (D C a : Nat) : Nat := (a+1)*(D*(6*a+17)+3*C)

theorem no_tag_two (D C a h t r y N : Nat) (hD : 0<D) (ha : 2≤a)
    (hr : r=1 ∨ r=2) (hx : 3^a+a+1=3^h*(3*t+r))
    (hy : y=3^a+a+1+2+h+t+r+1) (hgap : budget D C a<3^a) :
    D*y+C ≠ 3^N := by
  intro he
  let p := 3^h
  let x := 3^a+a+1
  let M := 3*p+1
  let Q := 3*h+2*r+9
  let E := D*(M*(a+1)+p*Q)+3*p*C
  obtain ⟨hh,hp⟩ := tag_two_bound a h t r ha hr hx
  have hQ : Q≤3*a+13 := by dsimp [Q]; omega
  have hM : M≤3*a+4 := by dsimp [M]; omega
  have hE1 : M*(a+1)≤(3*a+4)*(a+1) := Nat.mul_le_mul_right _ hM
  have hE2 : p*Q≤(a+1)*(3*a+13) := Nat.mul_le_mul hp hQ
  have hE3 : M*(a+1)+p*Q≤(a+1)*(6*a+17) := by
    rw [Nat.mul_comm (3*a+4) (a+1)] at hE1
    rw [show 6*a+17=(3*a+4)+(3*a+13) by omega,Nat.mul_add (a+1) (3*a+4) (3*a+13)]
    omega
  have hE4 := Nat.mul_le_mul_left D hE3
  have hE5 : 3*p*C≤(a+1)*(3*C) := by
    rw [Nat.mul_comm 3 p,Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ hp
  have hEsmall : E≤budget D C a := by
    unfold budget
    rw [Nat.mul_add,Nat.mul_left_comm (a+1) D]
    dsimp [E]
    omega
  have hp0 : 0<p := Nat.pow_pos (by decide)
  have hM0 : 0<M := by dsimp [M]; omega
  have hEpos : 0<E := by
    have hprod := Nat.mul_pos hM0 (show 0<a+1 by omega)
    have hpos := Nat.mul_pos hD (show 0<M*(a+1)+p*Q by omega)
    dsimp [E]; omega
  have hscale := scaled_tag_two p x y h t r hx hy
  change 3*p*y=M*x+p*Q at hscale
  have hcalc : 3^(N+h+1)=3^a*(D*M)+E := by
    calc
      3^(N+h+1) = (3*p)*3^N := by rw [Nat.pow_succ,Nat.pow_add]; dsimp [p]; ac_rfl
      _ = (3*p)*(D*y+C) := by rw [he]
      _ = D*(3*p*y)+3*p*C := by rw [Nat.mul_add,Nat.mul_left_comm (3*p) D]
      _ = D*(M*x+p*Q)+3*p*C := by rw [hscale]
      _ = 3^a*(D*M)+E := by
        dsimp [x,E]
        rw [show 3^a+a+1=3^a+(a+1) by omega]
        simp only [Nat.mul_add]
        rw [show D*(M*3^a)=3^a*(D*M) by ac_rfl]
        omega
  exact no_small_remainder (D*M) E a (N+h+1) (Nat.mul_pos hD hM0) hEpos (by omega) hcalc

#print axioms no_pure_power
#print axioms no_tag_two

-- Once the generic cutoff holds, it holds at every larger valuation.
theorem generic_cutoff (D C H h : Nat) (hH : H≤h)
    (hg : 2*(C+D*(H+4))<3^H) : 2*(C+D*(h+4))<3^h := by
  induction h with
  | zero =>
    have he : H=0 := by omega
    simpa [he] using hg
  | succ h ih =>
    by_cases hh : H≤h
    · have h0 := ih hh
      have h1 : D≤D*(h+4) := Nat.le_mul_of_pos_right D (by omega)
      rw [Nat.pow_succ,show h+1+4=(h+4)+1 by omega,Nat.mul_add D (h+4) 1,Nat.mul_one]
      omega
    · have he : H=h+1 := by omega
      simpa [he] using hg

-- The polynomial budget grows by at most a factor of 3 when a≥1.
theorem budget_growth (D C a : Nat) (ha : 1≤a) : budget D C (a+1)≤3*budget D C a := by
  let L := D*(6*a+17)+3*C
  let L' := D*(6*(a+1)+17)+3*C
  have h1 : 2*(a+2)≤3*(a+1) := by omega
  have h2 : L'≤2*L := by
    have e : 6*(a+1)+17=(6*a+17)+6 := by omega
    dsimp [L,L']; rw [e,Nat.mul_add]
    have h := Nat.mul_le_mul_left D (show 6≤6*a+17 by omega)
    omega
  have hprod := Nat.mul_le_mul h1 h2
  have hleft : (2*(a+2))*L'=2*budget D C (a+1) := by
    dsimp [budget,L']; ac_rfl
  have hright : (3*(a+1))*(2*L)=6*budget D C a := by
    change (3*(a+1))*(2*L)=6*((a+1)*L)
    calc
      _ = (3*2)*((a+1)*L) := by ac_rfl
      _ = _ := rfl
  rw [hleft,hright] at hprod
  omega

theorem exception_cutoff (D C A a : Nat) (hA : 1≤A) (ha : A≤a)
    (hg : budget D C A<3^A) : budget D C a<3^a := by
  induction a with
  | zero => omega
  | succ a ih =>
    by_cases ha' : A≤a
    · have h1 := ih ha'
      have h2 := budget_growth D C a (by omega)
      rw [Nat.pow_succ]
      omega
    · have he : A=a+1 := by omega
      simpa [he] using hg

theorem pure_le_budget (D C a : Nat) (ha : 1≤a) : D*(a+3)+C≤budget D C a := by
  have h1 : D*(a+3)≤D*(6*a+17) := Nat.mul_le_mul_left D (by omega)
  have h2 : D*(6*a+17)+3*C≤(a+1)*(D*(6*a+17)+3*C) := Nat.le_mul_of_pos_left _ (by omega)
  unfold budget
  omega

-- Inverse affine family equation: the new denominator is still coprime to 3.
theorem inverse_affine (D C h r t N : Nat) (hr : r=1 ∨ r=2)
    (he : D*generic h r t+C=3^N) :
    D*(3*3^h+1)*(3^h*(3*t+r)) +
      3^h*(3*C+D*(3*(h+3+(if r=2 then 1 else 0))-r)) = 3^(N+h+1) := by
  let p := 3^h
  let M := 3*p+1
  let H := h+3+(if r=2 then 1 else 0)
  have hHr : r≤3*H := by dsimp [H]; omega
  have hHe : 3*H=r+(3*H-r) := by omega
  have hg : generic h r t=M*t+p*r+H := by unfold generic; dsimp [M,p,H]; omega
  rw [hg] at he
  change D*M*(p*(3*t+r))+p*(3*C+D*(3*H-r))=3^(N+h+1)
  have he2 : 3^(N+h+1)=(3*p)*3^N := by rw [Nat.pow_succ,Nat.pow_add]; dsimp [p]; ac_rfl
  rw [he2,← he]
  have hh : D*(M*(3*t+r))+(3*C+D*(3*H-r))=3*(D*(M*t+p*r+H)+C) := by
    have h3 : M*r=3*p*r+r := by dsimp [M]; rw [Nat.add_mul]; simp
    have h4 : D*(3*H)=D*r+D*(3*H-r) := by conv => lhs; rw [hHe,Nat.mul_add]
    have h5 : M*(3*t)=3*(M*t) := by ac_rfl
    rw [Nat.mul_add M (3*t) r,h5,h3]
    have h4' : 3*(D*H)=D*r+D*(3*H-r) := by rw [Nat.mul_left_comm 3 D H]; exact h4
    have h6 : D*(3*p*r)=3*(D*(p*r)) := by ac_rfl
    simp only [Nat.mul_add]
    rw [h6, Nat.mul_left_comm D 3 (M*t)]
    omega
  calc
    D*M*(p*(3*t+r))+p*(3*C+D*(3*H-r)) = p*(D*(M*(3*t+r))+(3*C+D*(3*H-r))) := by
      rw [Nat.mul_add p (D*(M*(3*t+r))) (3*C+D*(3*H-r))]
      congr 1
      ac_rfl
    _ = p*(3*(D*(M*t+p*r+H)+C)) := by rw [hh]
    _ = (3*p)*(D*(M*t+p*r+H)+C) := by ac_rfl

#print axioms generic_cutoff
#print axioms exception_cutoff
#print axioms inverse_affine
end F119AffineInverse
