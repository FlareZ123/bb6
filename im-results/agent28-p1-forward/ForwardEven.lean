import ForwardPhase
namespace BB6.Agent28Forward
open BB6.Agent1 BB6P1Unit

def A (j : Nat) : Nat := 7*2^j

theorem A_succ (j : Nat) : A (j+1)=2*A j := by unfold A; rw [Nat.pow_succ]; ac_rfl

theorem A_lower (j : Nat) : j+7≤A j := by
  induction j with
  | zero => decide
  | succ j ih => rw [A_succ]; omega

def drop : Nat → Nat
  | 0 => 0
  | j+1 => drop j+(A j-1)

theorem drop_identity (j : Nat) : drop j+j+7=A j := by
  induction j with
  | zero => decide
  | succ j ih => rw [drop,A_succ]; have := A_lower j; omega

theorem drop_lt (j : Nat) : drop j<drop (j+1) := by
  rw [drop]; have := A_lower j; omega

theorem drop_mono {i j : Nat} (h : i≤j) : drop i≤drop j := by
  induction j with
  | zero =>
    have he : i=0 := by omega
    subst i
    exact Nat.le_refl _
  | succ j ih =>
    by_cases he : i=j+1
    · simp [he]
    · have hle : i≤j := by omega
      exact Nat.le_trans (ih hle) (Nat.le_of_lt (drop_lt j))

theorem phase_index (x : Nat) : ∃ j, drop j≤x ∧ x<drop (j+1) := by
  induction x with
  | zero => exact ⟨0,by decide,by decide⟩
  | succ x ih =>
    obtain ⟨j,hlo,hhi⟩ := ih
    by_cases he : x+1<drop (j+1)
    · exact ⟨j,by omega,he⟩
    · have hh := drop_lt (j+1)
      exact ⟨j+1,by omega,by omega⟩

theorem phase_index_unique (x i j : Nat) (hi : drop i≤x ∧ x<drop (i+1))
    (hj : drop j≤x ∧ x<drop (j+1)) : i=j := by
  by_cases hlt : i<j
  · have := drop_mono (show i+1≤j by omega); omega
  · by_cases hgt : j<i
    · have := drop_mono (show j+1≤i by omega); omega
    · omega

def evenHub (j r : Nat) : Nat × Nat := (2*(A j-6),2*r)

theorem even_high (j r : Nat) (hr : A j-1≤r) :
    Walk (evenHub j r) 2 (evenHub (j+1) (r-(A j-1))) := by
  let a:=2*(A j-6)
  let k:=A j-4
  have hA := A_lower j
  have h1 : trans (a,2*r)=some (a+3,2*r-2) := by
    unfold trans T
    have ha : a%2=0 := by dsimp [a]; omega
    have h0 : 2*r≠0 := by omega
    have h1 : 2*r≠1 := by omega
    simp [ha,h0,h1]
  have h2 : trans (a+3,2*r-2)=some (G k (2*r-4)) := by
    unfold trans T
    have ha : (a+3)%2≠0 := by dsimp [a]; omega
    have h0 : 2*r-2≠0 := by omega
    have h1 : 2*r-2≠1 := by omega
    have h2 : 2*r-2≠2 := by omega
    have h3 : 2*r-2≠3 := by omega
    simp [ha,h0,h1,h2,h3]
    congr 1 <;> (dsimp [a,k]; omega)
  have hg : G k (2*r-4)=evenHub (j+1) (r-(A j-1)) := by
    rw [G]
    have hlo : ¬2*r-4<2*k := by dsimp [k]; omega
    have hmid : ¬2*r-4≤2*k+1 := by dsimp [k]; omega
    simp only [hlo,dite_false,hmid,ite_false,evenHub,A_succ]
    dsimp [k]
    congr 1 <;> omega
  rw [hg] at h2
  exact Walk.cons _ _ _ 1 h1 (Walk.single _ _ h2)

theorem even_prefix (x j : Nat) (hx : drop j≤x) :
    Walk (2,2*x) (2*j) (evenHub j (x-drop j)) := by
  induction j with
  | zero => simp [drop,evenHub,A]; exact Walk.nil _
  | succ j ih =>
    have he : drop (j+1)=drop j+(A j-1) := rfl
    have h1 := ih (by omega)
    have h2 := even_high j (x-drop j) (by omega)
    have h3 := h1.append h2
    have hd : x-drop j-(A j-1)=x-drop (j+1) := by omega
    rw [hd] at h3
    simpa only [show 2*(j+1)=2*j+2 by omega] using h3

theorem even_zero (j : Nat) : Walk (evenHub j 0) 1 (decode (A j-1) (A j-6)) := by
  have hA := A_lower j
  have hd : decode (A j-1) (A j-6)=(2,2*(A j-6)+1) := by
    unfold decode
    congr 1 <;> omega
  rw [hd]
  apply Walk.single
  simp [trans,evenHub,T]

theorem even_two (j : Nat) : Walk (evenHub j 1) 2 (2,2*(A j-4)) := by
  let a:=2*(A j-6)
  have ha : a%2=0 := by dsimp [a]; omega
  have hA := A_lower j
  have h1 : trans (a,2)=some (a+3,0) := by simp [trans,T,ha]
  have h2 : trans (a+3,0)=some (2,2*(A j-4)) := by simp [trans,T,a]; omega
  exact Walk.cons _ _ _ 1 h1 (Walk.single _ _ h2)

theorem even_halt (j : Nat) : ∃ p, Walk (evenHub j 2) 1 p ∧ trans p=none := by
  let a:=2*(A j-6)
  have ha : a%2=0 := by dsimp [a]; omega
  have hodd : (a+3)%2≠0 := by omega
  refine ⟨(a+3,2),Walk.single _ _ ?_,?_⟩
  · simp [trans,evenHub,T,a,ha]
  · simp [trans,T,hodd]

/-- Every small even exit has an ordinary moving-modulus first wrap, including the
    middle G branch where the next left counter is zero. -/
theorem even_small (j r : Nat) (hr : 3≤r) (hsmall : r<A j-1) :
    ∃ q v, Wrap (A j+r-2) (2*r-1) q v ∧ valid q v ∧ Walk (evenHub j r) 2 (decode q v) := by
  let a:=2*(A j-6)
  let k:=A j-4
  let p:=G k (2*r-4)
  have hA := A_lower j
  have h1 : trans (a,2*r)=some (a+3,2*r-2) := by
    unfold trans T
    have ha : a%2=0 := by dsimp [a]; omega
    have h0 : 2*r≠0 := by omega
    have h1 : 2*r≠1 := by omega
    simp [ha,h0,h1]
  have h2 : trans (a+3,2*r-2)=some p := by
    unfold trans T
    have ha : (a+3)%2≠0 := by dsimp [a]; omega
    have h0 : 2*r-2≠0 := by omega
    have h1 : 2*r-2≠1 := by omega
    have h2 : 2*r-2≠2 := by omega
    have h3 : 2*r-2≠3 := by omega
    simp [ha,h0,h1,h2,h3,p]
    congr 1 <;> (dsimp [a,k]; omega)
  have hw : Walk (evenHub j r) 2 p := Walk.cons _ _ _ 1 h1 (Walk.single _ _ h2)
  by_cases hmid : r=A j-2
  · have hg : p=(0,4*r-5) := by
      unfold p
      rw [G]
      have hlo : ¬2*r-4<2*k := by dsimp [k]; omega
      have hhi : 2*r-4≤2*k+1 := by dsimp [k]; omega
      simp [hlo,hhi]
      omega
    have hq : A j+r-2=2*r := by omega
    rw [hq]
    have hm := wrap_one (2*r) (2*r-1) (by omega) (by omega)
    have he : 2*(2*r-1)-(2*r+1)=2*r-3 := by omega
    rw [he] at hm
    refine ⟨2*r+1,2*r-3,hm,by unfold valid; omega,?_⟩
    have hd : decode (2*r+1) (2*r-3)=p := by rw [hg]; unfold decode; congr 1 <;> omega
    rwa [hd]
  · have hlo : 2*r-4<2*k := by dsimp [k]; omega
    let z:=2*r-1
    let l:=A j-r-3
    have hg : p=G l (2*z-3) := by
      unfold p
      rw [G]
      simp only [hlo,dite_true]
      congr 1 <;> (dsimp [k,l,z]; omega)
    have hq : l+z+2=A j+r-2 := by dsimp [l,z]; omega
    have hwrap := wrap_G l z (by dsimp [z]; omega)
    rw [hq,←hg] at hwrap
    refine ⟨(coordPair p).1,(coordPair p).2,hwrap,valid_coord p,?_⟩
    have hd : decode (coordPair p).1 (coordPair p).2=p := by
      rw [hg]
      exact decode_coord _ (G_first_even _ _) (G_second_odd _ _ (by dsimp [z]; omega))
    rwa [hd]

#print axioms phase_index
#print axioms even_prefix
#print axioms even_small
#print axioms even_halt
end BB6.Agent28Forward
