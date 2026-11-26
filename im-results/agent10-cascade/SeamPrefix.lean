import SeamMass
namespace SeamMass

set_option maxHeartbeats 0

def code : List (Nat × Nat) → List Bool
  | [] => []
  | (j,_)::w => List.replicate (j-1) false ++ true::code w

theorem path_valid {s : State} {w} (h : Path s w) : Valid s := by
  cases h with
  | nil => simp [Valid,root]
  | cons he _ _ => exact he.1

theorem edge_j_pos {s t j a} (h : Edge s t j a) : 0 < j := by
  cases j with
  | zero => exact False.elim (exponent_zero_forbidden _ h.2.2.2.2)
  | succ j => omega

theorem code_first_one (j a : Nat) (w : List (Nat × Nat)) :
    (code ((j,a)::w))[j-1]? = some true := by
  simp [code,List.getElem?_append]

theorem code_before_one (j a i : Nat) (w : List (Nat × Nat)) (hi : i < j-1) :
    (code ((j,a)::w))[i]? = some false := by
  simp [code,List.getElem?_append,hi,List.getElem?_replicate]

theorem code_drop_first (j a : Nat) (w : List (Nat × Nat)) (hj : 0 < j) :
    (code ((j,a)::w)).drop j = code w := by
  have he : j = (List.replicate (j-1) false ++ [true]).length := by
    simp; omega
  have eq : code ((j,a)::w) = (List.replicate (j-1) false ++ [true]) ++ code w := by
    simp only [code,List.append_assoc,List.singleton_append]
  rw [eq]
  exact (congrArg (fun n => ((List.replicate (j-1) false ++ [true]) ++ code w).drop n) he).trans List.drop_left

theorem code_length {s w} (h : Path s w) : (code w).length = totalJ w := by
  induction h with
  | nil => rfl
  | @cons s t j a w he hA hp ih =>
    have hj := edge_j_pos he
    simp [code,totalJ] at *
    omega

theorem code_head_eq {B j a k b : Nat} {w v : List (Nat × Nat)}
    (hj : 0<j) (hk : 0<k) (hjB : j≤B)
    (h : (code ((j,a)::w)).take B = (code ((k,b)::v)).take B) : j=k := by
  rcases Nat.lt_trichotomy j k with hlt|heq|hgt
  · have hi : j-1 < B := by omega
    have hi' : j-1 < k-1 := by omega
    have hg := congrArg (fun x : List Bool => x[j-1]?) h
    simp only [List.getElem?_take,if_pos hi,code_first_one,code_before_one _ _ _ _ hi'] at hg
    contradiction
  · exact heq
  · have hi : k-1 < B := by omega
    have hi' : k-1 < j-1 := by omega
    have hg := congrArg (fun x : List Bool => x[k-1]?) h
    simp only [List.getElem?_take,if_pos hi,code_first_one,code_before_one _ _ _ _ hi'] at hg
    contradiction

theorem add_mod_cancel {p q c m : Nat} (h : (p+c)%m=(q+c)%m) : p%m=q%m := by
  obtain ⟨i,j,hij⟩ := Nat.mod_eq_mod_iff.mp h
  exact Nat.mod_eq_mod_iff.mpr ⟨i,j,by omega⟩

/-- Matching binary prefixes identify the odd numerator modulo 2^(B+1). -/
theorem prefix_mod {s : State} {w : List (Nat × Nat)} (hw : Path s w)
    {t : State} {v : List (Nat × Nat)} (hv : Path t v)
    (hA : s.A=t.A) (B : Nat) (hBw : B≤totalJ w) (hBv : B≤totalJ v)
    (hprefix : (code w).take B = (code v).take B) :
    s.p%2^(B+1)=t.p%2^(B+1) := by
  induction hw generalizing t v B with
  | nil =>
    have hb : B=0 := by simpa [totalJ] using hBw
    subst B
    simpa [root] using (path_valid hv).2.2.symm
  | @cons s u j a w he hAs hw ih =>
    by_cases hzero : B=0
    · subst B
      simpa using he.1.2.2.trans (path_valid hv).2.2.symm
    cases hv with
    | nil => simp [totalJ] at hBv; contradiction
    | @cons t z k b v ge hAt hv =>
      have hj := edge_j_pos he
      have hk := edge_j_pos ge
      have hp := he.2.2.2.1
      have hq := ge.2.2.2.1
      apply add_mod_cancel (c:=3^s.A)
      rw [hp,hA,hq]
      by_cases hjB : j≤B
      · have hjk := code_head_eq hj hk hjB hprefix
        subst k
        have hab := exponent_unique he.2.2.2.2 ge.2.2.2.2
        subst b
        have hAz : u.A=z.A := by have h1:=he.2.2.1; have h2:=ge.2.2.1; omega
        have hb1 : B-j≤totalJ w := by simpa [totalJ] using (show B-j≤totalJ ((j,a)::w)-j by omega)
        have hb2 : B-j≤totalJ v := by simpa [totalJ] using (show B-j≤totalJ ((j,a)::v)-j by omega)
        have htail := congrArg (List.drop j) hprefix
        simp only [List.drop_take,code_drop_first _ _ _ hj] at htail
        have hm := ih hv hAz (B-j) hb1 hb2 htail
        have heq : B+1=j+(B-j+1) := by omega
        rw [heq,Nat.pow_add,Nat.mul_mod_mul_left,Nat.mul_mod_mul_left,hm]
      · have hkB : B<k := by
          by_cases hnot : k≤B
          · have heq := code_head_eq hk hj hnot hprefix.symm
            omega
          · omega
        have hd1 : 2^(B+1) ∣ 2^j*u.p := Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) (Nat.dvd_mul_right _ _)
        have hd2 : 2^(B+1) ∣ 2^k*z.p := Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) (Nat.dvd_mul_right _ _)
        rw [Nat.mod_eq_zero_of_dvd hd1,Nat.mod_eq_zero_of_dvd hd2]

/-- If the prefix length covers the numerator interval, the prefix determines
    the entire ideal word. -/
theorem prefix_injective {s t : State} {w v : List (Nat × Nat)}
    (hw : Path s w) (hv : Path t v) (hA : s.A=t.A) (hpos : 0<s.A)
    (B : Nat) (hlo : 2^B≤3^s.A) (hhi : 3^s.A<2^(B+1))
    (hprefix : (code w).take B = (code v).take B) : s=t ∧ w=v := by
  have hBw : B≤totalJ w := by
    by_cases h : B≤totalJ w
    · exact h
    · have hm := Nat.pow_le_pow_right (by decide : 0<2) (by omega : totalJ w≤B)
      have hb := (path_budget hw).2 hpos
      omega
  have hBv : B≤totalJ v := by
    by_cases h : B≤totalJ v
    · exact h
    · have hm := Nat.pow_le_pow_right (by decide : 0<2) (by omega : totalJ v≤B)
      have hb := (path_budget hv).2 (by omega)
      rw [←hA] at hb
      omega
  have hmod := prefix_mod hw hv hA B hBw hBv hprefix
  have hp : s.p<2^(B+1) := Nat.lt_of_le_of_lt (path_valid hw).2.1 hhi
  have hq : t.p<2^(B+1) := Nat.lt_of_le_of_lt (path_valid hv).2.1 (by rw [←hA]; exact hhi)
  rw [Nat.mod_eq_of_lt hp,Nat.mod_eq_of_lt hq] at hmod
  have he : s=t := by cases s; cases t; simp_all
  subst t
  exact ⟨rfl,path_unique hw hv⟩

#print axioms code_length
#print axioms prefix_mod
#print axioms prefix_injective
end SeamMass
