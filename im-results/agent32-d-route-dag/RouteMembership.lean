import RouteBridge

set_option maxHeartbeats 5000000
namespace BB6.Agent32Route
open CryptidBoundary BB6.Padding BB6.BoundaryPadding

/-- The executable graph test exactly recognizes arithmetic realizations of the
    finite path list. The path list is mathematical only, never enumerated. -/
theorem routeTest_iff_path (g : List (List Cert)) (n : Nat) (v : List Bool) :
    routeTest n v g = true ↔ ∃ es ∈ paths v g, ∃ z, RunWord (es++[terminalCert]) n z := by
  induction g generalizing n v with
  | nil =>
    constructor
    · intro h
      simp [routeTest,Bool.and_eq_true] at h
      obtain ⟨⟨hn,hr⟩,hv⟩ := h
      subst v
      let k := (n-4)/3
      have hk : n=inputN k terminalCert.r := by simp [inputN,terminalCert,k]; omega
      refine ⟨[],by simp [paths],terminalCert.outputN k,?_⟩
      rw [hk]
      exact RunWord.cons terminalCert [] k _ (RunWord.nil _)
    · rintro ⟨es,he,z,hz⟩
      unfold paths at he
      split at he
      · rename_i hv
        simp at he; subst es; subst v
        obtain ⟨k,hk,_⟩ := word_cons_inv terminalCert [] n z hz
        rw [hk]
        simp [routeTest,inputN,terminalCert]
      · simp at he
  | cons layer rest ih =>
    constructor
    · intro h
      obtain ⟨e,he,ht⟩ := List.any_eq_true.mp h
      simp only [Bool.and_eq_true,beq_iff_eq] at ht
      obtain ⟨⟨hv,hn⟩,hnext⟩ := ht
      let k := (n-(if e.r=1 then 4 else 2))/3
      obtain ⟨es,hes,z,hz⟩ := (ih (e.outputN k) e.out).mp hnext
      refine ⟨e::es,?_,z,?_⟩
      · unfold paths
        apply List.mem_flatMap.mpr
        exact ⟨e,he,by simp [hv,hes]⟩
      · rw [hn]
        exact RunWord.cons e (es++[terminalCert]) k z hz
    · rintro ⟨es,he,z,hz⟩
      obtain ⟨e,hem,hs⟩ := List.mem_flatMap.mp he
      split at hs
      · rename_i hv
        obtain ⟨tail,ht,rfl⟩ := List.mem_map.mp hs
        obtain ⟨k,hk,hw⟩ := word_cons_inv e (tail++[terminalCert]) n z hz
        apply List.any_eq_true.mpr
        refine ⟨e,hem,?_⟩
        have hk' : (n-(if e.r=1 then 4 else 2))/3=k := by unfold inputN at hk; omega
        simp only [Bool.and_eq_true,beq_iff_eq,hk']
        exact ⟨⟨hv,hk⟩,(ih _ _).mpr ⟨tail,ht,z,hw⟩⟩
      · simp at hs

/-- Membership is periodic for all suffixes and all remaining certified layers. -/
theorem routeTest_mod_invariant (g : List (List Cert)) (hg : validGraph g=true)
    (n m : Nat) (v : List Bool) (hn : 2≤n) (hm : 2≤m)
    (hmod : n%3^(g.length+1)=m%3^(g.length+1)) :
    routeTest n v g = routeTest m v g := by
  have aux (a b : Nat) (ha : 2≤a) (hb : 2≤b)
      (hab : a%3^(g.length+1)=b%3^(g.length+1)) (ht : routeTest a v g=true) :
      routeTest b v g=true := by
    obtain ⟨es,he,z,hz⟩ := (routeTest_iff_path g a v).mp ht
    obtain ⟨r,hr,hi⟩ := word_cylinder (es++[terminalCert]) (path_branches g v es hg he)
    have hl : (es++[terminalCert]).length=g.length+1 := by simp [path_length g v es he]
    rw [hl] at hi
    have har := (hi a ha).mp ⟨z,hz⟩
    have hbr := hab.symm.trans har
    obtain ⟨w,hw⟩ := (hi b hb).mpr hbr
    exact (routeTest_iff_path g b v).mpr ⟨es,he,w,hw⟩
  cases h : routeTest n v g <;> cases h' : routeTest m v g
  · rfl
  · have := aux m n hm hn hmod.symm h'; simp_all
  · have := aux n m hn hm hmod h; simp_all
  · rfl

def smallParameter (n d : Nat) : Nat := n%3^d+3^d

theorem smallParameter_mod (n d : Nat) : smallParameter n d%3^d=n%3^d := by
  simp [smallParameter,Nat.add_mod_right]

theorem smallParameter_ge (n d : Nat) (hd : 1≤d) : 2≤smallParameter n d := by
  have hp : 3≤3^d := by
    have h := Nat.pow_le_pow_right (by decide : 0<3) hd
    simpa using h
  unfold smallParameter; omega

theorem small_test_sound (g : List (List Cert)) (hg : validGraph g=true)
    (n : Nat) (v : List Bool) (hn : 2≤n)
    (h : routeTest (smallParameter n (g.length+1)) v g=true) : Halts (sect n v) := by
  have he := routeTest_mod_invariant g hg n (smallParameter n (g.length+1)) v hn
    (smallParameter_ge _ _ (by omega)) (smallParameter_mod _ _).symm
  exact routeTest_sound g hg n v (he.trans h)

/-- Test a giant unary integer using just its residue and a fixed 172-bit lift. -/
theorem graph_mod_halts (n : Nat) (hn : 2≤n)
    (h : routeTest (smallParameter n 108) [] graph=true) : Halts (sect n []) := by
  apply small_test_sound graph graph_checked n [] hn
  have hl : graph.length=107 := congrArg Prod.fst graph_size
  simpa [hl] using h

/-- Any true root prefix that reaches such a section gives actual blank halting. -/
theorem root_section_halts (t n : Nat) (v : List Bool)
    (h : ObsEq (CryptidBoundary.run t blank) (sect n v))
    (hh : Halts (sect n v)) : Halts blank := by
  obtain ⟨s,hs⟩ := hh
  refine ⟨t+s,?_⟩
  rw [run_add]
  exact (source_congr s h).2.2.2.trans hs

#print axioms routeTest_iff_path
#print axioms routeTest_mod_invariant
#print axioms graph_mod_halts
#print axioms root_section_halts
end BB6.Agent32Route
