import BB429AllRayEntropy
import Lean.Elab.Tactic.Omega

namespace BB429InverseWord

theorem two_even_power (m:Nat) : 2^(2*m)=4^m := by
  calc
    2^(2*m) = (2^2)^m := Nat.pow_mul 2 2 m
    _ = 4^m := by simp [show (2:Nat)^2=4 by decide]

theorem two_shell_powers (m:Nat) :
    16*2^(2*m+1)=32*4^m ∧
    32*2^(2*m+1)=64*4^m ∧
    16*2^(2*m+2)=64*4^m ∧
    32*2^(2*m+2)=128*4^m := by
  have hh:=two_even_power m
  have h1:2^(2*m+1)=2*4^m := by rw [Nat.pow_succ,hh]; omega
  have h2:2^(2*m+2)=4*4^m := by
    have hi:2*m+2=(2*m+1)+1 := by omega
    rw [hi,Nat.pow_succ,h1]
    omega
  constructor
  · rw [h1]; omega
  constructor
  · rw [h1]; omega
  constructor
  · rw [h2]; omega
  · rw [h2]; omega

theorem next_global_limit (m:Nat) :
    32*4^(m+1)=128*4^m := by
  rw [Nat.pow_succ]
  omega

/-- Uniform O(sqrt N) bound for the intersection of the original blank-root
accelerator with any fixed (even or odd) nonnegative-offset diagonal ray,
with a globally bounded first counter rather than one isolated shell. -/
theorem any_ray_global_dyadic_bound (c m:Nat)
    (l:List Nat) (hn:l.Nodup)
    (hl:∀a, a∈l → a<32*4^m ∧ AnyRayCandidate c a) :
    l.length ≤ 256*2^m := by
  induction m generalizing l with
  | zero =>
      have hsub:l ⊆ List.range 32 := by
        intro a ha
        have hh := (hl a ha).1
        simp at hh
        exact List.mem_range.mpr hh
      have hh:=List.Nodup.length_le_of_subset hn hsub
      simp at hh ⊢
      omega
  | succ m ih =>
      let cut1 := 32*4^m
      let cut2 := 64*4^m
      let lo := l.filter (fun a => decide (a<cut1))
      let rest := l.filter (fun a => decide (cut1≤a))
      let mid := rest.filter (fun a => decide (a<cut2))
      let hi := rest.filter (fun a => decide (cut2≤a))
      have hsize1 : l.length = lo.length+rest.length :=
        filter_cut_partition l cut1
      have hsize2 : rest.length = mid.length+hi.length :=
        filter_cut_partition rest cut2
      have hnlo : lo.Nodup := (List.filter_sublist).nodup hn
      have hnrest : rest.Nodup := (List.filter_sublist).nodup hn
      have hnmid : mid.Nodup := (List.filter_sublist).nodup hnrest
      have hnhi : hi.Nodup := (List.filter_sublist).nodup hnrest
      have hlo (a:Nat) (ha:a∈lo) : a∈l ∧ a<cut1 := by
        simp only [lo,List.mem_filter] at ha
        exact ⟨ha.1,(decide_eq_true_eq.mp ha.2)⟩
      have hrest (a:Nat) (ha:a∈rest) : a∈l ∧ cut1≤a := by
        simp only [rest,List.mem_filter] at ha
        exact ⟨ha.1,(decide_eq_true_eq.mp ha.2)⟩
      have hmid (a:Nat) (ha:a∈mid) : a∈l ∧ cut1≤a ∧ a<cut2 := by
        simp only [mid,List.mem_filter] at ha
        have hh:=hrest a ha.1
        exact ⟨hh.1,hh.2,decide_eq_true_eq.mp ha.2⟩
      have hhi (a:Nat) (ha:a∈hi) : a∈l ∧ cut2≤a := by
        simp only [hi,List.mem_filter] at ha
        have hh:=hrest a ha.1
        exact ⟨hh.1,decide_eq_true_eq.mp ha.2⟩
      have hlow : lo.length ≤256*2^m := by
        apply ih lo hnlo
        intro a ha
        obtain ⟨hal,hlt⟩:=hlo a ha
        exact ⟨hlt,(hl a hal).2⟩
      have hpow := two_shell_powers m
      have hlim := next_global_limit m
      have hmiddle : mid.length≤64*2^((2*m+1)/2) := by
        apply any_ray_dyadic_shell_bound c (2*m+1) mid hnmid
        intro a ha
        obtain ⟨hal,ha0,ha1⟩ := hmid a ha
        refine ⟨?_,?_,(hl a hal).2⟩
        · rw [hpow.1]; exact ha0
        · rw [hpow.2.1]; exact ha1
      have hhigh : hi.length≤64*2^((2*m+2)/2) := by
        apply any_ray_dyadic_shell_bound c (2*m+2) hi hnhi
        intro a ha
        obtain ⟨hal,ha0⟩ := hhi a ha
        refine ⟨?_,?_,(hl a hal).2⟩
        · rw [hpow.2.2.1]; exact ha0
        · rw [hpow.2.2.2]; simpa only [hlim] using (hl a hal).1
      have hm1:(2*m+1)/2=m := by omega
      have hm2:(2*m+2)/2=m+1 := by omega
      rw [hm1] at hmiddle
      rw [hm2, Nat.pow_succ] at hhigh
      rw [Nat.pow_succ]
      omega

#print axioms any_ray_global_dyadic_bound
end BB429InverseWord
