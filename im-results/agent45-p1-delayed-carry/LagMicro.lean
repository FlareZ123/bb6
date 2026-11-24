import LagCore
import P1CarryExact
namespace BB6.Agent45.DelayedCarry
open BB6.P1CarryExact (Micro)

theorem total_even (n : Nat) (hn : 1≤n) : total n%2=0 := by
  have hp : 2^n=2^(n-1)*2 := by rw [← Nat.pow_succ]; congr 1; omega
  unfold total
  rw [hp]
  have h : 7*(2^(n-1)*2)=2*(7*2^(n-1)) := by ac_rfl
  simp [h]

theorem lift_quotient (n i B a v u x : Nat) (hn : 1≤n)
    (hq : v+a=quotient n i B)
    (hv : 2*u+x*(n+i+3)=v+total n*x) :
    ∃ c, 2*c+target n i B=a+x*(n+i+3) ∧
      u+c=quotient n (i+1) (B+2^i*x) := by
  let q := quotient n (i+1) (B+2^i*x)
  have he : q=(quotient n i B+total n*x)/2 := quotient_step n i B x
  have hm : (quotient n i B+total n*x)%2=target n i B := by
    rw [target_eq, Nat.add_mod, Nat.mul_mod, total_even n hn]
    simp
  have hsum : 2*q+target n i B=quotient n i B+total n*x := by omega
  have hb := target_bound n i B
  have hqu : u≤q := by omega
  exact ⟨q-u,by omega,by omega⟩

/-- Both weighted residuals are strictly positive and bounded by the largest
weight times the corresponding word. The complementary word is 2^m-B. -/
def WordBound (n m v w B : Nat) : Prop :=
  2^m*v<total n*B ∧ total n*B≤2^m*v+(n+m+2)*B ∧
  2^m*w<total n*(2^m-B) ∧ total n*(2^m-B)≤2^m*w+(n+m+2)*(2^m-B)

theorem word_one (n m v w u z B : Nat) (h : WordBound n m v w B)
    (hB : B<2^m) (hv : v+total n=2*u+(n+m+3)) (hw : w=2*z) :
    WordBound n (m+1) u z (B+2^m) := by
  rcases h with ⟨h1,h2,h3,h4⟩
  let D := 2^m
  have hD : 2^(m+1)=2*D := by simp [D,Nat.pow_succ,Nat.mul_comm]
  have hA : (n+m+2)*B≤(n+m+3)*B := Nat.mul_le_mul_right B (by omega)
  have hAc : (n+m+2)*(D-B)≤(n+m+3)*(D-B) := Nat.mul_le_mul_right _ (by omega)
  have hr := congrArg (fun x : Nat => D*x) hv
  have hl := congrArg (fun x : Nat => D*x) hw
  change D*(v+total n)=D*(2*u+(n+m+3)) at hr
  rw [Nat.mul_add,Nat.mul_add] at hr
  have he : 2*D-(B+D)=D-B := by dsimp [D] at *; omega
  unfold WordBound
  rw [hD,he]
  simp only [Nat.mul_add,show n+(m+1)+2=n+m+3 by omega]
  change D*v<total n*B at h1
  change total n*B≤D*v+(n+m+2)*B at h2
  change D*w<total n*(D-B) at h3
  change total n*(D-B)≤D*w+(n+m+2)*(D-B) at h4
  have hru : D*(2*u)=2*D*u := by ac_rfl
  have hlu : D*(2*z)=2*D*z := by ac_rfl
  have hrw : D*(n+m+3)=(n+m+3)*D := Nat.mul_comm _ _
  have ht : D*total n=total n*D := Nat.mul_comm _ _
  rw [hru,hrw,ht] at hr
  rw [hlu] at hl
  change 2*D*u<total n*B+total n*D ∧ total n*B+total n*D≤2*D*u+((n+m+3)*B+(n+m+3)*D) ∧ 2*D*z<total n*(D-B) ∧ total n*(D-B)≤2*D*z+(n+m+3)*(D-B)
  omega

theorem word_zero (n m v w u z B : Nat) (h : WordBound n m v w B)
    (hB : B<2^m) (hv : v=2*u) (hw : w+total n=2*z+(n+m+3)) :
    WordBound n (m+1) u z B := by
  rcases h with ⟨h1,h2,h3,h4⟩
  let D := 2^m
  have hD : 2^(m+1)=2*D := by simp [D,Nat.pow_succ,Nat.mul_comm]
  have hA : (n+m+2)*B≤(n+m+3)*B := Nat.mul_le_mul_right B (by omega)
  have hAc : (n+m+2)*(D-B)≤(n+m+3)*(D-B) := Nat.mul_le_mul_right _ (by omega)
  have hr := congrArg (fun x : Nat => D*x) hv
  have hl := congrArg (fun x : Nat => D*x) hw
  change D*(w+total n)=D*(2*z+(n+m+3)) at hl
  rw [Nat.mul_add,Nat.mul_add] at hl
  have he : 2*D-B=(D-B)+D := by dsimp [D] at *; omega
  unfold WordBound
  rw [hD,he]
  simp only [Nat.mul_add,show n+(m+1)+2=n+m+3 by omega]
  change D*v<total n*B at h1
  change total n*B≤D*v+(n+m+2)*B at h2
  change D*w<total n*(D-B) at h3
  change total n*(D-B)≤D*w+(n+m+2)*(D-B) at h4
  have hru : D*(2*u)=2*D*u := by ac_rfl
  have hlu : D*(2*z)=2*D*z := by ac_rfl
  have hrw : D*(n+m+3)=(n+m+3)*D := Nat.mul_comm _ _
  have ht : D*total n=total n*D := Nat.mul_comm _ _
  rw [hlu,hrw,ht] at hl
  rw [hlu] at hr
  omega

/-- Every genuine micro history is represented by a small delayed carry,
with both coordinate bounds on the same word. -/
theorem micro_trace (n m v w : Nat) (hn : 14≤n) (heven : n%2=0)
    (h : Micro n m v w) (hm : 0<m) :
    ∃ B a, Trace n m B a ∧ v+a=quotient n m B ∧ WordBound n m v w B := by
  induction h with
  | root => omega
  | one m v w u z h hv hw ih =>
    by_cases hm0 : m=0
    · subst m
      cases h with
      | root =>
        have ht := BB6.P1CarryExact.total_large n hn
        change n+2≤total n at ht
        change 1+total n=2*u+(n+0+3) at hv
        change total n-n-2=2*z at hw
        refine ⟨1,(n+2)/2,Trace.first,?_,?_⟩
        · unfold quotient; simp; omega
        · unfold WordBound; simp; omega
    · obtain ⟨B,a,htr,hq,hbd⟩ := ih (by omega)
      have hv' : 2*u+1*(n+m+3)=v+total n*1 := by simpa [total,BB6.P1CarryExact.total] using hv.symm
      obtain ⟨c,hstep,hQ⟩ := lift_quotient n m B a v u 1 (by omega) hq hv'
      have hB := (trace_bounds n m B a htr).2.1
      refine ⟨B+2^m,c,?_,?_,?_⟩
      · simpa using Trace.step m B a 1 c htr (by decide) hstep
      · simpa using hQ
      · exact word_one n m v w u z B hbd hB (by simpa [total,BB6.P1CarryExact.total] using hv) hw
  | zero m v w u z h hm0 hv hw ih =>
    obtain ⟨B,a,htr,hq,hbd⟩ := ih hm0
    have hv' : 2*u+0*(n+m+3)=v+total n*0 := by simpa using hv.symm
    obtain ⟨c,hstep,hQ⟩ := lift_quotient n m B a v u 0 (by omega) hq hv'
    have hB := (trace_bounds n m B a htr).2.1
    refine ⟨B,c,?_,?_,?_⟩
    · simpa using Trace.step m B a 0 c htr (by decide) hstep
    · simpa using hQ
    · exact word_zero n m v w u z B hbd hB hv (by simpa [total,BB6.P1CarryExact.total] using hw)

end BB6.Agent45.DelayedCarry
