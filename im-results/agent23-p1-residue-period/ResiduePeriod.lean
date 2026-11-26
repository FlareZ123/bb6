import Lean
namespace BB6.Agent23ResiduePeriod

def Rep (M x : Int) : List Int → Prop
  | [] => M ∣ x
  | w::ws => Rep M x ws ∨ Rep M (x-w) ws

theorem half_base (M x w : Int) (hw : 2*M ∣ w-M) :
    ((2*M ∣ x) ∨ (2*M ∣ x-w)) ↔ M ∣ x := by
  obtain ⟨a,ha⟩ := hw
  constructor
  · rintro (⟨b,hb⟩ | ⟨b,hb⟩)
    · exact ⟨2*b, by grind⟩
    · exact ⟨2*b+2*a+1, by grind⟩
  · rintro ⟨b,hb⟩
    have hb' : b = 2*(b/2) ∨ b=2*(b/2)+1 := by omega
    rcases hb' with he|ho
    · left; exact ⟨b/2,by grind⟩
    · right; exact ⟨b/2-a,by grind⟩

theorem half_rep (M x w : Int) (ws : List Int) (hw : 2*M ∣ w-M) :
    Rep (2*M) x (w::ws) ↔ Rep M x ws := by
  induction ws generalizing x with
  | nil => exact half_base M x w hw
  | cons v vs ih =>
    simp only [Rep]
    rw [show x-w-v=x-v-w by omega]
    have h1 := ih x
    have h2 := ih (x-v)
    simp only [Rep] at h1 h2
    grind

def stripTop (M : Int) : List Int → Option (List Int)
  | [] => none
  | w::ws => if 2*M ∣ w-M then some ws else (stripTop M ws).map (w::·)

theorem stripTop_sound (M x : Int) (ws rs : List Int)
    (h : stripTop M ws = some rs) : Rep (2*M) x ws ↔ Rep M x rs := by
  induction ws generalizing x rs with
  | nil => simp [stripTop] at h
  | cons w ws ih =>
    unfold stripTop at h
    split at h
    · rename_i hw
      injection h with he
      subst rs
      exact half_rep M x w ws hw
    · cases hh : stripTop M ws with
      | none => simp [hh] at h
      | some ts =>
        simp [hh] at h
        subst rs
        simp only [Rep,ih x ts hh,ih (x-w) ts hh]

def reduce : Nat → List Int → Nat × List Int
  | 0,ws => (0,ws)
  | k+1,ws => match stripTop ((2:Int)^k) ws with
    | none => (k+1,ws)
    | some rs => reduce k rs

theorem reduce_sound (k : Nat) (ws : List Int) (x : Int) :
    Rep ((2:Int)^k) x ws ↔
      Rep ((2:Int)^(reduce k ws).1) x (reduce k ws).2 := by
  induction k generalizing ws with
  | zero => rfl
  | succ k ih =>
    unfold reduce
    split
    · rfl
    · rename_i rs h
      rw [Int.pow_succ,Int.mul_comm]
      exact (stripTop_sound _ _ _ _ h).trans (ih rs)

theorem reduce_le (k : Nat) (ws : List Int) : (reduce k ws).1 ≤ k := by
  induction k generalizing ws with
  | zero => simp [reduce]
  | succ k ih =>
    unfold reduce
    split
    · simp
    · exact Nat.le_trans (ih _) (Nat.le_succ _)

def weights (q : Nat) : Nat → List Int
  | 0 => []
  | k+1 => ((q+k)*2^k : Nat) :: weights q k

theorem rep_weight_iff (W : Nat → Nat → Nat → Int)
    (h0 : ∀ q, W q 0 0=0)
    (hzero : ∀ q k B, B<2^k → W q (k+1) B = W q k B)
    (hone : ∀ q k B, B<2^k → W q (k+1) (B+2^k) = W q k B + ((q+k)*2^k : Nat))
    (M x : Int) (q k : Nat) :
    Rep M x (weights q k) ↔ ∃ B, B<2^k ∧ M ∣ x-W q k B := by
  induction k generalizing x with
  | zero =>
    simp only [weights,Rep,Nat.pow_zero,Nat.lt_one_iff]
    constructor
    · intro h
      exact ⟨0,rfl,by simpa [h0] using h⟩
    · rintro ⟨B,rfl,h⟩
      simpa [h0] using h
  | succ k ih =>
    simp only [weights,Rep]
    constructor
    · rintro (h|h)
      · obtain ⟨B,hB,hres⟩ := (ih x).1 h
        exact ⟨B,by rw [Nat.pow_succ]; omega,by rw [hzero q k B hB]; exact hres⟩
      · obtain ⟨B,hB,hres⟩ := (ih (x-((q+k)*2^k : Nat))).1 h
        refine ⟨B+2^k,by rw [Nat.pow_succ]; omega,?_⟩
        rw [hone q k B hB]
        rw [show x-(W q k B+((q+k)*2^k : Nat)) = x-((q+k)*2^k : Nat)-W q k B by omega]
        exact hres
    · rintro ⟨B,hB,hres⟩
      by_cases hb : B<2^k
      · left
        exact (ih x).2 ⟨B,hb,by rwa [hzero q k B hb] at hres⟩
      · right
        let b := B-2^k
        have hb' : b<2^k := by rw [Nat.pow_succ] at hB; dsimp [b]; omega
        have he : B=b+2^k := by dsimp [b]; omega
        rw [he,hone q k b hb'] at hres
        refine (ih _).2 ⟨b,hb',?_⟩
        rw [show x-((q+k)*2^k : Nat)-W q k b = x-(W q k b+((q+k)*2^k : Nat)) by omega]
        exact hres

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem eight_suffix_reduced (h : Nat) :
    (reduce 8 (weights (32*h+16) 8)).1 = 3 := by
  have h0 : ((256:Int) ∣ (32*(h:Int)+16+7)*128-128) := by
    rw [Int.dvd_iff_emod_eq_zero]; omega
  have h1 : ¬ ((128:Int) ∣ (32*(h:Int)+16+6)*64-64) := by
    rw [Int.dvd_iff_emod_eq_zero]; omega
  have h2 : ¬ ((128:Int) ∣ (32*(h:Int)+16+5)*32-64) := by
    rw [Int.dvd_iff_emod_eq_zero]; omega
  have h3 : ((128:Int) ∣ (32*(h:Int)+16+4)*16-64) := by
    rw [Int.dvd_iff_emod_eq_zero]; omega
  have h4 : ¬ ((64:Int) ∣ (32*(h:Int)+16+6)*64-32) := by
    rw [Int.dvd_iff_emod_eq_zero]; omega
  have h5 : ((64:Int) ∣ (32*(h:Int)+16+5)*32-32) := by
    rw [Int.dvd_iff_emod_eq_zero]; omega
  have h6 : ¬ ((32:Int) ∣ (32*(h:Int)+16+6)*64-16) := by
    rw [Int.dvd_iff_emod_eq_zero]; omega
  have h7 : ¬ ((32:Int) ∣ (32*(h:Int)+16+3)*8-16) := by
    rw [Int.dvd_iff_emod_eq_zero]; omega
  have h8 : ¬ ((32:Int) ∣ (32*(h:Int)+16+2)*4-16) := by
    rw [Int.dvd_iff_emod_eq_zero]; omega
  have h9 : ¬ ((32:Int) ∣ (32*(h:Int)+16+1)*2-16) := by
    rw [Int.dvd_iff_emod_eq_zero]; omega
  have h10 : ((32:Int) ∣ (32*(h:Int)+16+0)*1-16) := by
    rw [Int.dvd_iff_emod_eq_zero]; omega
  have h11 : ¬ ((16:Int) ∣ (32*(h:Int)+16+6)*64-8) := by
    rw [Int.dvd_iff_emod_eq_zero]; omega
  have h12 : ((16:Int) ∣ (32*(h:Int)+16+3)*8-8) := by
    rw [Int.dvd_iff_emod_eq_zero]; omega
  have h13 : ¬ ((8:Int) ∣ (32*(h:Int)+16+6)*64-4) := by
    rw [Int.dvd_iff_emod_eq_zero]; omega
  have h14 : ¬ ((8:Int) ∣ (32*(h:Int)+16+2)*4-4) := by
    rw [Int.dvd_iff_emod_eq_zero]; omega
  have h15 : ¬ ((8:Int) ∣ (32*(h:Int)+16+1)*2-4) := by
    rw [Int.dvd_iff_emod_eq_zero]; omega
  simp [weights,reduce,stripTop,Int.natCast_add,Int.natCast_mul,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h11,h12,h13,h14,h15]

theorem stripTop_append (M : Int) (a b a' : List Int)
    (h : stripTop M a = some a') : stripTop M (a++b)=some (a'++b) := by
  induction a generalizing a' with
  | nil => simp [stripTop] at h
  | cons w ws ih =>
    simp only [stripTop] at h
    simp only [List.cons_append,stripTop]
    split at h
    · rename_i hw
      simp [hw]
      injection h
    · rename_i hw
      cases hh : stripTop M ws with
      | none => simp [hh] at h
      | some ts =>
        simp [hh] at h
        subst a'
        simp [hw,ih ts hh]

theorem stripTop_scale (M T : Int) (hT : T ≠ 0) (a : List Int) :
    stripTop (T*M) (a.map (T*·)) = (stripTop M a).map (List.map (T*·)) := by
  induction a with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons,stripTop]
    have h : (2*(T*M) ∣ T*w-T*M) ↔ (2*M ∣ w-M) := by
      rw [show 2*(T*M)=T*(2*M) by grind,show T*w-T*M=T*(w-M) by grind]
      exact Int.mul_dvd_mul_iff_left hT
    by_cases hw : 2*M ∣ w-M
    · simp [hw,h.mpr hw]
    · simp only [hw,ite_false,show ¬ (2*(T*M) ∣ T*w-T*M) from fun hd => hw (h.mp hd)]
      rw [ih]
      cases stripTop M ws <;> rfl

theorem weights_append (q k r : Nat) :
    weights q (k+r) = (weights (q+k) r).map ((2:Int)^k*·) ++ weights q k := by
  induction r with
  | zero => simp [weights]
  | succ r ih =>
    rw [Nat.add_succ]
    simp only [weights,List.map_cons,List.cons_append]
    rw [ih]
    congr 1
    push_cast
    change ((q:Int)+(↑(k+r):Int))*2^(k+r) = _
    rw [Int.pow_add,Int.natCast_add]
    grind

theorem reduce_scaled_suffix_le (k r : Nat) (a b : List Int) :
    (reduce (k+r) (a.map ((2:Int)^k*·) ++ b)).1 ≤ k+(reduce r a).1 := by
  induction r generalizing a with
  | zero => simpa [reduce] using reduce_le k (a.map ((2:Int)^k*·) ++ b)
  | succ r ih =>
    cases hh : stripTop ((2:Int)^r) a with
    | none =>
      rw [show reduce (r+1) a = (r+1,a) by simp [reduce,hh]]
      exact reduce_le _ _
    | some rs =>
      have hs := stripTop_scale ((2:Int)^r) ((2:Int)^k) (Int.pow_ne_zero (by decide)) a
      rw [hh] at hs
      simp only [Option.map_some] at hs
      have ha := stripTop_append _ _ b _ hs
      rw [← Int.pow_add] at ha
      rw [Nat.add_succ]
      simp only [reduce,ha,hh]
      exact ih rs

theorem final24_reduced (q k h : Nat) (hq : q+k=32*h+16) :
    (reduce (k+8) (weights q (k+8))).1 ≤ k+3 := by
  rw [weights_append]
  have hh := reduce_scaled_suffix_le k 8 (weights (q+k) 8) (weights q k)
  rw [hq,eight_suffix_reduced] at hh
  simpa [hq] using hh

theorem residue_eq_iff (M Y c w : Int) (hc : 0 ≤ c) (hc' : c < M) :
    c = (Y-w)%M ↔ M ∣ (Y-c)-w := by
  rw [show Y-c-w=Y-w-c by omega,Int.dvd_iff_emod_eq_zero,← Int.emod_eq_emod_iff_emod_sub_eq_zero,Int.emod_eq_of_lt hc hc']
  exact eq_comm

theorem reduced_weight_iff (W : Nat → Nat → Nat → Int)
    (h0 : ∀ q, W q 0 0=0)
    (hzero : ∀ q k B, B<2^k → W q (k+1) B = W q k B)
    (hone : ∀ q k B, B<2^k → W q (k+1) (B+2^k) = W q k B + ((q+k)*2^k : Nat))
    (q k : Nat) (Y c : Int) (hc : 0≤c) (hc' : c<(2:Int)^k) :
    (∃ B, B<2^k ∧ c=(Y-W q k B)%((2:Int)^k)) ↔
      Rep ((2:Int)^(reduce k (weights q k)).1) (Y-c) (reduce k (weights q k)).2 := by
  rw [← reduce_sound,rep_weight_iff W h0 hzero hone]
  constructor <;> rintro ⟨B,hB,hr⟩
  · exact ⟨B,hB,(residue_eq_iff _ _ _ _ hc hc').mp hr⟩
  · exact ⟨B,hB,(residue_eq_iff _ _ _ _ hc hc').mpr hr⟩

#print axioms reduce_sound
#print axioms final24_reduced
#print axioms reduced_weight_iff
end BB6.Agent23ResiduePeriod
