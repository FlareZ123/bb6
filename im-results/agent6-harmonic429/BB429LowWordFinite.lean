import BB429LowWordProgression
import Lean.Elab.Tactic.Omega

namespace BB429.LowWord
set_option maxHeartbeats 3000000

def guardBound (vs : List Move) : Nat :=
  let f := symbolic vs initial
  1+((allForms vs).map fun l => ((Modulus f)*l.c-(Offset f)*l.d).natAbs).sum

theorem mem_le_sum (xs : List Nat) (x : Nat) (h : x∈xs) : x≤xs.sum := by
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.mp h with h|h
    · omega
    · have hh := ih h; omega

theorem guard_abs_bound (vs : List Move) (l : Linear) (hl : l ∈ allForms vs) :
    let f := symbolic vs initial
    ((Modulus f)*l.c-(Offset f)*l.d).natAbs < guardBound vs := by
  dsimp [guardBound]
  have hh := mem_le_sum _ _ (List.mem_map_of_mem hl : ((Modulus (symbolic vs initial))*l.c-(Offset (symbolic vs initial))*l.d).natAbs ∈
    (allForms vs).map (fun l => ((Modulus (symbolic vs initial))*l.c-(Offset (symbolic vs initial))*l.d).natAbs))
  omega

theorem affine_stable (a b X : Int) (hX : (b.natAbs:Int)<X) :
    0≤a*X+b ↔ (0<a ∨ a=0 ∧ 0≤b) := by
  have hb1 : b≤(b.natAbs:Int) := Int.le_natAbs
  have hb2 : -b≤(b.natAbs:Int) := by simpa using (Int.le_natAbs (a := -b))
  by_cases ha : 0<a
  · have hh := Int.mul_le_mul_of_nonneg_right (show 1≤a by omega) (show 0≤X by omega)
    rw [Int.one_mul] at hh
    omega
  · by_cases hz : a=0
    · simp [hz]
    · have hh := Int.mul_le_mul_of_nonneg_right (show a≤-1 by omega) (show 0≤X by omega)
      rw [Int.neg_mul,Int.one_mul] at hh
      omega

theorem pow16_ge (m : Nat) : m+1≤16^m := by
  induction m with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

theorem large_guard_equiv (vs : List Move) (l : Linear) (hl : l∈allForms vs) (m n : Nat)
    (hm : guardBound vs≤m) (hn : guardBound vs≤n) :
    let f := symbolic vs initial
    0≤l.elim (Modulus f) (Coefficient f) (Offset f) (16^m) ↔
    0≤l.elim (Modulus f) (Coefficient f) (Offset f) (16^n) := by
  let f := symbolic vs initial
  let a := Modulus f*l.x+Coefficient f*l.d
  let b := Modulus f*l.c-Offset f*l.d
  have hb : b.natAbs<guardBound vs := guard_abs_bound vs l hl
  have hmp := pow16_ge m
  have hnp := pow16_ge n
  have hm' : (b.natAbs:Int)<(16:Int)^m := by
    rw [show (16:Int)^m=((16^m:Nat):Int) by exact Int.natCast_pow 16 m |>.symm]
    omega
  have hn' : (b.natAbs:Int)<(16:Int)^n := by
    rw [show (16:Int)^n=((16^n:Nat):Int) by exact Int.natCast_pow 16 n |>.symm]
    omega
  change 0≤a*(16:Int)^m+b ↔ 0≤a*(16:Int)^n+b
  rw [affine_stable a b _ hm',affine_stable a b _ hn']

/-- Every finite mixed word has a witness, if at all, below this explicitly
    computable scale bound. The length of the word is not bounded here. -/
theorem finite_scale_search (vs : List Move) :
    let f := symbolic vs initial
    (∃ m, Terminal m vs) ↔ ∃ m, m≤guardBound vs+reduced (Modulus f) (Coefficient f) ∧ Terminal m vs := by
  let f := symbolic vs initial
  let B := guardBound vs
  let N := reduced (Modulus f) (Coefficient f)
  change (∃ m, Terminal m vs) ↔ ∃ m, m≤B+N ∧ Terminal m vs
  constructor
  · rintro ⟨m,hm⟩
    by_cases hsmall : m≤B+N
    · exact ⟨m,hsmall,hm⟩
    · obtain ⟨p,r,hp,hpN,hr,hper⟩ := terminal_progression vs m hm
      change p≤N at hpN
      have ⟨hm1,hmr,hmg⟩ := (hper m).mp hm
      let n := B+(m-B)%p
      have hnB : B≤n := by dsimp [n]; omega
      have hnlt : n<B+p := by
        have hh := Nat.mod_lt (m-B) hp; dsimp [n]; omega
      have he : n%p=m%p := by
        have eq : m=B+(m-B) := by omega
        conv => rhs; rw [eq,Nat.add_mod]
        dsimp [n]
        rw [Nat.add_mod,Nat.mod_mod]
      refine ⟨n,by omega,(hper n).mpr ⟨?_,he.trans hmr,?_⟩⟩
      · have hB : 1≤B := by dsimp [B,guardBound]; omega
        omega
      · intro l hl
        exact (large_guard_equiv vs l hl m n (by omega) hnB).mp (hmg l hl)
  · rintro ⟨m,_,hm⟩; exact ⟨m,hm⟩

#print axioms finite_scale_search
end BB429.LowWord
