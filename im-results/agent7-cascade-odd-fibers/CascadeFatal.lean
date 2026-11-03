import ResetChain

namespace CascadeFatal
open CascadeSource CascadeChain

def H (n : Nat) : Nat := 4*2^n-n-4

theorem pow_ge (n : Nat) : n+1≤2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ]
    omega

theorem height_eq (n : Nat) : H n+n+4=4*2^n := by
  have h:=pow_ge n
  dsimp [H]
  omega

theorem height_step (n : Nat) : H n≤H (n+1) := by
  have h:=height_eq n
  have h1:=height_eq (n+1)
  have hpow : 2^(n+1)=2*2^n := by rw [Nat.pow_succ];omega
  omega

theorem height_mono (a b : Nat) (h : a≤b) : H a≤H b := by
  obtain ⟨d,rfl⟩ : ∃d, b=a+d := ⟨b-a,by omega⟩
  induction d with
  | zero => simp
  | succ d ih =>
    have hstep:=height_step (a+d)
    have hb : a+(d+1)=(a+d)+1 := by omega
    rw [hb]
    omega

theorem height_base (k : Nat) : H (k+1)+k+5=8*2^k := by
  have hh:=height_eq (k+1)
  have hp : 2^(k+1)=2*2^k := by rw [Nat.pow_succ]; omega
  omega

theorem fatal_guard (n k : Nat) (hk : k<n) :
    8*2^k ≤ H n+k+5 := by
  have hb:=height_base k
  have hm:=height_mono (k+1) n (by omega)
  omega

/-- Weak continuation guard works exactly at the equality boundary of fatal heights. -/
theorem cascade_one_weak (h k : Nat) (hh : 8*2^k≤h+k+5) :
    Cstep (A k) (B h k) = some (A (k+1),B h (k+1)) := by
  have hp : 1≤2^k := Nat.one_le_pow _ _ (by decide)
  have hA : A k+2=4*2^k := by dsimp [A]; omega
  have hB : B h k+8*2^k=2*h+2*k+9 := by dsimp [B]; omega
  have hb : 2≤B h k := by omega
  have hd : 2*(A k) ≤ B h k-2 := by omega
  rw [Cstep_large (A k) (B h k) hb hd]
  have hpow : 2^(k+1)=2*2^k := by rw [Nat.pow_succ];omega
  have ha2 : 2*(A k)+2=A (k+1) := by dsimp [A];omega
  have hb2 : B h k-2-2*(A k)=B h (k+1) := by dsimp [B];omega
  rw [ha2,hb2]

/-- Parameter-uniform exact source C/P path through the finite cascade to the first halt gate. -/
theorem cascade_run_weak (h m : Nat)
    (hh : ∀k<m,8*2^k≤h+k+5) :
    Reach (.C h 0) (.C (A m) (B h m)) := by
  have hbase : Reach (.C h 0) (.C (A 0) (B h 0)) := by
    rw [(AB0 h).1,(AB0 h).2]
    exact Reach.one rfl
  induction m with
  | zero => exact hbase
  | succ m ih =>
    have hm := ih (by intro k hk; exact hh k (by omega))
    exact hm.trans (C_step_sound (A m) (B h m) (A (m+1)) (B h (m+1))
      (cascade_one_weak h m (hh m (by omega))))

/-- Every target c_n is genuinely a halting gateway for the copied source next. -/
theorem every_fatal_height_halts (n : Nat) :
    ∃ a, Reach (.C (H n) 0) (.C a 1) ∧ next (.C a 1)=none := by
  have hr := cascade_run_weak (H n) n (fatal_guard n)
  have hb : B (H n) n=1 := by
    have hh:=height_eq n
    dsimp [B]
    omega
  rw [hb] at hr
  exact ⟨A n,hr,rfl⟩

/-- For n mod6=4 or5 and n>=4 there is a synthetic (nonblank) source start that halts. -/
theorem complementary_halting_seeds (n : Nat) (hn : 4≤n)
    (hc : n%6=4 ∨ n%6=5) :
    ∃ (h a : Nat), Reach (.C h 0) (.C a 1) ∧ next (.C a 1)=none := by
  obtain ⟨h,hs⟩ := all_complementary_source_reachable n hn hc
  obtain ⟨a,hr,hhalt⟩ := every_fatal_height_halts n
  have hh : H n=4*2^n-n-4 := rfl
  rw [hh] at hr
  exact ⟨h,a,hs.trans hr,hhalt⟩

#print axioms every_fatal_height_halts
#print axioms complementary_halting_seeds

end CascadeFatal
