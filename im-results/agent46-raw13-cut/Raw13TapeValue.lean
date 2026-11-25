import Raw13Frames

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13TapeValue
open BB6Coverage BB6Coverage.Agent31Pump
open BB6.Agent46Raw13Frames
open BB6.Agent46Raw13Detour (base blank0 live)

def val : List Bool → Nat
  | [] => 0
  | b::L => b.toNat + 2 * val L

theorem val_append (L R : List Bool) : val (L++R) = val L + 2^L.length * val R := by
  induction L with
  | nil => simp [val]
  | cons b L ih => simp only [List.cons_append,val,ih,List.length_cons,Nat.pow_succ]; rw [Nat.mul_comm (2^L.length) 2, Nat.mul_assoc]; omega

theorem val_zeros (n : Nat) : val (zeros n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [zeros,List.replicate_succ,val,Bool.toNat_false] at ih ⊢; omega

theorem val_pad (L : List Bool) (n : Nat) : val (L++zeros n) = val L := by rw [val_append,val_zeros,Nat.mul_zero,Nat.add_zero]

theorem headVal (L : List Bool) : (L.headD false).toNat = val L % 2 := by
  cases L with
  | nil => rfl
  | cons b L => cases b <;> simp [val,Bool.toNat] <;> omega

theorem tailVal (L : List Bool) : val L.tail = val L / 2 := by
  cases L with
  | nil => rfl
  | cons b L => cases b <;> simp [val,Bool.toNat] <;> omega

structure NConf where
  q : Fin 6
  l : Nat
  r : Nat
  deriving DecidableEq, Repr

def nv (z : Z0) : NConf := ⟨z.q,val z.l,val z.r⟩
def stepN (z : NConf) : Option NConf := do
  let mv ← (base (z.q,z.l%2=1)).join
  if mv.right then return ⟨mv.next,z.r%2+2*(mv.write.toNat+2*(z.l/2)),z.r/2⟩
  else return ⟨mv.next,z.l/2,mv.write.toNat+2*z.r⟩

theorem headBool (L : List Bool) : decide (val L % 2=1) = L.headD false := by
  rw [← headVal]
  cases h : L.headD false <;> rfl

theorem step_project (z : Z0) : stepN (nv z) = (step0 base z).map nv := by
  obtain ⟨q,l,r⟩ := z
  unfold stepN step0 nv
  simp only [headBool]
  cases h : base (q,l.headD false) with
  | none => rfl
  | some o =>
    cases o with
    | none => rfl
    | some mv =>
      cases hh : mv.right <;> simp [h,hh,move0,nv,val,headVal,tailVal]; cases r with | nil => rfl | cons b r => exact (headVal (b::r)).symm

def runN : Nat → NConf → Option NConf
  | 0,z => some z
  | n+1,z => (stepN z).bind (runN n)

theorem project_run (n : Nat) (z : Z0) : runN n (nv z) = (run0 base n z).map nv := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    rw [runN,step_project,run0]
    cases h : step0 base z with
    | none => rfl
    | some z' => simpa only [Option.map_some,Option.bind_some] using ih z'

theorem runN_add (n m : Nat) (z : NConf) : runN (n+m) z = (runN n z).bind (runN m) := by
  induction n generalizing z with
  | zero => simp [runN]
  | succ n ih =>
    rw [show n+1+m=n+m+1 by omega,runN,runN]
    cases h : stepN z with
    | none => rfl
    | some z' => simpa only [Option.bind_some] using ih z'

def Reach (x y : NConf) : Prop := ∃ k, 0<k ∧ runN k x = some y

theorem reach_trans {a b c : NConf} (h : Reach a b) (g : Reach b c) : Reach a c := by
  obtain ⟨k,hk,hr⟩ := h
  obtain ⟨j,hj,hs⟩ := g
  exact ⟨k+j,by omega,by rw [runN_add,hr,Option.bind_some,hs]⟩

theorem path_reach {a b : Z0} (h : Path0 a b) : Reach (nv a) (nv b) := by
  obtain ⟨k,hk,hr⟩ := h
  exact ⟨k,hk,by rw [project_run,hr];rfl⟩

def F (L W : List Bool) : NConf := nv (A L W)

theorem F_pad (L W : List Bool) (n : Nat) : F (L++zeros n) W = F L W := by
  simp [F,nv,A,val_pad]

theorem invariant_live (S : NConf → Prop) (entry : Nat) (z : NConf)
    (first : runN entry (nv blank0) = some z) (hz : S z)
    (progress : ∀ z, S z → ∃ z', Reach z z' ∧ S z') : live base := by
  have arbitrary : ∀ n, ∃ t w, n≤t ∧ runN t (nv blank0) = some w ∧ S w := by
    intro n
    induction n with
    | zero => exact ⟨entry,z,by omega,first,hz⟩
    | succ n ih =>
      obtain ⟨t,w,ht,hr,hw⟩ := ih
      obtain ⟨w',⟨k,hk,hs⟩,hw'⟩ := progress w hw
      exact ⟨t+k,w',by omega,by rw [runN_add,hr,Option.bind_some,hs],hw'⟩
  intro n
  obtain ⟨t,w,ht,hr,_⟩ := arbitrary n
  rw [show t=n+(t-n) by omega,runN_add] at hr
  have hh : (runN n (nv blank0)).isSome := by cases he : runN n (nv blank0) with
    | none => simp [he] at hr
    | some v => rfl
  rw [project_run] at hh
  cases he : run0 base n blank0 with
  | none => simp [he] at hh
  | some v => exact ⟨v,rfl⟩

#print axioms invariant_live
end BB6.Agent46Raw13TapeValue
