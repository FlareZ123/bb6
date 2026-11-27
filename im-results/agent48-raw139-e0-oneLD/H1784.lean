import H1784Macro

namespace BB6Coverage.Agent48.H1784
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper
set_option maxRecDepth 4096
set_option maxHeartbeats 0

def value : List Bool → Nat
  | [] => 0
  | false::w => 2*value w
  | true::w => 1+2*value w

theorem bit_len (b : Bool) (u : Nat) : (rep [b] u).length=u := by
  induction u with
  | zero => rfl
  | succ u ih => simp [rep,ih]

theorem value_ones (u : Nat) : value (ones u)+1=2^u := by
  induction u with
  | zero => rfl
  | succ u ih =>
    change value (rep [true] u)+1=2^u at ih
    simp only [rep,List.cons_append,List.nil_append,value,Nat.pow_succ]
    omega

theorem value_zeros (u : Nat) : value (zeros u)=0 := by
  induction u with
  | zero => rfl
  | succ u ih => simp [rep,value,ih]

theorem inc_value (u : Nat) (w : List Bool) :
    value (zeros u++true::w) = value (ones u++false::w)+1 := by
  induction u with
  | zero =>
    change 1+2*value w = 2*value w+1
    omega
  | succ u ih =>
    change value (rep [false] u++true::w)=value (rep [true] u++false::w)+1 at ih
    simp only [rep,List.cons_append,List.nil_append,value,List.append_assoc]
    omega

theorem inc_len (u : Nat) (w : List Bool) :
    (zeros u++true::w).length=(ones u++false::w).length := by
  simp only [List.length_append,bit_len,List.length_cons]

theorem split_word (w : List Bool) :
    (∃ u, w=ones u) ∨ ∃ u z, w=ones u++false::z := by
  induction w with
  | nil => exact Or.inl ⟨0,rfl⟩
  | cons b w ih =>
    cases b with
    | false => exact Or.inr ⟨0,w,rfl⟩
    | true =>
      rcases ih with ⟨u,h⟩ | ⟨u,z,h⟩
      · exact Or.inl ⟨u+1,by rw [h]; rfl⟩
      · exact Or.inr ⟨u+1,z,by rw [h]; rfl⟩

theorem pow_width (u : Nat) (h : 0<u) : 2^u=2^(u-1)*2 := by
  calc
    _ = 2^(u-1+1) := by rw [show u-1+1=u by omega]
    _ = _ := Nat.pow_succ 2 (u-1)

inductive Good : Z0 → Prop where
  | main (w : List Bool) (j : Nat)
      (hv : value w=j+1) (hl : 2≤w.length) : Good (Y w j T101)
  | auxMode (w : List Bool) (j i : Nat)
      (hv : value w=j) (hl : 3≤w.length) (hb : j+i+2=2^(w.length-1)) :
      Good (Y w j (aux i))
  | turnMode (w : List Bool) (j : Nat)
      (hv : value w=j) (hl : 3≤w.length) (hb : j+1=2^(w.length-1)) (hj : 0<j) :
      Good (Y w j T11)

theorem good_step {z : Z0} (h : Good z) :
    ∃ y, Live z y ∧ Good y := by
  cases h with
  | main w j hv hl =>
    rcases split_word w with ⟨u,rfl⟩ | ⟨u,v,rfl⟩
    · have hu := value_ones u
      have hlen : 2≤u := by simpa only [bit_len] using hl
      refine ⟨_,main_over u j,Good.auxMode (zeros (u+1)) 0 j (value_zeros _) ?_ ?_⟩
      · rw [bit_len]; omega
      · rw [bit_len,show u+1-1=u by omega]
        omega
    · have hc := inc_value u v
      have he := inc_len u v
      exact ⟨_,main_inc u j v,Good.main _ (j+1) (by omega) (by omega)⟩
  | auxMode w j i hv hl hb =>
    rcases split_word w with ⟨u,rfl⟩ | ⟨u,v,rfl⟩
    · have hu := value_ones u
      have hlen : 3≤u := by simpa only [bit_len] using hl
      rw [bit_len] at hb
      have he := pow_width u (by omega)
      omega
    · have hc := inc_value u v
      have he := inc_len u v
      cases i with
      | zero =>
        refine ⟨_,aux_end u j v,Good.turnMode _ (j+1) (by omega) (by omega) ?_ (by omega)⟩
        rw [he]
        omega
      | succ i =>
        refine ⟨_,aux_inc u j i v,Good.auxMode _ (j+1) i (by omega) (by omega) ?_⟩
        rw [he]
        omega
  | turnMode w j hv hl hb hj =>
    rcases split_word w with ⟨u,rfl⟩ | ⟨u,v,rfl⟩
    · have hu := value_ones u
      have hlen : 3≤u := by simpa only [bit_len] using hl
      rw [bit_len] at hb
      have he := pow_width u (by omega)
      omega
    · have hc := inc_value u v
      have he := inc_len u v
      cases j with
      | zero => omega
      | succ j =>
        exact ⟨_,turn_inc u j v,Good.main _ (j+1) (by omega) (by omega)⟩

def entry : Z0 := Y [true,true] 2 T101

theorem first : RRun 364 ⟨0,[],[]⟩ entry := by
  refine ⟨⟨0,entry.l++[false],entry.r⟩,rfl,?_⟩
  exact ⟨rfl,same_symm (same_zero entry.l),same_refl _⟩

theorem entry_good : Good entry := Good.main [true,true] 2 (by decide) (by decide)

theorem unbounded (n : Nat) :
    ∃ t z, n≤t ∧ RRun t ⟨0,[],[]⟩ z ∧ Good z := by
  induction n with
  | zero => exact ⟨364,entry,by omega,first,entry_good⟩
  | succ n ih =>
    obtain ⟨t,z,ht,hr,hg⟩ := ih
    obtain ⟨y,⟨k,hk,hs⟩,hy⟩ := good_step hg
    exact ⟨t+k,y,by omega,rjoin hr hs,hy⟩

theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m := by
  intro n
  obtain ⟨t,z,ht,⟨u,hu,he⟩,hg⟩ := unbounded n
  have hz : (zrun ctr t start).map project = some u :=
    (run_project ctr t start).trans hu
  cases h : zrun ctr t start with
  | none => simp [h] at hz
  | some a =>
    have H := zrun_sound ctr m hm t start a h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

theorem cover (B : Nat) : Cover (BB6.Agent13BlankDelay.WeightedBound B) ctr := by
  refine .leaf ctr ?_
  intro m hm k d hk hd
  have h := never m hm (k+1)
  rw [hk.2] at h
  simp at h

#print axioms first
#print axioms good_step
#print axioms never
#print axioms cover

end BB6Coverage.Agent48.H1784
