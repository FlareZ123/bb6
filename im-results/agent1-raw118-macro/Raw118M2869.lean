import Raw118M2869Cert
import Raw118M2869Macro
namespace BB6Coverage.Agent1Raw118M2869
open BB6Coverage Agent31Pump Agent50Zipper
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sumL : List Frame → LI
  | [] => 1
  | f::l => pushL (sumL l) f
def sumR : List Tok → RI
  | [] => 1
  | t::r => pushR (sumR r) t

def Good (back p : Bool) (l : List Frame) (r : List Tok) : Prop :=
  phaseL (sumL l) = p ∧ Safe back (sumL l) (sumR r)
instance (b p : Bool) (l : List Frame) (r : List Tok) : Decidable (Good b p l r) := by unfold Good; infer_instance

theorem rbase (r : List Tok) (h : sumR r = 1) : r = [] := by
  cases r with
  | nil => rfl
  | cons t r =>
    change pushR (sumR r) t = 1 at h
    have hn : pushR (sumR r) t ≠ 0 := by rw [h]; decide
    exact False.elim ((rmeta (sumR r) t hn).1 h)

theorem atop (l : List Frame) (hn : sumL l ≠ 0) (ht : topL (sumL l) = 1) : ∃ t, l = .a::t := by
  cases l with
  | nil => exact False.elim ((by decide : topL (sumL []) ≠ 1) ht)
  | cons f l =>
    have hm := lmeta (sumL l) f hn
    have he := hm.2.2.1
    change topL (pushL (sumL l) f) = 1 at ht
    rw [ht] at he
    cases f <;> first | exact ⟨l,rfl⟩ | contradiction

theorem pushed (b : Bool) (l : List Frame) (f : Frame) (r : List Tok)
    (h : Safe b (pushL (sumL l) f) (sumR r)) : Good b (after f) (f::l) r :=
  ⟨(lmeta (sumL l) f h.1).2.1,h⟩

theorem grow (b p : Bool) (l : List Frame) (r : List Tok) (h : Good b p l r) :
    ∃ b' p' l' r' n, 0 < n ∧ Good b' p' l' r' ∧
      run0 table n (cfg b p l r) = some (cfg b' p' l' r') := by
  obtain ⟨hp,hs⟩ := h
  cases b with
  | false =>
    cases r with
    | nil =>
      cases p with
      | false => exact ⟨true,false,l,[.x],13,by decide,⟨hp,(facts (sumL l) 1).feP hp hs⟩,feP_run l⟩
      | true => exact ⟨true,true,l,[.v],16,by decide,⟨hp,(facts (sumL l) 1).feQ hp hs⟩,feQ_run l⟩
    | cons t r =>
      have F := facts (sumL l) (sumR r)
      cases t with
      | x =>
        cases p with
        | false => exact ⟨false,true,.a::l,r,2,by decide,pushed false l .a r (F.fxP hp hs),fxP_run l r⟩
        | true => exact ⟨false,false,.b::l,r,4,by decide,pushed false l .b r (F.fxQ hp hs),fxQ_run l r⟩
      | y =>
        cases p with
        | false => exact ⟨false,false,.c::l,r,4,by decide,pushed false l .c r (F.fyP hp hs),fyP_run l r⟩
        | true => exact ⟨false,true,.d::l,r,6,by decide,pushed false l .d r (F.fyQ hp hs),fyQ_run l r⟩
      | z =>
        cases p with
        | false => exact ⟨true,false,l,.x::.y::r,29,by decide,⟨hp,F.fzP hp hs⟩,fzP_run l r⟩
        | true => exact ⟨false,true,.e::l,r,8,by decide,pushed false l .e r (F.fzQ hp hs),fzQ_run l r⟩
      | v =>
        have hr := rbase r ((rmeta (sumR r) .v hs.2.1).2 (Or.inr rfl))
        subst r
        cases p with
        | false => exact ⟨true,false,l,[.x,.u],29,by decide,⟨hp,(facts (sumL l) 1).fvP hp hs⟩,fvP_run l⟩
        | true => exact ⟨true,true,l,[.z],32,by decide,⟨hp,(facts (sumL l) 1).fvQ hp hs⟩,fvQ_run l⟩
      | u =>
        have hr := rbase r ((rmeta (sumR r) .u hs.2.1).2 (Or.inl rfl))
        subst r
        obtain ⟨l',rfl⟩ := atop l hs.1 ((facts (sumL l) 1).fuShape hs)
        have he := (lmeta (sumL l') .a hs.1).2.1
        have hq : p = true := hp.symm.trans he
        rw [hq]
        exact ⟨false,true,.s::l',[],19,by decide,pushed false l' .s [] ((facts (sumL l') 1).fu hs),fu_run l'⟩
  | true =>
    cases l with
    | nil =>
      have he : p = false := hp.symm
      rw [he]
      exact ⟨false,false,[],.x::r,23,by decide,⟨rfl,(facts 1 (sumR r)).base hs⟩,base_run r⟩
    | cons f l =>
      have hm := lmeta (sumL l) f hs.1
      have he : p = after f := hp.symm.trans hm.2.1
      rw [he]
      have F := facts (sumL l) (sumR r)
      cases f with
      | a => exact ⟨true,false,l,.x::r,11,by decide,⟨hm.1,F.ba hs⟩,ba_run l r⟩
      | b => exact ⟨true,true,l,.x::r,11,by decide,⟨hm.1,F.bb hs⟩,bb_run l r⟩
      | c => exact ⟨true,false,l,.y::r,20,by decide,⟨hm.1,F.bc hs⟩,bc_run l r⟩
      | e => exact ⟨true,true,l,.z::r,24,by decide,⟨hm.1,F.be hs⟩,be_run l r⟩
      | s => exact ⟨true,false,l,.z::r,24,by decide,⟨hm.1,F.bs hs⟩,bs_run l r⟩
      | d =>
        have hn : sumL l ≠ 0 := by
          intro h0
          apply hs.1
          change pushL (sumL l) .d = 0
          rw [h0]; rfl
        obtain ⟨l',rfl⟩ := atop l hn (hm.2.2.2.2 rfl)
        exact ⟨false,true,.s::l',r,13,by decide,pushed false l' .s r ((facts (sumL l') (sumR r)).bd hs),bd_run l' r⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  have arbitrary : ∀ k, ∃ t b p l r, k ≤ t ∧ Good b p l r ∧ run0 table t ⟨0,[],[]⟩ = some (cfg b p l r) := by
    intro k
    induction k with
    | zero => exact ⟨53,false,false,[],[.z],by decide,by decide,entry_run⟩
    | succ k ih =>
      obtain ⟨t,b,p,l,r,ht,hg,hr⟩ := ih
      obtain ⟨b',p',l',r',n,hn,hg',hr'⟩ := grow b p l r hg
      exact ⟨t+n,b',p',l',r',by omega,hg',join0 hr hr'⟩
  intro n
  obtain ⟨t,b,p,l,r,ht,_,hr⟩ := arbitrary n
  have hz : (zrun table t Agent31Pump.start).map project = some (cfg b p l r) :=
    (run_project table t Agent31Pump.start).trans hr
  cases h : zrun table t Agent31Pump.start with
  | none => simp [h] at hz
  | some z =>
    have H := zrun_sound table m hm t Agent31Pump.start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms never
end BB6Coverage.Agent1Raw118M2869
