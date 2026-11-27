import Raw54E1RF47Abstract
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.RF47
open BB6Coverage BB6Coverage.Agent31Pump

theorem cls_zero : cls 0 = 0 := rfl

theorem cls_add_small (n d : Nat) (hd : d<4) : cls (n+d) = addA (cls n) d := by
  unfold addA; rw [cls_add n d, (cls_small d d hd).mpr rfl]

theorem prependZA_sound {E : ER} {r : RWord} {s : MR} {P : MR → Prop}
    (hr : RRep E r s) (h : Good (prependZA E s) P) : ∃ t, RRep E (addZ r) t ∧ P t := by
  unfold prependZA at h
  have H := good_bind h
  cases r with
  | nil => exact ⟨[],Rep.nil,good_pure (pop_nil hr H)⟩
  | cons p rs =>
    rcases p with ⟨g,b⟩
    obtain ⟨rt,hrt,hp⟩ := pop_cons hr H
    change Good (pushA E (addA (cls g) 1,cls b) rt) P at hp
    rw [← cls_add_small g 1 (by decide)] at hp
    obtain ⟨ha,hb⟩ := push_sound hrt hp
    exact ⟨_,ha,hb⟩

theorem prependRunA_sound {E : ER} {r : RWord} {s : MR} {P : MR → Prop} (n : Nat) (hn : n<4)
    (hr : RRep E r s) (h : Good (prependRunA E n s) P) : ∃ t, RRep E (addRun n r) t ∧ P t := by
  unfold prependRunA at h
  obtain ⟨rt,hrt,hp⟩ := prependZA_sound hr (good_bind h)
  have he : (0,n) = classR (0,n) := by unfold classR; rw [(cls_small n n hn).mpr rfl]; rfl
  rw [he] at hp
  obtain ⟨ha,hb⟩ := push_sound hrt hp
  exact ⟨_,ha,hb⟩

theorem decLA_sound {E : EL} {l : LWord} {s : ML} {P : ML → Prop}
    (hl : LRep E l s) (h : Good (decLA E s) P) :
    l.headD 1 ≠ 0 ∧ ∃ t, LRep E (decL l) t ∧ P t := by
  unfold decLA at h
  have H := good_bind h
  cases l with
  | nil => exact ⟨by decide,[],Rep.nil,good_pure (pop_nil hl H)⟩
  | cons g ls =>
    obtain ⟨lt,hlt,hp⟩ := pop_cons hl H
    change Good (if cls g < 2 then badM else bindM (subA (cls g) 1) (fun d => pushA E d lt)) P at hp
    split at hp
    · exact False.elim (good_bad hp)
    · rename_i hh
      have hg : 2≤g := (cls_ge g 2 (by decide)).mp (by omega)
      have hpush := sub_sound (n:=g) (d:=1) (by omega) (by decide) (good_bind hp)
      obtain ⟨ha,hb⟩ := push_sound hlt hpush
      exact ⟨by simp; omega,_,ha,hb⟩

theorem stripRunA_sound {E : ER} {r : RWord} {s : MR} {P : Nat × MR → Prop}
    (hr : RRep E r s) (h : Good (stripRunA E s) P) :
    ∃ t, RRep E (stripRun r).2 t ∧ P (cls (stripRun r).1,t) := by
  unfold stripRunA at h
  have H := good_bind h
  cases r with
  | nil => exact ⟨s,hr,good_pure (pop_nil hr H)⟩
  | cons p rs =>
    rcases p with ⟨g,b⟩
    obtain ⟨rt,hrt,hp⟩ := pop_cons hr H
    change Good (if cls g=0 then pureM (cls b,rt) else pureM (0,s)) P at hp
    by_cases hg : g=0
    · subst g; exact ⟨rt,hrt,good_pure hp⟩
    · have hgc : cls g≠0 := fun he => hg ((cls_small g 0 (by decide)).mp he)
      rw [if_neg hgc] at hp
      cases g with
      | zero => contradiction
      | succ g => exact ⟨s,hr,good_pure hp⟩

-- A sound abstract closure gives a strictly positive concrete macro and another
-- represented configuration satisfying the arbitrary continuation predicate.
def Progress (ELs : EL) (ERs : ER) (l : LWord) (r : RWord) (P : ML × MR → Prop) : Prop :=
  ∃ l' r' ls rs, goes (cfg l r) (cfg l' r') ∧ LRep ELs l' ls ∧ RRep ERs r' rs ∧ P (ls,rs)

theorem a0A_sound {ELs : EL} {ERs : ER} {l : LWord} {r : RWord} {ls : ML} {rs : MR} {P : ML × MR → Prop}
    (hl : LRep ELs l ls) (hr : RRep ERs r rs) (h : Good (a0A ELs ERs ls rs) P) : Progress ELs ERs l r P := by
  unfold a0A at h
  obtain ⟨hl0,ld,hld,h1⟩ := decLA_sound hl (good_bind h)
  obtain ⟨rt,hrt,h2⟩ := stripRunA_sound hr (good_bind h1)
  cases he : stripRun r with
  | mk b tail =>
    rw [he] at hrt h2
    dsimp only at hrt h2
    have h3 := good_bind h2
    cases tail with
    | nil =>
      have h4 := pop_nil hrt h3
      obtain ⟨hll,h5⟩ := push_sound (a:=0) hld (good_bind h4)
      have h6 := good_bind h5
      change Good (pushA ERs (0,addA (cls b) 2) []) (fun rr => Good (pureM (stkPush 0 ld,rr)) P) at h6
      rw [← cls_add_small b 2 (by decide)] at h6
      obtain ⟨hrr,h7⟩ := push_sound (Rep.nil (E:=ERs)) h6
      exact ⟨0::decL l,[(0,b+2)],_,_,a0_blank l r b hl0 he,hll,hrr,good_pure h7⟩
    | cons p rest =>
      rcases p with ⟨g,c⟩
      obtain ⟨ra,hra,h4⟩ := pop_cons hrt h3
      -- The two comparison tests are exact in the quotient.
      by_cases hg0 : g=0
      · subst g; exact False.elim (good_bad h4)
      by_cases hc0 : c=0
      · subst c; exact False.elim (good_bad (by simpa [classR,cls] using h4))
      have hg0' : cls g≠0 := fun e => hg0 ((cls_small g 0 (by decide)).mp e)
      have hc0' : cls c≠0 := fun e => hc0 ((cls_small c 0 (by decide)).mp e)
      simp only [classR, hg0', hc0', or_self, if_false] at h4
      by_cases hg1 : g=1
      · subst g
        have h5 := sub_sound (n:=c) (d:=1) (by omega) (by decide) (good_bind h4)
        have h6 : ∃ rr, RRep ERs (afterOne c rest) rr ∧ Good (bindM (pushA ELs 1 ld) (fun ll => bindM (pushA ELs (cls b) ll) (fun ll2 => pureM (ll2,rr)))) P := by
          by_cases hc1 : c=1
          · subst c
            have H := good_bind h5
            change Good (pureM ra) _ at H
            exact ⟨ra,hra,good_pure (a:=ra) H⟩
          · have hcc : cls (c-1)≠0 := fun e => by have hz := (cls_small (c-1) 0 (by decide)).mp e; omega
            simp only [hcc,if_false] at h5
            obtain ⟨ha,hb⟩ := push_sound hra (good_bind h5)
            exact ⟨_,by simpa only [afterOne,hc1,if_false,RRep,List.map_cons,classR,cls_zero] using ha,hb⟩
        obtain ⟨rr,hrr,h7⟩ := h6
        obtain ⟨ha,h8⟩ := push_sound (a:=1) hld (good_bind h7)
        obtain ⟨hb,h9⟩ := push_sound (a:=cls b) ha (good_bind h8)
        exact ⟨b::1::decL l,afterOne c rest,_,rr,a0_push l r rest b c hl0 he (by omega),hb,hrr,good_pure h9⟩
      · have hg1' : cls g≠1 := fun e => hg1 ((cls_small g 1 (by decide)).mp e)
        simp only [hg1',if_false] at h4
        have h5 := sub_sound (n:=g) (d:=2) (by omega) (by decide) (good_bind h4)
        have h6 : ∃ rr, RRep ERs (afterZero b g c rest) rr ∧ Good (bindM (pushA ELs 0 ld) (fun ll => pureM (ll,rr))) P := by
          by_cases hg2 : g=2
          · subst g
            have H := good_bind h5
            change Good (pushA ERs (0,addA (addA (cls b) 2) (cls c)) ra) _ at H
            rw [← cls_add_small b 2 (by decide)] at H
            unfold addA at H
            rw [← cls_add (b+2) c] at H
            obtain ⟨ha,hb⟩ := push_sound hra H
            exact ⟨_,ha,hb⟩
          · have hgg : cls (g-2)≠0 := fun e => by have hz := (cls_small (g-2) 0 (by decide)).mp e; omega
            simp only [hgg,if_false] at h5
            have H := good_bind (good_bind h5)
            obtain ⟨ha,hb⟩ := push_sound hra H
            rw [← cls_add_small b 2 (by decide)] at hb
            obtain ⟨hc,hd⟩ := push_sound ha hb
            exact ⟨_,by simpa only [afterZero,hg2,if_false,RRep,List.map_cons,classR,cls_zero] using hc,hd⟩
        obtain ⟨rr,hrr,h7⟩ := h6
        obtain ⟨hll,h8⟩ := push_sound (a:=0) hld (good_bind h7)
        exact ⟨0::decL l,afterZero b g c rest,_,rr,a0_merge l r rest b g c hl0 he (by omega),hll,hrr,good_pure h8⟩

theorem a1A_sound {ELs : EL} {ERs : ER} {l : LWord} {r : RWord} {ls : ML} {rs : MR} {P : ML × MR → Prop}
    (hl : LRep ELs (0::l) ls) (hr : RRep ERs r rs) (h : Good (a1A ELs ERs ls rs) P) : Progress ELs ERs (0::l) r P := by
  unfold a1A at h
  obtain ⟨lt,hlt,h1⟩ := pop_cons hl (good_bind h)
  simp only [cls_zero,ne_eq,not_true_eq_false,if_false] at h1
  have h2 := good_bind h1
  cases l with
  | nil =>
    have h3 := pop_nil hlt h2
    obtain ⟨rr,hrr,h4⟩ := prependRunA_sound 3 (by decide) hr (good_bind h3)
    exact ⟨[],addRun 3 r,[],rr,a1_end r,Rep.nil,hrr,good_pure h4⟩
  | cons g rest =>
    obtain ⟨la,hla,h3⟩ := pop_cons hlt h2
    by_cases hg0 : g=0
    · subst g; exact False.elim (good_bad h3)
    have hg0' : cls g≠0 := fun e => hg0 ((cls_small g 0 (by decide)).mp e)
    simp only [hg0',if_false] at h3
    by_cases hg1 : g=1
    · subst g
      have h4 := good_bind h3
      have h5 : ∃ ll, LRep ELs (leftMerge rest) ll ∧ Good (bindM (prependZA ERs rs) (fun rr => pureM (ll,rr))) P := by
        cases rest with
        | nil =>
          have H := pop_nil hla h4
          have H1 := good_pure (a:=[]) (good_bind H)
          obtain ⟨ha,hb⟩ := push_sound (a:=0) (Rep.nil (E:=ELs)) (good_bind H1)
          exact ⟨_,ha,hb⟩
        | cons n ns =>
          obtain ⟨tail,htail,H⟩ := pop_cons hla h4
          have H1 := good_bind H
          change Good (pushA ELs (addA (cls n) 1) tail) _ at H1
          rw [← cls_add_small n 1 (by decide)] at H1
          obtain ⟨ha,hb⟩ := push_sound htail H1
          obtain ⟨hc,hd⟩ := push_sound (a:=0) ha (good_bind hb)
          exact ⟨_,hc,hd⟩
      obtain ⟨ll,hll,h6⟩ := h5
      obtain ⟨rr,hrr,h7⟩ := prependZA_sound hr (good_bind h6)
      exact ⟨leftMerge rest,addZ r,ll,rr,a1_gap1 rest r,hll,hrr,good_pure h7⟩
    · have hg1' : cls g≠1 := fun e => hg1 ((cls_small g 1 (by decide)).mp e)
      simp only [hg1',if_false] at h3
      by_cases hg2 : g=2
      · subst g
        have hhead := left_head hla
        have hrest : rest.headD 1 ≠0 := by
          intro H
          have H' : la.headD 1 = 0 := by rw [hhead,H]; rfl
          simp only [H',if_true] at h3
          exact good_bad h3
        have hlhead : la.headD 1 ≠0 := by
          intro H; rw [hhead] at H; exact hrest ((cls_small _ 0 (by decide)).mp H)
        simp only [hlhead,if_false] at h3
        obtain ⟨hll,h4⟩ := push_sound (a:=0) hla (good_bind h3)
        obtain ⟨rr,hrr,h5⟩ := prependRunA_sound 2 (by decide) hr (good_bind h4)
        exact ⟨0::rest,addRun 2 r,_,rr,a1_gap2 rest r hrest,hll,hrr,good_pure h5⟩
      · have hg2' : cls g≠2 := fun e => hg2 ((cls_small g 2 (by decide)).mp e)
        simp only [hg2',if_false] at h3
        have hg3 : 3≤g := by omega
        have h4 := sub_sound (n:=g) (d:=3) hg3 (by decide) (good_bind h3)
        obtain ⟨hll,h5⟩ := push_sound hla (good_bind h4)
        obtain ⟨rr,hrr,h6⟩ := prependRunA_sound 3 (by decide) hr (good_bind h5)
        exact ⟨(g-3)::rest,addRun 3 r,_,rr,a1_gap3 g rest r hg3,hll,hrr,good_pure h6⟩

theorem advanceA_sound {ELs : EL} {ERs : ER} {l : LWord} {r : RWord} {ls : ML} {rs : MR} {P : ML × MR → Prop}
    (hl : LRep ELs l ls) (hr : RRep ERs r rs) (h : Good (advanceA ELs ERs ls rs) P) : Progress ELs ERs l r P := by
  unfold advanceA at h
  split at h
  · rename_i hh
    have H : l.headD 1=0 := (cls_small _ 0 (by decide)).mp ((left_head hl).symm.trans hh)
    cases l with
    | nil => contradiction
    | cons g rest =>
      change g=0 at H; subst g
      exact a1A_sound hl hr h
  · exact a0A_sound hl hr h

#print axioms advanceA_sound
end BB6.Agent8Raw54.RF47
