import Raw40A0LA1LC66Drain
import Raw40A0LA1LC66Macros
import Raw40A0LA1LC66Entry
import CrossingSource
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19Raw40.A0LA1LCLeaf66
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper
open BB6Coverage.Agent42Crossing
open Leaf66Drain Leaf66Macros

abbrev table := Leaf66Macros.table

def leftWord : List Nat → List Bool
  | [] => []
  | x::u => false::(O x ++ leftWord u)

def rightWord : List Token → List Bool
  | [] => []
  | (g,c)::v => W g ++ O c ++ rightWord v

def liftZ (h : Int) (z : Z0) : Z := ⟨z.q,h,z.l,z.r⟩

def fam (c : C) (h : Int) : Config :=
  embed (liftZ h (A (O c.k ++ leftWord c.u) (O c.b ++ rightWord c.v)))

theorem frame_run (m : Machine) (hm : compatible table m) (n : Nat)
    (h : Int) (a b : Z0) (hr : run0 table n a = some b) :
    ∃ j, run m n (embed (liftZ h a)) = some (embed (liftZ j b)) := by
  have hp : (zrun table n (liftZ h a)).map project = some b :=
    (run_project table n (liftZ h a)).trans hr
  cases hz : zrun table n (liftZ h a) with
  | none => simp [hz] at hp
  | some z =>
    have hproj : project z = b := by simpa [hz] using hp
    have he : liftZ z.h b = z := by rw [← hproj]; cases z; rfl
    exact ⟨z.h, by rw [he]; exact zrun_sound table m hm n _ _ hz⟩

def unpop (u : List Nat) : List Bool := O (u.headD 0) ++ leftWord u.tail

theorem leftPad (k : Nat) (u : List Nat) (i : Nat) :
    (false::(O k++false::unpop u)).getD i false =
    (false::(O k++leftWord u)).getD i false := by
  cases u with
  | nil =>
    change (([false]++O k)++[false]).getD i false =
      (([false]++O k)++[]).getD i false
    exact append_getD _ _ _ (padEq_sound [false] [] (by decide)) i
  | cons x u => rfl

theorem splitFrame (m : Machine) (hm : compatible table m)
    (n k : Nat) (u : List Nat) (R : List Bool) (h : Int) :
    ∃ j, run m (2*n+k+31)
        (embed (liftZ h (A (O k++leftWord u) (O (n+4)++[false,false,false,false,false]++R)))) =
      some (embed (liftZ j (A (unpop u) (O (k+6)++W (n+1)++[true,true,true]++R)))) := by
  obtain ⟨j,H⟩ := frame_run m hm _ h _ _ (splitGap n k (unpop u) R)
  have he : embed (liftZ h (A (O k++false::unpop u) (O (n+4)++[false,false,false,false,false]++R))) =
      embed (liftZ h (A (O k++leftWord u) (O (n+4)++[false,false,false,false,false]++R))) :=
    embed_congr _ _ rfl rfl (leftPad k u) (fun _ => rfl)
  rw [he] at H
  exact ⟨j,H⟩

theorem step_sound (m : Machine) (hm : compatible table m)
    {a b : C} (hs : Step a b) (h : Int) :
    ∃ n j, 0<n ∧ run m n (fam a h) = some (fam b j) := by
  cases hs with
  | join k b c u v hb hc =>
    obtain ⟨n,rfl⟩ : ∃ n : Nat, b=n+4 := ⟨b-4,by omega⟩
    obtain ⟨t,rfl⟩ : ∃ t : Nat, c=t+1 := ⟨c-1,by omega⟩
    obtain ⟨j,H⟩ := frame_run m hm _ h _ _ (joinGap n k t (leftWord u) (rightWord v))
    have e : n+t+6 = n+4+(t+1)+1 := by omega
    rw [e] at H
    refine ⟨2*n+16,j,by omega,?_⟩
    simpa only [fam,zero,leftWord,rightWord,List.append_assoc] using H
  | split k b g c u v hb hg =>
    obtain ⟨n,rfl⟩ : ∃ n : Nat, b=n+4 := ⟨b-4,by omega⟩
    obtain ⟨d,rfl⟩ : ∃ d : Nat, g=5+d := ⟨g-5,by omega⟩
    obtain ⟨j,H⟩ := splitFrame m hm n k u (W d++O c++rightWord v) h
    have e1 : n+4-3=n+1 := by omega
    have e2 : 5+d-5=d := by omega
    refine ⟨2*n+k+31,j,by omega,?_⟩
    simpa only [fam,pop,unpop,rightWord,e1,e2,W_add 5 d,List.append_assoc] using H
  | five k b c u v hb =>
    obtain ⟨n,rfl⟩ : ∃ n : Nat, b=n+4 := ⟨b-4,by omega⟩
    obtain ⟨j,H⟩ := splitFrame m hm n k u (O c++rightWord v) h
    have e1 : n+4-3=n+1 := by omega
    have e2 : O (c+3) = [true,true,true]++O c := by
      rw [Nat.add_comm c 3,O_add]; rfl
    refine ⟨2*n+k+31,j,by omega,?_⟩
    simpa only [fam,pop,unpop,rightWord,e1,e2,List.append_assoc] using H
  | blank k b u hb =>
    obtain ⟨n,rfl⟩ : ∃ n : Nat, b=n+4 := ⟨b-4,by omega⟩
    obtain ⟨j,H⟩ := splitFrame m hm n k u [] h
    have he : embed (liftZ h (A (O k++leftWord u) (O (n+4)++[false,false,false,false,false]++[]))) =
        fam ⟨k,n+4,u,[]⟩ h := by
      apply embed_congr _ _ rfl rfl (fun _ => rfl)
      exact append_getD _ _ _ (padEq_sound [false,false,false,false,false] [] (by decide))
    rw [he] at H
    have e : n+4-3=n+1 := by omega
    refine ⟨2*n+k+31,j,by omega,?_⟩
    simpa only [fam,pop,unpop,rightWord,e,List.append_assoc,List.append_nil] using H

theorem reach_sound (m : Machine) (hm : compatible table m)
    {a b : C} (hr : Reach a b) (h : Int) :
    ∃ n j, 0<n ∧ run m n (fam a h) = some (fam b j) := by
  induction hr generalizing h with
  | one hs => exact step_sound m hm hs h
  | trans ha hb iha ihb =>
    obtain ⟨n,j,hn,Hn⟩ := iha h
    obtain ⟨k,j',hk,Hk⟩ := ihb j
    exact ⟨n+k,j',by omega,by rw [run_append,Hn]; exact Hk⟩

theorem never_from_entry (m : Machine) (hm : compatible table m) (entry : Nat)
    (h : Int) (he : run m entry blank = some (fam (X 11) h)) : NeverHalts m := by
  have arbitrary : ∀ n, ∃ t j, n≤t ∧ run m t blank = some (fam (X (n+11)) j) := by
    intro n
    induction n with
    | zero => exact ⟨entry,h,by omega,he⟩
    | succ n ih =>
      obtain ⟨t,j,ht,Ht⟩ := ih
      have hg : Reach (X (n+11)) (X (n+1+11)) := by
        simpa only [show n+10+1=n+11 by omega,show n+10+2=n+1+11 by omega] using growth (n+10)
      obtain ⟨k,j',hk,Hk⟩ := reach_sound m hm hg j
      exact ⟨t+k,j',by omega,by rw [run_append,Ht]; exact Hk⟩
  intro n
  obtain ⟨t,j,ht,Ht⟩ := arbitrary n
  rw [show t=n+(t-n) by omega,run_append] at Ht
  cases H : run m n blank with
  | none => simp [H] at Ht
  | some z => rfl

#print axioms reach_sound
#print axioms never_from_entry

theorem entry (m : Machine) (hm : compatible table m) :
    run m 93860 blank = some (fam (X 11) 10) := by
  have H := zrun_sound table m hm 93860 ⟨0,0,[],[]⟩ Leaf66Entry.entryZ Leaf66Entry.entryRun
  have he : embed Leaf66Entry.entryZ = fam (X 11) 10 := by
    apply embed_congr _ _ (by decide) (by decide)
    · exact padEq_sound _ _ (by decide +kernel)
    · exact padEq_sound _ _ (by decide +kernel)
  rwa [start_embed,he] at H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_from_entry m hm 93860 10 (entry m hm)

#print axioms never

end BB6.Agent19Raw40.A0LA1LCLeaf66
