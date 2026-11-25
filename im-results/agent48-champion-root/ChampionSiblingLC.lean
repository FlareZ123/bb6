import ChampionSiblingCounter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent48SiblingLC
open BB6Coverage BB6Coverage.Agent48Champion BB6Coverage.Agent31Pump BB6.Agent48SiblingCounter

def lc : PartialMachine := fun s =>
  if s = (0,true) then some (some ⟨true,false,2⟩)
  else (championTable s).map some

abbrev P : List Bool := [false,true,true,true]
abbrev Q : List Bool := [true,false,false,false]
abbrev sep : List Bool := [false,true,false,false]
abbrev shortMark : List Bool := [true,false,true,true,true]
abbrev longMark : List Bool := [true,false,true,true,true,true,true,true,true,true,true,false,true,true,true]
abbrev eight : List Bool := [true,true,true,true,true,true,true,true]

def queue (n b : Nat) : List Bool := rep P n ++ pad b

theorem queue_sweep (n : Nat) (L R : List Bool) :
    run0 lc (6*n) ⟨0,aHead++L,xRight++rep P n++R⟩ =
    some ⟨0,aHead++rep Q n++L,xRight++R⟩ :=
  sweepR lc 0 aHead xRight P Q 6 (by intro L R; rfl) n L R

theorem queue_end (b : Nat) (L : List Bool) :
    run0 lc 17 ⟨0,aHead++L,xRight++pad b⟩ =
      some ⟨3,Q++L,xMark++pad (b-4)⟩ := by
  cases b with
  | zero => rfl
  | succ b => cases b with
    | zero => rfl
    | succ b => cases b with
      | zero => rfl
      | succ b => cases b <;> rfl

theorem queue_restore (n : Nat) (L R : List Bool) :
    run0 lc (14*n) ⟨3,rep Q n++L,xMark++R⟩ =
      some ⟨3,L,xMark++rep P n++R⟩ := by
  simpa only [List.nil_append] using
    sweepL lc 3 [] xMark Q P 14 (by intro L R; rfl) n L R

theorem queue_entry (n b : Nat) (L : List Bool) :
    run0 lc (6*n+17+14*(n+1)) ⟨0,aHead++L,xRight++queue n b⟩ =
      some ⟨3,L,xMark++queue (n+1) (b-4)⟩ := by
  have h1 := queue_sweep n L (pad b)
  have h2 := queue_end b (rep Q n++L)
  have h3 := queue_restore (n+1) L (pad (b-4))
  simp only [rep,List.append_assoc] at h3
  have h := join0 (join0 h1 h2) h3
  simpa only [queue,rep,List.append_assoc] using h

theorem ds (n : Nat) (L R : List Bool) :
    run0 lc (9*n) ⟨3,rep d1 n++true::L,R⟩ =
      some ⟨3,true::L,rep d1 n++R⟩ := by
  rw [rep_comm_true]
  simpa only [List.nil_append,List.cons_append] using
    sweepL lc 3 [true] [] d1 d1 9 (by intro L R; rfl) n L R

theorem cs (n : Nat) (L R : List Bool) :
    run0 lc (3*n) ⟨2,true::L,rep d1 n++R⟩ =
      some ⟨2,true::(rep d0 n++L),R⟩ := by
  simpa only [List.nil_append,List.cons_append] using
    sweepR lc 2 [true] [] d1 d0 3 (by intro L R; rfl) n L R

theorem carryCoreLC (L R : List Bool) :
    run0 lc 5 ⟨3,d0++L,true::R⟩ = some ⟨2,true::(d1++L),R⟩ := by rfl

theorem post1 (L R : List Bool) :
    run0 lc 11 ⟨2,true::L,[true,true]++xMark++R⟩ =
      some ⟨0,aHead++d1++L,xRight++R⟩ := by rfl

theorem post0 (L R : List Bool) :
    run0 lc 2 ⟨2,true::L,false::true::R⟩ =
      some ⟨0,aHead++L,R⟩ := by rfl

theorem prep0 (L R : List Bool) :
    run0 lc 6 ⟨3,d0++L,false::false::true::R⟩ =
      some ⟨3,d1++L,true::false::true::R⟩ := by rfl

theorem carry1 (k : Nat) (L R : List Bool) :
    run0 lc (9*(k+1)+5+3*k+11)
      ⟨3,rep d1 (k+1)++d0++L,xMark++R⟩ =
      some ⟨0,aHead++d1++rep d0 k++d1++L,xRight++R⟩ := by
  have h2 := ds (k+1) (false::false::L) (xMark++R)
  have h3 := carryCoreLC L (rep d1 k ++ [true,true]++xMark++R)
  have hr : rep d1 (k+1) ++ (xMark++R) = true::(rep d1 k ++ [true,true]++xMark++R) := by
    simp only [rep,d1,List.cons_append,List.nil_append,List.append_assoc]
    rw [rep_two_comm]
  rw [hr] at h2
  have h4 := cs k (d1++L) ([true,true]++xMark++R)
  have h5 := post1 (rep d0 k++d1++L) R
  simp only [List.append_assoc] at h2 h3 h4 h5
  have h := join0 (join0 (join0 h2 h3) h4) h5
  simpa only [List.append_assoc,d0,List.cons_append,List.nil_append] using h

theorem carryMark (k : Nat) (L R : List Bool) :
    run0 lc (9*(k+1)+5+3*(k+1)+2)
      ⟨3,rep d1 (k+1)++d0++L,true::false::true::R⟩ =
      some ⟨0,aHead++d0++rep d0 k++d1++L,R⟩ := by
  have h2 := ds (k+1) (false::false::L) (true::false::true::R)
  have hr : rep d1 (k+1) ++ true::false::true::R = true::(rep d1 (k+1) ++ false::true::R) := rep_comm_true _ _
  rw [hr] at h2
  have h3 := carryCoreLC L (rep d1 (k+1)++false::true::R)
  have h4 := cs (k+1) (d1++L) (false::true::R)
  have h5 := post0 (rep d0 (k+1)++d1++L) R
  simp only [List.append_assoc] at h2 h3 h4 h5
  have h := join0 (join0 (join0 h2 h3) h4) h5
  simpa only [rep,List.append_assoc,d0,List.cons_append,List.nil_append] using h

theorem carry0 (k : Nat) (L R : List Bool) :
    run0 lc (6+9*(k+1)+5+3*(k+1)+2)
      ⟨3,d0++rep d1 k++d0++L,xMark++R⟩ =
      some ⟨0,aHead++d0++rep d0 k++d1++L,xRight++R⟩ := by
  have h1 := prep0 (rep d1 k++d0++L) (xRight++R)
  have h2 := carryMark k L (xRight++R)
  have h := join0 h1 (by simpa only [rep,List.append_assoc] using h2)
  have he : 6+(9*(k+1)+5+3*(k+1)+2) = 6+9*(k+1)+5+3*(k+1)+2 := by omega
  rw [he] at h
  simpa only [List.append_assoc,xMark,xRight,List.cons_append,List.nil_append] using h

theorem overflowLeftLC (a : Nat) (R : List Bool) :
    run0 lc 25 ⟨3,d1++sent++pad a,R⟩ =
      some ⟨2,true::(d1++sent++pad (a-2)),true::R⟩ := by
  cases a with
  | zero => rfl
  | succ a => cases a <;> rfl

theorem leftOverflow (k a : Nat) (R : List Bool) :
    run0 lc (9*k+25+3*k) ⟨3,rep d1 (k+1)++sent++pad a,R⟩ =
      some ⟨2,true::(rep d0 k++d1++sent++pad (a-2)),true::R⟩ := by
  let L := sent++pad a
  have h1 := ds k (true::true::L) R
  have h2 := overflowLeftLC a (rep d1 k++R)
  rw [← rep_comm_true] at h2
  have h3 := cs k (d1++sent++pad (a-2)) (true::R)
  have h := join0 (join0 h1 h2) h3
  have hl : rep d1 (k+1)++L = rep d1 k++true::true::true::L := by
    rw [rep,← rep_snoc]; simp only [List.append_assoc]; rfl
  simp only [L] at hl h
  rw [← hl] at h
  simpa only [List.append_assoc] using h

theorem postOverflow1 (L R : List Bool) :
    run0 lc 20 ⟨2,true::(d0++d0++L),true::(xMark++P++P++R)⟩ =
      some ⟨0,aHead++d0++d1++d1++sep++d0++L,xRight++R⟩ := by rfl

theorem postOverflow0 (L R : List Bool) :
    run0 lc 14 ⟨2,true::L,true::(shortMark++P++R)⟩ =
      some ⟨0,aHead++d0++d1++L,xRight++R⟩ := by rfl

theorem outerPrep (L R : List Bool) :
    run0 lc 38 ⟨3,d0++d1++d1++sep++L,xMark++R⟩ =
      some ⟨3,d1++L,longMark++R⟩ := by rfl

theorem outerPost (L R : List Bool) :
    run0 lc 12 ⟨0,aHead++d0++L,eight++P++R⟩ =
      some ⟨0,aHead++d0++d0++d0++sep++L,xRight++R⟩ := by rfl

theorem postOuterOverflow (L R : List Bool) :
    run0 lc 20 ⟨2,true::L,true::(longMark++R)⟩ =
      some ⟨0,aHead++d0++d0++d0++d1++L,xRight++R⟩ := by rfl

def single (f : Bool) (bs : List Bool) (n a b : Nat) : Z0 :=
  ⟨0,aHead++(if f then d1 else d0)++encode bs++sent++pad a,xRight++queue n b⟩
def nested (is bs : List Bool) (n a b : Nat) : Z0 :=
  ⟨0,aHead++d0++encode is++sep++encode bs++sent++pad a,xRight++queue n b⟩

inductive Inv : Z0 → Prop where
  | single (f : Bool) (bs : List Bool) (n a b : Nat)
      (hlen : 2 ≤ bs.length) (hpos : f = true → 0 < n) : Inv (single f bs n a b)
  | nested (is bs : List Bool) (n a b : Nat)
      (hi : is.length = 2) (hb : 2 ≤ bs.length) : Inv (nested is bs n a b)

abbrev qCost (n : Nat) := 6*n+17+14*(n+1)

theorem singleCarry (f : Bool) (k n a b : Nat) (ys : List Bool) :
    ∃ t, 0<t ∧ run0 lc t (single f (List.replicate k true++false::ys) n a b) =
      some (single f (List.replicate k false++true::ys) (n+1) a (b-4)) := by
  let L := encode ys++sent++pad a
  let R := queue (n+1) (b-4)
  cases f with
  | true =>
    have h1 := queue_entry n b (rep d1 (k+1)++d0++L)
    have h2 := carry1 k L R
    have h := join0 h1 h2
    refine ⟨qCost n+(9*(k+1)+5+3*k+11),by omega,?_⟩
    simpa [single,L,R,encode_append,encode_repeat,encode,rep,List.append_assoc] using h
  | false =>
    have h1 := queue_entry n b (d0++rep d1 k++d0++L)
    have h2 := carry0 k L R
    have h := join0 h1 h2
    refine ⟨qCost n+(6+9*(k+1)+5+3*(k+1)+2),by omega,?_⟩
    simpa [single,L,R,encode_append,encode_repeat,encode,List.append_assoc] using h

theorem singleOverflow1 (k n a b : Nat) :
    ∃ t, 0<t ∧ run0 lc t (single true (List.replicate (k+2) true) (n+1) a b) =
      some (nested [true,true] (List.replicate (k+1) false++[true]) n (a-2) (b-4)) := by
  let R := queue (n+2) (b-4)
  have h1 := queue_entry (n+1) b (rep d1 (k+3)++sent++pad a)
  have h2 := leftOverflow (k+2) a (xMark++R)
  have h3 := postOverflow1 (rep d0 k++d1++sent++pad (a-2)) (queue n (b-4))
  have h12 := join0 h1 (by simpa only [List.append_assoc] using h2)
  have h := join0 h12 (by simpa only [R,queue,rep,List.append_assoc] using h3)
  refine ⟨qCost (n+1)+(9*(k+2)+25+3*(k+2))+20,by omega,?_⟩
  simpa [single,nested,queue,encode_append,encode_repeat,encode,rep,List.append_assoc] using h

theorem singleOverflow0 (k n a b : Nat) :
    ∃ t, 0<t ∧ run0 lc t (single false (List.replicate k true) n a b) =
      some (single false (true::(List.replicate k false++[true])) n (a-2) (b-4)) := by
  let R := queue (n+1) (b-4)
  let L := rep d1 k++sent++pad a
  have h1 := queue_entry n b (d0++L)
  have h2 := prep0 L (xRight++R)
  have h3 := leftOverflow k a (shortMark++R)
  have h4 := postOverflow0 (rep d0 k++d1++sent++pad (a-2)) (queue n (b-4))
  have h12 := join0 h1 (by simpa only [xMark,xRight,List.cons_append,List.nil_append,List.append_assoc] using h2)
  have h123 := join0 h12 (by simpa only [L,rep,shortMark,xRight,List.cons_append,List.nil_append,List.append_assoc] using h3)
  have h := join0 h123 (by simpa only [R,queue,rep,shortMark,d1,sent,List.cons_append,List.nil_append,List.append_assoc] using h4)
  refine ⟨qCost n+6+(9*k+25+3*k)+14,by omega,?_⟩
  simpa [single,L,queue,encode_append,encode_repeat,encode,List.append_assoc] using h

theorem nestedCarry (k n a b : Nat) (ys bs : List Bool) :
    ∃ t, 0<t ∧ run0 lc t (nested (List.replicate k true++false::ys) bs n a b) =
      some (nested (List.replicate k false++true::ys) bs (n+1) a (b-4)) := by
  let L := encode ys++sep++encode bs++sent++pad a
  have h1 := queue_entry n b (d0++rep d1 k++d0++L)
  have h2 := carry0 k L (queue (n+1) (b-4))
  have h := join0 h1 h2
  refine ⟨qCost n+(6+9*(k+1)+5+3*(k+1)+2),by omega,?_⟩
  simpa [nested,L,encode_append,encode_repeat,encode,List.append_assoc] using h

theorem outerCarry (k n a b : Nat) (ys : List Bool) :
    ∃ t, 0<t ∧ run0 lc t (nested [true,true] (List.replicate k true++false::ys) n a b) =
      some (nested [false,false] (List.replicate k false++true::ys) (n+1) a (b-4)) := by
  let L := encode ys++sent++pad a
  let R := queue (n+1) (b-4)
  have h1 := queue_entry n b (d0++d1++d1++sep++rep d1 k++d0++L)
  have h2 := outerPrep (rep d1 k++d0++L) R
  have h3 := carryMark k L (eight++P++R)
  have h12 := join0 h1 (by simpa only [List.append_assoc] using h2)
  have h123 := join0 h12 (by simpa only [rep,longMark,eight,P,List.cons_append,List.nil_append,List.append_assoc] using h3)
  have h4 := outerPost (rep d0 k++d1++L) R
  have h := join0 h123 (by simpa only [aHead,d0,d1,eight,P,List.cons_append,List.nil_append,List.append_assoc] using h4)
  refine ⟨qCost n+38+(9*(k+1)+5+3*(k+1)+2)+12,by omega,?_⟩
  simpa [nested,L,R,encode_append,encode_repeat,encode,queue,List.append_assoc] using h

theorem outerOverflow (k n a b : Nat) :
    ∃ t, 0<t ∧ run0 lc t (nested [true,true] (List.replicate k true) n a b) =
      some (single false ([false,false,true]++List.replicate k false++[true]) (n+1) (a-2) (b-4)) := by
  let L := rep d1 k++sent++pad a
  let R := queue (n+1) (b-4)
  have h1 := queue_entry n b (d0++d1++d1++sep++L)
  have h2 := outerPrep L R
  have h3 := leftOverflow k a (longMark++R)
  have h4 := postOuterOverflow (rep d0 k++d1++sent++pad (a-2)) R
  have h12 := join0 h1 (by simpa only [List.append_assoc] using h2)
  have h123 := join0 h12 (by simpa only [L,rep,List.append_assoc] using h3)
  have h := join0 h123 (by simpa only [List.append_assoc] using h4)
  refine ⟨qCost n+38+(9*k+25+3*k)+20,by omega,?_⟩
  simpa [single,nested,L,R,encode_append,encode_repeat,encode,List.append_assoc] using h

theorem nextInv (z : Z0) (h : Inv z) : ∃ t z', 0<t ∧ run0 lc t z=some z' ∧ Inv z' := by
  cases h with
  | single f bs n a b hlen hp =>
    rcases bits_split bs with ⟨k,rfl⟩ | ⟨k,ys,rfl⟩
    · simp at hlen
      cases f with
      | false =>
        obtain ⟨t,ht,hr⟩ := singleOverflow0 k n a b
        exact ⟨t,_,ht,hr,.single false _ _ _ _ (by simp) (by simp)⟩
      | true =>
        have hn := hp rfl
        obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hlen
        cases n with
        | zero => omega
        | succ n =>
          obtain ⟨t,ht,hr⟩ := singleOverflow1 j n a b
          rw [show 2+j=j+2 by omega]
          exact ⟨t,_,ht,hr,.nested _ _ _ _ _ (by decide) (by simp)⟩
    · obtain ⟨t,ht,hr⟩ := singleCarry f k n a b ys
      exact ⟨t,_,ht,hr,.single f _ _ _ _ (by simpa using hlen) (by intro; omega)⟩
  | nested is bs n a b hi hb =>
    rcases bits_split is with ⟨k,rfl⟩ | ⟨k,ys,rfl⟩
    · have hk : k=2 := by simpa using hi
      subst k
      rcases bits_split bs with ⟨k,rfl⟩ | ⟨k,ys,rfl⟩
      · obtain ⟨t,ht,hr⟩ := outerOverflow k n a b
        exact ⟨t,_,ht,hr,.single false _ _ _ _ (by simp) (by simp)⟩
      · obtain ⟨t,ht,hr⟩ := outerCarry k n a b ys
        exact ⟨t,_,ht,hr,.nested _ _ _ _ _ (by decide) (by simpa using hb)⟩
    · obtain ⟨t,ht,hr⟩ := nestedCarry k n a b ys bs
      exact ⟨t,_,ht,hr,.nested _ _ _ _ _ (by simpa using hi) hb⟩

theorem initial : run0 lc 269 ⟨0,[],[]⟩ = some (single true [true,true,false,true] 1 0 0) := by rfl

theorem arbitrary_live_prefix (k : Nat) :
    ∃ t z, k ≤ t ∧ run0 lc t ⟨0,[],[]⟩ = some z ∧ Inv z := by
  induction k with
  | zero => exact ⟨269,_,by decide,initial,.single _ _ _ _ _ (by decide) (by decide)⟩
  | succ k ih =>
    obtain ⟨t,z,ht,hr,hz⟩ := ih
    obtain ⟨u,z',hu,hs,hz'⟩ := nextInv z hz
    exact ⟨t+u,z',by omega,join0 hr hs,hz'⟩

theorem lc_never (m : Machine) (hm : compatible lc m) : NeverHalts m := by
  intro n
  obtain ⟨t,z,ht,hr,_⟩ := arbitrary_live_prefix n
  have hz : (Agent50Zipper.zrun lc t start).map project = some z :=
    (run_project lc t start).trans hr
  cases h : Agent50Zipper.zrun lc t start with
  | none => simp [h] at hz
  | some z' =>
    have H := Agent50Zipper.zrun_sound lc m hm t start z' h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

theorem lc_cover : Cover NeverHalts lc := .leaf _ lc_never

#print axioms arbitrary_live_prefix
#print axioms lc_never
end BB6.Agent48SiblingLC
