import SweepPumping
namespace BB6.Agent10Raw107LF1424
open BB6Coverage BB6Coverage.Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨false,true,1⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | _,_ => none

abbrev P : List Bool := [false,false,false,false,true,true,true,true]
abbrev Q : List Bool := [false,false,true,true]
abbrev H : List Bool := [false,true,true,true]
abbrev J : List Bool := [true,true,false,false]
abbrev Base : List Bool := [false,true,false,true,true]
abbrev Bpre : List Bool := [false,true,true]
abbrev Dpre : List Bool := [false,false,false,false,false]
abbrev A (L R : List Bool) : Z0 := ⟨0,L,R⟩
abbrev B (L R : List Bool) : Z0 := ⟨1,Bpre++L,R⟩

def reps (w : List Bool) : Nat → List Bool
  | 0 => []
  | n+1 => w ++ reps w n

theorem reps_snoc (w : List Bool) (n : Nat) (R : List Bool) :
    reps w n ++ (w++R) = reps w (n+1) ++ R := by
  induction n with
  | zero => simp [reps]
  | succ n ih =>
    change (w ++ reps w n) ++ (w++R) = (w ++ reps w (n+1)) ++ R
    simp only [List.append_assoc,ih]

theorem rotate (k : Nat) (R : List Bool) :
    [true,true] ++ (reps Q k ++ R) = reps J k ++ (true::true::R) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change J ++ ([true,true] ++ (reps Q k ++ R)) = J ++ (reps J k ++ (true::true::R))
    rw [ih]

theorem unrotate (k : Nat) (R : List Bool) :
    [false,false] ++ (reps J k ++ R) = reps Q k ++ (false::false::R) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change Q ++ ([false,false] ++ (reps J k ++ R)) = Q ++ (reps Q k ++ (false::false::R))
    rw [ih]

theorem start (R : List Bool) :
    run0 table 24 (A [] (P++R)) = some (B Base (true::true::R)) := by rfl

theorem scan_pair (L R : List Bool) :
    run0 table 4 (B L (J++R)) = some (B (H++L) R) := by rfl

theorem scan_pairs (k : Nat) (L R : List Bool) :
    run0 table (4*k) (B L (reps J k++R)) = some (B (reps H k++L) R) := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    have h := join0 (scan_pair L (reps J k++R)) (ih (H++L))
    rw [reps_snoc] at h
    rw [show 4*(k+1)=4+4*k by omega]
    simpa only [reps,List.append_assoc] using h

theorem scan_ones (L R : List Bool) :
    run0 table 8 (B L (true::true::true::true::R)) = some (B (true::true::L) (true::true::R)) := by rfl

theorem many_ones (n : Nat) (L R : List Bool) :
    run0 table (8*n) (B L (List.replicate (2*n+2) true++R)) =
      some (B (List.replicate (2*n) true++L) (true::true::R)) := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have h := join0 (scan_ones L (List.replicate (2*n) true++R)) (ih (true::true::L))
    rw [show 8*(n+1)=8+8*n by omega]
    have hi : 2*(n+1)+2=2*n+4 := by omega
    have ho : 2*(n+1)=2*n+2 := by omega
    rw [hi,ho]
    simp only [List.replicate_succ,List.cons_append]
    -- The two inserted ones are indistinguishable from the prior ones.
    have he : List.replicate (2*n) true ++ true::true::L = true::true::(List.replicate (2*n) true++L) := by
      change List.replicate (2*n) true ++ ([true,true]++L) = [true,true]++(List.replicate (2*n) true++L)
      rw [← List.append_assoc,← List.append_assoc]
      change List.replicate (2*n) true ++ List.replicate 2 true ++ L = List.replicate 2 true ++ List.replicate (2*n) true ++ L
      rw [List.replicate_append_replicate,List.replicate_append_replicate,Nat.add_comm (2*n) 2]
    rw [he] at h
    exact h

theorem turn (L R : List Bool) :
    run0 table 8 (B L (false::false::R)) = some (A (true::true::true::L) (true::true::R)) := by rfl

theorem scan_last (L : List Bool) :
    run0 table 4 (B L [true,true]) = some (B (H++L) []) := by rfl

theorem turn_last (L : List Bool) :
    run0 table 8 (B L []) = some (A (true::true::true::L) [true,true]) := by rfl

theorem strip_ones (n : Nat) (L R : List Bool) :
    run0 table n (A (List.replicate n true++L) R) =
      some (A L (List.replicate n false++R)) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h1 : run0 table 1 (A (true::(List.replicate n true++L)) R) =
        some (A (List.replicate n true++L) (false::R)) := by rfl
    have h := join0 h1 (ih (false::R))
    rw [show 1+n=n+1 by omega] at h
    have he : List.replicate n false ++ false::R = false::(List.replicate n false++R) := by
      change List.replicate n false ++ ([false]++R) = [false]++(List.replicate n false++R)
      rw [← List.append_assoc,← List.append_assoc]
      change List.replicate n false ++ List.replicate 1 false ++ R = List.replicate 1 false ++ List.replicate n false ++ R
      rw [List.replicate_append_replicate,List.replicate_append_replicate,Nat.add_comm n 1]
    rw [he] at h
    exact h

theorem left_block (L R : List Bool) :
    run0 table 14 (A (H++L) (false::false::false::R)) =
      some (A L (Dpre++true::true::R)) := by rfl

theorem left_many (k : Nat) (L R : List Bool) :
    run0 table (14*k) (A (reps H k++L) (Dpre++R)) =
      some (A L (Dpre++(reps J k++R))) := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    have h1 := left_block (reps H k++L) (false::false::R)
    have h2 := ih (J++R)
    have h := join0 h1 h2
    rw [reps_snoc] at h
    rw [show 14*(k+1)=14+14*k by omega]
    exact h

theorem finish (R : List Bool) :
    run0 table 25 (A Base (Dpre++R)) = some (A [] (P++false::false::R)) := by rfl

theorem enter_scan (k : Nat) (R : List Bool) :
    run0 table (24+4*k) (A [] (P++(reps Q k++R))) =
      some (B (reps H k++Base) (true::true::R)) := by
  have h := start (reps Q k++R)
  change run0 table 24 _ = some (B Base ([true,true] ++ (reps Q k++R))) at h
  rw [rotate] at h
  exact join0 h (scan_pairs k Base (true::true::R))

theorem tail_finish (k n : Nat) (R : List Bool) :
    run0 table (14*k+25) (A (reps H k++Base) (Dpre++(List.replicate n false++R))) =
      some (A [] (P++(reps Q k++(false::false::(List.replicate n false++R))))) := by
  have h := join0 (left_many k Base (List.replicate n false++R)) (finish (reps J k++(List.replicate n false++R)))
  have he : [false,false] ++ (reps J k ++ (List.replicate n false++R)) = reps Q k ++ (false::false::(List.replicate n false++R)) := unrotate k _
  change run0 table (14*k+25) _ = some (A [] (P++([false,false]++(reps J k++(List.replicate n false++R))))) at h
  rw [he] at h
  exact h

theorem zero_epoch (k : Nat) (R : List Bool) :
    ∃ t, 0<t ∧ run0 table t (A [] (P++(reps Q k++false::false::false::false::R))) =
      some (A [] (P++(reps Q (k+1)++true::true::R))) := by
  have h1 := enter_scan k (false::false::false::false::R)
  have h2 := scan_pair (reps H k++Base) (false::false::R)
  have h3 := turn (H++(reps H k++Base)) R
  have h4 := strip_ones 3 (H++(reps H k++Base)) (true::true::R)
  have h5 := left_block (reps H k++Base) (true::true::R)
  have h6 := tail_finish k 0 (true::true::true::true::R)
  have h := join0 (join0 (join0 (join0 (join0 h1 h2) h3) h4) h5) h6
  change run0 table _ _ = some (A [] (P++(reps Q k++(Q++true::true::R)))) at h
  rw [reps_snoc] at h
  exact ⟨_,by omega,h⟩

theorem one_scan (k m : Nat) (R : List Bool) :
    run0 table (24+4*k+8*(2*m+1))
      (A [] (P++(reps Q k++true::true::(List.replicate (4*m) true++R)))) =
      some (B (List.replicate (4*m+2) true++(reps H k++Base)) (true::true::R)) := by
  have h1 := enter_scan k (true::true::(List.replicate (4*m) true++R))
  have h2 := many_ones (2*m+1) (reps H k++Base) R
  rw [show 2*(2*m+1)+2=4*m+4 by omega,show 2*(2*m+1)=4*m+2 by omega] at h2
  exact join0 h1 h2

theorem one_back (k m : Nat) (R : List Bool) :
    run0 table (3+14+(4*m+2)+14*k+25)
      (A (true::true::true::(H++(List.replicate (4*m+2) true++(reps H k++Base)))) (true::true::R)) =
      some (A [] (P++(reps Q k++(List.replicate (4*m+4) false++true::true::true::true::R)))) := by
  have h1 := strip_ones 3 (H++(List.replicate (4*m+2) true++(reps H k++Base))) (true::true::R)
  have h2 := left_block (List.replicate (4*m+2) true++(reps H k++Base)) (true::true::R)
  have h3 := strip_ones (4*m+2) (reps H k++Base) (Dpre++true::true::true::true::R)
  have hr : List.replicate (4*m+2) false ++ (Dpre++true::true::true::true::R) = Dpre++(List.replicate (4*m+2) false++true::true::true::true::R) := by
    change List.replicate (4*m+2) false ++ (List.replicate 5 false++true::true::true::true::R) = List.replicate 5 false++(List.replicate (4*m+2) false++true::true::true::true::R)
    rw [← List.append_assoc,← List.append_assoc,List.replicate_append_replicate,List.replicate_append_replicate,Nat.add_comm (4*m+2) 5]
  rw [hr] at h3
  have h4 := tail_finish k (4*m+2) (true::true::true::true::R)
  have h := join0 (join0 (join0 h1 h2) h3) h4
  rw [show 4*m+4=(4*m+2)+2 by omega,List.replicate_succ,List.replicate_succ]
  rw [show 3+14+(4*m+2)+14*k+25=3+14+(4*m+2)+(14*k+25) by omega]
  exact h

theorem one_epoch (k m : Nat) (R : List Bool) :
    ∃ t, 0<t ∧ run0 table t (A [] (P++(reps Q k++true::true::(List.replicate (4*m) true++false::false::false::false::R)))) =
      some (A [] (P++(reps Q k++(List.replicate (4*m+4) false++true::true::true::true::R)))) := by
  have h1 := one_scan k m (false::false::false::false::R)
  have h2 := scan_pair (List.replicate (4*m+2) true++(reps H k++Base)) (false::false::R)
  have h3 := turn (H++(List.replicate (4*m+2) true++(reps H k++Base))) R
  have h4 := one_back k m R
  exact ⟨_,by omega,join0 (join0 (join0 h1 h2) h3) h4⟩

theorem one_epoch_last (k m : Nat) :
    ∃ t, 0<t ∧ run0 table t (A [] (P++(reps Q k++true::true::List.replicate (4*m) true))) =
      some (A [] (P++(reps Q k++(List.replicate (4*m+4) false++[true,true,true,true])))) := by
  have h1 := one_scan k m []
  simp only [List.append_nil] at h1
  have h2 := scan_last (List.replicate (4*m+2) true++(reps H k++Base))
  have h3 := turn_last (H++(List.replicate (4*m+2) true++(reps H k++Base)))
  have h4 := one_back k m []
  exact ⟨_,by omega,join0 (join0 (join0 h1 h2) h3) h4⟩

def quad : List Bool → List Bool
  | [] => []
  | b::bs => List.replicate 4 b ++ quad bs

theorem quad_append (a b : List Bool) : quad (a++b) = quad a ++ quad b := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append,quad,ih,List.append_assoc]

theorem quad_replicate (b : Bool) (n : Nat) : quad (List.replicate n b) = List.replicate (4*n) b := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ,quad,ih,List.replicate_append_replicate]
    rw [show 4*(n+1)=4+4*n by omega]

theorem split_ones (bs : List Bool) :
    (∃ m, bs = List.replicate m true) ∨
    ∃ m ds, bs = List.replicate m true ++ false::ds := by
  induction bs with
  | nil => exact Or.inl ⟨0,rfl⟩
  | cons b bs ih =>
    cases b with
    | false => exact Or.inr ⟨0,bs,rfl⟩
    | true =>
      rcases ih with ⟨m,hm⟩ | ⟨m,ds,hm⟩
      · exact Or.inl ⟨m+1,by rw [hm]; rfl⟩
      · exact Or.inr ⟨m+1,ds,by rw [hm]; rfl⟩

inductive Section where
  | zero (k : Nat) (bs : List Bool)
  | one (k : Nat) (bs : List Bool)

def cfg : Section → Z0
  | .zero k bs => A [] (P++(reps Q k++false::false::false::false::quad bs))
  | .one k bs => A [] (P++(reps Q k++true::true::quad bs))

theorem epoch (s : Section) : ∃ t s', 0<t ∧ run0 table t (cfg s) = some (cfg s') := by
  cases s with
  | zero k bs =>
    obtain ⟨t,ht,h⟩ := zero_epoch k (quad bs)
    exact ⟨t,.one (k+1) bs,ht,h⟩
  | one k bs =>
    rcases split_ones bs with ⟨m,hm⟩ | ⟨m,ds,hm⟩
    · obtain ⟨t,ht,h⟩ := one_epoch_last k m
      refine ⟨t,.zero k (List.replicate m false++[true]),ht,?_⟩
      rw [hm]
      simp only [cfg,quad_append,quad_replicate]
      rw [show 4*m+4=4*m+1+1+1+1 by omega] at h
      simpa only [List.replicate_succ,List.cons_append,quad,List.nil_append,List.append_nil,List.replicate_zero] using h
    · obtain ⟨t,ht,h⟩ := one_epoch k m (quad ds)
      refine ⟨t,.zero k (List.replicate m false++true::ds),ht,?_⟩
      rw [hm]
      simp only [cfg,quad_append,quad_replicate,quad]
      rw [show 4*m+4=4*m+1+1+1+1 by omega] at h
      simpa only [List.replicate_succ,List.cons_append,List.replicate_zero,List.nil_append] using h

noncomputable def next (s : Section) : Section := (epoch s).choose_spec.choose
noncomputable def epochCost (s : Section) : Nat := (epoch s).choose
noncomputable def sections : Nat → Section
  | 0 => .zero 0 [true,true]
  | n+1 => next (sections n)
noncomputable def family (n : Nat) : Z0 := cfg (sections n)
noncomputable def cost (n : Nat) : Nat := epochCost (sections n)

theorem entry : run0 table 252 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem cost_pos (n : Nat) : 0 < cost n := (epoch (sections n)).choose_spec.choose_spec.1

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) :=
  (epoch (sections n)).choose_spec.choose_spec.2

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 252 cost entry cost_pos growth m hm

#print axioms zero_epoch
#print axioms one_epoch
#print axioms one_epoch_last
#print axioms epoch
#print axioms growth
#print axioms never
end BB6.Agent10Raw107LF1424
