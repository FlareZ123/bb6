import SweepPumping

namespace BB6.Agent10Raw107LA385
open BB6Coverage BB6Coverage.Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨false,true,1⟩)
  | 5,true => some (some ⟨true,false,2⟩)
  | _,_ => none

abbrev A (L R : List Bool) : Z0 := ⟨0,L,R⟩
abbrev C (L R : List Bool) : Z0 := ⟨2,L,R⟩
abbrev D (L R : List Bool) : Z0 := ⟨3,L,R⟩
abbrev P : List Bool := [false,true]
abbrev Q : List Bool := [true,false]
abbrev G : List Bool := [false,true,false,true]
abbrev H : List Bool := [false,false,false,true]
abbrev W : List Bool := [true,false,true,false]
abbrev ones (n : Nat) := List.replicate n true
abbrev zeros (n : Nat) := List.replicate n false

def rep (w : List Bool) : Nat → List Bool
  | 0 => []
  | n+1 => w ++ rep w n

theorem rep_snoc (w : List Bool) (n : Nat) (R : List Bool) :
    rep w n ++ (w ++ R) = rep w (n+1) ++ R := by
  induction n with
  | zero => simp [rep]
  | succ n ih =>
    change (w ++ rep w n) ++ (w ++ R) = (w ++ rep w (n+1)) ++ R
    simp only [List.append_assoc,ih]

theorem rep_double (w : List Bool) (n : Nat) : rep (w++w) n = rep w (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [show 2*(n+1)=2*n+1+1 by omega]; simp only [rep,ih,List.append_assoc]

theorem pop_one (L R : List Bool) :
    run0 table 4 (A (P++L) (true::R)) = some (A L (Q++true::R)) := by rfl

theorem pop (n : Nat) (L R : List Bool) :
    run0 table (4*n) (A (rep P n++L) (true::R)) = some (A L (rep Q n++true::R)) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h := join0 (pop_one (rep P n++L) R) (ih (false::true::R))
    change run0 table (4+4*n) (A (P++(rep P n++L)) (true::R)) = some (A L (rep Q n++(Q++true::R))) at h
    rw [rep_snoc] at h
    simpa only [rep,List.append_assoc,show 4*(n+1)=4+4*n by omega] using h

theorem scan_one (L R : List Bool) :
    run0 table 6 (C (false::L) (W++R)) = some (C (H++false::L) R) := by rfl

theorem scan (n : Nat) (L R : List Bool) :
    run0 table (6*n) (C (false::L) (rep W n++R)) = some (C (rep H n++false::L) R) := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have h := join0 (scan_one L (rep W n++R)) (ih (false::false::true::false::L))
    change run0 table (6+6*n) (C (false::L) (W++(rep W n++R))) = some (C (rep H n++(H++false::L)) R) at h
    rw [rep_snoc] at h
    simpa only [rep,List.append_assoc,show 6*(n+1)=6+6*n by omega] using h

theorem cscan (n z : Nat) (L : List Bool) :
    run0 table (n+1) (C (true::zeros z++L) (ones n)) = some (C (zeros (z+n+2)++L) []) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    have h : run0 table 1 (C (true::zeros z++L) (ones (n+1))) = some (C (true::zeros (z+1)++L) (ones n)) := by rfl
    have h' := join0 h (ih (z+1))
    rw [show z+1+n+2=z+(n+1)+2 by omega,show 1+(n+1)=n+1+1 by omega] at h'
    exact h'

theorem dscan (n : Nat) (L R : List Bool) :
    run0 table n (D (zeros n++L) R) = some (D L (ones n++R)) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h : run0 table 1 (D (zeros (n+1)++L) R) = some (D (zeros n++L) (true::R)) := by rfl
    have h' := join0 h (ih (true::R))
    have eq : ones n++true::R = ones (n+1)++R := by
      change ones n ++ (ones 1 ++ R) = ones (n+1) ++ R
      rw [← List.append_assoc,List.replicate_append_replicate]
    rw [eq,show 1+n=n+1 by omega] at h'
    exact h'

theorem odd_finish (k : Nat) (L : List Bool) :
    ∃ t, run0 table t (C (false::L) (Q++ones (k+1))) = some (A (P++false::L) (ones (k+3))) := by
  have h1 : run0 table 4 (C (false::L) (Q++ones (k+1))) = some (C (true::true::false::L) (ones (k+1))) := by rfl
  have h2 := cscan (k+1) 0 (true::false::L)
  simp only [Nat.zero_add] at h2
  have h3 : run0 table 1 (C (zeros (k+1+2)++true::false::L) []) = some (D (zeros (k+4)++true::false::L) []) := by rfl
  have h4 := dscan (k+4) (true::false::L) []
  simp only [List.append_nil] at h4
  have h5 : run0 table 3 (D (true::false::L) (ones (k+4))) = some (A (P++false::L) (ones (k+3))) := by rfl
  exact ⟨_,join0 (join0 (join0 (join0 h1 h2) h3) h4) h5⟩

theorem pop_blocks (n k : Nat) (L : List Bool) :
    run0 table (4+4*(2*n)) (A (P++rep G n++L) (ones (k+1))) =
      some (A L (rep W n++(Q++ones (k+1)))) := by
  have h1 := pop_one (rep G n++L) (ones k)
  have h2 := pop (2*n) L (false::ones (k+1))
  rw [← rep_double P n,← rep_double Q n] at h2
  rw [List.append_assoc]
  exact join0 h1 h2

theorem start_bad (n k : Nat) (L : List Bool) :
    run0 table 4 (A (H++L) (rep W n++(Q++ones (k+1)))) =
      some (C (G++L) (rep W n++(Q++ones (k+1)))) := by
  cases n <;> rfl

theorem odd_end (n k : Nat) (L : List Bool) :
    ∃ t, run0 table t (C (rep H n++(G++L)) (Q++ones (k+1))) =
      some (A (P++(rep H n++(G++L))) (ones (k+3))) := by
  cases n with
  | zero => exact odd_finish k (true::false::true::L)
  | succ n => exact odd_finish k (false::false::true::(rep H n++(G++L)))

theorem decr (n k : Nat) (L : List Bool) :
    ∃ t, run0 table t (A (P++(rep G n++(H++L))) (ones (k+1))) =
      some (A (P++(rep H n++(G++L))) (ones (k+3))) := by
  have h1 := pop_blocks n k (H++L)
  have h2 := start_bad n k L
  have h3 := scan n (true::false::true::L) (Q++ones (k+1))
  obtain ⟨t,h4⟩ := odd_end n k L
  exact ⟨_,join0 (join0 (join0 h1 h2) h3) h4⟩

def digit (b : Bool) : List Bool := if b then H else G

def enc : List Bool → List Bool
  | [] => []
  | b::bs => digit b ++ enc bs

theorem enc_append (a b : List Bool) : enc (a++b) = enc a++enc b := by
  induction a with
  | nil => rfl
  | cons x a ih => simp [enc,ih,List.append_assoc]

theorem enc_true (n : Nat) : enc (ones n) = rep H n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,enc,digit,rep,ih]

theorem clear (n : Nat) (bs : List Bool) (hlen : bs.length = n) (L : List Bool) (k : Nat) :
    ∃ t k', k ≤ k' ∧ (true ∈ bs → k+2 ≤ k') ∧
      run0 table t (A (P++(enc bs.reverse++L)) (ones (k+1))) =
        some (A (P++(rep G n++L)) (ones (k'+1))) := by
  induction n generalizing bs L k with
  | zero =>
    have h : bs = [] := List.eq_nil_of_length_eq_zero hlen
    subst bs
    exact ⟨0,k,by omega,by simp,rfl⟩
  | succ n ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have hb : bs.length = n := by simpa using hlen
      obtain ⟨t,k1,hk1,hk2,ht⟩ := ih bs hb (digit b++L) k
      have hstart : enc (b::bs).reverse ++ L = enc bs.reverse ++ (digit b++L) := by
        simp [List.reverse_cons,enc_append,enc,List.append_assoc]
      rw [hstart]
      cases b with
      | false =>
        change run0 table t _ = some (A (P++(rep G n++(G++L))) (ones (k1+1))) at ht
        rw [rep_snoc] at ht
        exact ⟨t,k1,hk1,by simpa using hk2,ht⟩
      | true =>
        obtain ⟨u,hu⟩ := decr n k1 L
        obtain ⟨v,k2,hk3,_,hv⟩ := ih (ones n) (by simp) (G++L) (k1+2)
        rw [List.reverse_replicate,enc_true,rep_snoc] at hv
        exact ⟨_,k2,by omega,by omega,join0 (join0 ht hu) hv⟩

theorem even_start (n k : Nat) :
    run0 table 4 (A [] (rep W (n+1)++ones (k+3))) = some (C P (rep W (n+1)++ones (k+3))) := by rfl

theorem even_finish (n k : Nat) :
    run0 table 4 (C (rep H n++P) (ones (k+3))) =
      some (A (P++(rep H n++P)) (ones (k+1))) := by
  cases n <;> rfl

theorem epoch (n k : Nat) : ∃ t k', 0 < t ∧
    run0 table t (A [] (rep W (n+1)++ones (k+3))) =
      some (A [] (rep W (n+2)++ones (k'+3))) := by
  have h1 := even_start n k
  have h2 := scan (n+1) [true] (ones (k+3))
  have h3 := even_finish (n+1) k
  obtain ⟨t,k1,_,hk,h4⟩ := clear (n+1) (ones (n+1)) (by simp) P k
  rw [List.reverse_replicate,enc_true] at h4
  have hk' := hk (by simp)
  have h5 := pop (2*(n+2)) [] (ones k1)
  rw [← rep_double P (n+2),← rep_double Q (n+2)] at h5
  have hs (j : Nat) : P++(rep G j++P) = rep G (j+1) := by
    induction j with
    | zero => rfl
    | succ j ih =>
      change P++((G++rep G j)++P) = G++rep G (j+1)
      simp only [List.append_assoc]
      change G++(P++(rep G j++P)) = G++rep G (j+1)
      rw [ih]
  have he := hs (n+1)
  rw [he] at h4
  simp only [List.append_nil] at h5
  change run0 table _ (A (rep G (n+2)) (ones (k1+1))) = some (A [] (rep W (n+2)++ones (k1+1))) at h5
  have hall := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  rw [show k1+1=k1-2+3 by omega] at hall
  exact ⟨_,k1-2,by omega,hall⟩

noncomputable def tail : Nat → Nat
  | 0 => 0
  | n+1 => (epoch n (tail n)).choose_spec.choose

noncomputable def family (n : Nat) : Z0 := A [] (rep W (n+1)++ones (tail n+3))

noncomputable def cost (n : Nat) : Nat := (epoch n (tail n)).choose

theorem entry : run0 table 36 (A [] []) = some (family 0) := by rfl

theorem cost_pos (n : Nat) : 0 < cost n := (epoch n (tail n)).choose_spec.choose_spec.1

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) :=
  (epoch n (tail n)).choose_spec.choose_spec.2

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 36 cost entry cost_pos growth m hm

#print axioms entry
#print axioms decr
#print axioms clear
#print axioms epoch
#print axioms growth
#print axioms never
end BB6.Agent10Raw107LA385
