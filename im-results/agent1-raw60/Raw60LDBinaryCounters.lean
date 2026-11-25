import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent1Raw60LDBinaryCounters
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none

abbrev A (L R : List Bool) : Z0 := ⟨0,L,R⟩
abbrev C (L R : List Bool) : Z0 := ⟨2,L,R⟩
abbrev E (L R : List Bool) : Z0 := ⟨4,L,R⟩
abbrev F (L R : List Bool) : Z0 := ⟨5,L,R⟩
abbrev U (n : Nat) := List.replicate n true
abbrev Z (n : Nat) := List.replicate n false
abbrev P : List Bool := [true,true]
abbrev G : List Bool := [true,true,false,false]
abbrev Q : List Bool := [false,false]
abbrev H : List Bool := [false,true,true,true]
abbrev X : List Bool := [false,false,true,true,true]
abbrev Y : List Bool := [false,true,true,true,true]
abbrev S : List Bool := [true,true,false,true,true]
abbrev End : List Bool := [false,true,true,true,true,true]

def Reach (a b : Z0) : Prop := ∃ n, run0 table n a = some b

theorem Reach.refl (a : Z0) : Reach a a := ⟨0,rfl⟩
theorem Reach.trans {a b c : Z0} (h : Reach a b) (g : Reach b c) : Reach a c := by
  obtain ⟨n,h⟩ := h
  obtain ⟨k,g⟩ := g
  exact ⟨n+k,join0 h g⟩

theorem rep_single (b : Bool) (n : Nat) : rep [b] n = List.replicate n b := by
  induction n <;> simp [rep,List.replicate_succ, *]
theorem rep_pair (b : Bool) (n : Nat) : rep [b,b] n = List.replicate (2*n) b := by
  induction n with
  | zero => rfl
  | succ n ih => rw [show 2*(n+1)=2*n+1+1 by omega]; simp only [rep,ih]; rfl

theorem pushOne (L R : List Bool) :
    run0 table 21 (E (G++L) (P++Y++R)) = some (E (G++S++L) (P++R)) := by rfl

theorem push (k : Nat) (L R : List Bool) :
    run0 table (21*k) (E (G++L) (P++rep Y k++R)) = some (E (G++rep S k++L) (P++R)) :=
  sweepR table 4 G P Y S 21 pushOne k L R

theorem xStart (L R : List Bool) :
    run0 table 32 (E (G++L) (P++X++R)) = some (A (P++L) (H++Y++R)) := by rfl

theorem popOne (L R : List Bool) :
    run0 table 7 (A (P++S++L) (H++R)) = some (A (P++L) (H++X++R)) := by rfl

theorem pop (k : Nat) (L R : List Bool) :
    run0 table (7*k) (A (P++rep S k++L) (H++R)) = some (A (P++L) (H++rep X k++R)) :=
  sweepL table 0 P H S X 7 popOne k L R

theorem overflowStart (L : List Bool) :
    run0 table 54 (E (G++S++L) [true,true,true]) = some (A (P++S++L) (H++End)) := by rfl

theorem rightCarry (k : Nat) (L R : List Bool) :
    run0 table (21*k+32+7*k) (E (G++Q++L) (P++rep Y k++X++R)) =
      some (A (G++L) (H++rep X k++Y++R)) := by
  have h1 := push k (Q++L) (X++R)
  have h2 := xStart (rep S k++Q++L) R
  have h3 := pop k (Q++L) (Y++R)
  simp only [List.append_assoc] at h1 h2 h3 ⊢
  exact join0 (join0 h1 h2) h3

theorem rightOverflow (k : Nat) (L : List Bool) :
    run0 table (21*(k+1)+54+7*(k+1)) (E (G++Q++L) (P++rep Y k++End)) =
      some (A (G++L) (H++rep X (k+1)++End)) := by
  have h1 := push (k+1) (Q++L) [true]
  have h2 := overflowStart (rep S k++Q++L)
  have h3 := pop (k+1) (Q++L) End
  have he : P++rep Y (k+1)++[true] = P++rep Y k++End := by
    have h : rep Y (k+1)=rep Y k++Y := by rw [rep_snoc]; rfl
    rw [h]; simp only [List.append_assoc]; rfl
  rw [he] at h1
  have hj : E (G++rep S (k+1)++(Q++L)) (P++[true]) = E (G++S++(rep S k++Q++L)) [true,true,true] := by simp only [rep,List.append_assoc]; rfl
  rw [hj] at h1
  have ha : A (P++S++(rep S k++Q++L)) (H++End) = A (P++rep S (k+1)++(Q++L)) (H++End) := by simp only [rep,List.append_assoc]
  rw [ha] at h2
  simp only [List.append_assoc] at h1 h2 h3 ⊢
  exact join0 (join0 h1 h2) h3

theorem leftStart (L R : List Bool) :
    run0 table 17 (A (G++L) (H++R)) = some (F ([true,true,true]++L) (Y++R)) := by rfl

theorem oneF (L R : List Bool) : run0 table 1 (F (true::L) R) = some (F L (true::R)) := by rfl

theorem leftSweep (n : Nat) (L R : List Bool) :
    run0 table n (F (U n++L) R) = some (F L (U n++R)) := by
  simpa only [List.nil_append,Nat.one_mul,rep_single] using sweepL table 5 [] [] [true] [true] 1 oneF n L R

theorem oneC (L R : List Bool) : run0 table 1 (C (true::L) (true::R)) = some (C (true::false::L) R) := by rfl

theorem clearC (n : Nat) (L R : List Bool) :
    run0 table n (C (true::L) (U n++R)) = some (C (true::(Z n++L)) R) := by
  have h := sweepR table 2 [true] [] [true] [false] 1 oneC n L R
  simp only [List.nil_append,Nat.one_mul,rep_single] at h
  exact h

theorem leftReturn (n : Nat) (L R : List Bool) :
    run0 table 3 (F (Q++L) (U (n+3)++Y++R)) = some (C ([true,true,true]++L) (U (n+2)++Y++R)) := by rfl

theorem leftFinish (L R : List Bool) :
    run0 table 3 (C (true::L) (Y++R)) = some (E (P++Q++L) (P++R)) := by rfl

theorem leftCarry (u : Nat) (L R : List Bool) :
    run0 table (17+(2*u+3)+3+(2*u+2)+3) (A (G++U (2*u)++Q++L) (H++R)) =
      some (E (G++Q++Z (2*u)++P++L) (P++R)) := by
  have h1 := leftStart (U (2*u)++Q++L) R
  have h2 := leftSweep (2*u+3) (Q++L) (Y++R)
  have h3 := leftReturn (2*u) L R
  have h4 := clearC (2*u+2) (P++L) (Y++R)
  have h5 := leftFinish (Z (2*u+2)++P++L) R
  rw [show 2*u+3=2*u+1+1+1 by omega] at h2
  simp only [List.append_assoc] at h1 h2 h3 h4 h5 ⊢
  have H1 := join0 h1 h2
  have H2 := join0 H1 h3
  have H3 := join0 H2 h4
  have H4 := join0 H3 h5
  have ht : 17+(2*u+1+1+1)+3+(2*u+2)+3 = 17+(2*u+3)+3+(2*u+2)+3 := by omega
  rw [ht] at H4
  exact H4

theorem leftOverflow (u : Nat) (R : List Bool) :
    run0 table (17+(2*u+3)) (A (G++U (2*u)) (H++R)) = some (F [] (U (2*u+3)++Y++R)) := by
  have h1 := leftStart (U (2*u)) R
  have h2 := leftSweep (2*u+3) [] (Y++R)
  rw [show 2*u+3=2*u+1+1+1 by omega] at h2
  simp only [List.append_nil,List.append_assoc] at h1 h2 ⊢
  exact join0 h1 h2

theorem startF (n : Nat) (R : List Bool) :
    run0 table 3 (F [] (U (n+1)++Y++R)) = some (C [true,true,true] (U n++Y++R)) := by rfl

theorem startup (n : Nat) (R : List Bool) :
    run0 table (3+n+3) (F [] (U (n+1)++Y++R)) = some (E (P++Q++Z n++P) (P++R)) := by
  have h1 := startF n R
  have h2 := clearC n P (Y++R)
  have h3 := leftFinish (Z n++P) R
  simp only [List.append_assoc] at h1 h2 h3 ⊢
  exact join0 (join0 h1 h2) h3

-- Binary words are little-endian, with distinct physical encodings on each side.
def encL : List Bool → List Bool
  | [] => []
  | b::bs => [b,b]++encL bs
def encR : List Bool → List Bool
  | [] => []
  | b::bs => (if b then Y else X)++encR bs

theorem encL_append (a b : List Bool) : encL (a++b) = encL a++encL b := by
  induction a <;> simp [encL,List.append_assoc, *]
theorem encR_append (a b : List Bool) : encR (a++b) = encR a++encR b := by
  induction a <;> simp [encR,List.append_assoc, *]
theorem encL_rep (b : Bool) (n : Nat) : encL (List.replicate n b) = List.replicate (2*n) b := by
  induction n with
  | zero => rfl
  | succ n ih => rw [show 2*(n+1)=2*n+1+1 by omega]; simp only [List.replicate_succ,encL,ih]; rfl

theorem encR_rep (b : Bool) (n : Nat) : encR (List.replicate n b) = rep (if b then Y else X) n := by
  induction n <;> simp [List.replicate_succ,encR,rep, *]

def inc : List Bool → Option (List Bool)
  | [] => none
  | false::bs => some (true::bs)
  | true::bs => (inc bs).map (false::·)

def val : List Bool → Nat
  | [] => 0
  | b::bs => (if b then 1 else 0)+2*val bs

theorem inc_split {a b : List Bool} (h : inc a = some b) :
    ∃ k t, a = U k++false::t ∧ b = Z k++true::t := by
  induction a generalizing b with
  | nil => simp [inc] at h
  | cons x xs ih =>
    cases x with
    | false => simp [inc] at h; subst b; exact ⟨0,xs,rfl,rfl⟩
    | true =>
      cases he : inc xs with
      | none => simp [inc,he] at h
      | some ys =>
        simp [inc,he] at h; subst b
        obtain ⟨k,t,hx,hy⟩ := ih he
        exact ⟨k+1,t,by rw [hx]; rfl,by rw [hy]; rfl⟩

theorem inc_none {a : List Bool} (h : inc a = none) : a = U a.length := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | false => simp [inc] at h
    | true =>
      cases he : inc xs with
      | none => simp only [List.length_cons,List.replicate_succ]; exact congrArg (true::·) (ih he)
      | some ys => simp [inc,he] at h

theorem inc_stats {a b : List Bool} (h : inc a = some b) : b.length=a.length ∧ val b=val a+1 := by
  induction a generalizing b with
  | nil => simp [inc] at h
  | cons x xs ih =>
    cases x with
    | false => simp [inc] at h; subst b; simp [val]; omega
    | true =>
      cases he : inc xs with
      | none => simp [inc,he] at h
      | some ys =>
        simp [inc,he] at h; subst b
        obtain ⟨hl,hv⟩ := ih he
        simp [hl,val,hv]; omega

theorem val_bound (a : List Bool) : val a < 2^a.length := by
  induction a with
  | nil => decide
  | cons x xs ih => cases x <;> simp [val,Nat.pow_succ] <;> omega

theorem val_ones (n : Nat) : val (U n)+1=2^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change 1+2*val (U n)+1=2^n*2
    omega

theorem val_zeros (n : Nat) : val (Z n)=0 := by
  induction n <;> simp [List.replicate_succ,val, *]

theorem val_unique {a b : List Bool} (hl : a.length=b.length) (hv : val a=val b) : a=b := by
  induction a generalizing b with
  | nil => exact (List.length_eq_zero_iff.mp hl.symm).symm
  | cons x xs ih =>
    cases b with
    | nil => simp at hl
    | cons y ys =>
      simp only [List.length_cons,Nat.add_right_cancel_iff] at hl
      cases x <;> cases y <;> simp [val] at hv <;> first | omega | congr 1 <;> exact ih hl (by omega)

theorem inc_exists (a : List Bool) (h : val a+1 < 2^a.length) : ∃ b, inc a = some b := by
  cases he : inc a with
  | some b => exact ⟨b,rfl⟩
  | none =>
    have ha := inc_none he
    have hv : val a+1=2^a.length := by rw [ha] at *; simpa using val_ones a.length
    omega

def cfg (l r : List Bool) : Z0 := E (G++Q++encL l) (P++encR r++End)
def mid (l r : List Bool) : Z0 := A (G++encL l) (H++encR r++End)

theorem rightNormal {r r' : List Bool} (h : inc r=some r') (l : List Bool) : Reach (cfg l r) (mid l r') := by
  obtain ⟨k,t,hr,hr'⟩ := inc_split h
  subst r r'
  refine ⟨21*k+32+7*k,?_⟩
  simpa [cfg,mid,encR_append,encR_rep,encR,List.append_assoc] using rightCarry k (encL l) (encR t++End)

theorem rightWrap (k : Nat) (l : List Bool) : Reach (cfg l (U k)) (mid l (Z (k+1))) := by
  refine ⟨21*(k+1)+54+7*(k+1),?_⟩
  simpa [cfg,mid,encR_rep,List.append_assoc] using rightOverflow k (encL l)

theorem leftNormal {l l' : List Bool} (h : inc l=some l') (r : List Bool) : Reach (mid l r) (cfg l' r) := by
  obtain ⟨k,t,hl,hl'⟩ := inc_split h
  subst l l'
  refine ⟨17+(2*k+3)+3+(2*k+2)+3,?_⟩
  simpa only [cfg,mid,encL_append,encL_rep,encL,List.append_assoc] using leftCarry k (encL t) (encR r++End)

theorem leftWrap (k : Nat) (r : List Bool) : Reach (mid (U k) r) (F [] (U (2*k+3)++Y++encR r++End)) := by
  refine ⟨17+(2*k+3),?_⟩
  simpa only [mid,encL_rep,List.append_assoc] using leftOverflow k (encR r++End)

theorem bothIter (d : Nat) (l r : List Bool)
    (hl : val l+d < 2^l.length) (hr : val r+d < 2^r.length) :
    ∃ l' r', l'.length=l.length ∧ r'.length=r.length ∧ val l'=val l+d ∧ val r'=val r+d ∧ Reach (cfg l r) (cfg l' r') := by
  induction d generalizing l r with
  | zero => exact ⟨l,r,rfl,rfl,by omega,by omega,Reach.refl _⟩
  | succ d ih =>
    obtain ⟨l1,hl1⟩ := inc_exists l (by omega)
    obtain ⟨r1,hr1⟩ := inc_exists r (by omega)
    obtain ⟨hll,hlv⟩ := inc_stats hl1
    obtain ⟨hrl,hrv⟩ := inc_stats hr1
    obtain ⟨l',r',hll',hrl',hlv',hrv',ht⟩ := ih l1 r1 (by rw [hll,hlv]; omega) (by rw [hrl,hrv]; omega)
    exact ⟨l',r',hll'.trans hll,hrl'.trans hrl,by omega,by omega,(rightNormal hr1 l).trans ((leftNormal hl1 r1).trans ht)⟩

-- The right counter wraps once. Then the left counter wraps first, advancing the family.
def lstart (n : Nat) : List Bool := Z (n+5)++[true]
def rstart (n : Nat) : List Bool := true::false::false::U (n+1)
def family (n : Nat) : Z0 := F [] (U (2*n+13)++Y++encR (rstart n)++End)

theorem lstart_len (n : Nat) : (lstart n).length=n+6 := by simp [lstart]
theorem rstart_len (n : Nat) : (rstart n).length=n+4 := by simp [rstart]
theorem val_lstart (n : Nat) : val (Z n++[true])=2^n := by
  induction n <;> simp [List.replicate_succ,val,Nat.pow_succ, *] <;> omega

theorem val_rstart (n : Nat) : val (rstart n)+7=2^(n+4) := by
  have h := val_ones (n+1)
  simp [rstart,val] 
  rw [show n+4=(n+1)+1+1+1 by omega]
  simp only [Nat.pow_succ]
  omega

theorem pow_small (n : Nat) : 16 ≤ 2^(n+4) := by
  induction n with
  | zero => decide
  | succ n ih => rw [show n+1+4=n+4+1 by omega,Nat.pow_succ]; omega

theorem family_start (n : Nat) : run0 table (3+(2*n+12)+3) (family n) = some (cfg (lstart n) (rstart n)) := by
  have h := startup (2*n+12) (encR (rstart n)++End)
  have he : encL (lstart n)=Z (2*n+10)++P := by simp only [lstart,encL_append,encL_rep,encL]; rw [show 2*(n+5)=2*n+10 by omega]; rfl
  rw [cfg,he,family]
  have hL : P++Q++Z (2*n+12)++P = G++Q++(Z (2*n+10)++P) := by
    rw [show 2*n+12=2*n+10+1+1 by omega]; rfl
  rw [hL] at h
  simpa only [List.append_assoc,show 2*n+12+1=2*n+13 by omega] using h

theorem epoch (n : Nat) : Reach (cfg (lstart n) (rstart n)) (family (n+1)) := by
  have h16 := pow_small n
  have h5 : 2^(n+5)=2*2^(n+4) := by rw [show n+5=n+4+1 by omega,Nat.pow_succ]; omega
  have h6 : 2^(n+6)=2*2^(n+5) := by rw [show n+6=n+5+1 by omega,Nat.pow_succ]; omega
  have hlv : val (lstart n)=2^(n+5) := val_lstart (n+5)
  have hrv := val_rstart n
  obtain ⟨l1,r1,hll1,hrl1,hlv1,hrv1,hfirst⟩ := bothIter 6 (lstart n) (rstart n)
    (by rw [lstart_len,hlv]; omega) (by rw [rstart_len]; omega)
  rw [lstart_len] at hll1
  rw [rstart_len] at hrl1
  have hr1 : r1=U (n+4) := val_unique (by simpa using hrl1) (by have h := val_ones (n+4); omega)
  obtain ⟨l2,hl2⟩ := inc_exists l1 (by rw [hll1]; omega)
  obtain ⟨hll2,hlv2⟩ := inc_stats hl2
  rw [hll1] at hll2
  have hwrap : Reach (cfg l1 r1) (cfg l2 (Z (n+5))) := by
    rw [hr1,show n+5=n+4+1 by omega]
    exact (rightWrap (n+4) l1).trans (leftNormal hl2 _)
  let d := 2^(n+5)-8
  obtain ⟨l3,r3,hll3,hrl3,hlv3,hrv3,hsecond⟩ := bothIter d l2 (Z (n+5))
    (by rw [hll2]; dsimp [d]; omega) (by rw [List.length_replicate,val_zeros]; dsimp [d]; omega)
  rw [hll2] at hll3
  rw [List.length_replicate] at hrl3
  rw [val_zeros] at hrv3
  have hl3 : l3=U (n+6) := val_unique (by simpa using hll3) (by have h := val_ones (n+6); dsimp [d] at hlv3; omega)
  obtain ⟨r4,hr4⟩ := inc_exists r3 (by rw [hrl3]; dsimp [d] at hrv3; omega)
  obtain ⟨hrl4,hrv4⟩ := inc_stats hr4
  rw [hrl3] at hrl4
  have hr4' : r4=rstart (n+1) := val_unique (by rw [rstart_len]; omega) (by have h := val_rstart (n+1); rw [show n+1+4=n+5 by omega] at h; dsimp [d] at hrv3; omega)
  have hlast := (rightNormal hr4 l3).trans (by rw [hl3,hr4']; exact leftWrap (n+6) (rstart (n+1)))
  have hfinal := hfirst.trans (hwrap.trans (hsecond.trans hlast))
  simpa only [family,show 2*(n+6)+3=2*(n+1)+13 by omega] using hfinal

theorem grow (n : Nat) : ∃ k, 0<k ∧ run0 table k (family n) = some (family (n+1)) := by
  obtain ⟨t,ht⟩ := epoch n
  exact ⟨3+(2*n+12)+3+t,by omega,join0 (family_start n) ht⟩

theorem entry : run0 table 2437 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  classical
  exact never_of_growth table family 2437 (fun n => Classical.choose (grow n)) entry
    (fun n => (Classical.choose_spec (grow n)).1) (fun n => (Classical.choose_spec (grow n)).2) m hm

#print axioms epoch
#print axioms never
end BB6.Agent1Raw60LDBinaryCounters
