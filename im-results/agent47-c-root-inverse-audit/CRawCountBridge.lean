import Frontier
import ThinGatewayCounted

namespace BB6.Agent47CRaw
open BB6Coverage BB6CLine BB6.Agent47ThinCounted

/-- Literal historical holdout #39, identical to MachineCPath.machineC. -/
def cMachine : Machine := fun (s,b) =>
  match s.val,b with
  | 0,false => some ⟨true,true,1⟩
  | 0,true => some ⟨true,false,2⟩
  | 1,false => some ⟨true,false,2⟩
  | 1,true => some ⟨true,true,3⟩
  | 2,false => some ⟨true,false,0⟩
  | 2,true => some ⟨false,false,1⟩
  | 3,false => some ⟨false,true,1⟩
  | 3,true => some ⟨true,true,4⟩
  | 4,false => some ⟨true,true,5⟩
  | 4,true => some ⟨false,true,0⟩
  | 5,false => none
  | 5,true => some ⟨false,true,2⟩
  | _,_ => none

abbrev Stream := Nat → Bool

def zeros : Stream := fun _ => false

def cons (b : Bool) (s : Stream) : Stream
  | 0 => b
  | n+1 => s n

def hd (s : Stream) := s 0

def tl (s : Stream) : Stream := fun n => s (n+1)

def ones : Nat → Stream → Stream
  | 0,s => s
  | n+1,s => cons true (ones n s)

def pairs : Nat → Stream → Stream
  | 0,s => s
  | n+1,s => cons false (cons true (pairs n s))

theorem ones_add (m n : Nat) (s : Stream) : ones (m+n) s = ones m (ones n s) := by
  induction m with
  | zero => simp [ones]
  | succ m ih => rw [show m+1+n=(m+n)+1 by omega]; simp only [ones,ih]

theorem pairs_add (m n : Nat) (s : Stream) : pairs (m+n) s = pairs m (pairs n s) := by
  induction m with
  | zero => simp [pairs]
  | succ m ih => rw [show m+1+n=(m+n)+1 by omega]; simp only [pairs,ih]

structure Z where
  q : Fin 6
  l : Stream
  r : Stream

/-- Right-facing and left-facing zipper presentations; r includes current
    in cr, l includes current in cl. -/
def cr (q : Fin 6) (l r : Stream) : Z := ⟨q,l,r⟩
def cl (q : Fin 6) (l r : Stream) : Z := ⟨q,tl l,cons (hd l) r⟩

def zMove (z : Z) (m : Move) : Z :=
  if m.right then cr m.next (cons m.write z.l) (tl z.r)
  else cl m.next z.l (cons m.write (tl z.r))

def zStep (z : Z) : Option Z := (cMachine (z.q,hd z.r)).map (zMove z)

def zRun : Nat → Z → Option Z
  | 0,z => some z
  | n+1,z => (zStep z).bind (zRun n)

theorem zRun_add (n m : Nat) (z : Z) : zRun (n+m) z = (zRun n z).bind (zRun m) := by
  induction n generalizing z with
  | zero => simp [zRun]
  | succ n ih =>
    rw [show n+1+m=n+m+1 by omega]
    simp only [zRun]
    cases h : zStep z with
    | none => rfl
    | some z' => simpa using ih z'

theorem zRun_join {n m : Nat} {z u v : Z} (h : zRun n z=some u) (g : zRun m u=some v) :
    zRun (n+m) z=some v := by rw [zRun_add,h]; exact g

/-- Sweep C left across k alternating pairs, converting them to ones. -/
theorem c_left_pairs (k : Nat) (l r : Stream) :
    zRun (2*k) (cl 2 (pairs k l) r)=some (cl 2 l (ones (2*k) r)) := by
  induction k generalizing r with
  | zero => rfl
  | succ k ih =>
    have h : zRun 2 (cl 2 (pairs (k+1) l) r)=some (cl 2 (pairs k l) (ones 2 r)) := by rfl
    have hh := zRun_join h (ih (ones 2 r))
    rw [←ones_add,show 2*k+2=2*(k+1) by omega,show 2+2*k=2*(k+1) by omega] at hh
    exact hh

/-- Sweep B left across k alternating pairs, preserving them. -/
theorem b_left_pairs (k : Nat) (l r : Stream) :
    zRun (2*k) (cl 1 (pairs k l) r)=some (cl 1 l (pairs k r)) := by
  induction k generalizing r with
  | zero => rfl
  | succ k ih =>
    have h : zRun 2 (cl 1 (pairs (k+1) l) r)=some (cl 1 (pairs k l) (pairs 1 r)) := by rfl
    have hh := zRun_join h (ih (pairs 1 r))
    rw [←pairs_add,show 2+2*k=2*(k+1) by omega] at hh
    exact hh

/-- Sweep B right over k pairs after a leading one. -/
theorem b_right_pairs (k : Nat) (l r : Stream) :
    zRun (2*k) (cr 1 l (cons true (pairs k r)))=some (cr 1 (pairs k l) (cons true r)) := by
  induction k generalizing l with
  | zero => rfl
  | succ k ih =>
    have h : zRun 2 (cr 1 l (cons true (pairs (k+1) r)))=some (cr 1 (pairs 1 l) (cons true (pairs k r))) := by rfl
    have hh := zRun_join h (ih (pairs 1 l))
    rw [←pairs_add,show 2+2*k=2*(k+1) by omega] at hh
    exact hh

/-- E converts two alternating pairs to four ones in six raw moves. -/
theorem e_right_pairs (m : Nat) (l r : Stream) :
    zRun (6*m) (cr 4 l (pairs (2*m) r))=some (cr 4 (ones (4*m) l) r) := by
  induction m generalizing l with
  | zero => rfl
  | succ m ih =>
    have h : zRun 6 (cr 4 l (pairs (2*m+2) r))=some (cr 4 (ones 4 l) (pairs (2*m) r)) := by rfl
    have hh := zRun_join h (ih (ones 4 l))
    rw [←ones_add,show 4*m+4=4*(m+1) by omega,show 6+6*m=6*(m+1) by omega,
      show 2*m+2=2*(m+1) by omega] at hh
    exact hh

/-- Canonical CLine state in the relative infinite tape. -/
def enc (s : State) : Z := cr 1 (pairs s.2.1 (ones s.1 zeros)) (ones s.2.2 zeros)


/-- Finite local microprograms use arbitrary tails. -/
theorem high_start (l r : Stream) :
    zRun 7 (cr 1 l (ones 4 r))=some (cl 1 l (cons false (ones 3 r))) := by rfl

theorem high_nonzero_finish (k : Nat) (l r : Stream) :
    zRun (2*k+2) (cl 1 (cons true l) (pairs k (cons false r)))=
      some (cr 1 (pairs (k+1) l) r) := by
  have hh := b_right_pairs k l (cons false r)
  change zRun (2*k) (cl 1 (cons true l) (pairs k (cons false r)))=
      some (cr 1 (pairs k l) (cons true (cons false r))) at hh
  have h : zRun 2 (cr 1 (pairs k l) (cons true (cons false r)))=
      some (cr 1 (pairs (k+1) l) r) := by rfl
  exact zRun_join hh h

theorem high_zero_start (r : Stream) :
    zRun 5 (cl 1 zeros r)=some (cr 4 (ones 3 zeros) r) := by rfl

theorem high_even_finish (l r : Stream) :
    zRun 9 (cr 4 (cons true l) (cons false (ones 3 r)))=
      some (cr 1 (pairs 2 l) (cons true r)) := by rfl

theorem high_odd_finish (l r : Stream) :
    zRun 4 (cr 4 l (pairs 1 (cons false (ones 3 r))))=
      some (cr 1 (ones 2 l) (ones 4 r)) := by rfl

theorem zero_start (l r : Stream) :
    zRun 1 (cr 1 l (cons false r))=some (cl 2 l (cons true r)) := by rfl

theorem zero_high_finish (l r : Stream) :
    zRun 3 (cl 2 (ones 2 l) r)=some (cr 1 (pairs 1 l) r) := by rfl

theorem zero_zero_finish (r : Stream) :
    zRun 2 (cl 2 zeros r)=some (cr 1 (ones 1 zeros) (cons true r)) := by rfl

theorem zero_one_empty_finish :
    zRun 10 (cl 2 (ones 1 zeros) (ones 1 zeros))=some (enc (5,0,1)) := by rfl

theorem zero_one_finish (r : Stream) :
    zRun 15 (cl 2 (ones 1 zeros) (ones 3 r))=some (cr 1 (pairs 2 (ones 2 zeros)) (cons true r)) := by rfl

theorem right_one_finish (l : Stream) :
    zRun 2 (cr 1 l (ones 1 zeros))=some (cr 1 (pairs 1 l) zeros) := by rfl

theorem right_three_finish (l : Stream) :
    zRun 12 (cr 1 l (ones 3 zeros))=some (cr 1 (pairs 2 l) (ones 1 zeros)) := by rfl

theorem right_two_finish (l : Stream) :
    zRun 3 (cr 1 l (ones 2 zeros))=some (cr 5 (ones 3 l) zeros) := by rfl


theorem high_nonzero_rule (a k d : Nat) :
    zRun (4*k+9) (enc (a+1,k,d+4))=some (enc (a,k+1,d+3)) := by
  have h1 := high_start (pairs k (ones (a+1) zeros)) (ones d zeros)
  rw [←ones_add,←ones_add] at h1
  have h2 := b_left_pairs k (ones (a+1) zeros) (cons false (ones (3+d) zeros))
  have h3 := high_nonzero_finish k (ones a zeros) (ones (3+d) zeros)
  have hh := zRun_join (zRun_join h1 h2) h3
  change zRun (7+2*k+(2*k+2)) (enc (a+1,k,4+d))=some (enc (a,k+1,3+d)) at hh
  rwa [show 7+2*k+(2*k+2)=4*k+9 by omega,Nat.add_comm 4 d,Nat.add_comm 3 d] at hh

theorem high_even_rule (m d : Nat) :
    zRun (10*m+21) (enc (0,2*m,d+4))=some (enc (4*m+2,2,d+1)) := by
  have h1 := high_start (pairs (2*m) zeros) (ones d zeros)
  rw [←ones_add,←ones_add] at h1
  have h2 := b_left_pairs (2*m) zeros (cons false (ones (3+d) zeros))
  have h3 := high_zero_start (pairs (2*m) (cons false (ones (3+d) zeros)))
  have h4 := e_right_pairs m (ones 3 zeros) (cons false (ones (3+d) zeros))
  rw [←ones_add,show 4*m+3=(4*m+2)+1 by omega] at h4
  have h5 := high_even_finish (ones (4*m+2) zeros) (ones d zeros)
  rw [←ones_add] at h5
  have hh := zRun_join (zRun_join (zRun_join (zRun_join h1 h2) h3) h4) h5
  change zRun (7+2*(2*m)+5+6*m+9) (enc (0,2*m,4+d))=some (enc (4*m+2,2,d+1)) at hh
  rwa [show 7+2*(2*m)+5+6*m+9=10*m+21 by omega,Nat.add_comm 4 d] at hh

theorem high_odd_rule (m d : Nat) :
    zRun (10*m+18) (enc (0,2*m+1,d+4))=some (enc (4*m+5,0,d+4)) := by
  have h1 := high_start (pairs (2*m+1) zeros) (ones d zeros)
  rw [←ones_add,←ones_add] at h1
  have h2 := b_left_pairs (2*m+1) zeros (cons false (ones (3+d) zeros))
  have h3 := high_zero_start (pairs (2*m+1) (cons false (ones (3+d) zeros)))
  have h4 := e_right_pairs m (ones 3 zeros) (pairs 1 (cons false (ones (3+d) zeros)))
  rw [←pairs_add,←ones_add] at h4
  have h5 := high_odd_finish (ones (4*m+3) zeros) (ones d zeros)
  rw [←ones_add,←ones_add,←ones_add] at h5
  have hh := zRun_join (zRun_join (zRun_join (zRun_join h1 h2) h3) h4) h5
  change zRun (7+2*(2*m+1)+5+6*m+4) (enc (0,2*m+1,4+d))=some (enc (2+(4*m+3),0,4+d)) at hh
  rwa [show 7+2*(2*m+1)+5+6*m+4=10*m+18 by omega,show 2+(4*m+3)=4*m+5 by omega,Nat.add_comm 4 d] at hh

theorem zero_high_rule (a k : Nat) :
    zRun (2*k+4) (enc (a+2,k,0))=some (enc (a,1,2*k+1)) := by
  have h1 := zero_start (pairs k (ones (a+2) zeros)) zeros
  have h2 := c_left_pairs k (ones (a+2) zeros) (ones 1 zeros)
  rw [←ones_add] at h2
  have h3 := zero_high_finish (ones a zeros) (ones (2*k+1) zeros)
  rw [←ones_add,Nat.add_comm 2 a] at h3
  have hh := zRun_join (zRun_join h1 h2) h3
  change zRun (1+2*k+3) (enc (a+2,k,0))=some (enc (a,1,2*k+1)) at hh
  rwa [show 1+2*k+3=2*k+4 by omega] at hh

theorem zero_zero_rule (k : Nat) :
    zRun (2*k+3) (enc (0,k,0))=some (enc (1,0,2*k+2)) := by
  have h1 := zero_start (pairs k zeros) zeros
  have h2 := c_left_pairs k zeros (ones 1 zeros)
  rw [←ones_add] at h2
  have h3 := zero_zero_finish (ones (2*k+1) zeros)
  have hh := zRun_join (zRun_join h1 h2) h3
  change zRun (1+2*k+2) (enc (0,k,0))=some (enc (1,0,2*k+2)) at hh
  rwa [show 1+2*k+2=2*k+3 by omega] at hh

theorem zero_one_rule (k : Nat) :
    zRun (2*k+18) (enc (1,k+1,0))=some (enc (2,2,2*k+1)) := by
  have h1 := zero_start (pairs (k+1) (ones 1 zeros)) zeros
  have h2 := c_left_pairs (k+1) (ones 1 zeros) (ones 1 zeros)
  rw [←ones_add,show 2*(k+1)+1=3+2*k by omega,ones_add] at h2
  have h3 := zero_one_finish (ones (2*k) zeros)
  have hh := zRun_join (zRun_join h1 h2) h3
  change zRun (1+2*(k+1)+15) (enc (1,k+1,0))=some (enc (2,2,2*k+1)) at hh
  rwa [show 1+2*(k+1)+15=2*k+18 by omega] at hh


/-- Exact number of ordinary zipper-machine moves for every successful
    accelerator edge, with no restrictions on the natural counters. -/
theorem zrule_counted {s t : State} (h : nextC s=some t) :
    zRun (weight s) (enc s)=some (enc t) := by
  rcases s with ⟨a,k,c⟩
  rcases c with _|_|_|_|d
  · rcases a with _|_|a
    · simp only [nextC,Option.some.injEq] at h; subst t
      exact zero_zero_rule k
    · rcases k with _|k
      · simp only [nextC,Option.some.injEq] at h; subst t
        rfl
      · simp only [nextC,Option.some.injEq] at h; subst t
        exact zero_one_rule k
    · simp only [nextC,Option.some.injEq] at h; subst t
      exact zero_high_rule a k
  · simp only [nextC,Option.some.injEq] at h; subst t
    exact right_one_finish _
  · simp [nextC] at h
  · simp only [nextC,Option.some.injEq] at h; subst t
    exact right_three_finish _
  · rcases a with _|a
    · by_cases hk : k%2=0
      · obtain ⟨m,hm⟩ : ∃ m, k=2*m := ⟨k/2,by omega⟩
        subst k
        simp only [nextC,hk,↓reduceIte,Option.some.injEq] at h
        subst t
        simp only [weight,hk,↓reduceIte,show 2*m/2=m by omega]
        exact high_even_rule m d
      · obtain ⟨m,hm⟩ : ∃ m, k=2*m+1 := ⟨k/2,by omega⟩
        subst k
        simp only [nextC,hk,↓reduceIte,Option.some.injEq] at h
        subst t
        simp only [weight,hk,↓reduceIte,show (2*m+1)/2=m by omega]
        exact high_odd_rule m d
    · simp only [nextC,Option.some.injEq] at h; subst t
      exact high_nonzero_rule a k d

theorem zhalt_counted {s : State} (h : nextC s=none) :
    ∃ z, zRun (weight s) (enc s)=some z ∧ zStep z=none := by
  rcases s with ⟨a,k,c⟩
  rcases c with _|_|_|_|d
  · rcases a with _|_|a
    · simp [nextC] at h
    · rcases k <;> simp [nextC] at h
    · simp [nextC] at h
  · simp [nextC] at h
  · exact ⟨_,right_two_finish _,rfl⟩
  · simp [nextC] at h
  · rcases a with _|a
    · simp only [nextC] at h; split at h <;> contradiction
    · simp [nextC] at h

theorem path_zrun {n w : Nat} {s t : State} (p : Path n w s t) :
    zRun w (enc s)=some (enc t) := by
  induction p with
  | nil => rfl
  | cons h _ ih => exact zRun_join (zrule_counted h) ih

theorem zblank_prefix : zRun 12 (cr 0 zeros zeros)=some (enc (5,0,1)) := by rfl

#print axioms zrule_counted
#print axioms zhalt_counted
#print axioms path_zrun
#print axioms zblank_prefix

/-- Convert relative infinite streams to the exact Int-indexed physical tape
    used by the coverage contract. -/
def embed (h : Int) (z : Z) : Config :=
  ⟨z.q,h,fun x => if x<h then z.l (h-x-1).toNat else z.r (x-h).toNat⟩

theorem read_embed (h : Int) (z : Z) : readSlot (embed h z)=(z.q,hd z.r) := by
  simp [embed,hd]

theorem embed_move (h : Int) (z : Z) (m : Move) :
    applyMove (embed h z) m=embed (h+(if m.right then 1 else -1)) (zMove z m) := by
  rcases m with ⟨w,dir,q⟩
  cases dir
  · change (⟨q,h+(-1),fun x => if x=h then w else (embed h z).tape x⟩ : Config)=embed (h+(-1)) (cl q z.l (cons w (tl z.r)))
    congr 1
    funext x
    simp only [embed,cl,tl,hd]
    by_cases hlt : x<h-1
    · have hlt' : x<h := by omega
      have hne : x≠h := by omega
      have hnew : x<h+(-1) := by omega
      simp only [hne,↓reduceIte,hlt',hnew]
      congr 1
      omega
    · by_cases heq : x=h-1
      · subst x
        have hne : h-1≠h := by omega
        have hlt' : h-1<h := by omega
        have hnew : ¬h-1<h+(-1) := by omega
        simp only [hne,↓reduceIte,hlt',hnew]
        change z.l (h-(h-1)-1).toNat=cons (z.l 0) (cons w (fun n => z.r (n+1))) ((h-1-(h+(-1))).toNat)
        rw [show (h-(h-1)-1).toNat=0 by omega,show (h-1-(h+(-1))).toNat=0 by omega]
        rfl
      · by_cases he : x=h
        · subst x
          have hnew : ¬h<h+(-1) := by omega
          simp only [↓reduceIte,hnew,show (h-(h+(-1))).toNat=1 by omega]
          rfl
        · have hge : h<x := by omega
          have hlt' : ¬x<h := by omega
          have hnew : ¬x<h+(-1) := by omega
          simp only [he,↓reduceIte,hlt',hnew]
          have hx : (x-h).toNat = ((x-h-1).toNat)+1 := by omega
          have hy : (x-(h+(-1))).toNat = ((x-h-1).toNat)+2 := by omega
          rw [hx,hy]
          rfl
  · change (⟨q,h+1,fun x => if x=h then w else (embed h z).tape x⟩ : Config)=embed (h+1) (cr q (cons w z.l) (tl z.r))
    congr 1
    funext x
    simp only [embed,cr,tl]
    by_cases hlt : x<h
    · have hne : x≠h := by omega
      have hnew : x<h+1 := by omega
      simp only [hne,↓reduceIte,hlt,hnew]
      have hx : (h+1-x-1).toNat=(h-x-1).toNat+1 := by omega
      rw [hx]
      rfl
    · by_cases he : x=h
      · subst x
        have hnew : h<h+1 := by omega
        simp only [↓reduceIte,hnew,show (h+1-h-1).toNat=0 by omega]
        rfl
      · have hnew : ¬x<h+1 := by omega
        simp only [he,↓reduceIte,hlt,hnew]
        congr 1
        omega

theorem rawStep_embed_some (h : Int) (z z' : Z) (hs : zStep z=some z') :
    ∃ h', rawStep cMachine (embed h z)=some (embed h' z') := by
  unfold zStep at hs
  unfold rawStep
  rw [read_embed]
  cases hm : cMachine (z.q,hd z.r) with
  | none => simp [hm] at hs
  | some m =>
    simp only [hm,Option.map_some,Option.some.injEq] at hs
    subst z'
    refine ⟨h+(if m.right then 1 else -1),?_⟩
    simp only [Option.map_some,Option.some.injEq]
    exact embed_move h z m

theorem rawStep_embed_none (h : Int) (z : Z) (hs : zStep z=none) :
    rawStep cMachine (embed h z)=none := by
  unfold rawStep
  rw [read_embed]
  cases hm : cMachine (z.q,hd z.r) with
  | none => rfl
  | some m => simp [zStep,hm] at hs

theorem raw_run_join (m : Machine) {n k : Nat} {s t u : Config}
    (h : run m n s=some t) (g : run m k t=some u) : run m (n+k) s=some u := by
  induction k generalizing u with
  | zero => simp [run] at g; subst u; simpa using h
  | succ k ih =>
    cases hk : run m k t with
    | none => simp [run,hk] at g
    | some t' =>
      have hh := ih hk
      have he : rawStep m t'=some u := by simpa [run,hk] using g
      simp [run,hh,he]

theorem zrun_to_raw {n : Nat} {z t : Z} (hs : zRun n z=some t) (h : Int) :
    ∃ h', run cMachine n (embed h z)=some (embed h' t) := by
  induction n generalizing z h with
  | zero =>
    simp [zRun] at hs; subst t; exact ⟨h,rfl⟩
  | succ n ih =>
    cases hz : zStep z with
    | none => simp [zRun,hz] at hs
    | some u =>
      obtain ⟨h',h'run⟩ := rawStep_embed_some h z u hz
      have hh : zRun n u=some t := by simpa [zRun,hz] using hs
      obtain ⟨h'',h''run⟩ := ih hh h'
      have h1 : run cMachine 1 (embed h z)=some (embed h' u) := by simpa [run] using h'run
      refine ⟨h'',?_⟩
      have hr := raw_run_join cMachine h1 h''run
      rwa [show 1+n=n+1 by omega] at hr


/-- Every successful counted path is an exact raw execution on the
    original literal 12-entry machine. -/
theorem raw_path {n w : Nat} {s t : State} (p : Path n w s t) (h : Int) :
    ∃ h', run cMachine w (embed h (enc s))=some (embed h' (enc t)) :=
  zrun_to_raw (path_zrun p) h

theorem raw_halt_from {s : State} (hs : nextC s=none) (h : Int) :
    ∃ d, run cMachine (weight s) (embed h (enc s))=some d ∧ rawStep cMachine d=none := by
  obtain ⟨z,hz,hstop⟩ := zhalt_counted hs
  obtain ⟨h',hr⟩ := zrun_to_raw hz h
  exact ⟨_,hr,rawStep_embed_none h' z hstop⟩

theorem halt_weight {s : State} (h : nextC s=none) : weight s=3 := by
  rcases s with ⟨a,k,c⟩
  rcases c with _|_|_|_|d
  · rcases a with _|_|a
    · simp [nextC] at h
    · rcases k <;> simp [nextC] at h
    · simp [nextC] at h
  · simp [nextC] at h
  · rfl
  · simp [nextC] at h
  · rcases a with _|a
    · simp only [nextC] at h; split at h <;> contradiction
    · simp [nextC] at h

theorem blank_embed : embed 0 (cr 0 zeros zeros)=blank := by
  unfold embed blank cr
  congr 1
  funext x
  simp [zeros]

theorem raw_blank_path {n w : Nat} {t : State} (p : Path n w (5,0,1) t) :
    ∃ h, run cMachine (12+w) blank=some (embed h (enc t)) := by
  obtain ⟨h,hp⟩ := zrun_to_raw zblank_prefix 0
  obtain ⟨h',hr⟩ := raw_path p h
  exact ⟨h',by rw [←blank_embed]; exact raw_run_join cMachine hp hr⟩

theorem raw_halting_score {n w : Nat} {t : State} (p : Path n w (5,0,1) t)
    (ht : nextC t=none) : HaltsAfter cMachine (15+w) := by
  obtain ⟨h,hp⟩ := raw_blank_path p
  obtain ⟨d,hd,hs⟩ := raw_halt_from ht h
  rw [halt_weight ht] at hd
  have hr := raw_run_join cMachine hp hd
  rw [show 12+w+3=15+w by omega] at hr
  exact ⟨by simp [hr],by simp [run,hr,hs]⟩

theorem weight_pos (s : State) : 1≤weight s := by
  rcases s with ⟨a,k,c⟩
  rcases c with _|_|_|_|d
  · rcases a with _|_|a
    · simp [weight]
    · rcases k <;> simp [weight] <;> omega
    · simp [weight]
  · simp [weight]
  · simp [weight]
  · simp [weight]
  · rcases a with _|a
    · simp only [weight]; split <;> omega
    · simp [weight]

theorem Path.weight_ge {n w : Nat} {s t : State} (p : Path n w s t) : n≤w := by
  induction p with
  | nil => decide
  | @cons n w s t u h p ih => have hw := weight_pos s; omega

/-- A path of prescribed accelerator length exists unless a shorter
    genuine path ends at a stopping state. -/
theorem path_or_stop (n : Nat) (s : State) :
    (∃ w t, Path n w s t) ∨
    (∃ m w t, m<n ∧ Path m w s t ∧ nextC t=none) := by
  induction n generalizing s with
  | zero => exact Or.inl ⟨0,s,Path.nil s⟩
  | succ n ih =>
    cases h : nextC s with
    | none => exact Or.inr ⟨0,0,s,by omega,Path.nil _,h⟩
    | some u =>
      rcases ih u with ⟨w,t,p⟩ | ⟨m,w,t,hm,p,ht⟩
      · exact Or.inl ⟨_,_,Path.cons h p⟩
      · exact Or.inr ⟨_,_,_,by omega,Path.cons h p,ht⟩

/-- Exact raw-score correspondence, including the reverse direction.
    The successful ordinary-move count is 15+w; standard Busy Beaver
    score adds one for the terminal halting query, hence 16+w. -/
theorem raw_haltsAfter_iff (N : Nat) : HaltsAfter cMachine N ↔
    ∃ n w t, Path n w (5,0,1) t ∧ nextC t=none ∧ N=15+w := by
  constructor
  · intro h
    rcases path_or_stop (N+1) (5,0,1) with ⟨w,t,p⟩ | ⟨n,w,t,hn,p,ht⟩
    · have hw := Path.weight_ge p
      obtain ⟨h',hr⟩ := raw_blank_path p
      have hnone := run_none_add cMachine blank (N+1) (12+w-(N+1)) h.2
      rw [show N+1+(12+w-(N+1))=12+w by omega,hr] at hnone
      contradiction
    · exact ⟨n,w,t,p,ht,halting_time_unique _ _ _ h (raw_halting_score p ht)⟩
  · rintro ⟨n,w,t,p,ht,rfl⟩
    exact raw_halting_score p ht

/-- Quantitative form of the high-family conditional certificate. -/
theorem high_blank_score (j m q k n w : Nat)
    (hj : j+2=2^(2*m)*(q+3)) (hk : k+q+3*m+5=4*(j+2))
    (p : Path n w (5,0,1) (2*q+3,k,0)) :
    ∃ v, HaltsAfter cMachine (15+w+v) ∧ Attainable (16+w+v) ∧
      3*v+21+102*m+8*(2*q+6)*(2*q+6)+39*(2*j+4)=
      3*(2*(2*q+2)*(2*q+2)+8*(2*q+2)+(2*k-2*q))+
        8*(2*j+4)*(2*j+4)+39*(2*q+6)+3*(32*j*j+122*j+100) := by
  obtain ⟨l,v,ht,hl,hv⟩ := high_stop_counted j m q k hj hk
  have hr := raw_halting_score (p.append ht) (by rfl)
  rw [←Nat.add_assoc] at hr
  exact ⟨v,hr,⟨cMachine,15+w+v,hr,by omega⟩,hv⟩

/-- Quantitative form of the exceptional low-family conditional certificate. -/
theorem low_blank_score (j m k n w : Nat) (hm : 1≤m)
    (hj : j+2=2^(2*m+1)) (hk : k+3*m+4=4*(j+2))
    (p : Path n w (5,0,1) (1,k,0)) :
    ∃ v, HaltsAfter cMachine (15+w+v) ∧ Attainable (16+w+v) ∧
      3*v+51*(2*m-1)+8*8*8+39*(2*j+4)=
      3*(2*k-3+57)+8*(2*j+4)*(2*j+4)+39*8+3*(32*j*j+122*j+100) := by
  obtain ⟨l,v,ht,hl,hv⟩ := low_stop_counted j m k hm hj hk
  have hr := raw_halting_score (p.append ht) (by rfl)
  rw [←Nat.add_assoc] at hr
  exact ⟨v,hr,⟨cMachine,15+w+v,hr,by omega⟩,hv⟩

#print axioms embed_move
#print axioms raw_path
#print axioms raw_haltsAfter_iff
#print axioms high_blank_score
#print axioms low_blank_score

open BB6.Agent47ThinExact

theorem path_reach {n w : Nat} {s t : State} (p : Path n w s t) (hs : Reach s) : Reach t := by
  induction p with
  | nil => exact hs
  | cons h _ ih => exact ih (Reach.next _ _ hs h)

theorem reach_path {s : State} (h : Reach s) : ∃ n w, Path n w (5,0,1) s := by
  induction h with
  | init => exact ⟨0,0,Path.nil _⟩
  | next s t _ h ih =>
    obtain ⟨n,w,p⟩ := ih
    exact ⟨_,_,p.append (Path.cons h (Path.nil t))⟩

/-- An exact score certificate for a candidate in the high stopping family. -/
def HighCertificate (N : Nat) : Prop :=
  ∃ j m q k n w v : Nat,
    j+2=2^(2*m)*(q+3) ∧ k+q+3*m+5=4*(j+2) ∧
    Path n w (5,0,1) (2*q+3,k,0) ∧ N=15+w+v ∧
    3*v+21+102*m+8*(2*q+6)*(2*q+6)+39*(2*j+4)=
      3*(2*(2*q+2)*(2*q+2)+8*(2*q+2)+(2*k-2*q))+
        8*(2*j+4)*(2*j+4)+39*(2*q+6)+3*(32*j*j+122*j+100)

/-- An exact score certificate for a candidate in the exceptional low family. -/
def LowCertificate (N : Nat) : Prop :=
  ∃ j m k n w v : Nat,
    1≤m ∧ j+2=2^(2*m+1) ∧ k+3*m+4=4*(j+2) ∧
    Path n w (5,0,1) (1,k,0) ∧ N=15+w+v ∧
    3*v+51*(2*m-1)+8*8*8+39*(2*j+4)=
      3*(2*k-3+57)+8*(2*j+4)*(2*j+4)+39*8+3*(32*j*j+122*j+100)

/-- Complete iff for the historical Machine C's exact score, reducing the
    only unresolved obligation to a weighted blank-prefix certificate in
    one of the two explicit stopping families. -/
theorem raw_haltsAfter_iff_families (N : Nat) :
    HaltsAfter cMachine N ↔ HighCertificate N ∨ LowCertificate N := by
  constructor
  · intro h
    obtain ⟨n,w,t,p,ht,_⟩ := (raw_haltsAfter_iff N).mp h
    obtain ⟨j,hj⟩ := stops_iff_thin.mp ⟨t,path_reach p Reach.init,ht⟩
    rcases (thin_reach_iff j).mp hj with ⟨m,q,k,h1,h2,hr⟩ | ⟨m,k,hm,h1,h2,hr⟩
    · obtain ⟨l,u,pp⟩ := reach_path hr
      obtain ⟨v,hv,_,hv'⟩ := high_blank_score j m q k l u h1 h2 pp
      exact Or.inl ⟨j,m,q,k,l,u,v,h1,h2,pp,halting_time_unique _ _ _ h hv,hv'⟩
    · obtain ⟨l,u,pp⟩ := reach_path hr
      obtain ⟨v,hv,_,hv'⟩ := low_blank_score j m k l u hm h1 h2 pp
      exact Or.inr ⟨j,m,k,l,u,v,hm,h1,h2,pp,halting_time_unique _ _ _ h hv,hv'⟩
  · rintro (⟨j,m,q,k,n,w,v,h1,h2,p,rfl,hv⟩ | ⟨j,m,k,n,w,v,hm,h1,h2,p,rfl,hv⟩)
    · obtain ⟨v',h,_,hv'⟩ := high_blank_score j m q k n w h1 h2 p
      have he : v=v' := by omega
      rwa [←he] at h
    · obtain ⟨v',h,_,hv'⟩ := low_blank_score j m k n w hm h1 h2 p
      have he : v=v' := by omega
      rwa [←he] at h

#print axioms raw_haltsAfter_iff_families
end BB6.Agent47CRaw
