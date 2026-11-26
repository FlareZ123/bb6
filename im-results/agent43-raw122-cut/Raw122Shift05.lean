import PackedSweep122
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace BB6Coverage.Agent43Raw122Shift05
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper BB6Coverage.Agent29PackedRun

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

-- Exact partial prefix transducer, on little-endian natural tape words.
inductive R : Nat → Nat → Prop where
  | stop0 (x : Nat) : R (16*x) (16*x+8)
  | stop11 (x : Nat) : R (4*x+3) (4*x+1)
  | stop0011 (x : Nat) : R (16*x+12) (16*x)
  | stop00011 (x : Nat) : R (32*x+24) (32*x+4)
  | cont10 {x y : Nat} : R x y → R (4*x+1) (4*y+1)
  | cont0010 {x y : Nat} : R x y → R (16*x+4) (16*y)
  | cont00010 {x y : Nat} : R x y → R (32*x+8) (32*y+4)

def S (s : Nat) (x y : Nat) : Prop := R (2^s*x) (2^s*y)

inductive Chain (r : Nat → Nat → Prop) : Nat → Nat → Nat → Prop where
  | nil (x : Nat) : Chain r 0 x x
  | cons {n x y z : Nat} : r x y → Chain r n y z → Chain r (n+1) x z

theorem Chain.append {r : Nat → Nat → Prop} {n k x y z : Nat}
    (p : Chain r n x y) (q : Chain r k y z) : Chain r (n+k) x z := by
  induction p with
  | nil => simpa using q
  | @cons n x y z h _ ih =>
    rw [show n+1+k = n+k+1 by omega]
    exact .cons h (ih q)

theorem triple {r : Nat → Nat → Prop} {a b c d : Nat}
    (h1 : r a b) (h2 : r b c) (h3 : r c d) : Chain r 3 a d :=
  .cons h1 (.cons h2 (.cons h3 (.nil d)))

theorem expand {r t : Nat → Nat → Prop} (f : Nat → Nat)
    (h : ∀ x y, r x y → Chain t 3 (f x) (f y))
    {n x y : Nat} (p : Chain r n x y) : Chain t (3*n) (f x) (f y) := by
  induction p with
  | nil x => exact .nil (f x)
  | @cons n x y z hxy _ ih =>
    have hp := Chain.append (h x y hxy) ih
    rw [show 3*(n+1)=3+3*n by omega]
    exact hp

-- Three shifted phases.  The third phase wraps through a four-bit block.
theorem step0a (x : Nat) : S 0 (32*x) (32*x+8) := by
  simp only [S,Nat.pow_zero,Nat.one_mul]
  have h := R.stop0 (2*x)
  rw [show 16*(2*x)=32*x by omega] at h
  exact h
theorem step0b {x y : Nat} (h : S 0 x y) : S 0 (32*x+8) (32*y+4) := by
  simpa [S] using R.cont00010 (show R x y by simpa [S] using h)
theorem step0c {x y : Nat} (h : S 1 x y) : S 0 (32*x+4) (32*y) := by
  simp only [S,Nat.pow_zero,Nat.one_mul]
  change R (2*x) (2*y) at h
  have H := R.cont0010 h
  rw [show 16*(2*x)=32*x by omega,show 16*(2*y)=32*y by omega] at H
  exact H

theorem step1a (x : Nat) : S 1 (32*x) (32*x+4) := by
  change R (2*(32*x)) (2*(32*x+4))
  have H := R.stop0 (4*x)
  rw [show 16*(4*x)=2*(32*x) by omega,show 2*(32*x)+8=2*(32*x+4) by omega] at H
  exact H
theorem step1b {x y : Nat} (h : S 1 x y) : S 1 (32*x+4) (32*y+2) := by
  change R (2*x) (2*y) at h
  change R (2*(32*x+4)) (2*(32*y+2))
  have H := R.cont00010 h
  rw [show 32*(2*x)+8=2*(32*x+4) by omega,show 32*(2*y)+4=2*(32*y+2) by omega] at H
  exact H
theorem step1c {x y : Nat} (h : S 2 x y) : S 1 (32*x+2) (32*y) := by
  change R (4*x) (4*y) at h
  change R (2*(32*x+2)) (2*(32*y))
  have H := R.cont0010 h
  rw [show 16*(4*x)+4=2*(32*x+2) by omega,show 16*(4*y)=2*(32*y) by omega] at H
  exact H

theorem step2a (x : Nat) : S 2 (32*x) (32*x+2) := by
  change R (4*(32*x)) (4*(32*x+2))
  have H := R.stop0 (8*x)
  rw [show 16*(8*x)=4*(32*x) by omega,show 4*(32*x)+8=4*(32*x+2) by omega] at H
  exact H
theorem step2b {x y : Nat} (h : S 2 x y) : S 2 (32*x+2) (32*y+1) := by
  change R (4*x) (4*y) at h
  change R (4*(32*x+2)) (4*(32*y+1))
  have H := R.cont00010 h
  rw [show 32*(4*x)+8=4*(32*x+2) by omega,show 32*(4*y)+4=4*(32*y+1) by omega] at H
  exact H
theorem step2c {x y : Nat} (h : S 3 x y) : S 2 (32*x+1) (32*y) := by
  change R (8*x) (8*y) at h
  change R (4*(32*x+1)) (4*(32*y))
  have H := R.cont0010 h
  rw [show 16*(8*x)+4=4*(32*x+1) by omega,show 16*(8*y)=4*(32*y) by omega] at H
  exact H

theorem shift1 (x : Nat) : S 1 (32*x) (32*x+4) := step1a x
theorem shift2 (x : Nat) : S 2 (32*x) (32*x+2) := step2a x
theorem shift3 (x : Nat) : S 3 (16*x) (16*x+1) := by
  change R (8*(16*x)) (8*(16*x+1))
  have H := R.stop0 (8*x)
  rw [show 16*(8*x)=8*(16*x) by omega,show 8*(16*x)+8=8*(16*x+1) by omega] at H
  exact H

theorem wrap2 {x y : Nat} (h : S 2 x y) : S 2 (16*x+1) (16*y) := by
  change R (4*x) (4*y) at h
  change R (4*(16*x+1)) (4*(16*y))
  have H := R.cont0010 h
  rw [show 16*(4*x)+4=4*(16*x+1) by omega,show 16*(4*y)=4*(16*y) by omega] at H
  exact H

theorem lift0 (x y : Nat) (h : S 1 x y) :
    Chain (S 0) 3 (32*(32*x+4)) (32*(32*y+4)) :=
  triple (step0a (32*x+4)) (step0b (step0c h)) (step0c (shift1 y))
theorem lift1 (x y : Nat) (h : S 2 x y) :
    Chain (S 1) 3 (32*(32*x+2)) (32*(32*y+2)) :=
  triple (step1a (32*x+2)) (step1b (step1c h)) (step1c (shift2 y))
theorem lift2 (x y : Nat) (h : S 2 x y) :
    Chain (S 2) 3 (32*(16*x+1)) (32*(16*y+1)) :=
  triple (step2a (16*x+1)) (step2b (wrap2 h)) (step2c (shift3 y))

theorem seed1 : Chain (S 1) 6 0 64 := by
  have h1 : S 1 0 4 := step1a 0
  have h2 : S 1 4 130 := step1b h1
  have h3 : S 1 130 192 := step1c (show S 2 4 6 from R.stop0 1)
  have h4 : S 1 192 196 := step1a 6
  have h5 : S 1 196 2 := step1b (show S 1 6 0 from R.stop0011 0)
  have h6 : S 1 2 64 := step1c (show S 2 0 2 from R.stop0 0)
  exact .cons h1 (.cons h2 (.cons h3 (.cons h4 (.cons h5 (.cons h6 (.nil _))))))
theorem seed2 : Chain (S 2) 6 0 32 := by
  have h1 : S 2 0 2 := step2a 0
  have h2 : S 2 2 65 := step2b h1
  have h3 : S 2 65 96 := step2c (show S 3 2 3 from R.stop0 1)
  have h4 : S 2 96 98 := step2a 3
  have h5 : S 2 98 1 := step2b (show S 2 3 0 from R.stop0011 0)
  have h6 : S 2 1 32 := step2c (show S 3 0 1 from R.stop0 0)
  exact .cons h1 (.cons h2 (.cons h3 (.cons h4 (.cons h5 (.cons h6 (.nil _))))))

-- The self-lift grows every finite phase-2 path to a strictly longer path.
theorem phase2 (n : Nat) : ∃ k y, n ≤ k ∧ Chain (S 2) k 0 y := by
  induction n with
  | zero => exact ⟨0,0,by omega,.nil 0⟩
  | succ n ih =>
    obtain ⟨k,y,hk,hp⟩ := ih
    have H := expand (fun x => 32*(16*x+1)) lift2 hp
    exact ⟨6+3*k,32*(16*y+1),by omega,Chain.append seed2 H⟩
theorem phase1 (n : Nat) : ∃ k y, n ≤ k ∧ Chain (S 1) k 0 y := by
  obtain ⟨k,y,hk,hp⟩ := phase2 n
  have H := expand (fun x => 32*(32*x+2)) lift1 hp
  exact ⟨6+3*k,32*(32*y+2),by omega,Chain.append seed1 H⟩
theorem phase0 (n : Nat) : ∃ k y, n ≤ k ∧ Chain (S 0) k 4 y := by
  obtain ⟨k,y,hk,hp⟩ := phase1 n
  have H := expand (fun x => 32*(32*x+4)) lift0 hp
  have h : S 0 4 128 := R.cont0010 (R.stop0 0)
  exact ⟨3*k+1,32*(32*y+4),by omega,.cons h H⟩

-- Transport arbitrary-tail local computations into the packed semantics.
theorem frame (k : Nat) (q q' : Fin 6) (lp rp lp' rp' : List Bool)
    (h : ∀ L R : List Bool, run0 table k ⟨q,lp++L,rp++R⟩ = some ⟨q',lp'++L,rp'++R⟩)
    (L R : Nat) : prun table k (pzip q lp rp L R) = some (pzip q' lp' rp' L R) := by
  obtain ⟨ls,hl⟩ := pack_surj L
  obtain ⟨rs,hr⟩ := pack_surj R
  have H := (enc_run table k ⟨q,lp++ls,rp++rs⟩).symm.trans (congrArg (Option.map enc) (h ls rs))
  simpa only [enc,Option.map_some,pzip,prepend,pack_append,hl,hr] using H

theorem stop0_run (L x : Nat) : prun table 11 ⟨4,2*L,16*x⟩ = some ⟨5,L,2*(16*x+8)⟩ := by
  have H := frame 11 4 5 [false] [false,false,false,false] [] [false,false,false,false,true] (by intro L R; rfl) L x
  simpa [pzip,prepend,pack,Bool.toNat,Nat.mul_add,← Nat.mul_assoc,Nat.add_comm] using H
theorem stop11_run (L x : Nat) : prun table 5 ⟨4,2*L,4*x+3⟩ = some ⟨5,L,2*(4*x+1)⟩ := by
  have H := frame 5 4 5 [false] [true,true] [] [false,true,false] (by intro L R; rfl) L x
  simpa [pzip,prepend,pack,Bool.toNat,Nat.mul_add,← Nat.mul_assoc,Nat.add_comm] using H
theorem stop0011_run (L x : Nat) : prun table 9 ⟨4,2*L,16*x+12⟩ = some ⟨5,L,2*(16*x)⟩ := by
  have H := frame 9 4 5 [false] [false,false,true,true] [] [false,false,false,false,false] (by intro L R; rfl) L x
  simpa [pzip,prepend,pack,Bool.toNat,Nat.mul_add,← Nat.mul_assoc,Nat.add_comm] using H
theorem stop00011_run (L x : Nat) : prun table 11 ⟨4,2*L,32*x+24⟩ = some ⟨5,L,2*(32*x+4)⟩ := by
  have H := frame 11 4 5 [false] [false,false,false,true,true] [] [false,false,false,true,false,false] (by intro L R; rfl) L x
  simpa [pzip,prepend,pack,Bool.toNat,Nat.mul_add,← Nat.mul_assoc,Nat.add_comm] using H
theorem push10 (L x : Nat) : prun table 2 ⟨4,2*L,4*x+1⟩ = some ⟨4,2*(4*L+2),x⟩ := by
  have H := frame 2 4 4 [false] [true,false] [false,false,true] [] (by intro L R; rfl) L x
  simpa [pzip,prepend,pack,Bool.toNat,Nat.mul_add,← Nat.mul_assoc,Nat.add_comm] using H
theorem pop10 (L x : Nat) : prun table 2 ⟨5,4*L+2,2*x⟩ = some ⟨5,L,2*(4*x+1)⟩ := by
  have H := frame 2 5 5 [false,true] [false] [] [false,true,false] (by intro L R; rfl) L x
  simpa [pzip,prepend,pack,Bool.toNat,Nat.mul_add,← Nat.mul_assoc,Nat.add_comm] using H
theorem push0010 (L x : Nat) : prun table 4 ⟨4,2*L,16*x+4⟩ = some ⟨4,2*(16*L+15),x⟩ := by
  have H := frame 4 4 4 [false] [false,false,true,false] [false,true,true,true,true] [] (by intro L R; rfl) L x
  simpa [pzip,prepend,pack,Bool.toNat,Nat.mul_add,← Nat.mul_assoc,Nat.add_comm] using H
theorem pop0010 (L x : Nat) : prun table 4 ⟨5,16*L+15,2*x⟩ = some ⟨5,L,2*(16*x)⟩ := by
  have H := frame 4 5 5 [true,true,true,true] [false] [] [false,false,false,false,false] (by intro L R; rfl) L x
  simpa [pzip,prepend,pack,Bool.toNat,Nat.mul_add,← Nat.mul_assoc,Nat.add_comm] using H
theorem push00010 (L x : Nat) : prun table 5 ⟨4,2*L,32*x+8⟩ = some ⟨4,2*(32*L+29),x⟩ := by
  have H := frame 5 4 4 [false] [false,false,false,true,false] [false,true,false,true,true,true] [] (by intro L R; rfl) L x
  simpa [pzip,prepend,pack,Bool.toNat,Nat.mul_add,← Nat.mul_assoc,Nat.add_comm] using H
theorem pop00010 (L x : Nat) : prun table 5 ⟨5,32*L+29,2*x⟩ = some ⟨5,L,2*(32*x+4)⟩ := by
  have H := frame 5 5 5 [true,false,true,true,true] [false] [] [false,false,false,true,false,false] (by intro L R; rfl) L x
  simpa [pzip,prepend,pack,Bool.toNat,Nat.mul_add,← Nat.mul_assoc,Nat.add_comm] using H

theorem core_sound {x y : Nat} (h : R x y) (L : Nat) :
    ∃ k, 0 < k ∧ prun table k ⟨4,2*L,x⟩ = some ⟨5,L,2*y⟩ := by
  induction h generalizing L with
  | stop0 x => exact ⟨11,by decide,stop0_run L x⟩
  | stop11 x => exact ⟨5,by decide,stop11_run L x⟩
  | stop0011 x => exact ⟨9,by decide,stop0011_run L x⟩
  | stop00011 x => exact ⟨11,by decide,stop00011_run L x⟩
  | @cont10 x y h ih =>
    obtain ⟨k,hk,hp⟩ := ih (4*L+2)
    exact ⟨2+k+2,by omega,pjoin (pjoin (push10 L x) hp) (pop10 L y)⟩
  | @cont0010 x y h ih =>
    obtain ⟨k,hk,hp⟩ := ih (16*L+15)
    exact ⟨4+k+4,by omega,pjoin (pjoin (push0010 L x) hp) (pop0010 L y)⟩
  | @cont00010 x y h ih =>
    obtain ⟨k,hk,hp⟩ := ih (32*L+29)
    exact ⟨5+k+5,by omega,pjoin (pjoin (push00010 L x) hp) (pop00010 L y)⟩

abbrev I : List Bool := [true,false]
abbrev O : List Bool := [false,true]

def frontList (k : Nat) (r : List Bool) : Z0 := ⟨4,[],rep I (k+1) ++ r⟩

theorem scanList (k : Nat) (r : List Bool) :
    run0 table (2+2*k) (frontList k r) = some ⟨4,false :: rep O (k+1),r⟩ := by
  have h1 : run0 table 2 (frontList k r) = some ⟨4,[false] ++ O,rep I k ++ r⟩ := by rfl
  have h2 := sweepR table 4 [false] [] I O 2 (by intro L R; rfl) k O r
  have h2' : run0 table (2*k) ⟨4,[false] ++ O,rep I k ++ r⟩ = some ⟨4,false :: rep O (k+1),r⟩ := by
    rw [show rep O (k+1) = rep O k ++ O by rw [rep,rep_snoc]]
    simpa only [List.nil_append,List.singleton_append,List.cons_append] using h2
  exact join0 h1 h2'

theorem finishList (k : Nat) (r : List Bool) :
    run0 table (2*(k+1)+1) ⟨5,rep O (k+1),false::r⟩ = some (frontList (k+1) r) := by
  have h1 := sweepL table 5 [] [] O O 2 (by intro L R; rfl) (k+1) [] (false::r)
  have h1' : run0 table (2*(k+1)) ⟨5,rep O (k+1),false::r⟩ = some ⟨5,[],rep O (k+1) ++ [false] ++ r⟩ := by
    simpa only [List.nil_append,List.append_nil,List.append_assoc,List.singleton_append] using h1
  have h2 : run0 table 1 ⟨5,[],rep O (k+1) ++ [false] ++ r⟩ = some (frontList (k+1) r) := by
    have h : [true] ++ rep O (k+1) = rep I (k+1) ++ [true] := rotate true [false] (k+1)
    have hs : run0 table 1 ⟨5,[],rep O (k+1) ++ [false] ++ r⟩ =
        some ⟨4,[],[true] ++ rep O (k+1) ++ [false] ++ r⟩ := by rfl
    have he : [true] ++ rep O (k+1) ++ [false] ++ r = rep I (k+2) ++ r := by
      rw [h,show rep I (k+2) = rep I (k+1) ++ I by rw [rep,rep_snoc]]
      simp only [List.append_assoc]
      rfl
    rw [he] at hs
    exact hs
  exact join0 h1' h2

def front (k x : Nat) : PZ := ⟨4,0,prepend (rep I (k+1)) x⟩

theorem scan (k x : Nat) : prun table (2+2*k) (front k x) = some ⟨4,2*pack (rep O (k+1)),x⟩ := by
  obtain ⟨r,hr⟩ := pack_surj x
  have H := (enc_run table (2+2*k) (frontList k r)).symm.trans (congrArg (Option.map enc) (scanList k r))
  simpa [enc,frontList,front,prepend,pack_append,pack,hr,Bool.toNat] using H

theorem finish (k x : Nat) : prun table (2*(k+1)+1) ⟨5,pack (rep O (k+1)),2*x⟩ = some (front (k+1) x) := by
  obtain ⟨r,hr⟩ := pack_surj x
  have H := (enc_run table (2*(k+1)+1) ⟨5,rep O (k+1),false::r⟩).symm.trans (congrArg (Option.map enc) (finishList k r))
  simpa [enc,frontList,front,prepend,pack_append,pack,hr,Bool.toNat] using H

theorem front_step {x y : Nat} (h : R x y) (k : Nat) :
    ∃ d, 0 < d ∧ prun table d (front k x) = some (front (k+1) y) := by
  obtain ⟨d,hd,hp⟩ := core_sound h (pack (rep O (k+1)))
  exact ⟨(2+2*k)+d+(2*(k+1)+1),by omega,pjoin (pjoin (scan k x) hp) (finish k y)⟩

theorem chain_run {n x y : Nat} (p : Chain (S 0) n x y) (k : Nat) :
    ∃ d, n ≤ d ∧ prun table d (front k x) = some (front (k+n) y) := by
  induction p generalizing k with
  | nil x => exact ⟨0,by omega,rfl⟩
  | @cons n x y z h _ ih =>
    have hR : R x y := by simpa [S] using h
    obtain ⟨d,hd,hp⟩ := front_step hR k
    obtain ⟨e,he,hq⟩ := ih (k+1)
    refine ⟨d+e,by omega,?_⟩
    rw [show k+(n+1)=k+1+n by omega]
    exact pjoin hp hq

theorem entry : prun table 10 ⟨0,0,0⟩ = some (front 0 4) := by rfl

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨k,y,hk,hpath⟩ := phase0 n
  obtain ⟨d,hd,hp⟩ := chain_run hpath 0
  have H := pjoin entry hp
  have H0 := (enc_run table (10+d) ⟨0,[],[]⟩).trans H
  have J := run_project table (10+d) start
  change (zrun table (10+d) start).map project = run0 table (10+d) ⟨0,[],[]⟩ at J
  rw [← J,Option.map_map] at H0
  cases hs : zrun table (10+d) start with
  | none => simp [hs] at H0
  | some z =>
    have hr := zrun_sound table m hm (10+d) start z hs
    rw [start_embed,show 10+d=n+(10+d-n) by omega,run_append] at hr
    change (run m n blank).bind (run m (10+d-n)) = some (embed z) at hr
    cases hh : run m n blank with
    | none =>
      change (run m n blank).bind (run m (10+d-n)) = some (embed z) at hr
      rw [hh] at hr
      simp at hr
    | some c => rfl

#print axioms phase0
#print axioms core_sound
#print axioms never
end BB6Coverage.Agent43Raw122Shift05
