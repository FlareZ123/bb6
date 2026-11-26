import Raw122Shift05
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace BB6Coverage.Agent43Raw122AHole05
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper BB6Coverage.Agent29PackedRun

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

open BB6Coverage.Agent43Raw122Shift05 (Chain triple expand)

inductive R : Nat → Nat → Prop where
  | stop0 (x : Nat) : R (8*x) (8*x+4)
  | stop011 (x : Nat) : R (8*x+6) (8*x)
  | stop0011 (x : Nat) : R (16*x+12) (16*x+2)
  | cont10 {x y : Nat} : R x y → R (4*x+1) (4*y+1)
  | cont010 {x y : Nat} : R x y → R (8*x+2) (8*y)
  | cont0010 {x y : Nat} : R x y → R (16*x+4) (16*y+2)

-- One partial transducer step becomes three steps at the next scale.
theorem lift (x y : Nat) (h : R x y) : Chain R 3 (128*x+2) (128*y+2) := by
  have h1 := R.cont010 (R.stop0 (2*x))
  have h2 := R.stop0 (16*x+4)
  have h3 := R.cont0010 (R.cont010 h)
  rw [show 8*(8*(2*x))+2=128*x+2 by omega,show 8*(8*(2*x)+4)=128*x+32 by omega] at h1
  rw [show 8*(16*x+4)=128*x+32 by omega,show 128*x+32+4=128*x+36 by omega] at h2
  rw [show 16*(8*x+2)+4=128*x+36 by omega,show 16*(8*y)+2=128*y+2 by omega] at h3
  exact triple h1 h2 h3

theorem seed : Chain R 4 4 2 := by
  have h1 : R 4 66 := R.cont0010 (R.stop0 0)
  have h2 : R 66 96 := R.cont010 (R.stop0 1)
  have h3 : R 96 100 := R.stop0 12
  have h4 : R 100 2 := R.cont0010 (R.stop011 0)
  exact .cons h1 (.cons h2 (.cons h3 (.cons h4 (.nil _))))

theorem long0 (n : Nat) : ∃ k y, n ≤ k ∧ Chain R k 0 y := by
  induction n with
  | zero => exact ⟨0,0,by omega,.nil 0⟩
  | succ n ih =>
    obtain ⟨k,y,hk,hp⟩ := ih
    have H := expand (fun x => 128*x+2) lift hp
    have hseed : Chain R 5 0 2 := .cons (R.stop0 0) seed
    exact ⟨5+3*k,128*y+2,by omega,hseed.append H⟩

theorem long4 (n : Nat) : ∃ k y, n ≤ k ∧ Chain R k 4 y := by
  obtain ⟨k,y,hk,hp⟩ := long0 n
  have H := expand (fun x => 128*x+2) lift hp
  exact ⟨4+3*k,128*y+2,by omega,seed.append H⟩

def state (a : Bool) : Fin 6 := if a then 0 else 4

theorem frame (k : Nat) (q q' : Fin 6) (lp rp lp' rp' : List Bool)
    (h : ∀ L R : List Bool, run0 table k ⟨q,lp++L,rp++R⟩ = some ⟨q',lp'++L,rp'++R⟩)
    (L R : Nat) : prun table k (pzip q lp rp L R) = some (pzip q' lp' rp' L R) := by
  obtain ⟨ls,hl⟩ := pack_surj L
  obtain ⟨rs,hr⟩ := pack_surj R
  have H := (enc_run table k ⟨q,lp++ls,rp++rs⟩).symm.trans (congrArg (Option.map enc) (h ls rs))
  simpa only [enc,Option.map_some,pzip,prepend,pack_append,hl,hr] using H

theorem stop0_run (a : Bool) (L x : Nat) : prun table 9 ⟨state a,2*L,8*x⟩ = some ⟨5,L,2*(8*x+4)⟩ := by
  have H := frame 9 (state a) 5 [false] [false,false,false] [] [false,false,false,true] (by cases a <;> intro L R <;> rfl) L x
  simpa [pzip,prepend,pack,Bool.toNat,Nat.mul_add,← Nat.mul_assoc,Nat.add_comm] using H
theorem stop011_run (a : Bool) (L x : Nat) : prun table 7 ⟨state a,2*L,8*x+6⟩ = some ⟨5,L,2*(8*x)⟩ := by
  have H := frame 7 (state a) 5 [false] [false,true,true] [] [false,false,false,false] (by cases a <;> intro L R <;> rfl) L x
  simpa [pzip,prepend,pack,Bool.toNat,Nat.mul_add,← Nat.mul_assoc,Nat.add_comm] using H
theorem stop0011_run (a : Bool) (L x : Nat) : prun table 9 ⟨state a,2*L,16*x+12⟩ = some ⟨5,L,2*(16*x+2)⟩ := by
  have H := frame 9 (state a) 5 [false] [false,false,true,true] [] [false,false,true,false,false] (by cases a <;> intro L R <;> rfl) L x
  simpa [pzip,prepend,pack,Bool.toNat,Nat.mul_add,← Nat.mul_assoc,Nat.add_comm] using H
theorem push10 (a : Bool) (L x : Nat) : prun table 2 ⟨state a,2*L,4*x+1⟩ = some ⟨state true,2*(4*L+2),x⟩ := by
  have H := frame 2 (state a) (state true) [false] [true,false] [false,false,true] [] (by cases a <;> intro L R <;> rfl) L x
  simpa [pzip,prepend,pack,Bool.toNat,Nat.mul_add,← Nat.mul_assoc,Nat.add_comm] using H
theorem pop10 (L x : Nat) : prun table 2 ⟨5,4*L+2,2*x⟩ = some ⟨5,L,2*(4*x+1)⟩ := by
  have H := frame 2 5 5 [false,true] [false] [] [false,true,false] (by intro L R; rfl) L x
  simpa [pzip,prepend,pack,Bool.toNat,Nat.mul_add,← Nat.mul_assoc,Nat.add_comm] using H
theorem push010 (a : Bool) (L x : Nat) : prun table 3 ⟨state a,2*L,8*x+2⟩ = some ⟨state false,2*(8*L+7),x⟩ := by
  have H := frame 3 (state a) (state false) [false] [false,true,false] [false,true,true,true] [] (by cases a <;> intro L R <;> rfl) L x
  simpa [pzip,prepend,pack,Bool.toNat,Nat.mul_add,← Nat.mul_assoc,Nat.add_comm] using H
theorem pop010 (L x : Nat) : prun table 3 ⟨5,8*L+7,2*x⟩ = some ⟨5,L,2*(8*x)⟩ := by
  have H := frame 3 5 5 [true,true,true] [false] [] [false,false,false,false] (by intro L R; rfl) L x
  simpa [pzip,prepend,pack,Bool.toNat,Nat.mul_add,← Nat.mul_assoc,Nat.add_comm] using H
theorem push0010 (a : Bool) (L x : Nat) : prun table 4 ⟨state a,2*L,16*x+4⟩ = some ⟨state false,2*(16*L+13),x⟩ := by
  have H := frame 4 (state a) (state false) [false] [false,false,true,false] [false,true,false,true,true] [] (by cases a <;> intro L R <;> rfl) L x
  simpa [pzip,prepend,pack,Bool.toNat,Nat.mul_add,← Nat.mul_assoc,Nat.add_comm] using H
theorem pop0010 (L x : Nat) : prun table 4 ⟨5,16*L+13,2*x⟩ = some ⟨5,L,2*(16*x+2)⟩ := by
  have H := frame 4 5 5 [true,false,true,true] [false] [] [false,false,true,false,false] (by intro L R; rfl) L x
  simpa [pzip,prepend,pack,Bool.toNat,Nat.mul_add,← Nat.mul_assoc,Nat.add_comm] using H

theorem core_sound {x y : Nat} (h : R x y) (a : Bool) (L : Nat) :
    ∃ k, 0 < k ∧ prun table k ⟨state a,2*L,x⟩ = some ⟨5,L,2*y⟩ := by
  induction h generalizing a L with
  | stop0 x => exact ⟨9,by decide,stop0_run a L x⟩
  | stop011 x => exact ⟨7,by decide,stop011_run a L x⟩
  | stop0011 x => exact ⟨9,by decide,stop0011_run a L x⟩
  | @cont10 x y h ih =>
    obtain ⟨k,hk,hp⟩ := ih true (4*L+2)
    exact ⟨2+k+2,by omega,pjoin (pjoin (push10 a L x) hp) (pop10 L y)⟩
  | @cont010 x y h ih =>
    obtain ⟨k,hk,hp⟩ := ih false (8*L+7)
    exact ⟨3+k+3,by omega,pjoin (pjoin (push010 a L x) hp) (pop010 L y)⟩
  | @cont0010 x y h ih =>
    obtain ⟨k,hk,hp⟩ := ih false (16*L+13)
    exact ⟨4+k+4,by omega,pjoin (pjoin (push0010 a L x) hp) (pop0010 L y)⟩

abbrev I : List Bool := [true,false]
abbrev O : List Bool := [false,true]

def frontList (k : Nat) (r : List Bool) : Z0 := ⟨4,[],rep I (k+1) ++ r⟩

theorem scanList (k : Nat) (r : List Bool) :
    run0 table (2+2*k) (frontList k r) = some ⟨0,false :: rep O (k+1),r⟩ := by
  have h1 : run0 table 2 (frontList k r) = some ⟨0,[false] ++ O,rep I k ++ r⟩ := by rfl
  have h2 := sweepR table 0 [false] [] I O 2 (by intro L R; rfl) k O r
  have h2' : run0 table (2*k) ⟨0,[false] ++ O,rep I k ++ r⟩ = some ⟨0,false :: rep O (k+1),r⟩ := by
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

theorem scan (k x : Nat) : prun table (2+2*k) (front k x) = some ⟨0,2*pack (rep O (k+1)),x⟩ := by
  obtain ⟨r,hr⟩ := pack_surj x
  have H := (enc_run table (2+2*k) (frontList k r)).symm.trans (congrArg (Option.map enc) (scanList k r))
  simpa [enc,frontList,front,prepend,pack_append,pack,hr,Bool.toNat] using H

theorem finish (k x : Nat) : prun table (2*(k+1)+1) ⟨5,pack (rep O (k+1)),2*x⟩ = some (front (k+1) x) := by
  obtain ⟨r,hr⟩ := pack_surj x
  have H := (enc_run table (2*(k+1)+1) ⟨5,rep O (k+1),false::r⟩).symm.trans (congrArg (Option.map enc) (finishList k r))
  simpa [enc,frontList,front,prepend,pack_append,pack,hr,Bool.toNat] using H

theorem front_step {x y : Nat} (h : R x y) (k : Nat) :
    ∃ d, 0 < d ∧ prun table d (front k x) = some (front (k+1) y) := by
  obtain ⟨d,hd,hp⟩ := core_sound h true (pack (rep O (k+1)))
  exact ⟨(2+2*k)+d+(2*(k+1)+1),by omega,pjoin (pjoin (scan k x) hp) (finish k y)⟩

theorem chain_run {n x y : Nat} (p : Chain R n x y) (k : Nat) :
    ∃ d, n ≤ d ∧ prun table d (front k x) = some (front (k+n) y) := by
  induction p generalizing k with
  | nil x => exact ⟨0,by omega,rfl⟩
  | @cons n x y z h _ ih =>
    obtain ⟨d,hd,hp⟩ := front_step h k
    obtain ⟨e,he,hq⟩ := ih (k+1)
    refine ⟨d+e,by omega,?_⟩
    rw [show k+(n+1)=k+1+n by omega]
    exact pjoin hp hq

theorem entry : prun table 10 ⟨0,0,0⟩ = some (front 0 4) := by rfl

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨k,y,hk,hpath⟩ := long4 n
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

#print axioms long4
#print axioms core_sound
#print axioms never
end BB6Coverage.Agent43Raw122AHole05
