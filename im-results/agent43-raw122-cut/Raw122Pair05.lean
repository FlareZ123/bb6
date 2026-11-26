import Raw122Shift05
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace BB6Coverage.Agent43Raw122Pair05
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper BB6Coverage.Agent29PackedRun

def table (v : Bool) : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some (if v then ⟨true,true,1⟩ else ⟨false,false,3⟩))
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
  | stop0011 (x : Nat) : R (16*x+12) (16*x+2)
  | cont10 {x y : Nat} : R x y → R (4*x+1) (4*y+1)
  | cont01 {x y : Nat} : R x y → R (4*x+2) (4*y)
  | cont0010 {x y : Nat} : R x y → R (16*x+4) (16*y+2)

theorem lift2 (x y z : Nat) (h : R x y) (h' : R y z) : Chain R 6 (256*x+84) (256*z+84) := by
  have h1 := R.cont0010 (R.cont10 (R.cont10 h))
  have h2 := R.cont01 (R.cont0010 (R.cont10 h'))
  have h3 := R.stop0 (32*z+9)
  have h4 := R.stop0011 (16*z+4)
  have h5 := R.cont01 (R.stop0 (8*z+2))
  have h6 := R.stop0 (32*z+10)
  rw [show 16*(4*(4*x+1)+1)+4=256*x+84 by omega,show 16*(4*(4*y+1)+1)+2=256*y+82 by omega] at h1
  rw [show 4*(16*(4*y+1)+4)+2=256*y+82 by omega,show 4*(16*(4*z+1)+2)=256*z+72 by omega] at h2
  rw [show 8*(32*z+9)=256*z+72 by omega,show 256*z+72+4=256*z+76 by omega] at h3
  rw [show 16*(16*z+4)+12=256*z+76 by omega,show 16*(16*z+4)+2=256*z+66 by omega] at h4
  rw [show 4*(8*(8*z+2))+2=256*z+66 by omega,show 4*(8*(8*z+2)+4)=256*z+80 by omega] at h5
  rw [show 8*(32*z+10)=256*z+80 by omega,show 256*z+80+4=256*z+84 by omega] at h6
  exact .cons h1 (.cons h2 (.cons h3 (.cons h4 (.cons h5 (.cons h6 (.nil _))))))

def RR (x z : Nat) : Prop := ∃ y, R x y ∧ R y z

theorem pair {x y z : Nat} (h : R x y) (h' : R y z) : RR x z := ⟨y,h,h'⟩

theorem lift (x z : Nat) (h : RR x z) : Chain RR 3 (256*x+84) (256*z+84) := by
  obtain ⟨y,hy,hz⟩ := h
  have H := lift2 x y z hy hz
  cases H with
  | cons h1 hrest =>
    cases hrest with
    | cons h2 hrest =>
      cases hrest with
      | cons h3 hrest =>
        cases hrest with
        | cons h4 hrest =>
          cases hrest with
          | cons h5 hrest =>
            cases hrest with
            | cons h6 hrest =>
              cases hrest
              exact triple (pair h1 h2) (pair h3 h4) (pair h5 h6)

theorem seed : Chain RR 2 0 84 := by
  have h1 : R 0 4 := R.stop0 0
  have h2 : R 4 66 := R.cont0010 (R.stop0 0)
  have h3 : R 66 80 := R.cont01 (R.stop0 2)
  have h4 : R 80 84 := R.stop0 10
  exact .cons (pair h1 h2) (.cons (pair h3 h4) (.nil _))

theorem long0 (n : Nat) : ∃ k y, n ≤ k ∧ Chain RR k 0 y := by
  induction n with
  | zero => exact ⟨0,0,by omega,.nil 0⟩
  | succ n ih =>
    obtain ⟨k,y,hk,hp⟩ := ih
    have H := expand (fun x => 256*x+84) lift hp
    exact ⟨2+3*k,256*y+84,by omega,seed.append H⟩

theorem unpair {n x y : Nat} (h : Chain RR n x y) : Chain R (2*n) x y := by
  induction h with
  | nil x => exact .nil x
  | @cons n x y z h _ ih =>
    obtain ⟨w,hw,hy⟩ := h
    rw [show 2*(n+1) = 2*n+1+1 by omega]
    exact .cons hw (.cons hy ih)

theorem long4 (n : Nat) : ∃ k y, n ≤ k ∧ Chain R k 4 y := by
  obtain ⟨k,y,hk,hp⟩ := long0 n
  have H := expand (fun x => 256*x+84) lift hp
  have hs : Chain R 3 4 84 := triple (R.cont0010 (R.stop0 0)) (R.cont01 (R.stop0 2)) (R.stop0 10)
  exact ⟨3+2*(3*k),256*y+84,by omega,hs.append (unpair H)⟩

def coreL (L R : List Bool) : Z0 := ⟨1,R.headD false::true::L,R.tail⟩
def core (L x : Nat) : PZ := ⟨1,x%2+2+4*L,x/2⟩

theorem enc_core (L R : List Bool) : enc (coreL L R) = core (pack L) (pack R) := by
  simp [enc,coreL,core,pack,pack_head,pack_tail,Bool.toNat,Nat.mul_add,← Nat.mul_assoc,Nat.add_assoc]

theorem core_frame (v : Bool) (k : Nat) (I C : List Bool)
    (h : ∀ L R : List Bool, run0 (table v) k (coreL L (I++R)) = some (coreL (C++L) R)) (L x : Nat) :
    prun (table v) k (core L (prepend I x)) = some (core (prepend C L) x) := by
  obtain ⟨ls,hl⟩ := pack_surj L
  obtain ⟨rs,hr⟩ := pack_surj x
  have H := (enc_run (table v) k (coreL ls (I++rs))).symm.trans (congrArg (Option.map enc) (h ls rs))
  simpa only [enc_core,Option.map_some,prepend,pack_append,hl,hr] using H

theorem stop_frame (v : Bool) (k : Nat) (I O : List Bool)
    (h : ∀ L R : List Bool, run0 (table v) k (coreL L (I++R)) = some ⟨5,L,O++R⟩) (L x : Nat) :
    prun (table v) k (core L (prepend I x)) = some ⟨5,L,prepend O x⟩ := by
  obtain ⟨ls,hl⟩ := pack_surj L
  obtain ⟨rs,hr⟩ := pack_surj x
  have H := (enc_run (table v) k (coreL ls (I++rs))).symm.trans (congrArg (Option.map enc) (h ls rs))
  rw [enc_core] at H
  simpa only [enc,Option.map_some,prepend,pack_append,hl,hr] using H

theorem frame (v : Bool) (k : Nat) (q q' : Fin 6) (lp rp lp' rp' : List Bool)
    (h : ∀ L R : List Bool, run0 (table v) k ⟨q,lp++L,rp++R⟩ = some ⟨q',lp'++L,rp'++R⟩)
    (L R : Nat) : prun (table v) k (pzip q lp rp L R) = some (pzip q' lp' rp' L R) := by
  obtain ⟨ls,hl⟩ := pack_surj L
  obtain ⟨rs,hr⟩ := pack_surj R
  have H := (enc_run (table v) k ⟨q,lp++ls,rp++rs⟩).symm.trans (congrArg (Option.map enc) (h ls rs))
  simpa only [enc,Option.map_some,pzip,prepend,pack_append,hl,hr] using H

theorem stop0_run (v : Bool) (L x : Nat) : prun (table v) 8 (core L (8*x)) = some ⟨5,L,2*(8*x+4)⟩ := by
  have H := stop_frame v 8 [false,false,false] [false,false,false,true] (by cases v <;> intro L R <;> rfl) L x
  simpa [pzip,prepend,pack,Bool.toNat,Nat.mul_add,← Nat.mul_assoc,Nat.add_comm] using H
theorem stop0011_run (v : Bool) (L x : Nat) : prun (table v) 8 (core L (16*x+12)) = some ⟨5,L,2*(16*x+2)⟩ := by
  have H := stop_frame v 8 [false,false,true,true] [false,false,true,false,false] (by cases v <;> intro L R <;> rfl) L x
  simpa [pzip,prepend,pack,Bool.toNat,Nat.mul_add,← Nat.mul_assoc,Nat.add_comm] using H
theorem push10 (v : Bool) (L x : Nat) : prun (table v) 2 (core L (4*x+1)) = some (core (4*L+2) x) := by
  have H := core_frame v 2 [true,false] [false,true] (by cases v <;> intro L R <;> cases R <;> rfl) L x
  simpa [pzip,prepend,pack,Bool.toNat,Nat.mul_add,← Nat.mul_assoc,Nat.add_comm] using H
theorem pop10 (v : Bool) (L x : Nat) : prun (table v) 2 ⟨5,4*L+2,2*x⟩ = some ⟨5,L,2*(4*x+1)⟩ := by
  have H := frame v 2 5 5 [false,true] [false] [] [false,true,false] (by cases v <;> intro L R <;> rfl) L x
  simpa [pzip,prepend,pack,Bool.toNat,Nat.mul_add,← Nat.mul_assoc,Nat.add_comm] using H
theorem push01 (v : Bool) (L x : Nat) : prun (table v) (if v then 2 else 4) (core L (4*x+2)) = some (core (4*L+3) x) := by
  have H := core_frame v (if v then 2 else 4) [false,true] [true,true] (by cases v <;> intro L R <;> cases R <;> rfl) L x
  simpa [pzip,prepend,pack,Bool.toNat,Nat.mul_add,← Nat.mul_assoc,Nat.add_comm] using H
theorem pop01 (v : Bool) (L x : Nat) : prun (table v) 2 ⟨5,4*L+3,2*x⟩ = some ⟨5,L,2*(4*x)⟩ := by
  have H := frame v 2 5 5 [true,true] [false] [] [false,false,false] (by cases v <;> intro L R <;> rfl) L x
  simpa [pzip,prepend,pack,Bool.toNat,Nat.mul_add,← Nat.mul_assoc,Nat.add_comm] using H
theorem push0010 (v : Bool) (L x : Nat) : prun (table v) 4 (core L (16*x+4)) = some (core (16*L+13) x) := by
  have H := core_frame v 4 [false,false,true,false] [true,false,true,true] (by cases v <;> intro L R <;> cases R <;> rfl) L x
  simpa [pzip,prepend,pack,Bool.toNat,Nat.mul_add,← Nat.mul_assoc,Nat.add_comm] using H
theorem pop0010 (v : Bool) (L x : Nat) : prun (table v) 4 ⟨5,16*L+13,2*x⟩ = some ⟨5,L,2*(16*x+2)⟩ := by
  have H := frame v 4 5 5 [true,false,true,true] [false] [] [false,false,true,false,false] (by cases v <;> intro L R <;> rfl) L x
  simpa [pzip,prepend,pack,Bool.toNat,Nat.mul_add,← Nat.mul_assoc,Nat.add_comm] using H

theorem core_sound (v : Bool) {x y : Nat} (h : R x y) (L : Nat) :
    ∃ k, 0 < k ∧ prun (table v) k (core L x) = some ⟨5,L,2*y⟩ := by
  induction h generalizing L with
  | stop0 x => exact ⟨8,by decide,stop0_run v L x⟩
  | stop0011 x => exact ⟨8,by decide,stop0011_run v L x⟩
  | @cont10 x y h ih =>
    obtain ⟨k,hk,hp⟩ := ih (4*L+2)
    exact ⟨2+k+2,by omega,pjoin (pjoin (push10 v L x) hp) (pop10 v L y)⟩
  | @cont01 x y h ih =>
    obtain ⟨k,hk,hp⟩ := ih (4*L+3)
    exact ⟨(if v then 2 else 4)+k+2,by omega,pjoin (pjoin (push01 v L x) hp) (pop01 v L y)⟩
  | @cont0010 x y h ih =>
    obtain ⟨k,hk,hp⟩ := ih (16*L+13)
    exact ⟨4+k+4,by omega,pjoin (pjoin (push0010 v L x) hp) (pop0010 v L y)⟩

abbrev I : List Bool := [true,false]
abbrev O : List Bool := [false,true]

def frontList (k : Nat) (r : List Bool) : Z0 := ⟨4,[],rep I (k+1) ++ r⟩

theorem scanList (v : Bool) (k : Nat) (r : List Bool) :
    run0 (table v) (2+2*k) (frontList k r) = some ⟨0,false :: rep O (k+1),r⟩ := by
  have h1 : run0 (table v) 2 (frontList k r) = some ⟨0,[false] ++ O,rep I k ++ r⟩ := by cases v <;> rfl
  have h2 := sweepR (table v) 0 [false] [] I O 2 (by cases v <;> intro L R <;> rfl) k O r
  have h2' : run0 (table v) (2*k) ⟨0,[false] ++ O,rep I k ++ r⟩ = some ⟨0,false :: rep O (k+1),r⟩ := by
    rw [show rep O (k+1) = rep O k ++ O by rw [rep,rep_snoc]]
    simpa only [List.nil_append,List.singleton_append,List.cons_append] using h2
  exact join0 h1 h2'

theorem finishList (v : Bool) (k : Nat) (r : List Bool) :
    run0 (table v) (2*(k+1)+1) ⟨5,rep O (k+1),false::r⟩ = some (frontList (k+1) r) := by
  have h1 := sweepL (table v) 5 [] [] O O 2 (by cases v <;> intro L R <;> rfl) (k+1) [] (false::r)
  have h1' : run0 (table v) (2*(k+1)) ⟨5,rep O (k+1),false::r⟩ = some ⟨5,[],rep O (k+1) ++ [false] ++ r⟩ := by
    simpa only [List.nil_append,List.append_nil,List.append_assoc,List.singleton_append] using h1
  have h2 : run0 (table v) 1 ⟨5,[],rep O (k+1) ++ [false] ++ r⟩ = some (frontList (k+1) r) := by
    have h : [true] ++ rep O (k+1) = rep I (k+1) ++ [true] := rotate true [false] (k+1)
    have hs : run0 (table v) 1 ⟨5,[],rep O (k+1) ++ [false] ++ r⟩ =
        some ⟨4,[],[true] ++ rep O (k+1) ++ [false] ++ r⟩ := by cases v <;> rfl
    have he : [true] ++ rep O (k+1) ++ [false] ++ r = rep I (k+2) ++ r := by
      rw [h,show rep I (k+2) = rep I (k+1) ++ I by rw [rep,rep_snoc]]
      simp only [List.append_assoc]
      rfl
    rw [he] at hs
    exact hs
  exact join0 h1' h2

def front (k x : Nat) : PZ := ⟨4,0,prepend (rep I (k+1)) x⟩

theorem scan (v : Bool) (k x : Nat) : prun (table v) (2+2*k) (front k x) = some ⟨0,2*pack (rep O (k+1)),x⟩ := by
  obtain ⟨r,hr⟩ := pack_surj x
  have H := (enc_run (table v) (2+2*k) (frontList k r)).symm.trans (congrArg (Option.map enc) (scanList v k r))
  simpa [enc,frontList,front,prepend,pack_append,pack,hr,Bool.toNat] using H

theorem finish (v : Bool) (k x : Nat) : prun (table v) (2*(k+1)+1) ⟨5,pack (rep O (k+1)),2*x⟩ = some (front (k+1) x) := by
  obtain ⟨r,hr⟩ := pack_surj x
  have H := (enc_run (table v) (2*(k+1)+1) ⟨5,rep O (k+1),false::r⟩).symm.trans (congrArg (Option.map enc) (finishList v k r))
  simpa [enc,frontList,front,prepend,pack_append,pack,hr,Bool.toNat] using H

theorem front_step (v : Bool) {x y : Nat} (h : R x y) (k : Nat) :
    ∃ d, 0 < d ∧ prun (table v) d (front k x) = some (front (k+1) y) := by
  obtain ⟨d,hd,hp⟩ := core_sound v h (pack (rep O (k+1)))
  have h0 : prun (table v) 1 ⟨0,2*pack (rep O (k+1)),x⟩ = some (core (pack (rep O (k+1))) x) := by
    have hh : (2*pack (rep O (k+1))) % 2 = 0 := by omega
    have hh' : (2*pack (rep O (k+1))) / 2 = pack (rep O (k+1)) := by omega
    simp [prun,pstep,table,hh,hh',pmove,core,Bool.toNat,Nat.mul_add,← Nat.mul_assoc,Nat.add_assoc]
  exact ⟨(2+2*k)+1+d+(2*(k+1)+1),by omega,pjoin (pjoin (pjoin (scan v k x) h0) hp) (finish v k y)⟩

theorem chain_run (v : Bool) {n x y : Nat} (p : Chain R n x y) (k : Nat) :
    ∃ d, n ≤ d ∧ prun (table v) d (front k x) = some (front (k+n) y) := by
  induction p generalizing k with
  | nil x => exact ⟨0,by omega,rfl⟩
  | @cons n x y z h _ ih =>
    obtain ⟨d,hd,hp⟩ := front_step v h k
    obtain ⟨e,he,hq⟩ := ih (k+1)
    refine ⟨d+e,by omega,?_⟩
    rw [show k+(n+1)=k+1+n by omega]
    exact pjoin hp hq

theorem entry (v : Bool) : prun (table v) 10 ⟨0,0,0⟩ = some (front 0 4) := by cases v <;> rfl

theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  intro n
  obtain ⟨k,y,hk,hpath⟩ := long4 n
  obtain ⟨d,hd,hp⟩ := chain_run v hpath 0
  have H := pjoin (entry v) hp
  have H0 := (enc_run (table v) (10+d) ⟨0,[],[]⟩).trans H
  have J := run_project (table v) (10+d) start
  change (zrun (table v) (10+d) start).map project = run0 (table v) (10+d) ⟨0,[],[]⟩ at J
  rw [← J,Option.map_map] at H0
  cases hs : zrun (table v) (10+d) start with
  | none => simp [hs] at H0
  | some z =>
    have hr := zrun_sound (table v) m hm (10+d) start z hs
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
end BB6Coverage.Agent43Raw122Pair05
