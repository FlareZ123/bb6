import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.A0LB110
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,true,5⟩)
  | 5,true => some (some ⟨true,true,2⟩)
  | _,_ => none

abbrev U (n : Nat) := List.replicate n true
abbrev Zs (n : Nat) := List.replicate n false
abbrev B : List Bool := [true,true,true,false]
abbrev I : List Bool := [true,true,false,true]
abbrev S : List Bool := [true,true,true,true,true,false]

theorem uAdd (a b : Nat) : U (a+b)=U a++U b := List.replicate_append_replicate.symm
theorem zAdd (a b : Nat) : Zs (a+b)=Zs a++Zs b := List.replicate_append_replicate.symm
theorem uSucc (a : Nat) : U (a+1)=true::U a := List.replicate_succ

theorem repU (k : Nat) : rep [true,true,true,true] k = U (4*k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [rep,ih]
    change U 4 ++ U (4*k) = _
    rw [List.replicate_append_replicate]
    congr 1 <;> omega

theorem repBit (b : Bool) (k : Nat) : rep [b] k = List.replicate k b := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [rep,ih,List.singleton_append,List.replicate_succ]

theorem forwardOne (L R : List Bool) : run0 table 10 ⟨0,[false,false]++L,[true]++I++R⟩ =
    some ⟨0,[false,false]++U 4++L,[true]++R⟩ := by rfl

theorem forward (k : Nat) (L R : List Bool) :
    run0 table (10*k) ⟨0,[false,false]++L,[true]++rep I k++R⟩ =
    some ⟨0,[false,false]++U (4*k)++L,[true]++R⟩ := by
  simpa only [repU] using sweepR table 0 [false,false] [true] I [true,true,true,true] 10 forwardOne k L R

theorem firstBlock (R : List Bool) : run0 table 10 ⟨0,[],[true]++I++R⟩ = some ⟨0,[false,false]++U 4,[true]++R⟩ := by rfl

theorem specialBlock (L R : List Bool) : run0 table 12 ⟨0,[false,false]++L,S++true::R⟩ =
    some ⟨0,[false,false,false,false]++U 4++L,true::R⟩ := by rfl

theorem forwardLast (L R : List Bool) : run0 table 10 ⟨0,[false,false]++L,B++true::R⟩ =
    some ⟨0,[false,false]++U 4++L,true::R⟩ := by rfl

-- C erases the remaining unary run; D refills it and moves one cell farther left.
theorem eraseOne (L R : List Bool) : run0 table 1 ⟨2,[true]++L,[true]++R⟩ = some ⟨2,[true]++[false]++L,R⟩ := by rfl

theorem refillOne (L R : List Bool) : run0 table 1 ⟨3,[false]++L,R⟩ = some ⟨3,L,[true]++R⟩ := by rfl

theorem unary (n : Nat) (L : List Bool) :
    run0 table (2*n+6) ⟨2,true::true::L,U n⟩ = some ⟨0,L,U (n+4)⟩ := by
  have h1 := sweepR table 2 [true] [] [true] [false] 1 eraseOne n (true::L) []
  simp only [repBit,List.nil_append,List.append_nil,List.singleton_append,Nat.one_mul] at h1
  have h2 : run0 table 2 ⟨2,true::(Zs n++true::L),[]⟩ = some ⟨3,Zs (n+3)++true::L,[]⟩ := by
    rw [show n+3=3+n by omega,zAdd]
    rfl
  have h3 := sweepL table 3 [] [] [false] [true] 1 refillOne (n+3) (true::L) []
  simp only [repBit,List.nil_append,List.append_nil,Nat.one_mul] at h3
  have h4 : run0 table 1 ⟨3,true::L,U (n+3)⟩ = some ⟨0,L,U (n+4)⟩ := by rw [show n+4=(n+3)+1 by omega,uSucc]; rfl
  have h := join0 (join0 (join0 h1 h2) h3) h4
  rwa [show n+2+(n+3)+1=2*n+6 by omega] at h

theorem leftBlock (L R : List Bool) : run0 table 8 ⟨0,U 4++L,R⟩ = some ⟨0,L,B++R⟩ := by rfl

theorem backward (k : Nat) (L R : List Bool) : run0 table (8*k) ⟨0,U (4*k)++L,R⟩ = some ⟨0,L,rep B k++R⟩ := by
  simpa only [repU,List.nil_append] using sweepL table 0 [] [] [true,true,true,true] B 8 leftBlock k L R

def family (k : Nat) : Z0 := ⟨0,[],rep B (k+1)++S++B++U (16+4*k)⟩
def cost (k : Nat) := 222+42*k

theorem epoch (k : Nat) : run0 table (cost k) (family k) = some (family (k+1)) := by
  let n := 12+4*k
  let L := U (4*k+8)
  let R := [true,true,true,true,false]++B++U (n+4)
  have h0 := firstBlock (rep I k++R)
  have h1 := forward k (U 4) R
  have h2 := specialBlock (U (4*k+4)) (B.tail++U (n+4))
  have h2a : run0 table 12 ⟨0,[false,false]++U (4*k)++U 4,[true]++R⟩ = some ⟨0,[false,false]++[false,false]++L,B++U (n+4)⟩ := by
    simpa only [R,L,S,B,List.tail_cons,List.append_assoc,List.singleton_append,List.nil_append,List.cons_append,List.replicate_append_replicate,show 4+ (4*k+4)=4*k+8 by omega,show 4*k+4=4*k+4 by rfl] using h2
  have h3 : run0 table 10 ⟨0,[false,false]++[false,false]++L,B++U (n+4)⟩ = some ⟨0,[false,false]++U 4++[false,false]++L,U (n+4)⟩ := by
    rw [show n+4=(n+3)+1 by omega,uSucc]
    exact forwardLast ([false,false]++L) (U (n+3))
  have h4 : run0 table 7 ⟨0,[false,false]++U 4++[false,false]++L,U (n+4)⟩ = some ⟨2,U 9++[false,false]++L,U (n+1)⟩ := by
    rw [show n+4=3+(n+1) by omega,uAdd]
    rfl
  have h5 := unary (n+1) (U 7++[false,false]++L)
  have h6 : run0 table 8 ⟨0,U 7++[false,false]++L,U (n+5)⟩ = some ⟨0,U 3++[false,false]++L,B++U (n+5)⟩ := by rfl
  have h7 : run0 table 12 ⟨0,U 3++[false,false]++L,B++U (n+5)⟩ = some ⟨0,[false,false,false]++U 5++[false]++L,U (n+5)⟩ := by rfl
  have h8 : run0 table 7 ⟨0,[false,false,false]++U 5++[false]++L,U (n+5)⟩ = some ⟨2,U 5++[false]++U 5++[false]++L,U (n+2)⟩ := by
    rw [show n+5=3+(n+2) by omega,uAdd]
    rfl
  have h9 := unary (n+2) (U 3++[false]++U 5++[false]++L)
  have h10 : run0 table 8 ⟨0,U 3++[false]++U 5++[false]++L,U (n+6)⟩ = some ⟨2,U 11++[false]++L,U (n+4)⟩ := by
    rw [show n+6=2+(n+4) by omega,uAdd]
    rfl
  have h11 := unary (n+4) (U 9++[false]++L)
  have h12 : run0 table 16 ⟨0,U 9++[false]++L,U (n+8)⟩ = some ⟨0,[true,false]++L,B++B++U (n+8)⟩ := by rfl
  have h13 : run0 table 4 ⟨0,[true,false]++L,B++B++U (n+8)⟩ = some ⟨0,[false,true]++L,B++B++U (n+8)⟩ := by rfl
  have h14 : run0 table 8 ⟨0,[false,true]++L,B++B++U (n+8)⟩ = some ⟨0,L,S++B++U (n+8)⟩ := by rfl
  have h15 := backward (k+2) [] (S++B++U (n+8))
  have h15' : run0 table (8*(k+2)) ⟨0,L,S++B++U (n+8)⟩ = some ⟨0,[],rep B (k+2)++S++B++U (n+8)⟩ := by
    simpa only [List.append_nil,List.append_assoc,show 4*(k+2)=4*k+8 by omega,L] using h15
  simp only [List.append_assoc,List.cons_append,List.nil_append] at h0 h1 h2a h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15'
  have H := join0 h0 h1
  have H := join0 H h2a
  have H := join0 H h3
  have H := join0 H h4
  have H := join0 H h5
  have H := join0 H h6
  have H := join0 H h7
  have H := join0 H h8
  have H := join0 H h9
  have H := join0 H h10
  have H := join0 H h11
  have H := join0 H h12
  have H := join0 H h13
  have H := join0 H h14
  have H := join0 H h15'
  unfold cost family
  -- Rotate the forward-transfer word by one cell.
  have rot := rotate true [true,true,false] (k+1)
  change [true]++rep I (k+1)=rep B (k+1)++[true] at rot
  have he : (10+10*k+12+10+7+(2*(n+1)+6)+8+12+7+(2*(n+2)+6)+8+(2*(n+4)+6)+16+4+8+8*(k+2))=222+42*k := by dsimp [n]; omega
  rw [he] at H
  have hr : [true]++I++(rep I k++R)=rep B (k+1)++S++B++U (16+4*k) := by
    calc
      _ = ([true]++rep I (k+1))++R := by simp only [rep,List.append_assoc]
      _ = _ := by rw [rot]; simp only [List.append_assoc,R,show n+4=16+4*k by dsimp [n]; omega]; rfl
  simp only [List.append_assoc,List.cons_append,List.nil_append] at hr
  rw [hr] at H
  simpa only [n,show 12+4*k+8=16+4*(k+1) by omega,show k+1+1=k+2 by omega,List.append_assoc,List.cons_append,List.nil_append,S,B] using H

theorem entry : run0 table 381 (project start) = some (family 0) := by decide +kernel

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  have arbitrary : ∀ k, ∃ t, k ≤ t ∧ run0 table t (project start) = some (family k) := by
    intro k
    induction k with
    | zero => exact ⟨381,by omega,entry⟩
    | succ k ih =>
      obtain ⟨t,ht,hr⟩ := ih
      have hp : 0 < cost k := by unfold cost; omega
      exact ⟨t+cost k,by omega,join0 hr (epoch k)⟩
  intro n
  obtain ⟨t,ht,hr⟩ := arbitrary n
  have hz : (zrun table t start).map project = some (family n) := (run_project table t start).trans hr
  cases h : zrun table t start with
  | none => simp [h] at hz
  | some z =>
    have H := zrun_sound table m hm t start z h
    rw [start_embed,show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some _ => rfl

#print axioms epoch
#print axioms never
end BB6.Agent19Raw40.A0LB110
