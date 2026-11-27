import SweepPumping
import ZipAuditCore
import SparseBlankDelay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.A0LB561
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper BB6.Agent13BlankDelay

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨true,false,5⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

abbrev U (n : Nat) := List.replicate n true
abbrev Zs (n : Nat) := List.replicate n false

theorem uAdd (a b : Nat) : U (a+b)=U a++U b := List.replicate_append_replicate.symm
theorem uSucc (a : Nat) : U (a+1)=true::U a := List.replicate_succ

theorem repU3 (k : Nat) : rep [true,true,true] k = U (3*k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [rep,ih]
    change U 3++U (3*k) = _
    rw [←uAdd]
    congr 1 <;> omega

theorem repU1 (k : Nat) : rep [true] k = U k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [rep,ih,List.singleton_append,uSucc]

theorem triple (L R : List Bool) : run0 table 5 ⟨1,[false]++L,[true,true,true]++R⟩ = some ⟨1,[false]++[true,true,true]++L,R⟩ := by rfl

theorem scan (k : Nat) (R : List Bool) : run0 table (5*(k+1)) ⟨1,[],U (3*(k+1))++R⟩ = some ⟨1,false::U (3*(k+1)),R⟩ := by
  have h0 : run0 table 5 ⟨1,[],U 3++U (3*k)++R⟩ = some ⟨1,false::U 3,U (3*k)++R⟩ := by rfl
  have h1 := sweepR table 1 [false] [] [true,true,true] [true,true,true] 5 triple k (U 3) R
  simp only [repU3,List.nil_append,List.singleton_append] at h1
  have h := join0 h0 h1
  rw [←uAdd,show 3+3*k=3*(k+1) by omega,show 5+5*k=5*(k+1) by omega] at h
  have hu : U (3*k)++U 3=U (3*(k+1)) := by rw [←uAdd,show 3*k+3=3*(k+1) by omega]
  simpa only [List.cons_append,hu] using h

theorem backOne (L R : List Bool) : run0 table 1 ⟨1,[true]++L,R⟩ = some ⟨1,L,[true]++R⟩ := by rfl

theorem back (n : Nat) (R : List Bool) : run0 table n ⟨1,U n,R⟩ = some ⟨1,[],U n++R⟩ := by
  simpa only [repU1,List.nil_append,List.append_nil,Nat.one_mul] using sweepL table 1 [] [] [true] [true] 1 backOne n [] R

theorem startB (n : Nat) : run0 table 3 ⟨0,[],U (n+1)⟩ = some ⟨1,[],U (n+2)⟩ := by
  rw [uSucc n,show n+2=(n+1)+1 by omega,uSucc (n+1),uSucc n]
  rfl

-- A residual pair of ones consumes one marker zero and creates two marker zeros.
theorem pairMark (L R : List Bool) : run0 table 7 ⟨1,false::L,[true,true,false]++R⟩ = some ⟨1,L,[false,false,true,true]++R⟩ := by rfl

theorem pairEnd (L : List Bool) : run0 table 7 ⟨1,false::L,[true,true]⟩ = some ⟨1,L,[false,false,true,true]⟩ := by rfl

theorem mark1 (k b : Nat) : run0 table (8*k+7) ⟨1,[],U (3*k+2)++[false]++U b⟩ = some ⟨1,[],U (3*k)++[false,false]++U (b+2)⟩ := by
  cases k with
  | zero => rw [show b+2=2+b by omega,uAdd 2 b]; rfl
  | succ k =>
    have h0 := scan k ([true,true,false]++U b)
    have h1 := pairMark (U (3*(k+1))) (U b)
    have h2 := back (3*(k+1)) ([false,false,true,true]++U b)
    have h := join0 (join0 h0 h1) h2
    rw [show 3*(k+1)+2=3*(k+1)+2 by rfl,uAdd (3*(k+1)) 2,show b+2=2+b by omega,uAdd 2 b]
    rw [show 5*(k+1)+7+3*(k+1)=8*(k+1)+7 by omega] at h
    simpa only [List.append_assoc,List.cons_append,List.nil_append,show U 2=[true,true] by rfl] using h

theorem unary2 (k : Nat) : run0 table (8*k+7) ⟨1,[],U (3*k+2)⟩ = some ⟨1,[],U (3*k)++[false,false]++U 2⟩ := by
  cases k with
  | zero => rfl
  | succ k =>
    have h0 := scan k [true,true]
    have h1 := pairEnd (U (3*(k+1)))
    have h2 := back (3*(k+1)) [false,false,true,true]
    have h := join0 (join0 h0 h1) h2
    rw [uAdd (3*(k+1)) 2,show 5*(k+1)+7+3*(k+1)=8*(k+1)+7 by omega] at *
    simpa only [List.append_assoc,List.cons_append,List.nil_append,show U 2=[true,true] by rfl] using h

-- Zero residual ones with two marker zeros; refill them, then retreat left.
theorem zeroMark (L R : List Bool) : run0 table 5 ⟨1,false::L,[false,false]++R⟩ = some ⟨0,L,[true,true,true]++R⟩ := by rfl

theorem zeroEnd (L : List Bool) : run0 table 5 ⟨1,false::L,[]⟩ = some ⟨0,L,U 3⟩ := by rfl

theorem retreat (n : Nat) (R : List Bool) : run0 table (n+1) ⟨0,U (n+1),R⟩ = some ⟨1,[],U n++false::R⟩ := by
  have h0 : run0 table 1 ⟨0,U (n+1),R⟩ = some ⟨1,U n,false::R⟩ := by rw [uSucc];rfl
  have h1 := back n (false::R)
  have h := join0 h0 h1
  simpa only [Nat.add_comm 1 n] using h

theorem mark2 (k b : Nat) : run0 table (8*(k+1)+5) ⟨1,[],U (3*(k+1))++[false,false]++U b⟩ = some ⟨1,[],U (3*k+2)++[false]++U (b+3)⟩ := by
  have h0 := scan k ([false,false]++U b)
  have h1 := zeroMark (U (3*(k+1))) (U b)
  have h2 := retreat (3*k+2) ([true,true,true]++U b)
  rw [show 3*k+2+1=3*(k+1) by omega] at h2
  have h := join0 (join0 h0 h1) h2
  rw [show 5*(k+1)+5+3*(k+1)=8*(k+1)+5 by omega] at h
  rw [show b+3=3+b by omega,uAdd 3 b]
  simpa only [List.append_assoc,List.singleton_append,List.cons_append,List.nil_append,show U 3=[true,true,true] by rfl] using h

theorem unary0 (k : Nat) : run0 table (8*(k+1)+5) ⟨1,[],U (3*(k+1))⟩ = some ⟨1,[],U (3*k+2)++[false]++U 3⟩ := by
  have h0 := scan k []
  rw [List.append_nil] at h0
  have h1 := zeroEnd (U (3*(k+1)))
  have h2 := retreat (3*k+2) (U 3)
  rw [show 3*k+2+1=3*(k+1) by omega] at h2
  have h := join0 (join0 h0 h1) h2
  rw [show 5*(k+1)+5+3*(k+1)=8*(k+1)+5 by omega] at h
  simpa only [List.append_assoc,List.singleton_append] using h

theorem markerFinish (k b : Nat) : run0 table (8*k*k+12*k+5) ⟨1,[],U (3*k)++[false,false]++U b⟩ = some ⟨0,[],U (b+5*k+3)⟩ := by
  induction k generalizing b with
  | zero => rw [show b+5*0+3=3+b by omega,uAdd];rfl
  | succ k ih =>
    have h0 := mark2 k b
    have h1 := mark1 k (b+3)
    have h2 := ih (b+5)
    have h := join0 (join0 h0 h1) h2
    rw [show 8*(k+1)+5+(8*k+7)+(8*k*k+12*k+5)=8*(k+1)*(k+1)+12*(k+1)+5 by simp only [Nat.add_mul,Nat.mul_add];omega] at h
    simpa only [show b+3+2=b+5 by omega,show b+5+5*k+3=b+5*(k+1)+3 by omega] using h

theorem epoch1 (k : Nat) : run0 table (8*k*k+20*k+15) ⟨0,[],U (3*k+1)⟩ = some ⟨0,[],U (5*k+5)⟩ := by
  have h0 := startB (3*k)
  have h1 := unary2 k
  have h2 := markerFinish k 2
  have h := join0 (join0 h0 h1) h2
  rw [show 3+(8*k+7)+(8*k*k+12*k+5)=8*k*k+20*k+15 by omega] at h
  simpa only [show 2+5*k+3=5*k+5 by omega] using h

theorem epoch2 (k : Nat) : run0 table (8*(k+1)*(k+1)+12*(k+1)+8) ⟨0,[],U (3*k+2)⟩ = some ⟨0,[],U (5*k+8)⟩ := by
  have h0 := startB (3*k+1)
  rw [show 3*k+1+2=3*(k+1) by omega] at h0
  have h1 := unary0 k
  have h2 := mark1 k 3
  have h3 := markerFinish k 5
  have h := join0 (join0 (join0 h0 h1) h2) h3
  rw [show 3+(8*(k+1)+5)+(8*k+7)+(8*k*k+12*k+5)=8*(k+1)*(k+1)+12*(k+1)+8 by simp only [Nat.add_mul,Nat.mul_add];omega] at h
  simpa only [show 5+5*k+3=5*k+8 by omega] using h

theorem finalQuery (k : Nat) : run0 table (5*(k+1)+5) ⟨0,[],U (3*(k+1))⟩ = some ⟨4,false::U (3*(k+1)+2),[]⟩ := by
  have h0 := startB (3*k+2)
  rw [show 3*k+2+1=3*(k+1) by omega,show 3*k+2+2=3*(k+1)+1 by omega,uAdd (3*(k+1)) 1] at h0
  have h1 := scan k [true]
  have h2 : run0 table 2 ⟨1,false::U (3*(k+1)),[true]⟩ = some ⟨4,false::U (3*(k+1)+2),[]⟩ := by
    rw [show 3*(k+1)+2=2+3*(k+1) by omega,uAdd 2];rfl
  have h := join0 (join0 h0 h1) h2
  rw [show 3+5*(k+1)+2=5*(k+1)+5 by omega] at h
  exact h

theorem entry : run0 table 54 (project start) = some ⟨0,[],U 10⟩ := by decide +kernel
theorem query : run0 table 75493793 (project start) = some ⟨4,false::U 12290,[]⟩ := by
  have h := entry
  have h := join0 h (epoch1 3)
  have h := join0 h (epoch2 6)
  have h := join0 h (epoch2 12)
  have h := join0 h (epoch2 22)
  have h := join0 h (epoch1 39)
  have h := join0 h (epoch2 66)
  have h := join0 h (epoch2 112)
  have h := join0 h (epoch1 189)
  have h := join0 h (epoch2 316)
  have h := join0 h (epoch1 529)
  have h := join0 h (epoch1 883)
  have h := join0 h (epoch1 1473)
  have h := join0 h (epoch2 2456)
  have h := join0 h (finalQuery 4095)
  exact h

def witness : Machine := fun s => (table s).bind id
theorem witness_compatible : compatible table witness := by
  intro s t ht; simp only [witness,ht,Option.bind_some,id_eq]
theorem haltOfQuery (n : Nat) (L R : List Bool) (hr : run0 table n (project start) = some ⟨4,false::L,R⟩) : HaltsAfter witness n := by
  have hz : (zrun table n start).map project = some ⟨4,false::L,R⟩ := (run_project table n start).trans hr
  cases h : zrun table n start with
  | none => simp [h] at hz
  | some z =>
    have hq : project z = ⟨4,false::L,R⟩ := by simpa only [h,Option.map_some,Option.some.injEq] using hz
    have H := zrun_sound table witness witness_compatible _ start z h
    rw [start_embed] at H
    have hread : readSlot (embed z) = (4,false) := by
      rw [read_embed]
      have hq1 := congrArg Z0.q hq
      have hl := congrArg Z0.l hq
      change z.q=4 at hq1
      change z.l=false::L at hl
      rw [hq1,hl]; rfl
    constructor
    · rw [H]; rfl
    · rw [run_append,H,Option.bind_some]
      change rawStep witness (embed z) = none
      rw [rawStep,hread]; rfl
theorem witness_halts : HaltsAfter witness 75493793 := haltOfQuery _ _ _ query
theorem witness_delay : 0 ∈ delays (zeroNext witness) 0 := by decide
theorem lower : ¬ WeightedBound 75493793 witness := by
  intro hb
  have h := hb 75493793 0 witness_halts witness_delay
  omega

theorem allOfQuery (n : Nat) (L R : List Bool)
    (hr : run0 table n (project start) = some ⟨4,false::L,R⟩) :
    ∀ m, compatible table m → WeightedBound (n+1) m := by
  have hz : (zrun table n start).map project = some ⟨4,false::L,R⟩ := (run_project table n start).trans hr
  cases h : zrun table n start with
  | none => simp [h] at hz
  | some z =>
    have hq : project z = ⟨4,false::L,R⟩ := by simpa only [h,Option.map_some,Option.some.injEq] using hz
    have hread : readSlot (embed z) = (4,false) := by
      rw [read_embed]
      have hq1 := congrArg Z0.q hq
      have hl := congrArg Z0.l hq
      change z.q=4 at hq1
      change z.l=false::L at hl
      rw [hq1,hl]; rfl
    have hrun : knownRun table n = some (embed z) := by
      rw [BB6Coverage.Agent10ZipAudit.knownRun_zip,h]; rfl
    apply last_hole_sound (n+1) table n (embed z) (by rfl) hrun
    · rw [hread]; rfl
    · rw [hread]
      intro slot hs
      rcases slot with ⟨q,a⟩
      have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases a <;> first
        | exact ⟨_,rfl⟩
        | exact False.elim (hs rfl)
    · rw [hread]
      have hd : possibleDelays (refine table (4,false) none) 0 = [0] := by decide
      rw [hd]
      intro d hm
      simp only [List.mem_singleton] at hm
      omega

theorem all : ∀ m, compatible table m → WeightedBound 75493794 m := allOfQuery _ _ _ query
#print axioms all
#print axioms query
#print axioms witness_halts
#print axioms lower
#print axioms epoch1
#print axioms epoch2
#print axioms finalQuery
end BB6.Agent19Raw40.A0LB561
