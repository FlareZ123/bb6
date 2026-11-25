import F0SiblingCover
import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent48RA_RD
open BB6Coverage BB6Coverage.Agent31Pump

def ctr : PartialMachine := refine (BB6.Agent6F0.parent ⟨false,true,0⟩) (0,true) (some ⟨false,true,3⟩)
abbrev O : List Bool := [true,true,true]
abbrev Z : List Bool := [true,false,false]
abbrev S : List Bool := [false,false,true,true]
abbrev T : List Bool := [true,false,true,true]
abbrev h : List Bool := [true]
abbrev f : List Bool := [false]
abbrev t : List Bool := [true,false]

-- Encoded digit strings, with optional separator after a one digit.
inductive Good : List Bool → Prop
  | last : Good O
  | one {L} : Good L → Good (O++L)
  | zero {L} : Good L → Good (Z++L)
  | sep {L} : Good L → Good (O++f++L)

-- A word of three stack tokens, followed by the single sentinel one.
inductive Buffer : List Bool → Prop
  | last : Buffer h
  | one {R} : Buffer R → Buffer (O++R)
  | sep {R} : Buffer R → Buffer (S++R)
  | mark {R} : Buffer R → Buffer (T++R)

theorem head_good {L : List Bool} (g : Good L) : ∃ K, L = h++K := by
  cases g <;> exact ⟨_,rfl⟩

inductive Inv : Z0 → Prop
  | d {L R} : Good L → Buffer R → Inv ⟨3,L,R⟩
  | fn {L R} : Good L → Buffer R → Inv ⟨5,t++L,R⟩
  | fh {L R} : Good L → Buffer R → Inv ⟨5,t++L,h++R⟩
  | fz {L R} : Good L → Buffer R → Inv ⟨5,f++f++L,h++h++R⟩
  | fb {L} : Good L → Inv ⟨5,f++f++L,[]⟩

-- Exact finite arbitrary-tail computations for all macro edges.
theorem dlast (R : List Bool) : run0 ctr 12 ⟨3,O,R⟩ = some ⟨5,t++O,R⟩ := by rfl

theorem done (K R : List Bool) : run0 ctr 9 ⟨3,O++h++K,R⟩ = some ⟨3,h++K,O++R⟩ := by rfl

theorem dsep (K R : List Bool) : run0 ctr 8 ⟨3,O++f++h++K,R⟩ = some ⟨3,h++K,S++R⟩ := by rfl

theorem dzlast (L : List Bool) : run0 ctr 6 ⟨3,Z++L,h⟩ = some ⟨5,f++f++O++L,[]⟩ := by rfl

theorem dzone (L R : List Bool) : run0 ctr 6 ⟨3,Z++L,O++R⟩ = some ⟨5,t++O++L,h++R⟩ := by rfl

theorem dzsep (L R : List Bool) : run0 ctr 6 ⟨3,Z++L,S++R⟩ = some ⟨3,O++L,T++R⟩ := by rfl

theorem dzmark (L R : List Bool) : run0 ctr 6 ⟨3,Z++L,T++R⟩ = some ⟨5,f++f++O++L,h++h++R⟩ := by rfl

theorem fnlast (L : List Bool) : run0 ctr 9 ⟨5,t++L,h⟩ = some ⟨5,f++f++O++L,[]⟩ := by rfl

theorem fnone (L R : List Bool) : run0 ctr 3 ⟨5,t++L,O++R⟩ = some ⟨5,t++Z++L,R⟩ := by rfl

theorem fnsep (L R : List Bool) : run0 ctr 6 ⟨5,t++L,S++R⟩ = some ⟨5,t++O++f++L,R⟩ := by rfl

theorem fnmark (L R : List Bool) : run0 ctr 9 ⟨5,t++L,T++R⟩ = some ⟨5,t++O++L,h++R⟩ := by rfl

theorem fhlast (L : List Bool) : run0 ctr 3 ⟨5,t++L,h++h⟩ = some ⟨5,f++f++Z++L,[]⟩ := by rfl

theorem fhone (L R : List Bool) : run0 ctr 3 ⟨5,t++L,h++O++R⟩ = some ⟨5,t++Z++L,h++R⟩ := by rfl

theorem fhsep (L R : List Bool) : run0 ctr 9 ⟨5,t++L,h++S++R⟩ = some ⟨5,f++f++O++L,h++h++R⟩ := by rfl

theorem fhmark (L R : List Bool) : run0 ctr 3 ⟨5,t++L,h++T++R⟩ = some ⟨5,f++f++Z++L,h++h++R⟩ := by rfl

theorem fzlast (L : List Bool) : run0 ctr 8 ⟨5,f++f++L,h++h++h⟩ = some ⟨5,f++f++O++f++L,[]⟩ := by rfl

theorem fzone (L R : List Bool) : run0 ctr 8 ⟨5,f++f++L,h++h++O++R⟩ = some ⟨5,t++O++f++L,h++R⟩ := by rfl

theorem fzsep (L R : List Bool) : run0 ctr 8 ⟨5,f++f++L,h++h++S++R⟩ = some ⟨3,O++f++L,T++R⟩ := by rfl

theorem fzmark (L R : List Bool) : run0 ctr 8 ⟨5,f++f++L,h++h++T++R⟩ = some ⟨5,f++f++O++f++L,h++h++R⟩ := by rfl

theorem fbenter (K : List Bool) : run0 ctr 27 ⟨5,f++f++h++K,[]⟩ = some ⟨3,O++h++K,S++h⟩ := by rfl

theorem progress {z : Z0} (hz : Inv z) : ∃ n z', 0 < n ∧ run0 ctr n z = some z' ∧ Inv z' := by
  cases hz with
  | @d L R g b =>
    cases g with
    | last => exact ⟨12,_,by decide,dlast R,Inv.fn Good.last b⟩
    | @one L g =>
      obtain ⟨K,rfl⟩ := head_good g
      refine ⟨9,_,by decide,?_,Inv.d g (Buffer.one b)⟩
      simpa only [List.append_assoc] using done K R
    | @sep L g =>
      obtain ⟨K,rfl⟩ := head_good g
      refine ⟨8,_,by decide,?_,Inv.d g (Buffer.sep b)⟩
      simpa only [List.append_assoc] using dsep K R
    | @zero L g =>
      cases b with
      | last => exact ⟨6,_,by decide,dzlast L,Inv.fb (Good.one g)⟩
      | @one R b => exact ⟨6,_,by decide,dzone L R,Inv.fh (Good.one g) b⟩
      | @sep R b => exact ⟨6,_,by decide,dzsep L R,Inv.d (Good.one g) (Buffer.mark b)⟩
      | @mark R b => exact ⟨6,_,by decide,dzmark L R,Inv.fz (Good.one g) b⟩
  | @fn L R g b =>
    cases b with
    | last => exact ⟨9,_,by decide,fnlast L,Inv.fb (Good.one g)⟩
    | @one R b => exact ⟨3,_,by decide,fnone L R,Inv.fn (Good.zero g) b⟩
    | @sep R b => exact ⟨6,_,by decide,fnsep L R,Inv.fn (Good.sep g) b⟩
    | @mark R b => exact ⟨9,_,by decide,fnmark L R,Inv.fh (Good.one g) b⟩
  | @fh L R g b =>
    cases b with
    | last => exact ⟨3,_,by decide,fhlast L,Inv.fb (Good.zero g)⟩
    | @one R b => exact ⟨3,_,by decide,fhone L R,Inv.fh (Good.zero g) b⟩
    | @sep R b => exact ⟨9,_,by decide,fhsep L R,Inv.fz (Good.one g) b⟩
    | @mark R b => exact ⟨3,_,by decide,fhmark L R,Inv.fz (Good.zero g) b⟩
  | @fz L R g b =>
    cases b with
    | last => exact ⟨8,_,by decide,fzlast L,Inv.fb (Good.sep g)⟩
    | @one R b => exact ⟨8,_,by decide,fzone L R,Inv.fh (Good.sep g) b⟩
    | @sep R b => exact ⟨8,_,by decide,fzsep L R,Inv.d (Good.sep g) (Buffer.mark b)⟩
    | @mark R b => exact ⟨8,_,by decide,fzmark L R,Inv.fz (Good.sep g) b⟩
  | @fb L g =>
    obtain ⟨K,rfl⟩ := head_good g
    exact ⟨27,_,by decide,fbenter K,Inv.d (Good.one g) (Buffer.sep Buffer.last)⟩

def initial : Z0 := ⟨5,f++f++O++O++f++O,[]⟩
theorem entry : run0 ctr 53 ⟨0,[],[]⟩ = some initial := by rfl
theorem initial_inv : Inv initial := Inv.fb (Good.one (Good.sep Good.last))

theorem unbounded (k : Nat) : ∃ n z, k ≤ n ∧ run0 ctr n ⟨0,[],[]⟩ = some z ∧ Inv z := by
  induction k with
  | zero => exact ⟨53,initial,by decide,entry,initial_inv⟩
  | succ k ih =>
    obtain ⟨n,z,hn,hr,hi⟩ := ih
    obtain ⟨j,t,hj,ht,hit⟩ := progress hi
    exact ⟨n+j,t,by omega,join0 hr ht,hit⟩

#print axioms progress
#print axioms entry
#print axioms unbounded
open BB6.Agent13BlankDelay BB6.Agent47WeightedHalt

theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m := by
  intro n
  obtain ⟨j,t,hj,hr,_⟩ := unbounded n
  have hz : (Agent50Zipper.zrun ctr j start).map project = some t := (run_project ctr j start).trans hr
  cases h : Agent50Zipper.zrun ctr j start with
  | none => simp [h] at hz
  | some z =>
    have H := Agent50Zipper.zrun_sound ctr m hm j start z h
    rw [start_embed] at H
    rw [show j=n+(j-n) by omega,run_append] at H
    change (run m n blank).bind (run m (j - n)) = some (Agent50Zipper.embed z) at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

theorem cover_zeroRA_zeroRD (B : Nat) : Cover (WeightedBound B) ctr :=
  .leaf _ (fun m hm => weighted_never B m (never m hm))

#print axioms never
#print axioms cover_zeroRA_zeroRD
end BB6.Agent48RA_RD
