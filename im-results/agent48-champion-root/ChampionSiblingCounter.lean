import SweepPumping
import ChampionRootBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent48SiblingCounter
open BB6Coverage BB6Coverage.Agent48Champion BB6Coverage.Agent31Pump

inductive Variant where
  | ld | rd | le
  deriving DecidableEq, Repr

def variantMove : Variant → Move
  | .ld => ⟨true,false,3⟩
  | .rd => ⟨true,true,3⟩
  | .le => ⟨false,false,4⟩

def table (v : Variant) : PartialMachine := fun s =>
  if s = (0,true) then some (some (variantMove v))
  else (championTable s).map some

def entryCost : Variant → Nat
  | .ld => 3
  | .rd => 9
  | .le => 5

abbrev d1 : List Bool := [true,true,true]
abbrev d0 : List Bool := [true,false,false]
abbrev aHead : List Bool := [true,true,false]
abbrev xRight : List Bool := [true,true]
abbrev yRight : List Bool := [true,true,true,true,false,false,true,true,true]
abbrev xMark : List Bool := [false,false,true,true,true]
abbrev yMark : List Bool := [true,false,true,true,true,true,true,false,false,true,true,true]
abbrev sent : List Bool := [false,true,true,true]
def pad (n : Nat) : List Bool := List.replicate n false

/-- A single block digit is encoded in reverse physical tape order. -/
def encode : List Bool → List Bool
  | [] => []
  | b::bs => (if b then d1 else d0) ++ encode bs

def xCfg (bs : List Bool) (a b : Nat) : Z0 :=
  ⟨0,aHead++d1++encode bs++sent++pad a,xRight++pad b⟩
def yCfg (bs : List Bool) (a b : Nat) : Z0 :=
  ⟨0,aHead++d0++encode bs++sent++pad a,yRight++pad b⟩

theorem xEntry (v : Variant) (L R : List Bool) :
    run0 (table v) (entryCost v) ⟨0,aHead++L,xRight++R⟩ =
      some ⟨3,L,xMark++R⟩ := by cases v <;> rfl

theorem yEntry (v : Variant) (L R : List Bool) :
    run0 (table v) (entryCost v+6) ⟨0,aHead++d0++L,yRight++R⟩ =
      some ⟨3,d1++L,yMark++R⟩ := by cases v <;> rfl

theorem rep_comm_true (n : Nat) (L : List Bool) :
    rep d1 n ++ true::L = true::(rep d1 n ++ L) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep,List.cons_append,List.nil_append,ih]

theorem dSweep (v : Variant) (n : Nat) (L R : List Bool) :
    run0 (table v) (9*n) ⟨3,rep d1 n++true::L,R⟩ =
      some ⟨3,true::L,rep d1 n++R⟩ := by
  rw [rep_comm_true]
  simpa only [List.nil_append,List.cons_append] using
    sweepL (table v) 3 [true] [] d1 d1 9
      (by intro L R; cases v <;> rfl) n L R

theorem cSweep (v : Variant) (n : Nat) (L R : List Bool) :
    run0 (table v) (3*n) ⟨2,true::L,rep d1 n++R⟩ =
      some ⟨2,true::(rep d0 n++L),R⟩ := by
  simpa only [List.nil_append,List.cons_append] using
    sweepR (table v) 2 [true] [] d1 d0 3
      (by intro L R; cases v <;> rfl) n L R

theorem carryCore (v : Variant) (L R : List Bool) :
    run0 (table v) 5 ⟨3,d0++L,true::R⟩ =
      some ⟨2,true::(d1++L),R⟩ := by cases v <;> rfl

theorem xPost (v : Variant) (L R : List Bool) :
    run0 (table v) 11 ⟨2,true::L,[true,true]++xMark++R⟩ =
      some ⟨0,aHead++d1++L,xRight++R⟩ := by cases v <;> rfl

theorem yPost (v : Variant) (L R : List Bool) :
    run0 (table v) 2 ⟨2,true::L,yMark.tail++R⟩ =
      some ⟨0,aHead++L,yRight++R⟩ := by cases v <;> rfl

-- Left boundary expansion consumes at most two stored blank cells.
theorem overflowCore (v : Variant) (a : Nat) (R : List Bool) :
    run0 (table v) 19 ⟨3,true::(sent++pad a),true::true::R⟩ =
      some ⟨2,[true,true,true,true,false,true,true,true]++pad (a-2),true::R⟩ := by
  cases v <;> cases a with
  | zero => rfl
  | succ a => cases a <;> rfl

theorem rep_two_comm (n : Nat) (R : List Bool) :
    true::true::(rep d1 n ++ R) = rep d1 n ++ true::true::R := by
  rw [rep_comm_true, rep_comm_true]

theorem xCarry (v : Variant) (k : Nat) (L R : List Bool) :
    run0 (table v) (entryCost v+9*(k+1)+5+3*k+11)
      ⟨0,aHead++rep d1 (k+1)++d0++L,xRight++R⟩ =
      some ⟨0,aHead++d1++rep d0 k++d1++L,xRight++R⟩ := by
  have h1 := xEntry v (rep d1 (k+1)++d0++L) R
  have h2 := dSweep v (k+1) (false::false::L) (xMark++R)
  have h3 := carryCore v L (rep d1 k ++ [true,true]++xMark++R)
  have hR : rep d1 (k+1) ++ (xMark++R) = true::(rep d1 k ++ [true,true]++xMark++R) := by
    simp only [rep, d1, List.cons_append, List.nil_append,List.append_assoc]
    rw [rep_two_comm]
  rw [hR] at h2
  have h4 := cSweep v k (d1++L) ([true,true]++xMark++R)
  have h5 := xPost v (rep d0 k++d1++L) R
  simp only [List.append_assoc] at h1 h2 h3 h4 h5
  have h12 := join0 h1 h2
  have h123 := join0 h12 h3
  have h1234 := join0 h123 h4
  have h := join0 h1234 h5
  simpa only [List.append_assoc] using h

theorem yCarry (v : Variant) (k : Nat) (L R : List Bool) :
    run0 (table v) (entryCost v+6+9*(k+1)+5+3*(k+1)+2)
      ⟨0,aHead++d0++rep d1 k++d0++L,yRight++R⟩ =
      some ⟨0,aHead++d0++rep d0 k++d1++L,yRight++R⟩ := by
  have h1 := yEntry v (rep d1 k++d0++L) R
  have h2 := dSweep v (k+1) (false::false::L) (yMark++R)
  have hR : rep d1 (k+1) ++ (yMark++R) = true::(rep d1 (k+1)++(yMark.tail++R)) := by
    change rep d1 (k+1) ++ true::(yMark.tail++R) = _
    rw [rep_comm_true]
  rw [hR] at h2
  have h3 := carryCore v L (rep d1 (k+1)++(yMark.tail++R))
  have h4 := cSweep v (k+1) (d1++L) (yMark.tail++R)
  have h5 := yPost v (rep d0 (k+1)++d1++L) R
  simp only [List.append_assoc] at h1 h2 h3 h4 h5
  have h12 := join0 h1 h2
  have h123 := join0 h12 h3
  have h1234 := join0 h123 h4
  have h := join0 h1234 h5
  simpa only [rep,List.append_assoc] using h

theorem overflowLeft (v : Variant) (a : Nat) (R : List Bool) :
    run0 (table v) 25 ⟨3,d1++sent++pad a,R⟩ =
      some ⟨2,true::(d1++sent++pad (a-2)),true::R⟩ := by
  have h : run0 (table v) 6 ⟨3,d1++sent++pad a,R⟩ =
      some ⟨3,true::(sent++pad a),true::true::R⟩ := by cases v <;> rfl
  exact join0 h (overflowCore v a R)

theorem xOverflowPost (v : Variant) (b : Nat) (L : List Bool) :
    run0 (table v) 70 ⟨2,true::(d0++d0++L),true::(xMark++pad b)⟩ =
      some ⟨0,aHead++d0++d1++L,yRight++pad (b-5)⟩ := by
  cases v <;> cases b with
  | zero => rfl
  | succ b => cases b with
    | zero => rfl
    | succ b => cases b with
      | zero => rfl
      | succ b => cases b with
        | zero => rfl
        | succ b => cases b <;> rfl

theorem yOverflowPost (v : Variant) (L R : List Bool) :
    run0 (table v) 23 ⟨2,true::L,true::yMark++R⟩ =
      some ⟨0,aHead++d1++d0++d1++L,xRight++R⟩ := by cases v <;> rfl

/-- X overflow, for at least two variable counter digits. -/
theorem xOverflow (v : Variant) (k a b : Nat) :
    run0 (table v) (entryCost v+9*(k+2)+25+3*(k+2)+70)
      ⟨0,aHead++rep d1 (k+3)++sent++pad a,xRight++pad b⟩ =
      some ⟨0,aHead++d0++d1++rep d0 k++d1++sent++pad (a-2),yRight++pad (b-5)⟩ := by
  let L := sent++pad a
  let R := xMark++pad b
  let L' := d1++sent++pad (a-2)
  have h1 := xEntry v (rep d1 (k+3)++L) (pad b)
  have h2 := dSweep v (k+2) ([true,true]++L) R
  have hl : rep d1 (k+3)++L = rep d1 (k+2)++true::true::true::L := by
    rw [rep, ← rep_snoc]
    simp only [List.append_assoc]; rfl
  rw [hl] at h1
  have h3 := overflowLeft v a (rep d1 (k+2)++R)
  have hr : true::(rep d1 (k+2)++R) = rep d1 (k+2)++true::R :=
    (rep_comm_true _ _).symm
  rw [hr] at h3
  have h4 := cSweep v (k+2) L' (true::R)
  have h5 := xOverflowPost v b (rep d0 k++L')
  simp only [L,R,L',List.append_assoc] at h1 h2 h3 h4 h5
  have h12 := join0 h1 h2
  have h123 := join0 h12 h3
  have h1234 := join0 h123 h4
  have h := join0 h1234 (by simpa only [rep,List.append_assoc] using h5)
  change rep d1 (k+3)++ (sent++pad a) = _ at hl
  rw [← hl] at h
  simpa only [List.append_assoc] using h

/-- Y overflow increases the variable counter length by three digits. -/
theorem yOverflow (v : Variant) (k a b : Nat) :
    run0 (table v) (entryCost v+6+9*k+25+3*k+23)
      ⟨0,aHead++d0++rep d1 k++sent++pad a,yRight++pad b⟩ =
      some ⟨0,aHead++d1++d0++d1++rep d0 k++d1++sent++pad (a-2),xRight++pad b⟩ := by
  let L := sent++pad a
  let R := yMark++pad b
  let L' := d1++sent++pad (a-2)
  have h1 := yEntry v (rep d1 k++L) (pad b)
  have h2 := dSweep v k ([true,true]++L) R
  have hl : d1++(rep d1 k++L) = rep d1 k++true::true::true::L := by
    rw [← List.append_assoc, ← rep_snoc]; simp only [List.append_assoc]; rfl
  rw [hl] at h1
  have h3 := overflowLeft v a (rep d1 k++R)
  rw [← rep_comm_true] at h3
  have h4 := cSweep v k L' (true::R)
  have h5 := yOverflowPost v (rep d0 k++L') (pad b)
  simp only [L,R,L',List.append_assoc] at h1 h2 h3 h4 h5
  have h12 := join0 h1 h2
  have h123 := join0 h12 h3
  have h1234 := join0 h123 h4
  have h := join0 h1234 h5
  simpa only [List.append_assoc] using h

theorem encode_append (xs ys : List Bool) :
    encode (xs++ys) = encode xs ++ encode ys := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp [encode,ih,List.append_assoc]

theorem encode_repeat (b : Bool) (k : Nat) :
    encode (List.replicate k b) = rep (if b then d1 else d0) k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ,encode,rep,ih]

theorem bits_split (bs : List Bool) :
    (∃ k, bs = List.replicate k true) ∨
    (∃ k ys, bs = List.replicate k true ++ false::ys) := by
  induction bs with
  | nil => exact Or.inl ⟨0,rfl⟩
  | cons b bs ih =>
    cases b with
    | false => exact Or.inr ⟨0,bs,rfl⟩
    | true =>
      rcases ih with ⟨k,h⟩ | ⟨k,ys,h⟩
      · exact Or.inl ⟨k+1,by rw [h]; rfl⟩
      · exact Or.inr ⟨k+1,ys,by rw [h]; rfl⟩

def Invariant (z : Z0) : Prop :=
    ∃ bs : List Bool, ∃ a b : Nat, 2 ≤ bs.length ∧
      (z = xCfg bs a b ∨ z = yCfg bs a b)

/-- Every event in either encoding reaches another event in positive time.
    No assumptions about the counter's numeric value are required. -/
theorem invariant_step (v : Variant) (z : Z0) (hz : Invariant z) :
    ∃ n z', 0 < n ∧ run0 (table v) n z = some z' ∧ Invariant z' := by
  obtain ⟨bs,a,b,hlen,hz⟩ := hz
  rcases bits_split bs with ⟨k,rfl⟩ | ⟨k,ys,rfl⟩
  · simp at hlen
    obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hlen
    rcases hz with rfl | rfl
    · let out := true::(List.replicate j false ++ [true])
      have hh := xOverflow v j a b
      have hk : 2+j=j+2 := by omega
      rw [hk] at *
      refine ⟨entryCost v+9*(j+2)+25+3*(j+2)+70,yCfg out (a-2) (b-5),?_,?_,⟨out,a-2,b-5,by simp [out],Or.inr rfl⟩⟩
      · cases v <;> simp [entryCost]
      · simpa [xCfg,yCfg,out,encode_append,encode_repeat,encode,rep,List.append_assoc] using hh
    · let out := false::true::(List.replicate (2+j) false ++ [true])
      have hh := yOverflow v (2+j) a b
      refine ⟨entryCost v+6+9*(2+j)+25+3*(2+j)+23,xCfg out (a-2) b,?_,?_,⟨out,a-2,b,by simp [out],Or.inl rfl⟩⟩
      · cases v <;> simp [entryCost]
      · simpa [xCfg,yCfg,out,encode_append,encode_repeat,encode,List.append_assoc] using hh
  · let out := List.replicate k false ++ true::ys
    have hout : 2 ≤ out.length := by simpa [out] using hlen
    rcases hz with rfl | rfl
    · have hh := xCarry v k (encode ys++sent++pad a) (pad b)
      refine ⟨entryCost v+9*(k+1)+5+3*k+11,xCfg out a b,?_,?_,⟨out,a,b,hout,Or.inl rfl⟩⟩
      · cases v <;> simp [entryCost]
      · simpa [xCfg,out,encode_append,encode_repeat,encode,rep,List.append_assoc] using hh
    · have hh := yCarry v k (encode ys++sent++pad a) (pad b)
      refine ⟨entryCost v+6+9*(k+1)+5+3*(k+1)+2,yCfg out a b,?_,?_,⟨out,a,b,hout,Or.inr rfl⟩⟩
      · cases v <;> simp [entryCost]
      · simpa [yCfg,out,encode_append,encode_repeat,encode,List.append_assoc] using hh

theorem initial_event (v : Variant) :
    run0 (table v) 213 ⟨0,[],[]⟩ = some (xCfg [false,true,false,true] 0 0) := by
  cases v <;> rfl

theorem arbitrary_live_prefix (v : Variant) (k : Nat) :
    ∃ n z, k ≤ n ∧ run0 (table v) n ⟨0,[],[]⟩ = some z ∧ Invariant z := by
  induction k with
  | zero =>
    exact ⟨213,_,by decide,initial_event v,⟨_,0,0,by decide,Or.inl rfl⟩⟩
  | succ k ih =>
    obtain ⟨n,z,hn,hr,hz⟩ := ih
    obtain ⟨m,z',hm,hs,hz'⟩ := invariant_step v z hz
    exact ⟨n+m,z',by omega,join0 hr hs,hz'⟩

/-- Transfer the unbounded partial zipper prefixes to every total compatible
    machine in the repository's infinite-tape semantics. -/
theorem sibling_never (v : Variant) (m : Machine) (hm : compatible (table v) m) :
    NeverHalts m := by
  intro n
  obtain ⟨t,z,ht,hr,_⟩ := arbitrary_live_prefix v n
  have hz : (Agent50Zipper.zrun (table v) t start).map project = some z :=
    (run_project (table v) t start).trans hr
  cases h : Agent50Zipper.zrun (table v) t start with
  | none => simp [h] at hz
  | some z' =>
    have H := Agent50Zipper.zrun_sound (table v) m hm t start z' h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

theorem sibling_cover (v : Variant) : Cover NeverHalts (table v) :=
  .leaf _ (sibling_never v)

#print axioms invariant_step
#print axioms arbitrary_live_prefix
#print axioms sibling_never
#print axioms sibling_cover
end BB6.Agent48SiblingCounter
