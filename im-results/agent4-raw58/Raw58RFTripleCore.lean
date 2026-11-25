import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent4RFTriple
open BB6Coverage Agent31Pump

def D (r : List Bool) : Z0 := ⟨3,[true,true],r⟩
def F (k : Nat) (b : Bool) (r : List Bool) : Z0 :=
  ⟨5,b::false::false::(rep [false,false,false] k ++ [true,true]),r⟩
inductive Code : List Bool → Prop
  | nil : Code []
  | short : Code [true,true]
  | block (b : Bool) (r : List Bool) : Code r → Code (true::true::b::r)

theorem pref (k : Nat) (r : List Bool) (h : Code r) : Code (rep [true,true,true] k ++ r) := by
  induction k with
  | zero => exact h
  | succ k ih => exact Code.block true _ ih

theorem pref_nonempty (k : Nat) (r : List Bool) (h : r ≠ []) :
    rep [true,true,true] k ++ r ≠ [] := by
  simp [h]

theorem sweep (p : PartialMachine)
    (h : ∀ L R : List Bool, run0 p 3 ⟨3,[false,false,false]++L,R⟩ =
      some ⟨3,L,[true,true,true]++R⟩)
    (k : Nat) (R : List Bool) :
    run0 p (3*k) ⟨3,rep [false,false,false] k ++ [true,true],R⟩ =
      some (D (rep [true,true,true] k ++ R)) := by
  simpa only [D,List.nil_append] using
    sweepL p 3 [] [] [false,false,false] [true,true,true] 3 h k [true,true] R

/-- The right-hand word encodes triples 11b, with an optional terminal 11.
    Carry consumes one digit and accumulates zeros on the opposite side.
    Stop or overflow restores a nonempty word in the same language. -/
theorem returnF (p : PartialMachine) (a c e : Nat) (ending : List Bool)
    (hend : Code ending) (hnil : ending ≠ []) (hc : 0 < c) (he : 0 < e)
    (carry : ∀ k b r, run0 p a (F k false (true::true::b::r)) = some (F (k+1) b r))
    (shortCarry : ∀ k, run0 p a (F k false [true,true]) = some (F (k+1) false []))
    (stop : ∀ k r, run0 p (c+3*k) (F k true r) = some (D (rep [true,true,true] k ++ true::true::false::r)))
    (overflow : ∀ k, run0 p (e+3*k) (F k false []) = some (D (rep [true,true,true] k ++ ending)))
    (k : Nat) (b : Bool) (r : List Bool) (hr : Code r) :
    ∃ t s, 0 < t ∧ Code s ∧ s ≠ [] ∧ run0 p t (F k b r) = some (D s) := by
  induction hr generalizing k b with
  | nil =>
    cases b with
    | false => exact ⟨_,_,by omega,pref k _ hend,pref_nonempty k _ hnil,overflow k⟩
    | true => exact ⟨_,_,by omega,pref k _ (Code.block false _ Code.nil),pref_nonempty k _ (by decide),stop k []⟩
  | short =>
    cases b with
    | false => exact ⟨_,_,by omega,pref (k+1) _ hend,pref_nonempty (k+1) _ hnil,join0 (shortCarry k) (overflow (k+1))⟩
    | true => exact ⟨_,_,by omega,pref k _ (Code.block false _ Code.short),pref_nonempty k _ (by decide),stop k [true,true]⟩
  | block d r h ih =>
    cases b with
    | false =>
      obtain ⟨t,s,ht,hs,hn,hh⟩ := ih (k+1) d
      exact ⟨a+t,s,by omega,hs,hn,join0 (carry k d r) hh⟩
    | true => exact ⟨_,_,by omega,pref k _ (Code.block false _ (Code.block d r h)),pref_nonempty k _ (by simp),stop k (true::true::d::r)⟩

theorem arbitrary (p : PartialMachine) (a c e : Nat) (ending : List Bool)
    (hend : Code ending) (hnil : ending ≠ []) (hc : 0 < c) (he : 0 < e)
    (entry : run0 p 5 ⟨0,[],[]⟩ = some (D [true,true]))
    (anchor : ∀ b r, run0 p 3 (D (true::true::b::r)) = some (F 0 b r))
    (anchorShort : run0 p 3 (D [true,true]) = some (F 0 false []))
    (carry : ∀ k b r, run0 p a (F k false (true::true::b::r)) = some (F (k+1) b r))
    (shortCarry : ∀ k, run0 p a (F k false [true,true]) = some (F (k+1) false []))
    (stop : ∀ k r, run0 p (c+3*k) (F k true r) = some (D (rep [true,true,true] k ++ true::true::false::r)))
    (overflow : ∀ k, run0 p (e+3*k) (F k false []) = some (D (rep [true,true,true] k ++ ending)))
    (n : Nat) : ∃ t z, n ≤ t ∧ run0 p t ⟨0,[],[]⟩ = some z := by
  have aux : ∀ n : Nat, ∃ t r, n ≤ t ∧ Code r ∧ r ≠ [] ∧ run0 p t ⟨0,[],[]⟩ = some (D r) := by
    intro n
    induction n with
    | zero => exact ⟨5,_,by omega,Code.short,by decide,entry⟩
    | succ n ih =>
      obtain ⟨t,r,ht,hr,hn,hh⟩ := ih
      cases hr with
      | nil => exact False.elim (hn rfl)
      | short =>
        obtain ⟨u,s,hu,hs,hsn,hsr⟩ := returnF p a c e ending hend hnil hc he carry shortCarry stop overflow 0 false [] Code.nil
        exact ⟨t+(3+u),s,by omega,hs,hsn,join0 hh (join0 anchorShort hsr)⟩
      | block b r h =>
        obtain ⟨u,s,hu,hs,hsn,hsr⟩ := returnF p a c e ending hend hnil hc he carry shortCarry stop overflow 0 b r h
        exact ⟨t+(3+u),s,by omega,hs,hsn,join0 hh (join0 (anchor b r) hsr)⟩
  obtain ⟨t,r,ht,_,_,hh⟩ := aux n
  exact ⟨t,D r,ht,hh⟩
#print axioms arbitrary
end BB6Coverage.Agent4RFTriple
