import Raw54OneRDSixBlock

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option autoImplicit false

namespace BB6.Agent8Raw54.SixBlock
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent13BlankDelay

/-- The two block transfers are valid with arbitrary untouched tape suffixes. -/
theorem drain (a : Move) (k : Nat) (L R : List Bool) :
    run0 (table a) (27*k) ⟨3,lp ++ rep P k ++ L,R⟩ =
      some ⟨3,lp ++ L,rep Q k ++ R⟩ := by
  simpa only [List.nil_append] using
    sweepL (table a) 3 lp [] P Q 27 (left_one a) k L R

theorem restore (a : Move) (k : Nat) (L R : List Bool) :
    run0 (table a) (9*k) ⟨3,rp ++ L,true::(rep Q k ++ R)⟩ =
      some ⟨3,rp ++ rep P k ++ L,true::R⟩ := by
  simpa only [List.singleton_append,List.cons_append,List.nil_append] using
    sweepR (table a) 3 rp [true] Q P 9 (right_one a) k L R

theorem pass (a : Move) (k : Nat) (R : List Bool) :
    run0 (table a) (21+36*k) ⟨3,lp ++ rep P k,R⟩ =
      some ⟨3,rp ++ rep P k,true::R⟩ := by
  have h1 := drain a k [] R
  have h2 := turn a (rep Q k ++ R)
  have h3 := restore a k [] R
  rw [show 21+36*k=27*k+21+9*k by omega]
  simpa only [List.append_nil] using join0 (join0 (by simpa only [List.append_nil] using h1) h2) (by simpa only [List.append_nil] using h3)

namespace OneRE

def a : Move := ⟨true,true,4⟩
def X : List Bool := [false,false] ++ P
def Z : List Bool := [false,true,true,true,false] ++ P

def family (k : Nat) : Z0 := ⟨3,X ++ rep P (k+1),[]⟩

theorem entry : run0 (table a) 162 ⟨0,[],[]⟩ = some (family 0) := by decide +kernel

theorem start_one (L : List Bool) :
    run0 (table a) 36 ⟨3,X ++ P ++ L,[]⟩ =
      some ⟨3,lp ++ L,Q ++ [true,true,true]⟩ := by rfl

theorem phase1 (k : Nat) :
    run0 (table a) (66+36*k) (family k) =
      some ⟨3,rp ++ rep P (k+1),[true,true,true,true]⟩ := by
  have h1 : run0 (table a) 36 (family k) = some ⟨3,lp ++ rep P k,Q ++ [true,true,true]⟩ := by
    simpa only [family,rep,List.append_assoc] using start_one (rep P k)
  have h2 : run0 (table a) (27*k) ⟨3,lp ++ rep P k,Q ++ [true,true,true]⟩ =
      some ⟨3,lp,rep Q (k+1) ++ [true,true,true]⟩ := by
    simpa only [List.append_nil,←List.append_assoc,rep_snoc,rep] using drain a k [] (Q ++ [true,true,true])
  have h3 := turn a (rep Q (k+1) ++ [true,true,true])
  have h4 := restore a (k+1) [] [true,true,true]
  rw [show 66+36*k=36+27*k+21+9*(k+1) by omega]
  simpa only [List.append_nil] using join0 (join0 (join0 h1 h2) h3) h4

theorem mid1 (L : List Bool) :
    run0 (table a) 16 ⟨3,rp ++ L,[true,true,true,true]⟩ =
      some ⟨3,lp ++ L,[false,false,true,true]⟩ := by rfl

theorem mid2 (L : List Bool) :
    run0 (table a) 8 ⟨3,rp ++ L,[true,false,false,true,true]⟩ =
      some ⟨3,Z ++ L,[]⟩ := by rfl

theorem mid3 (L : List Bool) :
    run0 (table a) 26 ⟨3,Z ++ L,[]⟩ =
      some ⟨3,lp ++ L,[false,false,false,false,false,true]⟩ := by rfl

theorem last1 (L : List Bool) :
    run0 (table a) 9 ⟨3,rp ++ L,[true,false,false,false,false,false,true]⟩ =
      some ⟨3,rp ++ P ++ L,[]⟩ := by rfl

theorem last2 (L : List Bool) :
    run0 (table a) 5 ⟨3,rp ++ L,[]⟩ = some ⟨3,X ++ L,[]⟩ := by rfl

theorem epoch (k : Nat) : run0 (table a) (244+108*k) (family k) = some (family (k+1)) := by
  have h1 := phase1 k
  have h2 := mid1 (rep P (k+1))
  have h3 := pass a (k+1) [false,false,true,true]
  have h4 := mid2 (rep P (k+1))
  have h5 := mid3 (rep P (k+1))
  have h6 := pass a (k+1) [false,false,false,false,false,true]
  have h7 := last1 (rep P (k+1))
  have h8 := last2 (P ++ rep P (k+1))
  have H := join0 (join0 (join0 (join0 (join0 (join0 (join0 h1 h2) h3) h4) h5) h6) h7) h8
  rw [show 244+108*k=66+36*k+16+(21+36*(k+1))+8+26+(21+36*(k+1))+9+5 by omega]
  simpa only [family,rep,List.append_assoc] using H

theorem never (m : Machine) (hm : compatible (table a) m) : NeverHalts m :=
  never_of_growth (table a) family 162 (fun k => 244+108*k) entry (by intro k; omega) epoch m hm

theorem cover (B : Nat) : Cover (WeightedBound B) (table a) := by
  apply Cover.leaf
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms epoch
#print axioms cover
end OneRE

namespace ZeroRF

def a : Move := ⟨false,true,5⟩
def J : List Bool := [true,false] ++ P
def K : List Bool := false::J

def U (k : Nat) : Z0 := ⟨3,lp ++ rep P k ++ J ++ rep P k,[]⟩
def V (k : Nat) : Z0 := ⟨3,lp ++ rep P k ++ K ++ rep P (k+1),[]⟩

theorem defect (L R : List Bool) :
    run0 (table a) 22 ⟨3,lp ++ J ++ L,R⟩ =
      some ⟨3,lp ++ P ++ L,[true,true] ++ R⟩ := by rfl

theorem mid (L R : List Bool) :
    run0 (table a) 16 ⟨3,rp ++ L,[true,true,true] ++ R⟩ =
      some ⟨3,lp ++ L,[false,false,true] ++ R⟩ := by rfl

theorem finish_defect (L R : List Bool) :
    run0 (table a) 12 ⟨3,rp ++ L,[true,false,false,true] ++ Q ++ R⟩ =
      some ⟨3,rp ++ K ++ L,true::R⟩ := by rfl

theorem turn_defect (L R : List Bool) :
    run0 (table a) 21 ⟨3,lp ++ K ++ L,R⟩ =
      some ⟨3,rp ++ J ++ L,true::R⟩ := by rfl

/-- U_(k+1) -> V_(k+1). The defect survives two full sweeps, and a new block
    is inserted to its left. Starting at k+1 avoids the special empty suffix. -/
theorem U_to_V (k : Nat) :
    run0 (table a) (272+108*k) (U (k+1)) = some (V (k+1)) := by
  have h1 := drain a (k+1) (J ++ rep P (k+1)) []
  have h2 := defect (rep P (k+1)) (rep Q (k+1))
  have h3 := pass a ((k+1)+1) ([true,true] ++ rep Q (k+1))
  have h4 := mid (rep P ((k+1)+1)) (rep Q (k+1))
  have h5 := pass a ((k+1)+1) ([false,false,true] ++ rep Q (k+1))
  have h6 := finish_defect (rep P ((k+1)+1)) (rep Q k)
  have h7 := restore a k (K ++ rep P ((k+1)+1)) []
  have h8 := finish a (rep P k ++ K ++ rep P ((k+1)+1))
  have h1' : run0 (table a) (27*(k+1)) (U (k+1)) =
      some ⟨3,lp ++ J ++ rep P (k+1),rep Q (k+1)⟩ := by
    simpa only [U,List.append_nil,List.append_assoc] using h1
  have h2' : run0 (table a) 22 ⟨3,lp ++ J ++ rep P (k+1),rep Q (k+1)⟩ =
      some ⟨3,lp ++ rep P ((k+1)+1),[true,true] ++ rep Q (k+1)⟩ := by
    simpa only [rep,List.append_assoc] using h2
  have h6' : run0 (table a) 12 ⟨3,rp ++ rep P ((k+1)+1),[true,false,false,true] ++ rep Q (k+1)⟩ =
      some ⟨3,rp ++ K ++ rep P ((k+1)+1),true::rep Q k⟩ := by
    simpa only [rep,List.append_assoc] using h6
  have h7' : run0 (table a) (9*k) ⟨3,rp ++ K ++ rep P ((k+1)+1),true::rep Q k⟩ =
      some ⟨3,rp ++ rep P k ++ K ++ rep P ((k+1)+1),[true]⟩ := by
    simpa only [List.append_nil,List.append_assoc] using h7
  have H := join0 (join0 (join0 (join0 (join0 (join0 (join0 h1' h2') h3) h4) h5) h6') h7') h8
  rw [show 272+108*k=27*(k+1)+22+(21+36*((k+1)+1))+16+(21+36*((k+1)+1))+12+9*k+9 by omega]
  simpa only [V,rep,List.append_assoc] using H

theorem V_to_U (k : Nat) :
    run0 (table a) (30+36*k) (V k) = some (U (k+1)) := by
  have h1 := drain a k (K ++ rep P (k+1)) []
  have h2 := turn_defect (rep P (k+1)) (rep Q k)
  have h3 := restore a k (J ++ rep P (k+1)) []
  have h4 := finish a (rep P k ++ J ++ rep P (k+1))
  have h1' : run0 (table a) (27*k) (V k) =
      some ⟨3,lp ++ K ++ rep P (k+1),rep Q k⟩ := by
    simpa only [V,List.append_nil,List.append_assoc] using h1
  have h3' : run0 (table a) (9*k) ⟨3,rp ++ J ++ rep P (k+1),true::rep Q k⟩ =
      some ⟨3,rp ++ rep P k ++ J ++ rep P (k+1),[true]⟩ := by
    simpa only [List.append_nil,List.append_assoc] using h3
  rw [show 30+36*k=27*k+21+9*k+9 by omega]
  simpa only [U,rep,List.append_assoc] using join0 (join0 (join0 h1' h2) h3') h4

def family (k : Nat) : Z0 := U (k+1)
theorem entry : run0 (table a) 300 ⟨0,[],[]⟩ = some (family 0) := by decide +kernel

theorem epoch (k : Nat) : run0 (table a) (338+144*k) (family k) = some (family (k+1)) := by
  rw [show 338+144*k=(272+108*k)+(30+36*(k+1)) by omega]
  exact join0 (U_to_V k) (V_to_U (k+1))

theorem never (m : Machine) (hm : compatible (table a) m) : NeverHalts m :=
  never_of_growth (table a) family 300 (fun k => 338+144*k) entry (by intro k; omega) epoch m hm

theorem cover (B : Nat) : Cover (WeightedBound B) (table a) := by
  apply Cover.leaf
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms epoch
#print axioms cover
end ZeroRF
end BB6.Agent8Raw54.SixBlock
