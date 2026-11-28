import Raw54OneRDSixBlockExceptions

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option autoImplicit false

namespace BB6.Agent8Raw54.SixBlock.ZeroRA
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent13BlankDelay
open BB6.Agent8Raw54.SixBlock

def a : Move := ⟨false,true,0⟩
def X : List Bool := [false,false] ++ P
def J : List Bool := [true,false] ++ P
def K : List Bool := [false,false] ++ J
def S (n : Nat) : Z0 := ⟨3,X ++ J ++ rep P n,[]⟩
def T (n : Nat) : Z0 := ⟨3,X ++ K ++ rep P (n+1),[]⟩
def U (m : Nat) : Z0 := ⟨3,X ++ J ++ J ++ rep P m,[]⟩

def ones5 : List Bool := [true,true,true,true,true]

theorem start_one (L : List Bool) :
    run0 (table a) 31 ⟨3,X ++ J ++ L,[]⟩ =
      some ⟨3,lp ++ P ++ L,ones5⟩ := by rfl

theorem mid (L R : List Bool) :
    run0 (table a) 16 ⟨3,rp ++ L,[true,true,true] ++ R⟩ =
      some ⟨3,lp ++ L,[false,false,true] ++ R⟩ := by rfl

theorem tail1 (L : List Bool) :
    run0 (table a) 36 ⟨3,rp ++ L,[true,false,false,true,true,true,true]⟩ =
      some ⟨3,X ++ K ++ L,[]⟩ := by rfl

theorem S_to_T (n : Nat) : run0 (table a) (197+72*n) (S n) = some (T n) := by
  have h1 := start_one (rep P n)
  have h2 := pass a (n+1) ones5
  have h3 := mid (rep P (n+1)) [true,true,true]
  have h4 := pass a (n+1) [false,false,true,true,true,true]
  have h5 := tail1 (rep P (n+1))
  have h1' : run0 (table a) 31 (S n) = some ⟨3,lp ++ rep P (n+1),ones5⟩ := by
    simpa only [S,rep,List.append_assoc] using h1
  rw [show 197+72*n=31+(21+36*(n+1))+16+(21+36*(n+1))+36 by omega]
  exact join0 (join0 (join0 (join0 h1' h2) h3) h4) h5

theorem middle_one (L : List Bool) :
    run0 (table a) 101 ⟨3,X ++ K ++ L,[]⟩ =
      some ⟨3,X ++ J ++ J ++ L,[]⟩ := by rfl

theorem T_to_U (n : Nat) : run0 (table a) 101 (T n) = some (U (n+1)) :=
  middle_one (rep P (n+1))

theorem defect (L R : List Bool) :
    run0 (table a) 22 ⟨3,lp ++ J ++ L,R⟩ =
      some ⟨3,lp ++ P ++ L,[true,true] ++ R⟩ := by rfl

def midR : List Bool := [true,false,true,true,true,true,true,true,true]
def endR : List Bool := [false,false,false,true,true,true,true,true,true,true]

theorem convert (L : List Bool) :
    run0 (table a) 29 ⟨3,rp ++ L,[true,false,false,true] ++ Q ++ ones5⟩ =
      some ⟨3,lp ++ P ++ L,midR⟩ := by rfl

theorem mid2 (L : List Bool) :
    run0 (table a) 16 ⟨3,rp ++ L,true::midR⟩ =
      some ⟨3,lp ++ L,endR⟩ := by rfl

theorem convert2 (L : List Bool) :
    run0 (table a) 17 ⟨3,rp ++ L,true::endR⟩ =
      some ⟨3,rp ++ P ++ L,[true,true,true,true]⟩ := by rfl

theorem tail2 (L : List Bool) :
    run0 (table a) 34 ⟨3,rp ++ L,[true,false,false,true,true]⟩ =
      some ⟨3,X ++ J ++ L,[]⟩ := by rfl

theorem U_to_S (m : Nat) : run0 (table a) (637+180*m) (U m) = some (S (m+3)) := by
  have h1 := start_one (J ++ rep P m)
  have h2 := left_one a (J ++ rep P m) ones5
  have h3 := defect (rep P m) (Q ++ ones5)
  have h4 := pass a (m+1) ([true,true] ++ Q ++ ones5)
  have h5 := mid (rep P (m+1)) (Q ++ ones5)
  have h6 := pass a (m+1) ([false,false,true] ++ Q ++ ones5)
  have h7 := convert (rep P (m+1))
  have h8 := pass a (m+2) midR
  have h9 := mid2 (rep P (m+2))
  have h10 := pass a (m+2) endR
  have h11 := convert2 (rep P (m+2))
  have h12 := mid (rep P (m+3)) [true]
  have h13 := pass a (m+3) [false,false,true,true]
  have h14 := tail2 (rep P (m+3))
  have h1' : run0 (table a) 31 (U m) = some ⟨3,lp ++ P ++ J ++ rep P m,ones5⟩ := by
    simpa only [U,List.append_assoc] using h1
  have h2' : run0 (table a) 27 ⟨3,lp ++ P ++ J ++ rep P m,ones5⟩ =
      some ⟨3,lp ++ J ++ rep P m,Q ++ ones5⟩ := by
    simpa only [List.append_assoc] using h2
  have h3' : run0 (table a) 22 ⟨3,lp ++ J ++ rep P m,Q ++ ones5⟩ =
      some ⟨3,lp ++ rep P (m+1),[true,true] ++ Q ++ ones5⟩ := by
    simpa only [rep,List.append_assoc] using h3
  have h7' : run0 (table a) 29 ⟨3,rp ++ rep P (m+1),[true,false,false,true] ++ Q ++ ones5⟩ =
      some ⟨3,lp ++ rep P (m+2),midR⟩ := by
    simpa only [rep,List.append_assoc] using h7
  have h11' : run0 (table a) 17 ⟨3,rp ++ rep P (m+2),true::endR⟩ =
      some ⟨3,rp ++ rep P (m+3),[true,true,true,true]⟩ := by
    simpa only [rep,List.append_assoc] using h11
  have H := join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 h1' h2') h3') h4) h5) h6) h7') h8) h9) h10) h11') h12) h13) h14
  rw [show 637+180*m=31+27+22+(21+36*(m+1))+16+(21+36*(m+1))+29+(21+36*(m+2))+16+(21+36*(m+2))+17+16+(21+36*(m+3))+34 by omega]
  exact H

theorem return4 (n : Nat) : run0 (table a) (1115+252*n) (S n) = some (S (n+4)) := by
  rw [show 1115+252*n=(197+72*n)+101+(637+180*(n+1)) by omega]
  simpa only [Nat.add_assoc] using join0 (join0 (S_to_T n) (T_to_U n)) (U_to_S (n+1))

def family (k : Nat) : Z0 := S (4*k)
theorem entry : run0 (table a) 127 ⟨0,[],[]⟩ = some (family 0) := by decide +kernel

theorem epoch (k : Nat) : run0 (table a) (1115+1008*k) (family k) = some (family (k+1)) := by
  simpa only [family,show 4*(k+1)=4*k+4 by omega,show 1115+252*(4*k)=1115+1008*k by omega] using return4 (4*k)

theorem never (m : Machine) (hm : compatible (table a) m) : NeverHalts m :=
  never_of_growth (table a) family 127 (fun k => 1115+1008*k) entry (by intro k; omega) epoch m hm

theorem cover (B : Nat) : Cover (WeightedBound B) (table a) := by
  apply Cover.leaf
  intro m hm
  exact weighted_never B m (never m hm)
#print axioms return4
#print axioms cover
end BB6.Agent8Raw54.SixBlock.ZeroRA
