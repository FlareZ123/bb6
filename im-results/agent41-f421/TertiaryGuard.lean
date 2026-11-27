import Std

namespace F421TertiaryGuard
structure Cell where
  p : Nat
  q : Nat
  deriving Repr, DecidableEq

def drain (h carry : Nat) : List Cell → List Cell × Nat × Nat
  | [] => ([], h, carry)
  | c :: cs =>
    if c.p ≤ 2*h+1 then
      let t := (c.p+1)/2
      drain (h+t) (carry+c.q+t) cs
    else
      let (ys,H,r) := drain (2*h+1) 0 cs
      (⟨c.p-(2*h+1),c.q+h+1+carry⟩::ys,H,r)

def Marked8 (cs : List Cell) : Prop := ∀ c ∈ cs, c.p % 8 = 7
def Survives8 (cs : List Cell) : Prop := ∀ c ∈ cs, c.p % 8 = 0 ∧ 8 ≤ c.p

theorem drainMod8 (cs : List Cell) (h carry : Nat)
    (hh : h % 4 = 3) (hc : Marked8 cs) :
    let (ys,H,_) := drain h carry cs
    Survives8 ys ∧ H % 4 = 3 := by
  induction cs generalizing h carry with
  | nil => simp [drain,Survives8,hh]
  | cons c cs ih =>
    have hp := hc c (by simp)
    have ht : Marked8 cs := by intro x hx; exact hc x (by simp [hx])
    by_cases hd : c.p ≤ 2*h+1
    · have hh' : (h+(c.p+1)/2)%4=3 := by omega
      simpa [drain,hd] using ih (h+(c.p+1)/2) (carry+c.q+(c.p+1)/2) hh' ht
    · have hh' : (2*h+1)%4=3 := by omega
      have hi := ih (2*h+1) 0 hh' ht
      rcases he : drain (2*h+1) 0 cs with ⟨ys,H,r⟩
      rw [he] at hi
      simp only [drain,ite_eq_right hd,he]
      refine ⟨?_,hi.2⟩
      intro x hx
      rcases List.mem_cons.mp hx with hx|hx
      · subst x
        change (c.p-(2*h+1))%8=0 ∧ 8≤c.p-(2*h+1)
        omega
      · exact hi.1 x hx

theorem terminalParity (p : Nat) (h : p%8=7) : p%2=1 := by omega

theorem remark8 (cs : List Cell) (hc : Survives8 cs) :
    Marked8 (cs.map (fun c => ⟨c.p-1,c.q⟩)) := by
  intro x hx
  obtain ⟨c,hc',rfl⟩ := List.mem_map.mp hx
  have h := hc c hc'
  change (c.p-1)%8=7
  omega

def QBudget (k B : Nat) : List Cell → Prop
  | [] => True
  | c::cs => 2+k*B ≤ c.q ∧ QBudget k (2*B) cs

theorem drainQ (cs : List Cell) (k B C h carry : Nat)
    (hCB : C ≤ B) (hCH : C ≤ h+1) (hb : QBudget k B cs) :
    let (ys,H,_) := drain h carry cs
    QBudget (k+1) C ys ∧ ys.length ≤ cs.length ∧ C*2^ys.length ≤ H+1 := by
  induction cs generalizing B C h carry with
  | nil => simp [drain,QBudget,hCH]
  | cons c cs ih =>
    rcases hb with ⟨hq,ht⟩
    by_cases hd : c.p ≤ 2*h+1
    · have hi := ih (2*B) C (h+(c.p+1)/2) (carry+c.q+(c.p+1)/2) (by omega) (by omega) ht
      rcases he : drain (h+(c.p+1)/2) (carry+c.q+(c.p+1)/2) cs with ⟨ys,H,r⟩
      rw [he] at hi
      simp only [drain,ite_eq_left hd,he,List.length_cons]
      exact ⟨hi.1,by omega,hi.2.2⟩
    · have hi := ih (2*B) (2*C) (2*h+1) 0 (by omega) (by omega) ht
      rcases he : drain (2*h+1) 0 cs with ⟨ys,H,r⟩
      rw [he] at hi
      simp only [drain,ite_eq_right hd,he,List.length_cons,QBudget]
      have hmul := Nat.mul_le_mul_left k hCB
      have hn : 2+(k+1)*C ≤ c.q+h+1+carry := by rw [Nat.add_mul]; omega
      refine ⟨⟨hn,hi.1⟩,by omega,?_⟩
      calc
        C*2^(ys.length+1) = (2*C)*2^ys.length := by rw [Nat.pow_succ]; ac_rfl
        _ ≤ H+1 := hi.2.2

theorem thirdCrossBudget (B q : Nat) (hB : 1≤B) (h : 2+2*(2*B) ≤ q) :
    2*B+3 ≤ q-(2*B-1) := by omega

theorem nearestThirdBudget (M L hA hB rA rB : Nat)
    (hL : L ≤ 2*M) (hA' : 3 ≤ hA) (hB' : 3 ≤ hB) :
    3 ≤ (2*M+1+hA+hB+rA+rB)-(L-1) := by omega

theorem newLeadingMod (L hA hB : Nat) (hL : L%8=0)
    (hA' : hA%4=3) (hB' : hB%4=3) :
    (L+4+2*(hA+hB))%8=0 := by omega

theorem newHeadQMod (p B : Nat) (hp : p%8=0) (hB : B%8=0) (hp' : 8≤p) :
    (p-1+B+1)%8=0 ∧ 2≤p-1+B := by omega

theorem farBudget (B q k : Nat) (hB : 1≤B)
    (hq : 3*B*(k+1)+B+2 ≤ q) :
    4*B+2 ≤ q ∧ 3*B*k+B+2 ≤ q-3*B := by
  rw [Nat.mul_add] at hq
  omega

#print axioms drainMod8
#print axioms drainQ
#print axioms thirdCrossBudget
#print axioms newLeadingMod
#print axioms newHeadQMod
#print axioms farBudget
end F421TertiaryGuard
