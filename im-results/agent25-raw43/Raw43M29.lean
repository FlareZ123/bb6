import SweepPumping
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43M29
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | _,_ => none

private def P : List Bool := [false,true]
private theorem oneR (L R : List Bool) :
    run0 table 4 ⟨0,[true]++L,[]++P++R⟩ =
    some ⟨0,[true]++P++L,[]++R⟩ := by rfl
private theorem oneL (L R : List Bool) :
    run0 table 4 ⟨1,[true]++P++L,[true,true]++R⟩ =
    some ⟨1,[true]++L,[true,true]++P++R⟩ := by rfl
private theorem rightTurn (L : List Bool) :
    run0 table 14 ⟨0,[true]++L,[false]⟩ =
    some ⟨1,[true]++P++L,[true,true,false]⟩ := by rfl
private theorem leftTurn (R : List Bool) :
    run0 table 6 ⟨1,[true],[true,true]++R⟩ =
    some ⟨0,[true,false,true],P++R⟩ := by rfl

def sect (n : Nat) : Z0 := ⟨0,[true,false,true],rep P n++[false]⟩

theorem entry : run0 table 16 ⟨0,[],[]⟩ = some (sect 1) := by rfl

theorem epoch (n : Nat) : run0 table (8*n+28) (sect n) = some (sect (n+3)) := by
  have hr := sweepR table 0 [true] [] P P 4 oneR n P [false]
  simp only [List.nil_append] at hr
  have h1 : run0 table (4*n) (sect n) =
      some ⟨0,[true]++rep P (n+1),[false]⟩ := by
    change run0 table (4*n) ⟨0,[true]++P,rep P n++[false]⟩ = _
    simpa only [rep,rep_snoc,List.append_assoc] using hr
  have h2 := rightTurn (rep P (n+1))
  have h3 := sweepL table 1 [true] [true,true] P P 4 oneL (n+2) [] [false]
  have h3' : run0 table (4*(n+2)) ⟨1,[true]++P++rep P (n+1),[true,true,false]⟩ =
      some ⟨1,[true],[true,true]++(rep P (n+2)++[false])⟩ := by
    change run0 table (4*(n+2)) ⟨1,[true]++P++rep P (n+1),[true,true]++[false]⟩ = _
    simpa only [rep,List.append_nil,List.append_assoc] using h3
  have h4 := leftTurn (rep P (n+2)++[false])
  have h := join0 (join0 (join0 h1 h2) h3') h4
  rw [show 4*n+14+4*(n+2)+6=8*n+28 by omega] at h
  simpa only [sect,rep,List.append_assoc] using h

def family (k : Nat) : Z0 := sect (3*k+1)
def cost (k : Nat) : Nat := 24*k+36

theorem first : run0 table 16 ⟨0,[],[]⟩ = some (family 0) := by exact entry

theorem growth (k : Nat) : run0 table (cost k) (family k) = some (family (k+1)) := by
  have h := epoch (3*k+1)
  rw [show 8*(3*k+1)+28=24*k+36 by omega,
      show 3*k+1+3=3*(k+1)+1 by omega] at h
  exact h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 16 cost first (by intro k; unfold cost; omega) growth m hm

#print axioms first
#print axioms growth
#print axioms entry
#print axioms epoch
#print axioms never
end BB6.Agent25Raw43M29
