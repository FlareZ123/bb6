import Agent8SharpMass14EvenSource
namespace BB6.Agent8SharpSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource

theorem drainB_mass_odd_big11 (b : Nat) (hb : 7 ≤ b) (hodd : b%2=1)
    (a d aa dd : Nat) (ha : 0<a)
    (h : drainB a b d = some (.D aa dd)) :
    a+d+2*b+11 ≤ aa+dd := by
  rw [drainB] at h
  simp only [if_neg (by omega : b≠0)] at h
  cases he : evalA a (b-1) (d+2*b+3) with
  | none => simp [he] at h
  | some p =>
    rcases p with ⟨a1,b1,d1⟩
    simp only [he,Option.bind_some] at h
    by_cases hlt : b1<b
    · simp only [if_pos hlt] at h
      by_cases hz : b1=0
      · subst b1
        have hm:=evalA_mass_zero_even8 a (b-1) (d+2*b+3) a1 d1
          ha (by omega) (by omega) he
        have hr:=(drainB_mass 0 a1 d1 aa dd h).1
        omega
      · have hm:=evalA_mass_even_large a (b-1) (d+2*b+3) a1 b1 d1
          ha (by omega) (by omega) he
        have hr:=drainB_mass_b5 b1 a1 d1 aa dd (by omega) h
        omega
    · simp [hlt] at h

#print axioms drainB_mass_odd_big11
end BB6.Agent8SharpSource
