import Raw11ExtraFamily
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
namespace Raw11ExtraFamily
open BB6Coverage
open Root56 (Side z push c alt10)
def fB (w : Bool) : Move := ⟨w,true,1⟩
def s0 : Side := false ::: true ::: true ::: false ::: false ::: true ::: z
def s1 : Side := false ::: true ::: true ::: false ::: true ::: false ::: true ::: false ::: false ::: true ::: z
def s2 : Side := false ::: true ::: true ::: false ::: false ::: true ::: false ::: false ::: true ::: z
def s3 : Side := false ::: true ::: true ::: false ::: true ::: false ::: true ::: false ::: true ::: false ::: false ::: true ::: z
def s4 : Side := false ::: true ::: true ::: false ::: false ::: true ::: false ::: true ::: false ::: false ::: true ::: z
def s5 : Side := false ::: true ::: true ::: false ::: true ::: false ::: false ::: true ::: false ::: true ::: z
def s6 : Side := false ::: true ::: true ::: false ::: false ::: false ::: true ::: false ::: true ::: z
def s7 : Side := false ::: true ::: true ::: false ::: true ::: true ::: false ::: true ::: z
def s8 : Side := false ::: true ::: true ::: false ::: true ::: false ::: true ::: z

theorem turn0 (w : Bool) (l : Side) :
    run true (fB w) (if w then 55 else 57) (c 0 (false ::: false ::: true ::: l) false s0) = some (c 0 l true (alt10 2 s1)) := by
  cases w <;> rfl

theorem hop0 (w : Bool) (n : Nat) :
    run true (fB w) (10*(n+1)+(if w then 55 else 57)) (sec (n+1) s0) = some (sec (n+3) s1) :=
  advance true (fB w) n _ _ _ (turn0 w)

theorem turn1 (w : Bool) (l : Side) :
    run true (fB w) (if w then 27 else 29) (c 0 (false ::: false ::: true ::: l) false s1) = some (c 0 l true (alt10 2 s2)) := by
  cases w <;> rfl

theorem hop1 (w : Bool) (n : Nat) :
    run true (fB w) (10*(n+1)+(if w then 27 else 29)) (sec (n+1) s1) = some (sec (n+3) s2) :=
  advance true (fB w) n _ _ _ (turn1 w)

theorem turn2 (w : Bool) (l : Side) :
    run true (fB w) (if w then 65 else 67) (c 0 (false ::: false ::: true ::: l) false s2) = some (c 0 l true (alt10 2 s3)) := by
  cases w <;> rfl

theorem hop2 (w : Bool) (n : Nat) :
    run true (fB w) (10*(n+1)+(if w then 65 else 67)) (sec (n+1) s2) = some (sec (n+3) s3) :=
  advance true (fB w) n _ _ _ (turn2 w)

theorem turn3 (w : Bool) (l : Side) :
    run true (fB w) (if w then 27 else 29) (c 0 (false ::: false ::: true ::: l) false s3) = some (c 0 l true (alt10 2 s4)) := by
  cases w <;> rfl

theorem hop3 (w : Bool) (n : Nat) :
    run true (fB w) (10*(n+1)+(if w then 27 else 29)) (sec (n+1) s3) = some (sec (n+3) s4) :=
  advance true (fB w) n _ _ _ (turn3 w)

theorem turn4 (w : Bool) (l : Side) :
    run true (fB w) (if w then 39 else 41) (c 0 (false ::: false ::: true ::: l) false s4) = some (c 0 l true (alt10 2 s5)) := by
  cases w <;> rfl

theorem hop4 (w : Bool) (n : Nat) :
    run true (fB w) (10*(n+1)+(if w then 39 else 41)) (sec (n+1) s4) = some (sec (n+3) s5) :=
  advance true (fB w) n _ _ _ (turn4 w)

theorem turn5 (w : Bool) (l : Side) :
    run true (fB w) (if w then 27 else 29) (c 0 (false ::: false ::: true ::: l) false s5) = some (c 0 l true (alt10 2 s6)) := by
  cases w <;> rfl

theorem hop5 (w : Bool) (n : Nat) :
    run true (fB w) (10*(n+1)+(if w then 27 else 29)) (sec (n+1) s5) = some (sec (n+3) s6) :=
  advance true (fB w) n _ _ _ (turn5 w)

theorem turn6 (w : Bool) (l : Side) :
    run true (fB w) (if w then 33 else 35) (c 0 (false ::: false ::: true ::: l) false s6) = some (c 0 l true (alt10 2 s7)) := by
  cases w <;> rfl

theorem hop6 (w : Bool) (n : Nat) :
    run true (fB w) (10*(n+1)+(if w then 33 else 35)) (sec (n+1) s6) = some (sec (n+3) s7) :=
  advance true (fB w) n _ _ _ (turn6 w)

theorem turn7 (w : Bool) (l : Side) :
    run true (fB w) (if w then 27 else 29) (c 0 (false ::: false ::: true ::: l) false s7) = some (c 0 l true (alt10 2 s8)) := by
  cases w <;> rfl

theorem hop7 (w : Bool) (n : Nat) :
    run true (fB w) (10*(n+1)+(if w then 27 else 29)) (sec (n+1) s7) = some (sec (n+3) s8) :=
  advance true (fB w) n _ _ _ (turn7 w)

theorem turn8 (w : Bool) (l : Side) :
    run true (fB w) (if w then 27 else 29) (c 0 (false ::: false ::: true ::: l) false s8) = some (c 0 l true (alt10 2 s0)) := by
  cases w <;> rfl

theorem hop8 (w : Bool) (n : Nat) :
    run true (fB w) (10*(n+1)+(if w then 27 else 29)) (sec (n+1) s8) = some (sec (n+3) s0) :=
  advance true (fB w) n _ _ _ (turn8 w)

theorem cycle (w : Bool) (n : Nat) :
    run true (fB w) (90*(n+1)+(if w then 1047 else 1065)) (sec (n+1) s0) = some (sec (n+19) s0) := by
  rw [show 90*(n+1)+(if w then 1047 else 1065) = (10*(n+1)+(if w then 55 else 57))+(10*(n+3)+(if w then 27 else 29))+(10*(n+5)+(if w then 65 else 67))+(10*(n+7)+(if w then 27 else 29))+(10*(n+9)+(if w then 39 else 41))+(10*(n+11)+(if w then 27 else 29))+(10*(n+13)+(if w then 33 else 35))+(10*(n+15)+(if w then 27 else 29))+(10*(n+17)+(if w then 27 else 29)) by cases w <;> simp <;> omega]
  rw [show (10*(n+1)+(if w then 55 else 57))+(10*(n+3)+(if w then 27 else 29))+(10*(n+5)+(if w then 65 else 67))+(10*(n+7)+(if w then 27 else 29))+(10*(n+9)+(if w then 39 else 41))+(10*(n+11)+(if w then 27 else 29))+(10*(n+13)+(if w then 33 else 35))+(10*(n+15)+(if w then 27 else 29))+(10*(n+17)+(if w then 27 else 29)) = (10*(n+1)+(if w then 55 else 57))+((10*(n+3)+(if w then 27 else 29))+(10*(n+5)+(if w then 65 else 67))+(10*(n+7)+(if w then 27 else 29))+(10*(n+9)+(if w then 39 else 41))+(10*(n+11)+(if w then 27 else 29))+(10*(n+13)+(if w then 33 else 35))+(10*(n+15)+(if w then 27 else 29))+(10*(n+17)+(if w then 27 else 29))) by omega,run_add]
  have h0 := hop0 w (n+0)
  rw [show n+0+1=n+1 by omega,show n+0+3=n+3 by omega] at h0
  rw [h0]
  simp only [Option.bind_some]
  rw [show (10*(n+3)+(if w then 27 else 29))+(10*(n+5)+(if w then 65 else 67))+(10*(n+7)+(if w then 27 else 29))+(10*(n+9)+(if w then 39 else 41))+(10*(n+11)+(if w then 27 else 29))+(10*(n+13)+(if w then 33 else 35))+(10*(n+15)+(if w then 27 else 29))+(10*(n+17)+(if w then 27 else 29)) = (10*(n+3)+(if w then 27 else 29))+((10*(n+5)+(if w then 65 else 67))+(10*(n+7)+(if w then 27 else 29))+(10*(n+9)+(if w then 39 else 41))+(10*(n+11)+(if w then 27 else 29))+(10*(n+13)+(if w then 33 else 35))+(10*(n+15)+(if w then 27 else 29))+(10*(n+17)+(if w then 27 else 29))) by omega,run_add]
  have h1 := hop1 w (n+2)
  rw [show n+2+1=n+3 by omega,show n+2+3=n+5 by omega] at h1
  rw [h1]
  simp only [Option.bind_some]
  rw [show (10*(n+5)+(if w then 65 else 67))+(10*(n+7)+(if w then 27 else 29))+(10*(n+9)+(if w then 39 else 41))+(10*(n+11)+(if w then 27 else 29))+(10*(n+13)+(if w then 33 else 35))+(10*(n+15)+(if w then 27 else 29))+(10*(n+17)+(if w then 27 else 29)) = (10*(n+5)+(if w then 65 else 67))+((10*(n+7)+(if w then 27 else 29))+(10*(n+9)+(if w then 39 else 41))+(10*(n+11)+(if w then 27 else 29))+(10*(n+13)+(if w then 33 else 35))+(10*(n+15)+(if w then 27 else 29))+(10*(n+17)+(if w then 27 else 29))) by omega,run_add]
  have h2 := hop2 w (n+4)
  rw [show n+4+1=n+5 by omega,show n+4+3=n+7 by omega] at h2
  rw [h2]
  simp only [Option.bind_some]
  rw [show (10*(n+7)+(if w then 27 else 29))+(10*(n+9)+(if w then 39 else 41))+(10*(n+11)+(if w then 27 else 29))+(10*(n+13)+(if w then 33 else 35))+(10*(n+15)+(if w then 27 else 29))+(10*(n+17)+(if w then 27 else 29)) = (10*(n+7)+(if w then 27 else 29))+((10*(n+9)+(if w then 39 else 41))+(10*(n+11)+(if w then 27 else 29))+(10*(n+13)+(if w then 33 else 35))+(10*(n+15)+(if w then 27 else 29))+(10*(n+17)+(if w then 27 else 29))) by omega,run_add]
  have h3 := hop3 w (n+6)
  rw [show n+6+1=n+7 by omega,show n+6+3=n+9 by omega] at h3
  rw [h3]
  simp only [Option.bind_some]
  rw [show (10*(n+9)+(if w then 39 else 41))+(10*(n+11)+(if w then 27 else 29))+(10*(n+13)+(if w then 33 else 35))+(10*(n+15)+(if w then 27 else 29))+(10*(n+17)+(if w then 27 else 29)) = (10*(n+9)+(if w then 39 else 41))+((10*(n+11)+(if w then 27 else 29))+(10*(n+13)+(if w then 33 else 35))+(10*(n+15)+(if w then 27 else 29))+(10*(n+17)+(if w then 27 else 29))) by omega,run_add]
  have h4 := hop4 w (n+8)
  rw [show n+8+1=n+9 by omega,show n+8+3=n+11 by omega] at h4
  rw [h4]
  simp only [Option.bind_some]
  rw [show (10*(n+11)+(if w then 27 else 29))+(10*(n+13)+(if w then 33 else 35))+(10*(n+15)+(if w then 27 else 29))+(10*(n+17)+(if w then 27 else 29)) = (10*(n+11)+(if w then 27 else 29))+((10*(n+13)+(if w then 33 else 35))+(10*(n+15)+(if w then 27 else 29))+(10*(n+17)+(if w then 27 else 29))) by omega,run_add]
  have h5 := hop5 w (n+10)
  rw [show n+10+1=n+11 by omega,show n+10+3=n+13 by omega] at h5
  rw [h5]
  simp only [Option.bind_some]
  rw [show (10*(n+13)+(if w then 33 else 35))+(10*(n+15)+(if w then 27 else 29))+(10*(n+17)+(if w then 27 else 29)) = (10*(n+13)+(if w then 33 else 35))+((10*(n+15)+(if w then 27 else 29))+(10*(n+17)+(if w then 27 else 29))) by omega,run_add]
  have h6 := hop6 w (n+12)
  rw [show n+12+1=n+13 by omega,show n+12+3=n+15 by omega] at h6
  rw [h6]
  simp only [Option.bind_some]
  rw [show (10*(n+15)+(if w then 27 else 29))+(10*(n+17)+(if w then 27 else 29)) = (10*(n+15)+(if w then 27 else 29))+((10*(n+17)+(if w then 27 else 29))) by omega,run_add]
  have h7 := hop7 w (n+14)
  rw [show n+14+1=n+15 by omega,show n+14+3=n+17 by omega] at h7
  rw [h7]
  simp only [Option.bind_some]
  have h8 := hop8 w (n+16)
  rw [show n+16+1=n+17 by omega,show n+16+3=n+19 by omega] at h8
  rw [h8]

#print axioms cycle
end Raw11ExtraFamily
