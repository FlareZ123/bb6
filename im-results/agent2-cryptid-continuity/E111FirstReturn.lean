import Lean.Elab.Tactic.Omega
import EOneTripleReturn
import NoEarlierF

namespace BB6.CryptidE111FirstReturn
open CryptidBoundary
open BB6.Agent2EOneTriple
open BB6.CryptidFirstReturn
set_option maxHeartbeats 10000000
set_option maxRecDepth 3000
set_option linter.unusedSimpArgs false

/-- The head must be F scanning zero with *the entire physical left tape blank*. -/
def IsPhysicalReturn (c : Cfg) : Prop :=
  c.st = 5 ∧ c.h = false ∧ c.l = []

/-- Strict open interval: time zero is included and time n is excluded. -/
def NoReturn (c : Cfg) (n : Nat) : Prop :=
  ∀ t, t < n → ¬ IsPhysicalReturn (run t c)

private theorem appendNoReturn (c d : Cfg) (a b : Nat)
  (hc : NoReturn c a) (he : run a c = d)
  (hd : NoReturn d b) : NoReturn c (a+b) := by
  intro t ht
  by_cases hsmall : t < a
  · exact hc t hsmall
  · have hdecomp : t = a+(t-a) := by omega
    rw [hdecomp,run_add,he]
    exact hd (t-a) (by omega)

private theorem local_0 (m : Nat) (ys : List Bool) :
    NoReturn (e0 m ys) 10 := by
  intro t ht
  have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 ∨ t=7 ∨ t=8 ∨ t=9 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [IsPhysicalReturn,e0,run,step,goL,goR,pairs,List.append_assoc]

private theorem local_10 (m : Nat) (ys : List Bool) :
    NoReturn (e10 m ys) 10 := by
  intro t ht
  have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 ∨ t=7 ∨ t=8 ∨ t=9 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [IsPhysicalReturn,e10,run,step,goL,goR,pairs,List.append_assoc]

private theorem local_20 (m : Nat) (ys : List Bool) :
    NoReturn (e20 m ys) 10 := by
  intro t ht
  have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 ∨ t=7 ∨ t=8 ∨ t=9 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [IsPhysicalReturn,e20,run,step,goL,goR,pairs,List.append_assoc]

private theorem local_30 (m : Nat) (ys : List Bool) :
    NoReturn (e30 m ys) 10 := by
  intro t ht
  have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 ∨ t=7 ∨ t=8 ∨ t=9 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [IsPhysicalReturn,e30,run,step,goL,goR,pairs,List.append_assoc]

private theorem local_40 (m : Nat) (ys : List Bool) :
    NoReturn (e40 m ys) 10 := by
  intro t ht
  have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 ∨ t=7 ∨ t=8 ∨ t=9 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [IsPhysicalReturn,e40,run,step,goL,goR,pairs,List.append_assoc]

private theorem local_50 (m : Nat) (ys : List Bool) :
    NoReturn (e50 m ys) 10 := by
  intro t ht
  have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 ∨ t=7 ∨ t=8 ∨ t=9 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [IsPhysicalReturn,e50,run,step,goL,goR,pairs,List.append_assoc]

private theorem local_60 (m : Nat) (ys : List Bool) :
    NoReturn (e60 m ys) 10 := by
  intro t ht
  have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 ∨ t=7 ∨ t=8 ∨ t=9 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [IsPhysicalReturn,e60,run,step,goL,goR,pairs,List.append_assoc]

private theorem local_70 (m : Nat) (ys : List Bool) :
    NoReturn (e70 m ys) 10 := by
  intro t ht
  have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 ∨ t=7 ∨ t=8 ∨ t=9 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [IsPhysicalReturn,e70,run,step,goL,goR,pairs,List.append_assoc]

private theorem local_80 (m : Nat) (ys : List Bool) :
    NoReturn (e80 m ys) 10 := by
  intro t ht
  have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 ∨ t=7 ∨ t=8 ∨ t=9 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [IsPhysicalReturn,e80,run,step,goL,goR,pairs,List.append_assoc]

private theorem local_90 (m : Nat) (ys : List Bool) :
    NoReturn (e90 m ys) 10 := by
  intro t ht
  have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 ∨ t=7 ∨ t=8 ∨ t=9 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [IsPhysicalReturn,e90,run,step,goL,goR,pairs,List.append_assoc]

private theorem local_100 (m : Nat) (ys : List Bool) :
    NoReturn (e100 m ys) 10 := by
  intro t ht
  have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 ∨ t=7 ∨ t=8 ∨ t=9 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [IsPhysicalReturn,e100,run,step,goL,goR,pairs,List.append_assoc]

private theorem local_110 (m : Nat) (ys : List Bool) :
    NoReturn (e110 m ys) 10 := by
  intro t ht
  have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 ∨ t=7 ∨ t=8 ∨ t=9 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [IsPhysicalReturn,e110,run,step,goL,goR,pairs,List.append_assoc]

private theorem local_120 (m : Nat) (ys : List Bool) :
    NoReturn (e120 m ys) 10 := by
  intro t ht
  have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 ∨ t=7 ∨ t=8 ∨ t=9 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [IsPhysicalReturn,e120,run,step,goL,goR,pairs,List.append_assoc]

private theorem local_130 (m : Nat) (ys : List Bool) :
    NoReturn (e130 m ys) 4 := by
  intro t ht
  have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  all_goals simp [IsPhysicalReturn,e130,run,step,goL,goR,pairs,List.append_assoc]

private theorem before134 (m : Nat) (ys : List Bool) :
  NoReturn (e0 m ys) 134 := by
  have h130 : NoReturn (e130 m ys) 4 := local_130 m ys
  have h120 : NoReturn (e120 m ys) 14 := by
    simpa only [show 10+4 = 14 by omega] using
      (appendNoReturn (e120 m ys) (e130 m ys)
        10 4 (local_120 m ys) (ee120 m ys) h130)
  have h110 : NoReturn (e110 m ys) 24 := by
    simpa only [show 10+14 = 24 by omega] using
      (appendNoReturn (e110 m ys) (e120 m ys)
        10 14 (local_110 m ys) (ee110 m ys) h120)
  have h100 : NoReturn (e100 m ys) 34 := by
    simpa only [show 10+24 = 34 by omega] using
      (appendNoReturn (e100 m ys) (e110 m ys)
        10 24 (local_100 m ys) (ee100 m ys) h110)
  have h90 : NoReturn (e90 m ys) 44 := by
    simpa only [show 10+34 = 44 by omega] using
      (appendNoReturn (e90 m ys) (e100 m ys)
        10 34 (local_90 m ys) (ee90 m ys) h100)
  have h80 : NoReturn (e80 m ys) 54 := by
    simpa only [show 10+44 = 54 by omega] using
      (appendNoReturn (e80 m ys) (e90 m ys)
        10 44 (local_80 m ys) (ee80 m ys) h90)
  have h70 : NoReturn (e70 m ys) 64 := by
    simpa only [show 10+54 = 64 by omega] using
      (appendNoReturn (e70 m ys) (e80 m ys)
        10 54 (local_70 m ys) (ee70 m ys) h80)
  have h60 : NoReturn (e60 m ys) 74 := by
    simpa only [show 10+64 = 74 by omega] using
      (appendNoReturn (e60 m ys) (e70 m ys)
        10 64 (local_60 m ys) (ee60 m ys) h70)
  have h50 : NoReturn (e50 m ys) 84 := by
    simpa only [show 10+74 = 84 by omega] using
      (appendNoReturn (e50 m ys) (e60 m ys)
        10 74 (local_50 m ys) (ee50 m ys) h60)
  have h40 : NoReturn (e40 m ys) 94 := by
    simpa only [show 10+84 = 94 by omega] using
      (appendNoReturn (e40 m ys) (e50 m ys)
        10 84 (local_40 m ys) (ee40 m ys) h50)
  have h30 : NoReturn (e30 m ys) 104 := by
    simpa only [show 10+94 = 104 by omega] using
      (appendNoReturn (e30 m ys) (e40 m ys)
        10 94 (local_30 m ys) (ee30 m ys) h40)
  have h20 : NoReturn (e20 m ys) 114 := by
    simpa only [show 10+104 = 114 by omega] using
      (appendNoReturn (e20 m ys) (e30 m ys)
        10 104 (local_20 m ys) (ee20 m ys) h30)
  have h10 : NoReturn (e10 m ys) 124 := by
    simpa only [show 10+114 = 124 by omega] using
      (appendNoReturn (e10 m ys) (e20 m ys)
        10 114 (local_10 m ys) (ee10 m ys) h20)
  have h0 : NoReturn (e0 m ys) 134 := by
    simpa only [show 10+124 = 134 by omega] using
      (appendNoReturn (e0 m ys) (e10 m ys)
        10 124 (local_0 m ys) (ee0 m ys) h10)
  exact h0

theorem e111_boundary_first_return (m : Nat) (ys : List Bool) :
    (run (2*m+137) (e0 m ys)).st=5 ∧
    NoReturn (e0 m ys) (2*m+137) := by
  constructor
  · rw [e111_run]
  · have hBsweep : NoReturn (sweepB m (packet ++ ys)) (2*m+3) := by
      intro t ht h
      exact sweepB_firstF m (packet ++ ys) t ht h.1
    have h := appendNoReturn (e0 m ys) (sweepB m (packet ++ ys))
      134 (2*m+3) (before134 m ys) (front m ys) hBsweep
    simpa only [show 134+(2*m+3)=2*m+137 by omega] using h

#print axioms before134
#print axioms e111_boundary_first_return
end BB6.CryptidE111FirstReturn
