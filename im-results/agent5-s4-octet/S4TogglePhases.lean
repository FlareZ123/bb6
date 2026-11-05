import S4ToggleHead
import Lean.Elab.Tactic.Omega

namespace S4TogglePhases
open S4Power S4Octet S4Toggle
set_option maxHeartbeats 0

theorem p283 (S : List Nat) :
  P (283::S)=(G 1023 S).map (282::·) := by
  cases S with
  | nil => simp [P,G,H]
  | cons b R => simp [P,G,H]

private theorem a281 (S : List Nat) :
  G 509 (281::S) = some (397::bumpN 395 S) := by
  cases S <;> simp [G,H,bumpN]

private theorem b281 (S : List Nat) :
  G 290 (397::bumpN 395 S) = (G 739 S).map (343::·) := by
  cases S <;> simp [G,H,bumpN]

private theorem c281 (U : List Nat) :
  G 219 (343::U) = some (283::bumpN 281 U) := by
  cases U <;> simp [G,H,bumpN]

theorem p281 (S : List Nat) :
  P (281::S) = (G 739 S).map (fun U => 283::bumpN 281 U) := by
  unfold P
  rw [a281]
  simp only [Option.bind_some]
  rw [b281]
  cases h : G 739 S with
  | none => simp [h]
  | some U => simp [h,c281]

private theorem a280 (S : List Nat) :
  G 509 (280::S) = (G 395 S).map (394::·) := by
  cases S <;> simp [G,H]

private theorem b280 (U : List Nat) :
  G 290 (394::U) = some (344::bumpN 342 U) := by
  cases U <;> simp [G,H,bumpN]

private theorem c280 (U : List Nat) :
  G 219 (344::bumpN 342 U) = (G 624 U).map (281::·) := by
  cases U <;> simp [G,H,bumpN]

theorem p280 (S : List Nat) :
  P (280::S) = (G 395 S).bind (fun U => (G 624 U).map (281::·)) := by
  unfold P
  rw [a280]
  cases h : G 395 S with
  | none => simp [h]
  | some U => simp [h,b280,c280]

private theorem a282 (S : List Nat) :
  G 509 (282::S) = (G 396 S).map (395::·) := by
  cases S <;> simp [G,H]

private theorem b282 (U : List Nat) :
  G 290 (395::U) = (G 343 U).map (342::·) := by
  cases U <;> simp [G,H]

private theorem c282 (V : List Nat) :
  G 219 (342::V) = (G 281 V).map (280::·) := by
  cases V <;> simp [G,H]

theorem p282 (S : List Nat) :
  P (282::S) = (G 396 S).bind (fun U => (G 343 U).bind (fun V => (G 281 V).map (280::·))) := by
  unfold P
  rw [a282]
  cases h : G 396 S with
  | none => simp [h]
  | some U =>
      simp only [h,Option.map_some, Option.bind_some]
      rw [b282]
      cases h2 : G 343 U with
      | none => simp [h2]
      | some V => simp [h2,c282]

#print axioms p283
#print axioms p281
#print axioms p280
#print axioms p282
end S4TogglePhases
