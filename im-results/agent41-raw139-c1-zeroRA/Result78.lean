import Seg6_0
namespace BB6.Agent41SegmentTrace
open BB6.Coverage
set_option maxHeartbeats 1000000

def final78 : Config := cfg (-288) 576 (fun _ => false) s6998.dst

theorem start78 : cfg (-288) 576 (fun _ => false) s6998.src = blank := by
  change (⟨0,0,patch (-288) 576 0 (fun _ => false)⟩ : Config) = blank
  unfold blank
  congr
  funext x
  simp [patch]

theorem run78 : run (tick table) 14876964 = some final78 := by
  rw [←runFrom_blank,←start78]
  exact h6998 (-288) (fun _ => false)

theorem final_slot78 : final78.state = 5 ∧ final78.tape final78.head = false ∧ final78.head = 52 := by decide +kernel

theorem halt78 : HaltsAt (tick table) 14876965 := by
  constructor
  · change ((run (tick table) 14876964).bind (tick table)).isNone = true
    rw [run78]
    have ht : tick table final78 = none := by
      unfold tick
      rw [final_slot78.1,final_slot78.2.1]
      rfl
    rw [Option.bind_some,ht]
    rfl
  · intro k hk
    have hh : ∀ j : Nat, (run (tick table) (k+j)).isSome = true → (run (tick table) k).isSome = true := by
      intro j
      induction j with
      | zero => simpa
      | succ j ih =>
        intro h
        apply ih
        rw [Nat.add_succ,run] at h
        cases he : run (tick table) (k+j) <;> simp_all
    apply hh (14876964-k)
    rw [show k+(14876964-k) = 14876964 by omega,run78]
    rfl

#print axioms run78
#print axioms halt78
end BB6.Agent41SegmentTrace
