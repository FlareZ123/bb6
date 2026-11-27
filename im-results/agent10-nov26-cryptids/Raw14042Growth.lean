import Raw14042ArithmeticInvariant
import Raw14042Entry
import Raw140DoubleCore
namespace Raw14042Growth
open Raw14042ArithmeticInvariant
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140Double Raw140VariantTransfer
set_option maxHeartbeats 2000000

theorem terminal_growth (b : Bank) (p n s : Nat) (hp : 24≤p) (he : p%2=0) (hn : n<2) (hs : s<6) :
    p+12 ≤ (terminal b p n s).p := by
  have hN : n=0 ∨ n=1 := by omega
  have hS : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hN with rfl|rfl <;> rcases hS with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;>
    simp only [terminal,d,cc,a0,bs,b0,Raw14042ArithmeticInvariant.next,Raw14042ArithmeticInvariant.carry] <;> (try split) <;> simp_all <;> omega

theorem step_growth (x : Section) (hx : good x) : x.p+12 ≤ (step x).p := by
  unfold step
  split
  · simp [drainStep]
  · exact terminal_growth x.kind x.p x.n x.s hx.1 hx.2.1 (by omega) hx.2.2

def root : Section := ⟨.b,32,1,1⟩
def rootOrbit : Nat → Section
  | 0 => root
  | k+1 => step (rootOrbit k)
theorem root_good (k : Nat) : good (rootOrbit k) := by
  induction k with
  | zero => simp [rootOrbit, root, good]
  | succ k ih => exact step_good _ ih
theorem root_growth (k : Nat) : 32+12*k ≤ (rootOrbit k).p := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h := step_growth (rootOrbit k) (root_good k)
    change 32+12*(k+1) ≤ (step (rootOrbit k)).p
    omega

-- Once the source obligations are discharged, positive times accumulate
-- from the exact blank entry with no need to enumerate the arithmetic orbit.
def Plus (M : Table) (a b : Prim) : Prop := ∃ t, 0<t ∧ run M t a = some b

theorem root_runs (encode : Section → Prim)
    (hroot : encode root = Raw14042Entry.rootS5.prim)
    (hstep : ∀ x, good x → Plus M42 (encode x) (encode (step x))) (k : Nat) :
    ∃ t, 5985+k ≤ t ∧ run M42 t primBlank = some (encode (rootOrbit k)) := by
  induction k with
  | zero => exact ⟨5985,by omega,by simpa only [rootOrbit,hroot] using Raw14042Entry.entry⟩
  | succ k ih =>
    obtain ⟨t,ht,hr⟩ := ih
    obtain ⟨u,hu,hs⟩ := hstep (rootOrbit k) (root_good k)
    exact ⟨t+u,by omega,join hr hs⟩
theorem root_unbounded (encode : Section → Prim)
    (hroot : encode root = Raw14042Entry.rootS5.prim)
    (hstep : ∀ x, good x → Plus M42 (encode x) (encode (step x))) (n : Nat) :
    ∃ c, run M42 n primBlank = some c := by
  obtain ⟨t,ht,hr⟩ := root_runs encode hroot hstep n
  have he : t = n + (t-n) := by omega
  rw [he,run_add] at hr
  cases h : run M42 n primBlank with
  | none => simp [h] at hr
  | some c => exact ⟨c,rfl⟩
#print axioms step_growth
#print axioms root_growth
#print axioms root_runs
#print axioms root_unbounded
end Raw14042Growth
