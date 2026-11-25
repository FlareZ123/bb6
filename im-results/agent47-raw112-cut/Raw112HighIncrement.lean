import Raw112CarrySweeps
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Raw112HighIncrement
open BB6Coverage BB6Coverage.Agent31Pump Raw112CarrySweeps

def seed : Nat → List Bool
  | 0 => []
  | 1 => w "11111"
  | 2 => w "0000111111"
  | 3 => w "111000000111111"
  | 4 => w "001111110111111"
  | 5 => w "111111110111111"
  | _ => []
def evenPre : Nat → List Bool
  | 0 => w "000000000000000"
  | 1 => w "111110000000000"
  | 2 => w "000011111100000"
  | 3 => w "111000000111111"
  | 4 => w "001111110111111"
  | 5 => w "111111110111111"
  | _ => []
def oddPre : Nat → List Bool
  | 0 => w "000000011000001"
  | 1 => w "111110011000001"
  | 2 => w "000011111000001"
  | 3 => w "111000001111111"
  | 4 => w "001111111111111"
  | 5 => w "111111111111111"
  | _ => []
def digitPre (p r : Nat) : List Bool := if p = 0 then evenPre r else oddPre r

def high (k : Nat) : List Bool :=
  if hk : k < 6 then seed k
  else digitPre ((k/6)%2) (k%6) ++ high (k/6)
termination_by k
decreasing_by omega

theorem high_small (k : Nat) (h : k < 6) : high k = seed k := by rw [high]; simp [h]
theorem high_six (m r : Nat) (hm : 1 ≤ m) (hr : r < 6) :
    high (6*m+r) = digitPre (m%2) r ++ high m := by
  rw [high]
  have h1 : ¬ 6*m+r < 6 := by omega
  have h2 : (6*m+r)/6 = m := by omega
  have h3 : (6*m+r)%6 = r := by omega
  simp [h1,h2,h3]

def target (k : Nat) (L R : List Bool) : Z0 :=
  if k%2 = 0 then cfg 3 (true::L) (false::R) else cfg 1 (true::L) (true::R)

/-- A finite local increment, without inspecting either arbitrary context. -/
theorem digit_inc (p r : Nat) (hp : p < 2) (hr : r < 5) :
    ∃ t, 0<t ∧ ∀ L R, run0 table t (cfg 4 (w "10" ++ L) (digitPre p r ++ R)) =
      some (target r L (digitPre p (r+1) ++ R)) := by
  have hp' : p=0 ∨ p=1 := by omega
  have hr' : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 := by omega
  rcases hp' with h | h <;> subst p
  · rcases hr' with h|h|h|h|h <;> subst r
    · exact ⟨21,by decide,fun L R => by rfl⟩
    · exact ⟨53,by decide,fun L R => by rfl⟩
    · exact ⟨73,by decide,fun L R => by rfl⟩
    · exact ⟨41,by decide,fun L R => by rfl⟩
    · exact ⟨15,by decide,fun L R => by rfl⟩
  · rcases hr' with h|h|h|h|h <;> subst r
    · exact ⟨21,by decide,fun L R => by rfl⟩
    · exact ⟨47,by decide,fun L R => by rfl⟩
    · exact ⟨67,by decide,fun L R => by rfl⟩
    · exact ⟨41,by decide,fun L R => by rfl⟩
    · exact ⟨15,by decide,fun L R => by rfl⟩

def evenFrame := w "111111011111111"
def oddFrame := w "111111111111111"

theorem carry_even_enter (L R : List Bool) :
    run0 table 77 (cfg 4 (w "10" ++ L) (evenPre 5 ++ R)) =
      some (cfg 4 (w "10" ++ (evenFrame ++ L)) R) := by rfl

theorem carry_even_finish (L R : List Bool) :
    run0 table 23 (cfg 3 (true::(evenFrame ++ L)) (false::R)) =
      some (cfg 1 (true::L) (true::(oddPre 0 ++ R))) := by rfl

theorem carry_odd_enter (L R : List Bool) :
    run0 table 75 (cfg 4 (w "10" ++ L) (oddPre 5 ++ R)) =
      some (cfg 4 (w "10" ++ (oddFrame ++ L)) R) := by rfl

theorem carry_odd_finish (L R : List Bool) :
    run0 table 15 (cfg 1 (true::(oddFrame ++ L)) (true::R)) =
      some (cfg 1 (true::L) (true::(evenPre 0 ++ R))) := by rfl

/-- The exact high increment at every natural counter value. -/
theorem high_inc (k : Nat) : ∃ t, 0<t ∧ ∀ L,
    run0 table t (cfg 4 (w "10" ++ L) (high k)) = some (target k L (high (k+1))) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases hsmall : k < 6
    · have casesK : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 := by omega
      rcases casesK with h|h|h|h|h|h <;> subst k
      · exact ⟨21,by decide,fun L => by rw [high_small 0 (by decide),high_small 1 (by decide)]; rfl⟩
      · exact ⟨53,by decide,fun L => by rw [high_small 1 (by decide),high_small 2 (by decide)]; rfl⟩
      · exact ⟨73,by decide,fun L => by rw [high_small 2 (by decide),high_small 3 (by decide)]; rfl⟩
      · exact ⟨41,by decide,fun L => by rw [high_small 3 (by decide),high_small 4 (by decide)]; rfl⟩
      · exact ⟨15,by decide,fun L => by rw [high_small 4 (by decide),high_small 5 (by decide)]; rfl⟩
      · exact ⟨121,by decide,fun L => by rw [high_small 5 (by decide),show 5+1=6*1+0 by decide, high_six 1 0 (by decide) (by decide),high_small 1 (by decide)]; rfl⟩
    · let m := k/6
      let r := k%6
      have hm : 1 ≤ m := by dsimp [m]; omega
      have hr : r < 6 := by dsimp [r]; omega
      have hkr : k = 6*m+r := by dsimp [m,r]; omega
      have hmk : m < k := by dsimp [m]; omega
      have hk : high k = digitPre (m%2) r ++ high m := by rw [hkr,high_six m r hm hr]
      by_cases hcarry : r=5
      · obtain ⟨t,ht,hi⟩ := ih m hmk
        have hnext : k+1 = 6*(m+1)+0 := by omega
        have hp : k%2 ≠ 0 := by omega
        by_cases he : m%2=0
        · have he' : (m+1)%2=1 := by omega
          refine ⟨77+t+23,by omega,fun L => ?_⟩
          rw [hk,hnext,high_six (m+1) 0 (by omega) (by decide)]
          simp only [digitPre,he,he',ite_true,ite_false,show (1:Nat) ≠ 0 by decide,target,hp,hcarry]
          have h1 := carry_even_enter L (high m)
          have h2 := hi (evenFrame++L)
          simp only [target,he,ite_true] at h2
          exact join0 (join0 h1 h2) (carry_even_finish L (high (m+1)))
        · have he' : (m+1)%2=0 := by omega
          refine ⟨75+t+15,by omega,fun L => ?_⟩
          rw [hk,hnext,high_six (m+1) 0 (by omega) (by decide)]
          simp only [digitPre,he,he',ite_true,ite_false,target,hp,hcarry]
          have h1 := carry_odd_enter L (high m)
          have h2 := hi (oddFrame++L)
          simp only [target,he,ite_false] at h2
          exact join0 (join0 h1 h2) (carry_odd_finish L (high (m+1)))
      · have hr' : r<5 := by omega
        obtain ⟨t,ht,h⟩ := digit_inc (m%2) r (by omega) hr'
        refine ⟨t,ht,fun L => ?_⟩
        have hnext : k+1=6*m+(r+1) := by omega
        rw [hk,hnext,high_six m (r+1) hm (by omega)]
        have hpar : k%2=r%2 := by omega
        simpa only [target,hpar] using h L (high m)

#print axioms high_inc
end BB6Coverage.Agent31Pump.Raw112HighIncrement
