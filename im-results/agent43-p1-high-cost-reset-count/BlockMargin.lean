import BlockCarry
import MarginCert
namespace BB6.Agent43Block
open BB6.Agent43CarryCert

/-- The two distances to the moving endpoints contract by at most a factor two. -/
def Envelope (Q L j h c : Nat) : Prop := 3*2^h ≤ c ∧ c+2^h*L+j ≤ Q+2

theorem envelope_step (Q L j h v : Nat) (cs : List Nat)
    (hj : j≤Q) (hc : ∀ c∈cs, Envelope Q L j (h+1) c)
    (hv : v∈step Q j cs) : Envelope Q L (j+1) h v := by
  obtain ⟨c,hc',he⟩ := step_eqn hv
  obtain ⟨hl,hu⟩ := hc c hc'
  unfold Envelope
  rw [Nat.pow_succ] at hl
  rw [Nat.pow_succ,Nat.mul_comm (2^h) 2,Nat.mul_assoc] at hu
  rcases he with he|he <;> omega

theorem envelope_run (Q L j h i : Nat) (cs : List Nat)
    (hj : j+h≤Q+1) (hi : i≤h) (hc : ∀ c∈cs, Envelope Q L j h c)
    (v : Nat) (hv : v∈states Q j cs i) : Envelope Q L (j+i) (h-i) v := by
  induction i generalizing j h cs with
  | zero => simpa [states] using hc v hv
  | succ i ih =>
    cases h with
    | zero => omega
    | succ h =>
      have hs : ∀ c∈step Q j cs, Envelope Q L (j+1) h c :=
        fun c hm => envelope_step Q L j h c cs (by omega) hc hm
      have hh := ih (j+1) h (step Q j cs) (by omega) (by omega) hs hv
      simpa only [Nat.succ_sub_succ_eq_sub,show j+ (i+1)=j+1+i by omega] using hh

theorem envelope_good (Q L j h v : Nat) (he : Envelope Q L j h v) :
    v≠2 ∧ v+L+j≤Q+2 := by
  obtain ⟨hl,hu⟩ := he
  have hp : 1≤2^h := Nat.two_pow_pos h
  have hh := Nat.mul_le_mul_right L hp
  omega

/-- A block certificate is allowed to overapproximate endpoint states. -/
def Cover (Q L j : Nat) (cs : List Nat) (k : Nat) (ds : List Nat) : Prop :=
  (∀ v∈states Q j cs k, v∈ds) ∧
  ∀ i<k, ∀ c∈states Q j cs i, c≠2 ∧ c+L+(j+i)≤Q+2

theorem states_mono (Q j k : Nat) (cs ds : List Nat)
    (h : ∀ c∈cs, c∈ds) (v : Nat) (hv : v∈states Q j cs k) : v∈states Q j ds k := by
  induction k generalizing j cs ds with
  | zero => exact h v hv
  | succ k ih =>
    apply ih (j+1) (step Q j cs) (step Q j ds) _ hv
    intro c hc
    simp only [step,List.mem_flatMap] at hc ⊢
    obtain ⟨p,hp,hc⟩ := hc
    exact ⟨p,h p hp,hc⟩

theorem Cover.append {Q L j a b : Nat} {cs ds es : List Nat}
    (h : Cover Q L j cs a ds) (h' : Cover Q L (j+a) ds b es) : Cover Q L j cs (a+b) es := by
  obtain ⟨he,ha⟩ := h
  obtain ⟨he',hb⟩ := h'
  refine ⟨?_,?_⟩
  · intro v hv
    rw [states_add] at hv
    exact he' v (states_mono Q (j+a) b _ _ he v hv)
  · intro i hi c hc
    by_cases hlt : i<a
    · exact ha i hlt c hc
    · have hi' : i=a+(i-a) := by omega
      rw [hi',states_add] at hc
      have hm := states_mono Q (j+a) (i-a) _ _ he c hc
      have hg := hb (i-a) (by omega) c hm
      simpa only [show j+a+(i-a)=j+i by omega] using hg

def envelopeCheck (Q L j h : Nat) (cs : List Nat) : Bool :=
  cs.all fun c => decide (3*2^h≤c) && decide (c+2^h*L+j≤Q+2)

theorem cover_block (Q L j h : Nat) (cs ds : List Nat)
    (hj : j+h≤Q+1) (he : envelopeCheck Q L j h cs = true)
    (hd : blockStep Q j h cs = ds) : Cover Q L j cs h ds := by
  refine ⟨?_,?_⟩
  · intro v hv; rw [←hd]; exact block_sound Q j h cs v hv
  · intro i hi c hc
    have hh : ∀ v∈cs, Envelope Q L j h v := by
      intro v hv
      have hh := List.all_eq_true.mp he v hv
      simpa [Envelope] using hh
    exact envelope_good Q L (j+i) (h-i) c (envelope_run Q L j h i cs hj (by omega) hh c hc)

theorem Cover.toMargin {Q L j k : Nat} {cs : List Nat}
    (h : Cover Q L j cs k []) : MarginSafe Q L j cs k [] := by
  refine ⟨?_,h.2⟩
  cases he : states Q j cs k with
  | nil => rfl
  | cons c tail =>
    have hc : c∈states Q j cs k := by simp [he]
    have hh := h.1 c hc
    simp at hh

theorem cover_single (Q L j : Nat) (cs ds : List Nat)
    (hg : cs.all (Good Q L j) = true) (he : step Q j cs=ds) : Cover Q L j cs 1 ds := by
  refine ⟨?_,?_⟩
  · intro c hc; simpa [states,he] using hc
  · intro i hi c hc
    have hi' : i=0 := by omega
    subst i
    have hh := List.all_eq_true.mp hg c hc
    simpa [Good] using hh

#print axioms cover_block
#print axioms Cover.append
#print axioms Cover.toMargin
#print axioms cover_single
end BB6.Agent43Block
