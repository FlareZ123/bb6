import MarginCert
namespace BB6.Agent28HalfCarry
open BB6.Agent43CarryCert

def reflect (Q j c : Nat) : Nat := Q+2-j-c
def project (Q j c : Nat) : Nat := min c (reflect Q j c)

theorem step_reflect (Q j p c : Nat) (hj : j≤Q) (hp : p+j≤Q+2)
    (hc : c∈step Q j [p]) : reflect Q (j+1) c ∈ step Q j [reflect Q j p] := by
  simp only [step,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.mem_append] at hc ⊢
  rcases hc with h | h
  · by_cases he : p%2=0
    · simp [he] at h
      subst c
      right
      have hh : (reflect Q j p+(Q-j))%2=0 := by unfold reflect; omega
      simp only [hh,if_true,List.mem_singleton]
      unfold reflect
      omega
    · simp [he] at h
  · by_cases he : (p+(Q-j))%2=0
    · simp [he] at h
      subst c
      left
      have hh : reflect Q j p%2=0 := by unfold reflect; omega
      simp only [hh,if_true,List.mem_singleton]
      unfold reflect
      omega
    · simp [he] at h

theorem step_bounds (Q j p c : Nat) (hj : j≤Q) (hp : 0<p ∧ p+j<Q+2)
    (hc : c∈step Q j [p]) : 0<c ∧ c+j+1<Q+2 := by
  simp only [step,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.mem_append] at hc
  rcases hc with h | h
  · by_cases he : p%2=0
    · simp [he] at h; subst c; omega
    · simp [he] at h
  · by_cases he : (p+(Q-j))%2=0
    · simp [he] at h; subst c; omega
    · simp [he] at h

def halfOne (B p : Nat) : List Nat :=
  ((if p%2=0 then [p/2] else []) ++
    (if (B-p)%2=0 then [(B-p)/2] else [])).eraseDups

def halfStep (Q j : Nat) (cs : List Nat) : List Nat :=
  cs.flatMap (halfOne (Q+2-j))

theorem halfOne_left (B p : Nat) (he : p%2=0) : p/2∈halfOne B p := by
  simp [halfOne,he]

theorem halfOne_right (B p : Nat) (he : (B-p)%2=0) : (B-p)/2∈halfOne B p := by
  simp [halfOne,he]

theorem halfOne_reflect (B p c : Nat) (hp : p≤B) (hc : c∈halfOne B p) :
    c∈halfOne B (B-p) := by
  simp only [halfOne,Nat.sub_sub_self hp,List.mem_eraseDups,List.mem_append] at hc ⊢
  exact hc.elim Or.inr Or.inl

theorem halfOne_project (B p c : Nat) (hp : p≤B) (hc : c∈halfOne B p) :
    c∈halfOne B (min p (B-p)) := by
  by_cases h : p≤B-p
  · simpa [Nat.min_def,h] using hc
  · simpa [Nat.min_def,h] using halfOne_reflect B p c hp hc

theorem project_step (Q j p c : Nat) (hj : j≤Q) (hp : 0<p ∧ p+j<Q+2)
    (hc : c∈step Q j [p]) :
    project Q (j+1) c ∈ halfStep Q j [project Q j p] := by
  simp only [halfStep,List.mem_flatMap,List.mem_singleton]
  refine ⟨project Q j p,rfl,?_⟩
  unfold project reflect
  apply halfOne_project _ p _ (by omega)
  simp only [step,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.mem_append] at hc
  rcases hc with h | h
  · by_cases he : p%2=0
    · simp [he] at h
      subst c
      have hm : min (p/2) (Q+2-(j+1)-p/2)=p/2 := by
        rw [Nat.min_def,if_pos (by omega)]
      rw [hm]
      exact halfOne_left _ _ he
    · simp [he] at h
  · by_cases he : (p+(Q-j))%2=0
    · simp [he] at h
      subst c
      have hr : Q+2-(j+1)-(p+(Q-j))/2=(Q+2-j-p)/2 := by omega
      rw [hr]
      have hm : min ((p+(Q-j))/2) ((Q+2-j-p)/2)=(Q+2-j-p)/2 := by
        rw [Nat.min_comm,Nat.min_def,if_pos (by omega)]
      rw [hm]
      exact halfOne_right _ _ (by omega)
    · simp [he] at h

def halfStates (Q j : Nat) (cs : List Nat) : Nat → List Nat
  | 0 => cs
  | k+1 => halfStates Q (j+1) (halfStep Q j cs) k

theorem halfStates_add (Q j a b : Nat) (cs : List Nat) :
    halfStates Q j cs (a+b)=halfStates Q (j+a) (halfStates Q j cs a) b := by
  induction a generalizing j cs with
  | zero => simp [halfStates]
  | succ a ih =>
    rw [Nat.succ_add,halfStates,ih]
    have he : j+1+a=j+(a+1) := by omega
    rw [he]
    rfl

theorem full_to_half (Q j k : Nat) (cs hs : List Nat) (horizon : j+k≤Q+1)
    (h : ∀ p∈cs, 0<p ∧ p+j<Q+2 ∧ project Q j p∈hs) :
    ∀ c∈states Q j cs k, 0<c ∧ c+j+k<Q+2 ∧ project Q (j+k) c∈halfStates Q j hs k := by
  induction k generalizing j cs hs with
  | zero => simpa [states,halfStates] using h
  | succ k ih =>
    have hnext : ∀ c∈step Q j cs, 0<c ∧ c+(j+1)<Q+2 ∧ project Q (j+1) c∈halfStep Q j hs := by
      intro c hc
      simp only [step,List.mem_flatMap] at hc
      obtain ⟨p,hp,hc⟩ := hc
      have hc' : c∈step Q j [p] := by simpa [step] using hc
      obtain ⟨hpos,hb,hm⟩ := h p hp
      obtain ⟨hcpos,hcb⟩ := step_bounds Q j p c (by omega) ⟨hpos,hb⟩ hc'
      refine ⟨hcpos,by omega,?_⟩
      have hproj := project_step Q j p c (by omega) ⟨hpos,hb⟩ hc'
      simp only [halfStep,List.mem_flatMap,List.mem_singleton] at hproj ⊢
      obtain ⟨p',he,hc'⟩ := hproj
      subst p'
      exact ⟨project Q j p,hm,hc'⟩
    intro c hc
    have hh := ih (j+1) (step Q j cs) (halfStep Q j hs) (by omega) hnext c hc
    simpa only [halfStates,show j+(k+1)=j+1+k by omega,Nat.add_assoc] using hh

def halfCheck (Q L j : Nat) (cs ds : List Nat) : Nat → Bool
  | 0 => cs == ds
  | k+1 => cs.all (fun p => decide (L≤p)) && halfCheck Q L (j+1) (halfStep Q j cs) ds k

def HalfSafe (Q L j : Nat) (cs : List Nat) (k : Nat) (ds : List Nat) : Prop :=
  halfStates Q j cs k=ds ∧ ∀ i<k,∀ p∈halfStates Q j cs i,L≤p

theorem half_sound (Q L j : Nat) (cs ds : List Nat) (k : Nat)
    (h : halfCheck Q L j cs ds k=true) : HalfSafe Q L j cs k ds := by
  induction k generalizing j cs with
  | zero => simpa [HalfSafe,halfCheck,halfStates] using h
  | succ k ih =>
    simp only [halfCheck,Bool.and_eq_true] at h
    obtain ⟨hh,he⟩ := h
    obtain ⟨hend,hgood⟩ := ih (j+1) (halfStep Q j cs) he
    refine ⟨hend,?_⟩
    intro i hi p hp
    cases i with
    | zero => simpa using List.all_eq_true.mp hh p hp
    | succ i => exact hgood i (by omega) p hp

theorem HalfSafe.append {Q L j a b : Nat} {cs ds es : List Nat}
    (h : HalfSafe Q L j cs a ds) (h' : HalfSafe Q L (j+a) ds b es) : HalfSafe Q L j cs (a+b) es := by
  refine ⟨?_,?_⟩
  · rw [halfStates_add,h.1,h'.1]
  · intro i hi p hp
    by_cases hl : i<a
    · exact h.2 i hl p hp
    · have he : i=a+(i-a) := by omega
      rw [he,halfStates_add,h.1] at hp
      exact h'.2 (i-a) (by omega) p hp

theorem root_step (Q : Nat) (hQ : Q%2=1) : step Q 0 [1]=[(Q+1)/2] := by
  have he : (1+Q)%2=0 := by omega
  simp [step,he,show (Q+1)%2=0 by omega,Nat.add_comm]

theorem root_project (Q : Nat) (hQ : Q%2=1) : project Q 1 ((Q+1)/2)=(Q+1)/2 := by
  unfold project reflect
  have he : Q+2-1-(Q+1)/2=(Q+1)/2 := by omega
  rw [he,Nat.min_self]

theorem root_half_member (Q k c : Nat) (hQ : Q%2=1) (hk : k≤Q)
    (hc : c∈states Q 0 [1] (1+k)) :
    0<c ∧ c+1+k<Q+2 ∧ project Q (1+k) c∈halfStates Q 1 [(Q+1)/2] k := by
  have h : ∀ p∈[(Q+1)/2], 0<p ∧ p+1<Q+2 ∧ project Q 1 p∈[(Q+1)/2] := by
    intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    rw [root_project Q hQ]
    simp
    omega
  rw [states_add] at hc
  simp only [states, Nat.zero_add,root_step Q hQ] at hc
  exact full_to_half Q 1 k _ _ (by omega) h c hc

/-- A quotient certificate omits reflected copies of every carry. It is sufficient
    for the original full margin proposition; the data remain untrusted. -/
theorem margin_of_half (Q L K : Nat) (hQ : Q%2=1) (hK : 1≤K ∧ K≤Q+1)
    (hL : 3≤L ∧ L+1≤Q+2)
    (cert : HalfSafe Q L 1 [(Q+1)/2] (K-1) []) : MarginSafe Q L 0 [1] K [] := by
  refine ⟨?_,?_⟩
  · cases he : states Q 0 [1] K with
    | nil => rfl
    | cons c cs =>
      have hc : c∈states Q 0 [1] K := by rw [he]; simp
      have h : 1+(K-1)=K := by omega
      rw [←h] at hc
      have hm := (root_half_member Q (K-1) c hQ (by omega) hc).2.2
      rw [cert.1] at hm
      simp at hm
  · intro i hi c hc
    by_cases hz : i=0
    · subst i
      simp [states] at hc
      subst c
      omega
    · have he : 1+(i-1)=i := by omega
      rw [←he] at hc
      obtain ⟨hpos,hu,hm⟩ := root_half_member Q (i-1) c hQ (by omega) hc
      have hsmall := cert.2 (i-1) (by omega) _ hm
      have hmin := Nat.le_min.mp hsmall
      unfold reflect at hmin
      rw [he] at hmin
      omega

#print axioms step_reflect
#print axioms full_to_half
#print axioms margin_of_half
end BB6.Agent28HalfCarry
