import BB429InverseWordSource
import Lean.Elab.Tactic.Omega

namespace BB429InverseWord

/-- Pairing two exact source inverse paths with the same labels yields the certificate required by the abstract odd-slope uniqueness theorem. -/
theorem twin_of_two_high_chains (a b a' b' : Nat)
    {pref suffix : List Move}
    {x y x' y' u v u' v' : Nat}
    (hp : Twin a b a' b' pref x y x' y')
    (h1 : HighChain x y suffix u v)
    (h2 : HighChain x' y' suffix u' v') :
    Twin a b a' b' (pref++suffix) u v u' v' := by
  induction suffix generalizing pref x y x' y' with
  | nil =>
      cases h1 with
      | nil =>
          cases h2 with
          | nil => simpa using hp
  | cons m ws ih =>
      cases h1 with
      | @cons a0 b0 x0 y0 u0 v0 ws0 m0 he hrest =>
          cases h2 with
          | @cons a1 b1 x1 y1 u1 v1 ws1 m1 he' hrest' =>
              have hp' : Twin a b a' b' (pref++[m]) _ _ _ _ :=
                Twin.snoc m hp he he'
              have hh := ih hp' hrest hrest'
              simpa [List.append_assoc] using hh

/-- The entire dyadic residue uniqueness now applies to *two original-source
reachable* ray states whenever their (necessarily high) reverse prefixes share
an exact label word. -/
theorem original_same_word_unique (c a b a' b' : Nat)
    (hr:b+c=2*a) (hr':b'+c=2*a')
    (ha':a'≤a)
    {ws : List Move} {x y x' y' : Nat}
    (h1 : HighChain a b ws x y)
    (h2 : HighChain a' b' ws x' y') :
    2^(ws.length) ∣ a-a' := by
  have ht := twin_of_two_high_chains a b a' b' (Twin.nil) h1 h2
  simpa using twin_residue_unique c a b a' b' hr hr' ha' ht

/-- The exact two-choice alphabet at each alternating rank phase. -/
def AllowedAt (j : Nat) (m : Move) : Prop :=
  (j%2=0 → m=.F) ∧ (j%4=1 → m≠.E) ∧ (j%4=3 → m≠.S)

inductive Regular : Nat → List Move → Prop
  | nil (j : Nat) : Regular j []
  | cons (j : Nat) (m : Move) {ws : List Move} :
      AllowedAt j m → Regular (j+1) ws → Regular j (m::ws)

/-- From the authentic rank phase, every source inverse path obeys the forced
F (F|S) F (F|E) ... regular language. -/
theorem high_chain_regular (j a b : Nat)
    (hphase : (2*a+b)%4=(3+j)%4)
    {ws : List Move} {x y : Nat}
    (h : HighChain a b ws x y) : Regular j ws := by
  induction h generalizing j with
  | nil => exact Regular.nil j
  | @cons a b x y u v ws m he htail ih =>
      have hc := legit_cost m a b x y he
      have hphase' : (2*x+y)%4=(3+(j+1))%4 := by
        cases m <;> simp only [cost] at hc <;> omega
      have hm : AllowedAt j m := by
        unfold AllowedAt
        constructor
        · intro hj
          have hodd : (2*a+b)%2=1 := by omega
          exact legit_rank_odd_forces_F m a b x y he hodd
        constructor
        · intro hj
          have hmod : (2*a+b)%4=0 := by omega
          exact legit_rank0_notE m a b x y he hmod
        · intro hj
          have hmod : (2*a+b)%4=2 := by omega
          exact legit_rank2_notS m a b x y he hmod
      exact Regular.cons j m hm (ih (j+1) hphase')

/-- Actual original-source rooted diagonal-ray inverse words are regular. -/
theorem root_ray_regular (a b : Nat) (hb:b+13=2*a)
    {ws : List Move} {x y : Nat} (h:HighChain a b ws x y):
    Regular 0 ws := by
  have hphase : (2*a+b)%4=(3+0)%4 := by omega
  exact high_chain_regular 0 a b hphase h

/-- Exact alphabet for a fixed inverse depth, without an unused third letter. -/
def options (j:Nat) : List Move :=
  if j%2=0 then [.F]
  else if j%4=1 then [.F,.S]
  else [.F,.E]

theorem allowed_mem_options (j:Nat) (m:Move) (h:AllowedAt j m) :
    m∈options j := by
  by_cases he : j%2=0
  · have hm : m=.F := h.1 he
    subst hm
    simp [options, he]
  · by_cases h1 : j%4=1
    · cases m with
      | F => simp [options,he,h1]
      | S => simp [options,he,h1]
      | E => exact False.elim (h.2.1 h1 rfl)
    · have h3:j%4=3 := by omega
      cases m with
      | F => simp [options,he,h1]
      | S => exact False.elim (h.2.2 h3 rfl)
      | E => simp [options,he,h1]

def allWords (j:Nat) : (k:Nat) → List (List Move)
  | 0 => [[]]
  | k+1 =>
      (options j).flatMap (fun m => (allWords (j+1) k).map (fun ws => m::ws))

/-- Every legal length-k word belongs to the explicit finite enumeration. -/
theorem regular_mem_allWords (j:Nat) {ws:List Move}
    (h:Regular j ws) : ws∈allWords j ws.length := by
  induction h with
  | nil j => simp [allWords]
  | cons j m hm htail ih =>
      simp only [List.length_cons, allWords]
      apply List.mem_flatMap.mpr
      refine ⟨m, allowed_mem_options j m hm, ?_⟩
      apply List.mem_map.mpr
      exact ⟨_,ih,rfl⟩

/-- Flat-mapping fixed-length suffix extensions multiplies cardinality. -/
theorem extension_length (ls : List Move) (tails:List (List Move)) :
    (ls.flatMap fun m => tails.map (fun t => m::t)).length = ls.length*tails.length := by
  induction ls with
  | nil => simp
  | cons m ms ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_map,
        List.length_cons, ih]
      simp [Nat.add_mul, Nat.add_comm]

theorem allWords_len_step (j k:Nat) :
    (allWords j (k+1)).length = (options j).length*(allWords (j+1) k).length := by
  simp only [allWords]
  exact extension_length (options j) (allWords (j+1) k)

theorem options_even (j:Nat) (hj:j%2=0) : (options j).length=1 := by
  simp [options,hj]

theorem options_odd (j:Nat) (hj:j%2=1) : (options j).length=2 := by
  have hn : j%2≠0 := by omega
  by_cases h1 : j%4=1 <;> simp [options,hn,h1]

/-- Starting at even phase, the exact candidate language has
2^(floor(k/2)) words, despite having three possible move *names*. -/
theorem allWords_length_even (k:Nat) :
    ∀ j:Nat, j%2=0 →
      (allWords j (2*k)).length = 2^k ∧
      (allWords j (2*k+1)).length = 2^k := by
  induction k with
  | zero =>
      intro j hj
      constructor
      · simp [allWords]
      · change (allWords j (0+1)).length = 1
        rw [allWords_len_step]
        simp [allWords, options_even j hj]
  | succ k ih =>
      intro j hj
      have hj1 : (j+1)%2=1 := by omega
      have hj2 : (j+2)%2=0 := by omega
      obtain ⟨he,ho⟩ := ih (j+2) hj2
      have h1 := options_even j hj
      have h2 := options_odd (j+1) hj1
      constructor
      · have hc : (allWords j (2*(k+1))).length =
            (options j).length*((options (j+1)).length*(allWords (j+2) (2*k)).length) := by
          rw [show 2*(k+1)=(2*k+1)+1 by omega,
            allWords_len_step,allWords_len_step]
        rw [hc,h1,h2,he]
        simp [Nat.pow_succ, Nat.mul_comm]
      · have hc : (allWords j (2*(k+1)+1)).length =
            (options j).length*((options (j+1)).length*(allWords (j+2) (2*k+1)).length) := by
          rw [show 2*(k+1)+1=(2*k+1+1)+1 by omega,
            allWords_len_step,allWords_len_step]
        rw [hc,h1,h2,ho]
        simp [Nat.pow_succ, Nat.mul_comm]

#print axioms original_same_word_unique
#print axioms allWords_length_even
end BB429InverseWord
