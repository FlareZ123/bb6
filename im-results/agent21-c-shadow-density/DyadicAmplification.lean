import DyadicCollision

namespace BB6.Agent21Dyadic

structure Witness (a : Affine) (n : Nat) where
  b : Int
  words : List (List Nat)
  lo : 0≤b
  hi : b<P n
  nodup : words.Nodup
  correct : ∀ w∈words, Positive w ∧ cost w=n ∧ Compatible a w b

private theorem nodup_prefix (w : List Nat) (l : List (List Nat)) (h : l.Nodup) :
    (l.map (fun v=>w++v)).Nodup := by
  induction l with
  | nil => simp
  | cons v l ih =>
    simp only [List.map_cons,List.nodup_cons] at *
    refine ⟨?_,ih h.2⟩
    intro hm
    obtain ⟨u,hu,he⟩ := List.mem_map.mp hm
    have hv : u=v := by simpa using he
    exact h.1 (hv ▸ hu)

def prepend (a : Affine) (w : List Nat) (b : Int) (n : Nat)
    (h : Good a) (hp : Positive w) (hlo : 0≤b) (hhi : b<P (cost w))
    (hc : Compatible a w b) (W : Witness (follow a w b) n) : Witness a (cost w+n) where
  b := b+P (cost w)*W.b
  words := W.words.map (fun v=>w++v)
  lo := by
    have hm := Int.mul_nonneg (Int.le_of_lt (P_pos (cost w))) W.lo
    omega
  hi := by
    rw [P_add]
    have hm := Int.mul_le_mul_of_nonneg_left (show W.b+1≤P n by have := W.hi; omega) (Int.le_of_lt (P_pos (cost w)))
    rw [Int.mul_add,Int.mul_one] at hm
    omega
  nodup := nodup_prefix _ _ W.nodup
  correct := by
    intro v hv
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
    obtain ⟨hup,huc,hud⟩ := W.correct u hu
    exact ⟨positive_append _ _ hp hup,by rw [cost_append,huc],append_compatible _ _ _ _ _ h hc hud⟩

private theorem nodup_join (l r : List (List Nat)) (hl : l.Nodup) (hr : r.Nodup)
    (hd : ∀ w∈l, w∉r) : (l++r).Nodup := by
  induction l with
  | nil => exact hr
  | cons w l ih =>
    simp only [List.cons_append,List.nodup_cons] at *
    refine ⟨?_,ih hl.2 (fun u hu => hd u (List.mem_cons_of_mem _ hu))⟩
    intro hm
    rcases List.mem_append.mp hm with hh|hh
    · exact hl.1 hh
    · exact hd w (by simp) hh

def collisionDouble (a : Affine) (L : Nat) (hs : P (L+4)∣a.s+14)
    (hσ : P (L+4)∣a.sigma) (b : Int) (h : Good a) (hlo : 0≤b) (hhi : b<P 4)
    (hb : Compatible a [1,3] b) (n : Nat) (hn : n≤L)
    (W : Witness (follow a [1,3] b) n) : Witness a (4+n) := by
  let hb' := collision_compatible a L hs hσ b hb
  obtain ⟨hm,hz⟩ := collision_sync a L hs hσ b h hb
  let W' : Witness (follow a [3,1] b) n := {
    b := W.b
    words := W.words
    lo := W.lo
    hi := W.hi
    nodup := W.nodup
    correct := fun w hw => by
      obtain ⟨hp,hc,hd⟩ := W.correct w hw
      exact ⟨hp,hc,sync_compatible _ _ L hm hz w (by omega) W.b hd⟩
  }
  let A : Witness a (4+n) := prepend a [1,3] b n h (by simp [Positive]) hlo hhi hb W
  let B : Witness a (4+n) := prepend a [3,1] b n h (by simp [Positive]) hlo hhi hb' W'
  have he : A.b=B.b := rfl
  exact {
    b := A.b
    words := A.words++B.words
    lo := A.lo
    hi := A.hi
    nodup := nodup_join _ _ A.nodup B.nodup (by
      intro w hw hw'
      obtain ⟨u,hu,he⟩ := List.mem_map.mp hw
      obtain ⟨v,hv,he'⟩ := List.mem_map.mp hw'
      rw [←he] at he'
      simp at he')
    correct := by
      intro w hw
      rcases List.mem_append.mp hw with ha|hb
      · exact A.correct w ha
      · rw [he]; exact B.correct w hb
  }

theorem collisionDouble_length (a : Affine) (L : Nat) (hs : P (L+4)∣a.s+14)
    (hσ : P (L+4)∣a.sigma) (b : Int) (h : Good a) (hlo : 0≤b) (hhi : b<P 4)
    (hb : Compatible a [1,3] b) (n : Nat) (hn : n≤L)
    (W : Witness (follow a [1,3] b) n) :
    (collisionDouble a L hs hσ b h hlo hhi hb n hn W).words.length=2*W.words.length := by
  simp [collisionDouble,prepend]
  omega

def F : Nat → Nat
  | 0 => 0
  | k+1 => 2*F k+6+2^(F k+5)

/-- Any good affine root admits a uniformly bounded binary cylinder supporting
    at least 2^k distinct compatible positive cost words of the same cost. -/
theorem amplify (k : Nat) (a : Affine) (h : Good a) :
    ∃ n : Nat, n≤F k ∧ ∃ W : Witness a n, 2^k≤W.words.length := by
  induction k generalizing a with
  | zero =>
    let W : Witness a 0 := {
      b := 0
      words := [[]]
      lo := by decide
      hi := by decide
      nodup := by simp
      correct := by
        intro w hw
        simp at hw
        subst w
        simp [Positive,cost,Compatible,P]
    }
    exact ⟨0,by decide,W,by simp [W]⟩
  | succ k ih =>
    obtain ⟨w,b,hp,hlo,hhi,hc,hs,hσ,hbound⟩ := steer a (F k) h
    let a1 := follow a w b
    have h1 : Good a1 := follow_good _ _ _ h
    obtain ⟨c,hclo,hchi,hcc⟩ := word_exists a1 [1,3] h1
    let a2 := follow a1 [1,3] c
    have h2 : Good a2 := follow_good _ _ _ h1
    obtain ⟨n,hn,W,hw⟩ := ih a2 h2
    let W2 := collisionDouble a1 (F k) hs hσ c h1 hclo hchi hcc n hn W
    let W3 := prepend a w b (4+n) h hp hlo hhi hc W2
    refine ⟨cost w+(4+n),?_,W3,?_⟩
    · simp only [F]
      have hpow : 0<2^(F k+4) := Nat.two_pow_pos _
      have he : 2^(F k+5)=2^(F k+4)*2 := by rw [show F k+5=F k+4+1 by omega,Nat.pow_succ]
      omega
    · change 2^(k+1)≤(W2.words.map (fun v=>w++v)).length
      rw [List.length_map]
      have he := collisionDouble_length a1 (F k) hs hσ c h1 hclo hchi hcc n hn W
      change W2.words.length=2*W.words.length at he
      rw [Nat.pow_succ,he]
      omega

#print axioms amplify
end BB6.Agent21Dyadic
