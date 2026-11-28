import WordPrefixSparsity
import Lean.Elab.Tactic.Omega

namespace BB6.Agent2F321DangerCount
open BB6.Agent31F321Density
open BB6.Agent2F321Bulk
open BB6.Agent2F321WordGuard
open BB6.Agent2F321RootWord
open BB6.Agent2F321PrefixSparsity

/-- A legal word can be truncated at the first crossing of a binary digit
    cost m. Each letter costs at most two, so the overshoot is at most one. -/
theorem prefix_cross {w : List InverseLetter} {a d A D m : Nat}
    (hw : WordRun w a d A D) (hm : 0<m) (hs : m≤S w) :
    ∃ u v B C, w=u++v ∧ WordRun u a d B C ∧ m≤S u ∧ S u≤m+1 := by
  induction hw generalizing m with
  | nil => simp at hs; omega
  | @high w a d A D hg ht ih =>
      by_cases hm' : m=1
      · exact ⟨[.high],w,_,_,rfl,WordRun.high hg (WordRun.nil _ _),by simp [hm'],by simp [hm']⟩
      · have hs' : m-1≤S w := by simp at hs; omega
        rcases ih (m:=m-1) (by omega) hs' with ⟨u,v,B,C,he,hu,hlo,hhi⟩
        exact ⟨.high::u,v,B,C,by simp [he],WordRun.high hg hu,by simp; omega,by simp; omega⟩
  | @far w a d A D h1 h2 ht ih =>
      by_cases hm' : m≤2
      · exact ⟨[.far],w,_,_,rfl,WordRun.far h1 h2 (WordRun.nil _ _),by simp; omega,by simp; omega⟩
      · have hs' : m-2≤S w := by simp at hs; omega
        rcases ih (m:=m-2) (by omega) hs' with ⟨u,v,B,C,he,hu,hlo,hhi⟩
        exact ⟨.far::u,v,B,C,by simp [he],WordRun.far h1 h2 hu,by simp; omega,by simp; omega⟩

/-- A code is either an entire short terminal word or a long enough prefix
    that the exponential gap already distinguishes its original anchor. -/
def CodeRel (h c R : Nat) (u : List InverseLetter) : Prop :=
  (S u<h+6 ∧ ∃ t, PrefixTail h u R c t) ∨
  (h+6≤S u ∧ S u≤h+7 ∧ ∃ v a d A D,
    u=.far::v ∧ HighRun h R c a d ∧ WordRun u a d A D)

theorem code_unique {h c R R' : Nat} {u : List InverseLetter}
    (hc : c=1 ∨ c=2) (h1 : CodeRel h c R u) (h2 : CodeRel h c R' u) : R=R' := by
  rcases h1 with ⟨hs,t,ht⟩ | ⟨hl,hu,v,a,d,A,D,he,hh,hw⟩
  · rcases h2 with ⟨hs',t',ht'⟩ | ⟨hl',_⟩
    · exact short_terminal_unique ht ht'
    · omega
  · rcases h2 with ⟨hs',_⟩ | ⟨hl',hu',v',a',d',A',D',he',hh',hw'⟩
    · omega
    · subst u
      exact long_prefix_unique hc hl hh hh' hw (by simpa [←he'] using hw')

theorem code_cost {h c R : Nat} {u : List InverseLetter} (hr : CodeRel h c R u) :
    S u≤h+7 := by
  rcases hr with h | h <;> omega

theorem danger_has_code {h c R : Nat} {w : List InverseLetter} (hd : Danger h w R c) :
    ∃ u, CodeRel h c R u := by
  rcases danger_iff.mp hd with ⟨hshape,t,a,d,hh,hw⟩
  by_cases hs : S w<h+6
  · exact ⟨w,Or.inl ⟨hs,t,a,d,hh,hw⟩⟩
  · rcases hshape with rfl | ⟨w',rfl⟩
    · simp at hs
    · rcases prefix_cross hw (m:=h+6) (by omega) (by omega) with ⟨u,v,B,C,he,hu,hlo,hhi⟩
      cases u with
      | nil => simp at hlo
      | cons z u =>
          have hz : z=.far := by
            simpa using congrArg List.head? he.symm
          subst z
          exact ⟨.far::u,Or.inr ⟨hlo,hhi,u,a,d,B,C,rfl,hh,hu⟩⟩

/-- All H/F words of binary cost at most m, including the empty word. -/
def wordsThrough : Nat → List (List InverseLetter)
  | 0 => [[]]
  | 1 => [[],[.high]]
  | n+2 => [] :: ((wordsThrough (n+1)).map (List.cons .high) ++
      (wordsThrough n).map (List.cons .far))

theorem word_mem_through (m : Nat) (w : List InverseLetter) (hw : S w≤m) :
    w∈wordsThrough m := by
  induction m using Nat.strongRecOn generalizing w with
  | ind m ih =>
      cases m with
      | zero =>
          cases w with
          | nil => simp [wordsThrough]
          | cons z w => cases z <;> simp at hw
      | succ n =>
          cases n with
          | zero =>
              cases w with
              | nil => simp [wordsThrough]
              | cons z w =>
                  cases z with
                  | high =>
                      cases w with
                      | nil => simp [wordsThrough]
                      | cons z w => cases z <;> simp at hw
                  | far => simp at hw
          | succ n =>
              cases w with
              | nil => simp [wordsThrough]
              | cons z w =>
                  cases z with
                  | high =>
                      have hs : S w≤n+1 := by simp at hw; omega
                      have hm := ih (n+1) (by omega) w hs
                      simp only [wordsThrough,List.mem_cons,List.mem_append]
                      exact Or.inr (Or.inl (List.mem_map.mpr ⟨w,hm,rfl⟩))
                  | far =>
                      have hs : S w≤n := by simp at hw; omega
                      have hm := ih n (by omega) w hs
                      simp only [wordsThrough,List.mem_cons,List.mem_append]
                      exact Or.inr (Or.inr (List.mem_map.mpr ⟨w,hm,rfl⟩))

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 => fib (n+1)+fib n

/-- Exact Fibonacci count of the weighted word language. -/
theorem wordsThrough_count (m : Nat) : (wordsThrough m).length+1=fib (m+3) := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
      cases m with
      | zero => decide
      | succ n =>
          cases n with
          | zero => decide
          | succ n =>
              have h1 := ih (n+1) (by omega)
              have h2 := ih n (by omega)
              simp only [wordsThrough,List.length_cons,List.length_append,List.length_map]
              have hf : fib (n+1+1+3)=fib (n+1+3)+fib (n+3) := by rfl
              omega

/-- Decode a code into its unique possible anchor. Nonexistence gets the
    harmless dummy value zero; no assumption is made about root reachability. -/
noncomputable def decode (h c : Nat) (u : List InverseLetter) : Nat := by
  classical
  exact if he : ∃ R, CodeRel h c R u then Classical.choose he else 0

theorem decode_of_code {h c R : Nat} {u : List InverseLetter}
    (hc : c=1 ∨ c=2) (hr : CodeRel h c R u) : decode h c u=R := by
  classical
  unfold decode
  split
  · exact code_unique hc (Classical.choose_spec ‹∃ R, CodeRel h c R u›) hr
  · rename_i hn
    exact False.elim (hn ⟨R,hr⟩)

noncomputable def codesAt (c h : Nat) : List (Nat×Nat) :=
  (wordsThrough (h+7)).map (fun u => (decode h c u,c))

noncomputable def codesThrough (c : Nat) : Nat → List (Nat×Nat)
  | 0 => codesAt c 0
  | k+1 => codesThrough c k ++ codesAt c (k+1)

theorem code_mem_at {h c R : Nat} {u : List InverseLetter}
    (hc : c=1 ∨ c=2) (hr : CodeRel h c R u) : (R,c)∈codesAt c h := by
  unfold codesAt
  exact List.mem_map.mpr ⟨u,word_mem_through _ _ (code_cost hr),by rw [decode_of_code hc hr]⟩

theorem code_mem_through {h c R k : Nat} (hk : h≤k) (hr : (R,c)∈codesAt c h) :
    (R,c)∈codesThrough c k := by
  induction k with
  | zero =>
      have he : h=0 := by omega
      subst h
      exact hr
  | succ k ih =>
      by_cases he : h=k+1
      · subst h; exact List.mem_append.mpr (Or.inr hr)
      · exact List.mem_append.mpr (Or.inl (ih (by omega)))

theorem codesThrough_count (c k : Nat) :
    (codesThrough c k).length+(k+1)+fib 11=fib (k+12) := by
  induction k with
  | zero =>
      have h := wordsThrough_count 7
      change (wordsThrough 7).length+1+fib 11=fib 12
      change (wordsThrough 7).length+1=fib 10 at h
      have hf : fib 12=fib 11+fib 10 := rfl
      omega
  | succ k ih =>
      simp only [codesThrough,codesAt,List.length_append,List.length_map]
      have h := wordsThrough_count (k+1+7)
      have hf : fib (k+1+12)=fib (k+12)+fib (k+11) := rfl
      have he : k+1+7+3=k+11 := by omega
      rw [he] at h
      omega

/-- All prepared anchors with small second counter that can terminate without
    another reset, with no restriction whatsoever on the terminal word length. -/
def DangerousAnchor (R c : Nat) : Prop :=
  (c=1 ∨ c=2) ∧ ∃ h w, Danger h w R c

/-- A finite list containing every dangerous anchor up to 2^k. -/
noncomputable def anchorCover (k : Nat) : List (Nat×Nat) :=
  codesThrough 1 k ++ codesThrough 2 k

theorem danger_mem_cover {R c k : Nat} (hk : 2≤k) (hR : R≤2^k)
    (hd : DangerousAnchor R c) : (R,c)∈anchorCover k := by
  rcases hd with ⟨hc,h,w,hd⟩
  have hH : h≤k := by
    rcases danger_iff.mp hd with ⟨_,t,a,d,hh,hw⟩
    exact leadingHigh_le hk hR hc hh
  rcases danger_has_code hd with ⟨u,hu⟩
  have hm := code_mem_through hH (code_mem_at hc hu)
  unfold anchorCover
  rcases hc with rfl | rfl
  · exact List.mem_append.mpr (Or.inl hm)
  · exact List.mem_append.mpr (Or.inr hm)

/-- Uniform finite-count bound, including arbitrarily long terminal words.
    Any list of distinct dangerous anchors with R≤2^k has size ≤2 Fib(k+12).
    The Fibonacci growth rate is strictly smaller than 2^k. -/
theorem dangerous_count_bound (k : Nat) (hk : 2≤k) (xs : List (Nat×Nat))
    (hnd : xs.Nodup) (hall : ∀ p∈xs, p.1≤2^k ∧ DangerousAnchor p.1 p.2) :
    xs.length≤2*fib (k+12) := by
  have hs : xs⊆anchorCover k := by
    intro p hp
    exact danger_mem_cover hk (hall p hp).1 (hall p hp).2
  have hn := hnd.length_le_of_subset hs
  have h1 := codesThrough_count 1 k
  have h2 := codesThrough_count 2 k
  simp only [anchorCover,List.length_append] at hn
  omega

theorem fib_step_mono (n : Nat) : fib n≤fib (n+1) := by
  cases n with
  | zero => decide
  | succ n =>
      have he : fib (n+1+1)=fib (n+1)+fib n := rfl
      omega

theorem fib_two_step_bound (n : Nat) : fib (n+3)≤3*fib (n+1) := by
  have h := fib_step_mono n
  have e1 : fib (n+2)=fib (n+1)+fib n := rfl
  have e2 : fib (n+3)=fib (n+2)+fib (n+1) := rfl
  omega

theorem fib_even_bound (k : Nat) : fib (2*k+12)≤144*3^k := by
  induction k with
  | zero => decide
  | succ k ih =>
      have h := fib_two_step_bound (2*k+11)
      have e1 : 2*k+11+3=2*(k+1)+12 := by omega
      have e2 : 2*k+11+1=2*k+12 := by omega
      rw [e1,e2] at h
      rw [Nat.pow_succ]
      omega

/-- A completely integer-valued density-zero estimate. Among first counters
    at most 4^j there are at most 288*3^j dangerous pairs (j≥1).
    In particular the fraction tends to zero geometrically. -/
theorem dangerous_count_bound_pow4 (j : Nat) (hj : 1≤j) (xs : List (Nat×Nat))
    (hnd : xs.Nodup) (hall : ∀ p∈xs, p.1≤4^j ∧ DangerousAnchor p.1 p.2) :
    xs.length≤288*3^j := by
  have he : 2^(2*j)=4^j := by rw [Nat.pow_mul]
  have h := dangerous_count_bound (2*j) (by omega) xs hnd (by simpa [he] using hall)
  have hf := fib_even_bound j
  omega

#print axioms prefix_cross
#print axioms code_unique
#print axioms danger_has_code
#print axioms dangerous_count_bound
#print axioms dangerous_count_bound_pow4
end BB6.Agent2F321DangerCount
