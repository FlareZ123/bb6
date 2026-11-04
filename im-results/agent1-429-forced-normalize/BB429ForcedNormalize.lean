import BB429No381mod1024
import Lean.Elab.Tactic.Omega
namespace BB429ForcedNormalize
set_option maxHeartbeats 30000000
set_option maxRecDepth 30000

private theorem even_parent (x y a b : Nat)
    (hs : BB429.next (x,y)=some (a,b))
    (ha:6≤a) (he:a%2=0) :
    a%2=0 ∧ b%4=2 ∧ x=a-3+(b-2)/4 ∧ y=b/2 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

private theorem odd_forward (a b : Nat)
    (ha : 13≤a) (ho : a%2=1) :
    BB429.next ((a-3)/2,b+a)=some (a,b) := by
  have hdiv: 2*((a-3)/2)+3=a := by omega
  have hguard : b+a≥2*((a-3)/2)+3 := by omega
  simp only [BB429.next]
  rw [if_pos hguard]
  apply congrArg
  apply Prod.ext <;> omega

private theorem even_forward (a b : Nat)
    (ha:6≤a) (he:a%2=0) (hb:b%4=2) :
    BB429.next (a-3+(b-2)/4,b/2)=some (a,b) := by
  simp only [BB429.next]
  repeat' (split <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

private theorem root_odd_iff (a b : Nat)
    (ha:13≤a) (ho:a%2=1) (hb:b%8≠2) :
    (∃ n,BB429.run n (0,0)=some (a,b)) ↔
    (∃ n,BB429.run n (0,0)=some ((a-3)/2,b+a)) := by
  constructor
  · rintro ⟨n,hn⟩
    cases n with
    | zero => simp [BB429.run] at hn; omega
    | succ n =>
      simp only [BB429.run] at hn
      cases hp : BB429.run n (0,0) with
      | none => simp [hp] at hn
      | some p =>
        simp only [hp,Option.bind_some] at hn
        rcases BB429LowOddMod8.admissible_odd_predecessor p.1 p.2 a b hn ho ha
          (fun hx he => BB429LowOddMod8.rooted_even_parity n p.1 p.2 hp hx he) with hfirst | hbad
        · obtain ⟨heq,hy⟩ := hfirst
          have hpe : p=((a-3)/2,b+a) := Prod.ext (by omega) (by omega)
          exact ⟨n,by simpa only [hpe] using hp⟩
        · exact False.elim (hb hbad)
  · rintro ⟨n,hn⟩
    refine ⟨n+1,?_⟩
    simp only [BB429.run,hn,Option.bind_some]
    exact odd_forward a b ha ho

private theorem root_even_iff (a b : Nat)
    (ha:6≤a) (he:a%2=0) (hb:b%4=2) :
    (∃ n,BB429.run n (0,0)=some (a,b)) ↔
    (∃ n,BB429.run n (0,0)=some (a-3+(b-2)/4,b/2)) := by
  constructor
  · rintro ⟨n,hn⟩
    cases n with
    | zero => simp [BB429.run] at hn; omega
    | succ n =>
      simp only [BB429.run] at hn
      cases hp : BB429.run n (0,0) with
      | none => simp [hp] at hn
      | some p =>
        simp only [hp,Option.bind_some] at hn
        obtain ⟨_,_,hx,hy⟩ := even_parent p.1 p.2 a b hn ha he
        have hpe : p=(a-3+(b-2)/4,b/2) := Prod.ext hx hy
        exact ⟨n,by simpa only [hpe] using hp⟩
  · rintro ⟨n,hn⟩
    refine ⟨n+1,?_⟩
    simp only [BB429.run,hn,Option.bind_some]
    exact even_forward a b ha he hb

/-- Executable source-root-aware inverse normalizer with strict rank descent. -/
def forcedNormalize : (a b : Nat) → Nat × Nat
 | a,b =>
   if ho : 13≤a ∧ a%2=1 ∧ b%8≠2 then
     forcedNormalize ((a-3)/2) (b+a)
   else if he : 6≤a ∧ a%2=0 ∧ b%4=2 then
     forcedNormalize (a-3+(b-2)/4) (b/2)
   else (a,b)
termination_by a b => 2*a+b
decreasing_by
  all_goals
    simp_wf
    omega

/-- For any natural target, the rooted section visits it at some time
    exactly when it visits the computed fully normalized residual. -/
theorem blank_reach_iff_normalized (a b : Nat) :
   (∃ n, BB429.run n (0,0)=some (a,b)) ↔
   (∃ n, BB429.run n (0,0)=some (forcedNormalize a b)) := by
  generalize hz : 2*a+b=z
  induction z using Nat.strongRecOn generalizing a b with
  | ind z ih =>
      unfold forcedNormalize
      by_cases ho : 13≤a ∧ a%2=1 ∧ b%8≠2
      · rw [dif_pos ho]
        rcases ho with ⟨ha,hodd,hb⟩
        have hlt : 2*((a-3)/2)+(b+a)<z := by omega
        exact (root_odd_iff a b ha hodd hb).trans
          (ih _ hlt ((a-3)/2) (b+a) (by rfl))
      · rw [dif_neg ho]
        by_cases he : 6≤a ∧ a%2=0 ∧ b%4=2
        · rw [dif_pos he]
          rcases he with ⟨ha,hev,hb⟩
          have hlt : 2*(a-3+(b-2)/4)+b/2<z := by omega
          exact (root_even_iff a b ha hev hb).trans
            (ih _ hlt (a-3+(b-2)/4) (b/2) (by rfl))
        · rw [dif_neg he]


/-- A total executable sound all-time unreachability filter. This Boolean
    criterion may be incomplete; it never invents a halting witness. -/
def forcedExcluded (a b : Nat) : Bool :=
  let p := forcedNormalize a b
  decide (0<p.1 ∧ p.1%2=0 ∧ p.2%4≠2)

theorem forcedExcluded_sound (a b : Nat)
    (h : forcedExcluded a b=true) :
    ∀ n,BB429.run n (0,0) ≠ some (a,b) := by
  intro n hr
  obtain ⟨k,hk⟩ := (blank_reach_iff_normalized a b).mp ⟨n,hr⟩
  have he : 0<(forcedNormalize a b).1 ∧
    (forcedNormalize a b).1%2=0 ∧
    (forcedNormalize a b).2%4≠2 := by
      simpa only [forcedExcluded] using (of_decide_eq_true h)
  obtain ⟨hpos,heven,hbad⟩ := he
  have hh := BB429LowOddMod8.rooted_even_parity k
    (forcedNormalize a b).1 (forcedNormalize a b).2 hk hpos heven
  exact hbad hh


private theorem root_odd_one_step_iff (n a b : Nat)
    (ha:13≤a) (ho:a%2=1) (hb:b%8≠2) :
    BB429.run (n+1) (0,0)=some (a,b) ↔
    BB429.run n (0,0)=some ((a-3)/2,b+a) := by
  constructor
  · intro hn
    change (BB429.run n (0,0)).bind BB429.next=some (a,b) at hn
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hn
    | some p =>
      simp only [hp,Option.bind_some] at hn
      rcases BB429LowOddMod8.admissible_odd_predecessor p.1 p.2 a b hn ho ha
        (fun hx he => BB429LowOddMod8.rooted_even_parity n p.1 p.2 hp hx he)
          with hfirst | hbad
      · obtain ⟨hx,hy⟩ := hfirst
        have he : p=((a-3)/2,b+a) := Prod.ext (by omega) (by omega)
        simpa only [he] using hp
      · exact False.elim (hb hbad)
  · intro hn
    change (BB429.run n (0,0)).bind BB429.next=some (a,b)
    simp only [hn,Option.bind_some]
    exact odd_forward a b ha ho

private theorem root_even_one_step_iff (n a b : Nat)
    (ha:6≤a) (he:a%2=0) (hb:b%4=2) :
    BB429.run (n+1) (0,0)=some (a,b) ↔
    BB429.run n (0,0)=some (a-3+(b-2)/4,b/2) := by
  constructor
  · intro hn
    change (BB429.run n (0,0)).bind BB429.next=some (a,b) at hn
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hn
    | some p =>
      simp only [hp,Option.bind_some] at hn
      obtain ⟨_,_,hx,hy⟩ := even_parent p.1 p.2 a b hn ha he
      have heq : p=(a-3+(b-2)/4,b/2) := Prod.ext hx hy
      simpa only [heq] using hp
  · intro hn
    change (BB429.run n (0,0)).bind BB429.next=some (a,b)
    simp only [hn,Option.bind_some]
    exact even_forward a b ha he hb

/-- Number of strictly forced inverse macro-transitions, a total computable
    function, independent of any unknown blank-tape halting question. -/
def forcedDepth : (a b : Nat) → Nat
 | a,b =>
   if ho : 13≤a ∧ a%2=1 ∧ b%8≠2 then
     forcedDepth ((a-3)/2) (b+a)+1
   else if he : 6≤a ∧ a%2=0 ∧ b%4=2 then
     forcedDepth (a-3+(b-2)/4) (b/2)+1
   else 0
termination_by a b => 2*a+b
decreasing_by
  all_goals
    simp_wf
    omega

/-- Exact indexed time-transport, stronger than existence equivalence:
    the target at time n+depth is equivalent to its normalized ancestor
    at exactly time n, not merely at some unspecified time. -/
theorem blank_run_iff_normalized_at_shift (a b n : Nat) :
    BB429.run (n+forcedDepth a b) (0,0)=some (a,b) ↔
    BB429.run n (0,0)=some (forcedNormalize a b) := by
  generalize hz : 2*a+b=z
  induction z using Nat.strongRecOn generalizing a b n with
  | ind z ih =>
      unfold forcedDepth forcedNormalize
      by_cases ho : 13≤a ∧ a%2=1 ∧ b%8≠2
      · rw [dif_pos ho,dif_pos ho]
        rcases ho with ⟨ha,hodd,hb⟩
        have hlt : 2*((a-3)/2)+(b+a)<z := by omega
        rw [Nat.add_succ]
        exact (root_odd_one_step_iff (n+forcedDepth ((a-3)/2) (b+a))
          a b ha hodd hb).trans
          (ih _ hlt ((a-3)/2) (b+a) n (by rfl))
      · rw [dif_neg ho,dif_neg ho]
        by_cases he : 6≤a ∧ a%2=0 ∧ b%4=2
        · rw [dif_pos he,dif_pos he]
          rcases he with ⟨ha,hev,hb⟩
          have hlt : 2*(a-3+(b-2)/4)+b/2<z := by omega
          rw [Nat.add_succ]
          exact (root_even_one_step_iff (n+forcedDepth (a-3+(b-2)/4) (b/2))
            a b ha hev hb).trans
            (ih _ hlt (a-3+(b-2)/4) (b/2) n (by rfl))
        · rw [dif_neg he,dif_neg he]
          simp

#print axioms blank_run_iff_normalized_at_shift

#print axioms forcedExcluded_sound

#print axioms blank_reach_iff_normalized
end BB429ForcedNormalize
