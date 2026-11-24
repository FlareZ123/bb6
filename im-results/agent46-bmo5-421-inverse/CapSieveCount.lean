import CapSieveClasses
namespace CapSieve

def words : Nat → List (List Bool)
  | 0 => [[]]
  | t+1 => (words t).map (false::·) ++ (words t).map (true::·)

theorem words_length (t : Nat) : (words t).length=2^t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [words,ih,Nat.pow_succ]; omega

theorem words_mem {w : List Bool} {t : Nat} : w∈words t ↔ w.length=t := by
  induction t generalizing w with
  | zero => simp [words]
  | succ t ih =>
    cases w with
    | nil => simp [words]
    | cons e w =>
      cases e <;> simp [words,List.mem_map,ih]

theorem words_nodup (t : Nat) : (words t).Nodup := by
  induction t with
  | zero => decide
  | succ t ih =>
    unfold words
    rw [List.nodup_append]
    refine ⟨?_,?_,?_⟩
    · exact List.Pairwise.map (false::·) (by simp) ih
    · exact List.Pairwise.map (true::·) (by simp) ih
    · intro a ha b hb
      obtain ⟨u,_,rfl⟩ := List.mem_map.mp ha
      obtain ⟨v,_,rfl⟩ := List.mem_map.mp hb
      simp

noncomputable def residue (w : List Bool) (p : Bool) : Nat :=
  Classical.choose (word_class w (choose p) (by cases p <;> decide))

theorem residue_spec (w : List Bool) (p : Bool) : residue w p<modulus w ∧ residue w p%2=choose p ∧
    ∀ i, 4*w.length+10≤i → i%2=choose p → (Valid i w ↔ i%modulus w=residue w p) :=
  Classical.choose_spec (word_class w (choose p) (by cases p <;> decide))

theorem residue_injective {w v : List Bool} {p q : Bool} (hlen : w.length=v.length)
    (he : residue w p=residue v q) : w=v ∧ p=q := by
  obtain ⟨hw,hwp,hclass⟩ := residue_spec w p
  obtain ⟨hv,hvq,hclass'⟩ := residue_spec v q
  have hpq : p=q := by
    rw [he,hvq] at hwp
    cases p <;> cases q <;> simp [choose] at hwp ⊢
  subst q
  refine ⟨distinct_classes hlen hw ?_ ?_,rfl⟩
  · intro i hi hp; exact hclass i hi (hp.trans hwp)
  · intro i hi hp
    rw [he] at hp ⊢
    exact hclass' i hi (hp.trans hvq)

noncomputable def classes (t : Nat) : List Nat :=
  (words t).map (fun w=>residue w false) ++ (words t).map (fun w=>residue w true)

theorem classes_length (t : Nat) : (classes t).length=2^(t+1) := by
  simp [classes,words_length,Nat.pow_succ]; omega

theorem classes_nodup (t : Nat) : (classes t).Nodup := by
  unfold classes
  rw [List.nodup_append]
  have aux (p : Bool) : ((words t).map (fun w=>residue w p)).Nodup := by
    rw [List.nodup_iff_pairwise_ne,List.pairwise_map]
    apply List.Pairwise.imp_of_mem (p:=words_nodup t)
    intro w v hw hv hn he
    exact hn (residue_injective ((words_mem.mp hw).trans (words_mem.mp hv).symm) he).1
  refine ⟨aux false,aux true,?_⟩
  intro a ha b hb he
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ha
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hb
  have h := (residue_injective ((words_mem.mp hw).trans (words_mem.mp hv).symm) he).2
  contradiction

theorem classes_bound {t r : Nat} (hr : r∈classes t) : r<2*3^t := by
  unfold classes at hr
  rcases List.mem_append.mp hr with h|h <;>
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp h
  · simpa [modulus,words_mem.mp hw] using (residue_spec w false).1
  · simpa [modulus,words_mem.mp hw] using (residue_spec w true).1

theorem classes_exact (i t : Nat) (hi : 4*t+10≤i) :
    (∃ y, Back i t y) ↔ i%(2*3^t)∈classes t := by
  rw [back_iff_valid i t hi]
  constructor
  · rintro ⟨w,hw,hv⟩
    have hm : w∈words t := words_mem.mpr hw
    have hpar : i%2=0 ∨ i%2=1 := by omega
    rcases hpar with hp|hp
    · apply List.mem_append.mpr; left; apply List.mem_map.mpr
      refine ⟨w,hm,?_⟩
      have h := ((residue_spec w false).2.2 i (by omega) (by simpa [choose] using hp)).mp hv
      simpa [modulus,hw] using h.symm
    · apply List.mem_append.mpr; right; apply List.mem_map.mpr
      refine ⟨w,hm,?_⟩
      have h := ((residue_spec w true).2.2 i (by omega) (by simpa [choose] using hp)).mp hv
      simpa [modulus,hw] using h.symm
  · intro h
    unfold classes at h
    have aux (p : Bool) (h : i%(2*3^t)∈(words t).map (fun w=>residue w p)) :
        ∃ w : List Bool, w.length=t ∧ Valid i w := by
      obtain ⟨w,hw,hr⟩ := List.mem_map.mp h
      have hl := words_mem.mp hw
      have hm : i%modulus w=residue w p := by simpa [modulus,hl] using hr.symm
      have htwo : 2∣modulus w := ⟨3^w.length,rfl⟩
      have hp : i%2=choose p := by rw [←Nat.mod_mod_of_dvd i htwo,hm,(residue_spec w p).2.1]
      exact ⟨w,hl,((residue_spec w p).2.2 i (by omega) hp).mpr hm⟩
    rcases List.mem_append.mp h with h|h
    · exact aux false h
    · exact aux true h

/-- The exact finite residue theorem, including cardinality, without any computed class list. -/
theorem exact_classification (t : Nat) : ∃ rs : List Nat,
    rs.Nodup ∧ rs.length=2^(t+1) ∧ (∀ r∈rs, r<2*3^t) ∧
    (∀ i, 4*t+10≤i → ((∃ y, Back i t y) ↔ i%(2*3^t)∈rs)) :=
  ⟨classes t,classes_nodup t,classes_length t,fun _ hr=>classes_bound hr,fun i hi=>classes_exact i t hi⟩

#print axioms exact_classification
end CapSieve
