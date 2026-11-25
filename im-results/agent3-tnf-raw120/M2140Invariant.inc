def ones (n : Nat) := rep [true] n
theorem ones_add (n m : Nat) : ones (n+m) = ones n ++ ones m := by
  induction n with
  | zero => simp [ones,rep]
  | succ n ih =>
    rw [show n+1+m=(n+m)+1 by omega]
    change [true]++ones (n+m) = ([true]++ones n)++ones m
    rw [ih,List.append_assoc]
theorem pair_ones (n : Nat) : rep [true,true] n = ones (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.mul_succ, Nat.add_comm (2*n) 2,ones_add]; simp only [rep,ih]; rfl
inductive Mode where
  | short (m : Nat)
  | long (n m : Nat)
  | reset (m : Nat)
def config : Mode → Z0
  | .short m => ⟨0,[],[false,false,true,false]++ones m⟩
  | .long n m => ⟨0,[],[false,false,true,false,true,false]++rep [true,false] n++ones m⟩
  | .reset m => ⟨4,[],ones (m+4)⟩
theorem short0 : run0 table 26 (config (.short 0)) = some (config (.long 0 3)) := by rfl
theorem short1 : run0 table 28 (config (.short 1)) = some (config (.long 0 4)) := by rfl
theorem short2 : run0 table 29 (config (.short 2)) = some (config (.reset 5)) := by rfl
theorem short3 : run0 table 33 (config (.short 3)) = some (config (.reset 7)) := by rfl
theorem shortMany (R : List Bool) : run0 table 28 ⟨0,[],[false,false,true,false,true,true,true,true]++R⟩ = some ⟨0,[],[false,false,true,false,true,false,true,false,true,false]++R⟩ := by rfl
theorem reset4 (R : List Bool) : run0 table 8 ⟨4,[],[true,true,true,true]++R⟩ = some ⟨0,[],[false,false,true,false,true,true]++R⟩ := by rfl
theorem progress (a : Mode) : ∃ b : Mode, ∃ t : Nat, 0 < t ∧ run0 table t (config a) = some (config b) := by
  cases a with
  | reset m =>
    refine ⟨.short (m+2),8,by decide,?_⟩
    simp only [config,show m+4=4+m by omega,show m+2=2+m by omega,ones_add]
    simpa only [ones,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using reset4 (ones m)
  | short m =>
    match m with
    | 0 => exact ⟨.long 0 3,26,by decide,short0⟩
    | 1 => exact ⟨.long 0 4,28,by decide,short1⟩
    | 2 => exact ⟨.reset 5,29,by decide,short2⟩
    | 3 => exact ⟨.reset 7,33,by decide,short3⟩
    | m+4 =>
      refine ⟨.long 2 m,28,by decide,?_⟩
      simp only [config,show m+4=4+m by omega,ones_add]
      simpa only [ones,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using shortMany (ones m)
  | long n m =>
    match m with
    | 0 =>
      refine ⟨.long 0 (4+2*n),28+4*n,by omega,?_⟩
      simp only [config,ones_add]
      simpa only [pair_ones,ones,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using Case0.equation n
    | 1 =>
      refine ⟨.long 0 (6+2*n),32+4*n,by omega,?_⟩
      simp only [config,ones_add]
      simpa only [pair_ones,ones,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using Case1.equation n
    | 2 =>
      refine ⟨.reset (7+2*n),37+8*n,by omega,?_⟩
      simp only [config,show 7+2*n+4=11+2*n by omega,ones_add]
      simpa only [pair_ones,ones,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using Case2.equation n
    | 3 =>
      refine ⟨.reset (9+2*n),41+8*n,by omega,?_⟩
      simp only [config,show 9+2*n+4=13+2*n by omega,ones_add]
      simpa only [pair_ones,ones,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using Case3.equation n
    | m+4 =>
      refine ⟨.long (n+3) m,36+8*n,by omega,?_⟩
      simp only [config,show m+4=4+m by omega,ones_add]
      simpa only [ones,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using Case4.equation n (ones m)
noncomputable def next (a : Mode) : Mode := Classical.choose (progress a)
noncomputable def dt (a : Mode) : Nat := Classical.choose (Classical.choose_spec (progress a))
theorem step_positive (a : Mode) : 0 < dt a := (Classical.choose_spec (Classical.choose_spec (progress a))).1
theorem step_correct (a : Mode) : run0 table (dt a) (config a) = some (config (next a)) := (Classical.choose_spec (Classical.choose_spec (progress a))).2
noncomputable def orbit : Nat → Mode
  | 0 => .short 2
  | n+1 => next (orbit n)
theorem entry : run0 table 17 ⟨0,[],[]⟩ = some (config (orbit 0)) := by rfl
theorem growth (n : Nat) : run0 table (dt (orbit n)) (config (orbit n)) = some (config (orbit (n+1))) := step_correct (orbit n)
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table (fun n => config (orbit n)) 17 (fun n => dt (orbit n)) entry (fun n => step_positive (orbit n)) growth m hm
#print axioms progress
#print axioms growth
#print axioms never
