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
  | .short m => ⟨0,[],[true,false,true,false]++ones (m+1)⟩
  | .long n m => ⟨0,[],[true,false,true,false,true,false]++rep [true,false] n++ones m⟩
  | .reset m => ⟨4,[],ones (m+4)⟩
theorem short0 : run0 table 50 (config (.short 0)) = some (config (.long 2 2)) := by rfl
theorem short1 : run0 table 34 (config (.short 1)) = some (config (.reset 6)) := by rfl
theorem short2 : run0 table 38 (config (.short 2)) = some (config (.reset 8)) := by rfl
theorem short3 : run0 table 59 (config (.short 3)) = some (config (.reset 9)) := by rfl
theorem short4 : run0 table 63 (config (.short 4)) = some (config (.reset 11)) := by rfl
theorem shortMany (R : List Bool) : run0 table 58 ⟨0,[],[true,false,true,false,true,true,true,true,true,true]++R⟩ = some ⟨0,[],[true,false,true,false,true,false,true,false,true,false,true,false,true,false]++R⟩ := by rfl
theorem reset4 (R : List Bool) : run0 table 8 ⟨4,[],[true,true,true,true]++R⟩ = some ⟨0,[],[true,false,true,false,true,true]++R⟩ := by rfl
theorem progress (a : Mode) : ∃ b : Mode, ∃ t : Nat, 0 < t ∧ run0 table t (config a) = some (config b) := by
  cases a with
  | reset m =>
    refine ⟨.short (m+1),8,by decide,?_⟩
    simp only [config,show m+4=4+m by omega,show m+1+1=2+m by omega,ones_add]
    simpa only [ones,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using reset4 (ones m)
  | short m =>
    match m with
    | 0 => exact ⟨.long 2 2,50,by decide,short0⟩
    | 1 => exact ⟨.reset 6,34,by decide,short1⟩
    | 2 => exact ⟨.reset 8,38,by decide,short2⟩
    | 3 => exact ⟨.reset 9,59,by decide,short3⟩
    | 4 => exact ⟨.reset 11,63,by decide,short4⟩
    | m+5 =>
      refine ⟨.long 4 m,58,by decide,?_⟩
      simp only [config,show m+5+1=6+m by omega,ones_add]
      simpa only [ones,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using shortMany (ones m)
  | long n m =>
    match m with
    | 0 =>
      refine ⟨.long 2 (2+2*n),50+4*n,by omega,?_⟩
      simp only [config,ones_add]
      simpa only [pair_ones,ones,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using Case0.equation n
    | 1 =>
      refine ⟨.long 2 (4+2*n),54+4*n,by omega,?_⟩
      simp only [config,ones_add]
      simpa only [pair_ones,ones,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using Case1.equation n
    | 2 =>
      refine ⟨.reset (8+2*n),42+8*n,by omega,?_⟩
      simp only [config,show 8+2*n+4=12+2*n by omega,ones_add]
      simpa only [pair_ones,ones,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using Case2.equation n
    | 3 =>
      refine ⟨.reset (10+2*n),46+8*n,by omega,?_⟩
      simp only [config,show 10+2*n+4=14+2*n by omega,ones_add]
      simpa only [pair_ones,ones,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using Case3.equation n
    | 4 =>
      refine ⟨.reset (11+2*n),71+12*n,by omega,?_⟩
      simp only [config,show 11+2*n+4=15+2*n by omega,ones_add]
      simpa only [pair_ones,ones,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using Case4.equation n
    | 5 =>
      refine ⟨.reset (13+2*n),75+12*n,by omega,?_⟩
      simp only [config,show 13+2*n+4=17+2*n by omega,ones_add]
      simpa only [pair_ones,ones,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using Case5.equation n
    | m+6 =>
      refine ⟨.long (n+5) m,70+12*n,by omega,?_⟩
      simp only [config,show m+6=6+m by omega,ones_add]
      simpa only [ones,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using Case6.equation n (ones m)
noncomputable def next (a : Mode) : Mode := Classical.choose (progress a)
noncomputable def dt (a : Mode) : Nat := Classical.choose (Classical.choose_spec (progress a))
theorem step_positive (a : Mode) : 0 < dt a := (Classical.choose_spec (Classical.choose_spec (progress a))).1
theorem step_correct (a : Mode) : run0 table (dt a) (config a) = some (config (next a)) := (Classical.choose_spec (Classical.choose_spec (progress a))).2
noncomputable def orbit : Nat → Mode
  | 0 => .short 1
  | n+1 => next (orbit n)
theorem entry : run0 table 17 ⟨0,[],[]⟩ = some (config (orbit 0)) := by rfl
theorem growth (n : Nat) : run0 table (dt (orbit n)) (config (orbit n)) = some (config (orbit (n+1))) := step_correct (orbit n)
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table (fun n => config (orbit n)) 17 (fun n => dt (orbit n)) entry (fun n => step_positive (orbit n)) growth m hm
#print axioms progress
#print axioms growth
#print axioms never
