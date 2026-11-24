import ShadowPeriodicFamilies
import Root32ShadowArithmetic
namespace BB6.Agent19Root32Unbounded
open BB6.Agent19PeriodicFamilies

/-- A finite ordinary inverse path, requiring every nonterminal vertex
    to lie above the positive lower bound and avoid the forbidden leaf. -/
inductive SafePath (c : Nat) : Nat → Nat → Nat → Prop where
  | zero (u v : Nat) : SafePath c 0 u v
  | step {n u v u' v' : Nat}
      (hu : 2*c<u) (hv : 2*c<v) (hn : ¬ Bad u v)
      (he : DirectEdge c u v u' v' ∨ ∃ d, HighEdge c d u v u' v')
      (tail : SafePath c n u' v') : SafePath c (n+1) u v

theorem directTail (c n u v : Nat) (hc : 0<c) (hu : 2*c<u)
    (hv : 2*c<v) (hd : 2^n ∣ v-2*c) : SafePath c n u v := by
  induction n generalizing u v with
  | zero => exact .zero _ _
  | succ n ih =>
    obtain ⟨t,ht⟩ := hd
    have htpos : 0<t := by
      cases t with
      | zero => simp at ht; omega
      | succ t => omega
    rw [Nat.pow_succ] at ht
    have hveq : v=2*c+2*(2^n*t) := by
      rw [Nat.mul_assoc,Nat.mul_comm 2 t,←Nat.mul_assoc,Nat.mul_comm (2^n*t) 2] at ht
      omega
    apply SafePath.step hu hv (by unfold Bad; omega)
      (u':=u+v+2*c) (v':=2*c+2^n*t)
    · left
      unfold DirectEdge
      omega
    · have hp : 0<2^n*t := Nat.mul_pos (Nat.pow_pos (by decide)) htpos
      apply ih _ _ (by omega) (by omega)
      rw [Nat.add_sub_cancel_left]
      exact Nat.dvd_mul_right _ _

/-- The odd affine coefficient permits Hensel lifting by a single bit. -/
theorem odd_affine_lift (a b n : Nat) (ha : a%2=1) :
    ∃ j, 2^n ∣ a*j+b := by
  induction n with
  | zero => exact ⟨0,by simp⟩
  | succ n ih =>
    obtain ⟨j,t,ht⟩ := ih
    rw [Nat.pow_succ]
    by_cases h : t%2=0
    · refine ⟨j,t/2,?_⟩
      have h2 : t=2*(t/2) := by omega
      calc
        a*j+b = 2^n*t := ht
        _ = 2^n*(2*(t/2)) := congrArg (2^n*·) h2
        _ = _ := by rw [Nat.mul_assoc]
    · refine ⟨j+2^n,(t+a)/2,?_⟩
      have h2 : t+a=2*((t+a)/2) := by omega
      calc
        a*(j+2^n)+b = 2^n*(t+a) := by
          rw [Nat.mul_add,Nat.mul_comm a (2^n),Nat.add_right_comm,ht,Nat.mul_add]
        _ = 2^n*(2*((t+a)/2)) := congrArg (2^n*·) h2
        _ = _ := by rw [Nat.mul_assoc]

theorem edge0 (j : Nat) : ¬Bad (32549090918400*j+16687832340060) (61782290841600*j+31675616196630) ∧ DirectEdge 22155 (32549090918400*j+16687832340060) (61782290841600*j+31675616196630) (94331381760000*j+48363448581000) (30891145420800*j+15837808120470) := by
  unfold Bad DirectEdge
  omega

theorem edge1 (j : Nat) : ¬Bad (94331381760000*j+48363448581000) (30891145420800*j+15837808120470) ∧ DirectEdge 22155 (94331381760000*j+48363448581000) (30891145420800*j+15837808120470) (125222527180800*j+64201256745780) (15445572710400*j+7918904082390) := by
  unfold Bad DirectEdge
  omega

theorem edge2 (j : Nat) : ¬Bad (125222527180800*j+64201256745780) (15445572710400*j+7918904082390) ∧ DirectEdge 22155 (125222527180800*j+64201256745780) (15445572710400*j+7918904082390) (140668099891200*j+72120160872480) (7722786355200*j+3959452063350) := by
  unfold Bad DirectEdge
  omega

theorem edge3 (j : Nat) : ¬Bad (140668099891200*j+72120160872480) (7722786355200*j+3959452063350) ∧ DirectEdge 22155 (140668099891200*j+72120160872480) (7722786355200*j+3959452063350) (148390886246400*j+76079612980140) (3861393177600*j+1979726053830) := by
  unfold Bad DirectEdge
  omega

theorem edge4 (j : Nat) : ¬Bad (148390886246400*j+76079612980140) (3861393177600*j+1979726053830) ∧ DirectEdge 22155 (148390886246400*j+76079612980140) (3861393177600*j+1979726053830) (152252279424000*j+78059339078280) (1930696588800*j+989863049070) := by
  unfold Bad DirectEdge
  omega

theorem edge5 (j : Nat) : ¬Bad (152252279424000*j+78059339078280) (1930696588800*j+989863049070) ∧ DirectEdge 22155 (152252279424000*j+78059339078280) (1930696588800*j+989863049070) (154182976012800*j+79049202171660) (965348294400*j+494931546690) := by
  unfold Bad DirectEdge
  omega

theorem edge6 (j : Nat) : ¬Bad (154182976012800*j+79049202171660) (965348294400*j+494931546690) ∧ DirectEdge 22155 (154182976012800*j+79049202171660) (965348294400*j+494931546690) (155148324307200*j+79544133762660) (482674147200*j+247465795500) := by
  unfold Bad DirectEdge
  omega

theorem edge7 (j : Nat) : ¬Bad (155148324307200*j+79544133762660) (482674147200*j+247465795500) ∧ HighEdge 22155 3 (155148324307200*j+79544133762660) (482674147200*j+247465795500) (38907749613600*j+19947899933850) (58602961494000*j+30045582820680) := by
  unfold Bad HighEdge
  have ho : ((155148324307200*j+79544133762660)+(482674147200*j+247465795500))%2=0 := by omega
  rw [ho]
  refine ⟨by omega,by decide,by omega,⟨19453874806800*j+9973949944770,by omega⟩,by omega,by omega,by omega⟩

theorem edge8 (j : Nat) : ¬Bad (38907749613600*j+19947899933850) (58602961494000*j+30045582820680) ∧ DirectEdge 22155 (38907749613600*j+19947899933850) (58602961494000*j+30045582820680) (97510711107600*j+49993482798840) (29301480747000*j+15022791432495) := by
  unfold Bad DirectEdge
  omega

theorem edge9 (j : Nat) : ¬Bad (97510711107600*j+49993482798840) (29301480747000*j+15022791432495) ∧ HighEdge 22155 2 (97510711107600*j+49993482798840) (29301480747000*j+15022791432495) (63406095927300*j+32508137171055) (46353788337150*j+23765464323930) := by
  unfold Bad HighEdge
  have ho : ((97510711107600*j+49993482798840)+(29301480747000*j+15022791432495))%2=1 := by omega
  rw [ho]
  refine ⟨by omega,by decide,by omega,⟨31703047963650*j+16254068552295,by omega⟩,by omega,by omega,by omega⟩

/-- The D residual has a uniform 10-edge prefix (costs 1^7,3,1,2). -/
theorem dPrefix (j n : Nat)
    (tail : SafePath 22155 n (63406095927300*j+32508137171055)
      (46353788337150*j+23765464323930)) :
    SafePath 22155 (n+10) (32549090918400*j+16687832340060)
      (61782290841600*j+31675616196630) := by
  apply SafePath.step (u':=94331381760000*j+48363448581000) (v':=30891145420800*j+15837808120470) (by omega) (by omega) (edge0 j).1
  · exact Or.inl (edge0 j).2
  apply SafePath.step (u':=125222527180800*j+64201256745780) (v':=15445572710400*j+7918904082390) (by omega) (by omega) (edge1 j).1
  · exact Or.inl (edge1 j).2
  apply SafePath.step (u':=140668099891200*j+72120160872480) (v':=7722786355200*j+3959452063350) (by omega) (by omega) (edge2 j).1
  · exact Or.inl (edge2 j).2
  apply SafePath.step (u':=148390886246400*j+76079612980140) (v':=3861393177600*j+1979726053830) (by omega) (by omega) (edge3 j).1
  · exact Or.inl (edge3 j).2
  apply SafePath.step (u':=152252279424000*j+78059339078280) (v':=1930696588800*j+989863049070) (by omega) (by omega) (edge4 j).1
  · exact Or.inl (edge4 j).2
  apply SafePath.step (u':=154182976012800*j+79049202171660) (v':=965348294400*j+494931546690) (by omega) (by omega) (edge5 j).1
  · exact Or.inl (edge5 j).2
  apply SafePath.step (u':=155148324307200*j+79544133762660) (v':=482674147200*j+247465795500) (by omega) (by omega) (edge6 j).1
  · exact Or.inl (edge6 j).2
  apply SafePath.step (u':=38907749613600*j+19947899933850) (v':=58602961494000*j+30045582820680) (by omega) (by omega) (edge7 j).1
  · exact Or.inr ⟨3, (edge7 j).2⟩
  apply SafePath.step (u':=97510711107600*j+49993482798840) (v':=29301480747000*j+15022791432495) (by omega) (by omega) (edge8 j).1
  · exact Or.inl (edge8 j).2
  apply SafePath.step (u':=63406095927300*j+32508137171055) (v':=46353788337150*j+23765464323930) (by omega) (by omega) (edge9 j).1
  · exact Or.inr ⟨2, (edge9 j).2⟩
  exact tail

/-- For each finite requested depth, one actual natural root index has
    an ordinary non-leaf inverse path at least that long. -/
theorem unboundedD (n : Nat) :
    ∃ j, SafePath 22155 (n+10) (32549090918400*j+16687832340060)
      (61782290841600*j+31675616196630) := by
  obtain ⟨j,hj⟩ := odd_affine_lift 73577441805 37722959174 n (by decide)
  refine ⟨j,dPrefix j n ?_⟩
  apply directTail 22155 n _ _ (by decide) (by omega) (by omega)
  have hv : (46353788337150*j+23765464323930)-2*22155 =
      (73577441805*j+37722959174)*630 := by omega
  rw [hv]
  exact Nat.dvd_trans hj (Nat.dvd_mul_right _ _)


open BB6.Agent19Shadow

theorem leaf_false {u v : Nat} (h : ¬Bad u v) : leaf u v=false := by
  simp [leaf, Bad] at *
  omega

theorem depth_le_of_guard {u v w d p : Nat} (hg : branchGuard p u v w=true)
    (h : 2^d ∣ shadowMass u v) : d≤w := by
  simp only [branchGuard,decide_eq_true_eq] at hg
  by_cases hd : d≤w
  · exact hd
  · have hh := Nat.dvd_trans (Nat.pow_dvd_pow 2 (show w+1≤d by omega)) h
    have hz := Nat.mod_eq_zero_of_dvd hh
    rw [hg.2.2.2.2.2.1] at hz
    have hp := Nat.two_pow_pos w
    omega

theorem high_to_checker {u v u' v' d : Nat} (h : HighEdge C d u v u' v') :
    2^d ∣ shadowMass u v ∧
    (d-2)%2=(u+1+oddMass u v)%2 ∧ 2≤d ∧
    hiU u v (d-2)=u' ∧ hiV u v (d-2)=v' := by
  unfold HighEdge at h
  obtain ⟨hd,hpos,hdiv,hpar,hu,hv⟩ := h
  have he : d-2+1=d-1 := by omega
  have hp : 0<2^(d-1) := Nat.two_pow_pos _
  have hsum : shadowMass u v=u+v-C*oddMass u v := rfl
  change 2^d ∣ shadowMass u v at hdiv
  have hq := Nat.dvd_trans (Nat.pow_dvd_pow 2 (show d-1≤d by omega)) hdiv
  have hdivEq := Nat.div_mul_cancel hq
  have heU : hiU u v (d-2)=u' := by
    unfold hiU
    rw [he]
    change 2^(d-1)*u'=shadowMass u v+2^(d-1)*(C*(2+oddMass u v)) at hu
    have hprod : 2^(d-1)*(shadowMass u v / 2^(d-1)+C*(2+oddMass u v)) =
        2^(d-1)*u' := by
      rw [Nat.mul_add,Nat.mul_comm (2^(d-1)) (shadowMass u v / 2^(d-1)), hdivEq, ←hu]
    exact Nat.eq_of_mul_eq_mul_left hp hprod
  refine ⟨hdiv,by unfold oddMass; omega,hd,heU,?_⟩
  unfold hiV
  rw [heU]
  have hcoeff : 7+3*(d-2)=3*d+1 := by omega
  rw [hcoeff]
  omega

/-- A non-leaf path longer than the checker fuel makes it return false
    for every precision. No assumption about valuation computation is needed:
    a true branch guard already proves the needed valuation. -/
theorem path_blocks_checker (f p u v : Nat) (path : SafePath C (f+1) u v) :
    excluded f p u v=false := by
  induction f generalizing p u v with
  | zero =>
    cases path with
    | step hu hv hn he tail => simp [excluded,leaf_false hn]
  | succ f ih =>
    cases path with
    | @step n u v u' v' hu hv hn edge tail =>
      have hl := leaf_false hn
      apply Bool.eq_false_iff.mpr
      intro h
      simp [excluded,hl] at h
      obtain ⟨⟨hg,hdir⟩,hall⟩ := h
      rcases edge with hd|⟨d,hh⟩
      · obtain ⟨he,hU,hV⟩ := hd
        simp [he] at hdir
        have heV : (v+2*C)/2=v' := by omega
        rw [←hU,heV] at hdir
        rw [ih _ _ _ tail] at hdir
        contradiction
      · obtain ⟨hdvd,hpar,hd,heU,heV⟩ := high_to_checker hh
        let w := valuation (shadowMass u v)
        have hdw : d≤w := depth_le_of_guard hg hdvd
        have hnmem : d-2 ∈ List.range w := List.mem_range.mpr (by omega)
        have hguard : depthGuard u v w (d-2)=true := by
          simp [depthGuard,hpar]
          omega
        have ht := hall (d-2) (List.mem_range.mp hnmem)
        simp [w,hguard,heU,heV] at ht
        rw [ih _ _ _ tail] at ht
        exact Bool.noConfusion ht.2

theorem trimPath {c n u v : Nat} (h : SafePath c n u v) :
    ∀ m, m≤n → SafePath c m u v := by
  induction h with
  | zero u v =>
    intro m hm
    have : m=0 := by omega
    subst m
    exact .zero _ _
  | step hu hv hn he tail ih =>
    intro m hm
    cases m with
    | zero => exact .zero _ _
    | succ m =>
      exact .step hu hv hn he (ih m (by omega))

theorem d_checker_no_uniform_fuel (f : Nat) :
    ∃ j, ∀ p, excluded f p (32549090918400*j+16687832340060)
      (61782290841600*j+31675616196630)=false := by
  obtain ⟨j,hj⟩ := unboundedD f
  refine ⟨j,fun p => path_blocks_checker f p _ _ ?_⟩
  exact trimPath hj (f+1) (by omega)

#print axioms d_checker_no_uniform_fuel
#print axioms unboundedD
end BB6.Agent19Root32Unbounded
