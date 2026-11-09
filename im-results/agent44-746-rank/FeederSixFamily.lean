import FeederSixArithmetic
set_option maxHeartbeats 0
namespace CascadeFeederSix
open CascadeSweep
/-- Four formerly surviving residue classes of the genuine valuation-one
    #746 fatal first-reset feeder are excluded from the blank-root orbit. -/
theorem fatal_feeder_four_residues (n x : Nat)
   (hn : 76≤n)
   (hr : n%486=76 ∨ n%486=238 ∨ n%486=275 ∨ n%486=437)
   (hx : 9*x+17*n+39=56*2^(n-2)) :
   ¬ReachC (2,0) (x,0) := by
  let k := n-2
  let j := k-2
  let p := 2^k
  have hk : 5≤k := by dsimp [k]; omega
  have hpj : p=4*2^j := by
    have he : k=j+2 := by dsimp [j,k]; omega
    change 2^k=4*2^j
    rw [he,Nat.pow_add]
    omega
  have hgrowth : 10000*n+10000≤p := by
    simpa only [p,k] using growth n hn
  have hj : j+4=n := by dsimp [j,k]; omega
  have hxl : 9*x+17*n+39=56*p := by simpa only [p,k] using hx
  let h := 2*x-(8*p+k)
  have hpos : 8*p+k≤2*x := by omega
  have hxeq : 2*x=8*p+h+k := by dsimp [h]; omega
  have hlin : 9*h+43*n+60=40*p := by omega
  clear_value h
  have hmods := four_residue_numeric n hr
  have h9 : (2*h+5)%9=0 := h_divnine n p h hlin hmods
  clear hmods
  let z := (2*h+5)/9
  have hz : 9*z=2*h+5 := by dsimp [z]; omega
  clear_value z
  let a := 4*z-(8*2^j+j+5)
  have haPos : 8*2^j+j+5≤4*z := by
    clear hr h9
    omega
  have haEq : 4*z=8*2^j+a+j+5 := by
    clear hr h9
    dsimp [a]; omega
  have haLin : 81*a+425*n+381=158*p :=
    affine_a n p j h z a hj hpj hlin hz haEq
  clear_value a
  let b := 2*a-(8*2^j+j)
  have hbPos : 8*2^j+j≤2*a :=
    positive_even n p j a hgrowth hpj hj (geom_a n p a hgrowth haLin).1
  have hbEq : 2*a=8*2^j+b+j := by
    clear hr h9
    dsimp [b]; omega
  have hbLin : 81*b+931*n+438=154*p :=
    affine_b n p j a b hj hpj haLin hbEq
  clear_value b
  let c := 2*b-(8*2^j+j)
  have hcPos : 8*2^j+j≤2*b :=
    positive_even n p j b hgrowth hpj hj (geom_b n p b hgrowth hbLin).1
  have hcEq : 2*b=8*2^j+c+j := by
    clear hr h9
    dsimp [c]; omega
  have hcLin : 81*c+1943*n+552=146*p :=
    affine_c n p j b c hj hpj hbLin hcEq
  clear_value c
  let d := 2*c-(8*2^j+j)
  have hdPos : 8*2^j+j≤2*c :=
    positive_even n p j c hgrowth hpj hj (geom_c n p c hgrowth hcLin).1
  have hdEq : 2*c=8*2^j+d+j := by
    clear hr h9
    dsimp [d]; omega
  have hdLin : 81*d+3967*n+780=130*p :=
    affine_d n p j c d hj hpj hcLin hdEq
  clear_value d
  let e := 2*d-(8*2^j+j)
  have hePos : 8*2^j+j≤2*d :=
    positive_even n p j d hgrowth hpj hj (geom_d n p d hgrowth hdLin).1
  have heEq : 2*d=8*2^j+e+j := by
    clear hr h9
    dsimp [e]; omega
  have heLin : 81*e+8015*n+1236=98*p :=
    affine_e n p j d e hj hpj hdLin heEq
  clear_value e
  have hmods := four_residue_numeric n hr
  have hxmod := mod_x n p x hmods hxl
  have hh27 := mod_h n p h hmods hlin
  have ham := mod_a n p a hmods haLin
  have hbm := mod_b n p b hmods hbLin
  have hcm := mod_c n p c hmods hcLin
  have hdm := mod_d n p d hmods hdLin
  have hem := mod_e n p e hmods heLin
  clear hmods
  obtain ⟨hbxlo,hbxhi⟩ := geom_x n p x hgrowth hxl
  obtain ⟨hhlo,hhhi⟩ := geom_h n p h hgrowth hlin
  obtain ⟨hbalo,hbahi⟩ := geom_a n p a hgrowth haLin
  obtain ⟨hbblo,hbbhi⟩ := geom_b n p b hgrowth hbLin
  obtain ⟨hbclo,hbchi⟩ := geom_c n p c hgrowth hcLin
  obtain ⟨hbdlo,hbdhi⟩ := geom_d n p d hgrowth hdLin
  obtain ⟨helo,hehi⟩ := geom_e n p e hgrowth heLin
  have hz2 : z=(2*h+5)/9 := by omega
  have hOddEq : 4*((2*h+5)/9)=8*2^j+a+j+5 := by rw [←hz2]; exact haEq
  have hbandx : 6*2^k-1≤x ∧ x≤8*2^k-3 := by omega
  have hbandA : 6*2^j-1≤a ∧ a≤8*2^j-3 := by omega
  have hbandB : 6*2^j-1≤b ∧ b≤8*2^j-3 := by omega
  have hbandC : 6*2^j-1≤c ∧ c≤8*2^j-3 := by omega
  have hbandD : 6*2^j-1≤d ∧ d≤8*2^j-3 := by omega
  have heLower : 4*2^j≤e := by omega
  have heUpper : e<6*2^j-1 := by omega
  have hkj : j=k-2 := by dsimp [j,k]
  exact six_stage_root_exclusion k x h a b c d e hk hbandx hxeq hxmod
    (by omega) (by omega) h9 hh27 (by rw [←hkj]; exact hOddEq)
    (by rw [←hkj]; exact hbandA)
    (by rw [←hkj]; exact hbandB)
    (by rw [←hkj]; exact hbandC)
    (by rw [←hkj]; exact hbandD)
    (by rw [←hkj]; exact hbEq)
    (by rw [←hkj]; exact hcEq)
    (by rw [←hkj]; exact hdEq)
    (by rw [←hkj]; exact heEq)
    ham hbm hcm hdm hem
    (by rw [←hkj]; exact heLower) (by rw [←hkj]; exact heUpper)

#print axioms fatal_feeder_four_residues
end CascadeFeederSix
