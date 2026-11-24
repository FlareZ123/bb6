import CapSieveGraph
namespace CapSieve

def modulus (w : List Bool) := 2*3^w.length

theorem modulus_cons (e : Bool) (w : List Bool) : modulus (e::w)=3*modulus w := by simp [modulus,Nat.pow_succ]; omega

theorem modulus_pos (w : List Bool) : 0<modulus w := Nat.mul_pos (by decide) (Nat.pow_pos (by decide))

theorem numerator_lifts (i s : Nat) (w : List Bool) (hw : w.length=s+1) (hi : w.length≤i) (l : Nat) :
    numerator (i+l*(2*3^s)) w % (3^(s+1):Nat) =
      (numerator i w+(3^s:Nat)*(l:Int)) % (3^(s+1):Nat) := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [Nat.succ_mul,←Nat.add_assoc,numerator_shift _ s w hw (by omega)]
    rw [←Int.emod_add_emod,ih,Int.emod_add_emod]
    congr 1
    simp [Int.natCast_succ,Int.mul_add]; omega

theorem numerator_period (i : Nat) (e : Bool) (w : List Bool) (hi : (e::w).length≤i) (l : Nat) :
    numerator (i+l*modulus (e::w)) (e::w) % (3^((e::w).length):Nat) =
      numerator i (e::w) % (3^((e::w).length):Nat) := by
  rw [modulus_cons,show l*(3*modulus w)= (3*l)*(2*3^w.length) by simp [modulus]; ac_rfl]
  simp only [List.length_cons]
  rw [numerator_lifts i w.length (e::w) rfl hi (3*l)]
  simp only [Int.natCast_mul,Int.natCast_pow,Nat.pow_succ]
  change (numerator i (e::w)+(3:Int)^w.length*(3*(l:Int)))%((3:Int)^w.length*3)=_
  rw [show (3:Int)^w.length*(3*(l:Int))=((3:Int)^w.length*3)*(l:Int) by ac_rfl,Int.add_mul_emod_self_left]
  rfl

theorem valid_period (w : List Bool) (i l : Nat) (hi : w.length≤i) :
    Valid (i+l*modulus w) w ↔ Valid i w := by
  induction w generalizing l with
  | nil => simp [Valid]
  | cons e w ih =>
    change (Valid (i+l*modulus (e::w)) w ∧ numerator (i+l*modulus (e::w)) (e::w)%(3^((e::w).length):Nat)=0) ↔ _
    rw [numerator_period i e w hi l,modulus_cons,show l*(3*modulus w)= (3*l)*modulus w by ac_rfl,ih (3*l) (by simp at hi; omega)]
    rfl

theorem valid_congr (w : List Bool) {i j : Nat} (hi : w.length≤i) (hj : w.length≤j)
    (he : i%modulus w=j%modulus w) : Valid i w ↔ Valid j w := by
  have aux (i j : Nat) (hi : w.length≤i) (hij : i≤j) (he : i%modulus w=j%modulus w) : Valid i w ↔ Valid j w := by
    have hm := Nat.mod_add_div i (modulus w)
    have hn := Nat.mod_add_div j (modulus w)
    have hdiv := Nat.div_le_div_right (c:=modulus w) hij
    let l := j/modulus w-i/modulus w
    have hl : j=i+l*modulus w := by
      have hx : j/modulus w=i/modulus w+l := by dsimp [l]; omega
      rw [hx,Nat.mul_add] at hn
      rw [Nat.mul_comm (modulus w) l] at hn
      omega
    rw [hl]; exact (valid_period w i l hi).symm
  by_cases h : i≤j
  · exact aux i j hi h he
  · exact (aux j i hj (by omega) he.symm).symm

theorem child_lift (i : Nat) (w : List Bool) (e : Bool) (hi : 4*(w.length+1)+10≤i) (hv : Valid i w) :
    ∃ l : Nat, l<3 ∧ Valid (i+l*modulus w) (e::w) ∧
      ∀ k : Nat, k<3 → Valid (i+k*modulus w) (e::w) → k=l := by
  obtain ⟨y,_,hr⟩ := valid_packet hv (by omega)
  have hnum := child_numerator hr (by omega) e
  have hd : ((3^w.length:Nat):Int) ∣ numerator i (e::w) := by rw [hnum]; exact Int.dvd_mul_right ..
  obtain ⟨l,hl,hlv,hu⟩ := lift_unique (3^w.length) _ (Nat.pow_pos (by decide)) hd
  have eq (k : Nat) : Valid (i+k*modulus w) (e::w) ↔
      (numerator i (e::w)+(3^w.length:Nat)*(k:Int))%(3*((3^w.length:Nat):Int))=0 := by
    change (Valid (i+k*modulus w) w ∧ numerator (i+k*modulus w) (e::w)%↑(3^((e::w).length):Nat)=0) ↔ _
    rw [valid_period w i k (by omega)]
    change (Valid i w ∧ numerator (i+k*(2*3^w.length)) (e::w)%↑(3^(w.length+1):Nat)=0) ↔ _
    rw [numerator_lifts i w.length (e::w) rfl (by simp; omega) k]
    simp only [List.length_cons,Nat.pow_succ,Int.natCast_mul]
    change (Valid i w ∧ (numerator i (e::w)+(3^w.length:Nat)*(k:Int))%(((3^w.length:Nat):Int)*3)=0) ↔ _
    rw [Int.mul_comm ((3^w.length:Nat):Int) 3]
    simp [hv]
  exact ⟨l,hl,(eq l).mpr hlv,fun k hk hv' => hu k hk ((eq k).mp hv')⟩

/-- One residue class for each branch word and fixed index parity. -/
theorem word_class (w : List Bool) (p : Nat) (hp : p<2) :
    ∃ r : Nat, r<modulus w ∧ r%2=p ∧
      ∀ i : Nat, 4*w.length+10≤i → i%2=p → (Valid i w ↔ i%modulus w=r) := by
  induction w with
  | nil => exact ⟨p,by simpa [modulus] using hp,Nat.mod_eq_of_lt hp,by simp [Valid,modulus]⟩
  | cons e w ih =>
    obtain ⟨r,hr,hpar,hclass⟩ := ih
    let M := modulus w
    let g := 4*(w.length+1)+10
    let i := r+3*M*g
    have hM : 0<M := modulus_pos w
    have hi : g≤i := by
      have := Nat.mul_le_mul_right g (show 1≤3*M by omega)
      dsimp [i]; omega
    have hmod : i%M=r := by
      dsimp [i]; rw [show 3*M*g=M*(3*g) by ac_rfl,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hr]
    have htwo : 2∣M := ⟨3^w.length,rfl⟩
    have hip : i%2=p := by rw [←Nat.mod_mod_of_dvd i htwo,hmod,hpar]
    have hvi := (hclass i (by dsimp [g] at hi; omega) hip).mpr hmod
    obtain ⟨l,hl,hlv,hu⟩ := child_lift i w e (by exact hi) hvi
    let R := r+l*M
    have hR : R<3*M := by
      have hmul := Nat.mul_le_mul_right M (show l≤2 by omega)
      dsimp [R]; omega
    have hRM : R%M=r := by dsimp [R]; rw [Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt hr]
    have hRp : R%2=p := by rw [←Nat.mod_mod_of_dvd R htwo,hRM,hpar]
    have hLift (k : Nat) (hk : k<3) : (i+k*M)%(3*M)=r+k*M := by
      have hmul := Nat.mul_le_mul_right M (show k≤2 by omega)
      have hlt : r+k*M<3*M := by omega
      dsimp [i]; rw [show r+3*M*g+k*M=(r+k*M)+(3*M)*g by omega,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hlt]
    refine ⟨R,by rw [modulus_cons]; exact hR,hRp,?_⟩
    intro j hj hjp
    have hjlen : (e::w).length≤j := by simp at hj ⊢; omega
    constructor
    · intro hv
      have hvp : Valid j w := hv.1
      have hjM := (hclass j (by simp at hj; omega) hjp).mp hvp
      let q := j%(3*M)
      have hq : q<3*M := Nat.mod_lt _ (by omega)
      have hqM : q%M=r := by
        dsimp [q]; rw [Nat.mod_mod_of_dvd _ (show M∣3*M from ⟨3,by omega⟩),hjM]
      let k := q/M
      have hk : k<3 := (Nat.div_lt_iff_lt_mul hM).mpr hq
      have hqk : q=r+k*M := by
        have hh := Nat.mod_add_div q M
        rw [hqM,Nat.mul_comm] at hh
        exact hh.symm
      have hc : (i+k*M)%modulus (e::w)=j%modulus (e::w) := by
        rw [modulus_cons,hLift k hk]; exact hqk.symm
      have hvk := (valid_congr (e::w) (by simp; dsimp [g] at hi; omega) hjlen hc).mpr hv
      have hkl := hu k hk hvk
      rw [modulus_cons]; change q=R; rw [hqk,hkl]
    · intro hjR
      have hc : (i+l*M)%modulus (e::w)=j%modulus (e::w) := by
        rw [hjR,modulus_cons,hLift l hl]
      exact (valid_congr (e::w) (by simp; dsimp [g] at hi; omega) hjlen hc).mp hlv

theorem valid_unique {i : Nat} (w v : List Bool) (hlen : w.length=v.length)
    (hi : 4*w.length+10≤i) (hw : Valid i w) (hv : Valid i v) : w=v := by
  induction w generalizing v with
  | nil => cases v with
    | nil => rfl
    | cons b v => simp at hlen
  | cons e w ih =>
    cases v with
    | nil => simp at hlen
    | cons b v =>
      have hlen' : w.length=v.length := by simpa using hlen
      have hi' : 4*w.length+10≤i := by simp at hi; omega
      have h : w=v := ih v hlen' hi' hw.1 hv.1
      subst v
      obtain ⟨y,_,hr⟩ := valid_packet hw.1 hi'
      have hiLen : w.length+1≤i := by simp at hi; omega
      have he := (child_integral hr hiLen e).mp hw.2
      have hb := (child_integral hr hiLen b).mp hv.2
      have hidx := word_index i w
      have h0 : 0<i-(packetFor i w).d := by omega
      cases e <;> cases b <;> try rfl
      all_goals
        simp [choose] at he hb
        have h := p_adjacent (i-((packetFor i w).d+1))
        rw [show i-((packetFor i w).d+1)+1=i-(packetFor i w).d by omega] at h
        exact False.elim (h (by omega))

/-- Distinct words at the same depth cannot occupy the same residue class. -/
theorem distinct_classes {w v : List Bool} {r : Nat} (hlen : w.length=v.length)
    (hr : r<modulus w)
    (hw : ∀ i, 4*w.length+10≤i → i%2=r%2 → (Valid i w ↔ i%modulus w=r))
    (hv : ∀ i, 4*v.length+10≤i → i%2=r%2 → (Valid i v ↔ i%modulus v=r)) : w=v := by
  let g := 4*w.length+10
  let i := r+modulus w*g
  have hM := modulus_pos w
  have hi : g≤i := by
    have := Nat.mul_le_mul_right g (show 1≤modulus w by omega)
    dsimp [i]; omega
  have hmod : i%modulus w=r := by dsimp [i]; rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hr]
  have htwo : 2∣modulus w := ⟨3^w.length,rfl⟩
  have hip : i%2=r%2 := by rw [←Nat.mod_mod_of_dvd i htwo,hmod]
  have hmv : modulus w=modulus v := by simp [modulus,hlen]
  exact valid_unique w v hlen hi ((hw i hi hip).mpr hmod) ((hv i (by rw [←hlen]; exact hi) hip).mpr (by rw [←hmv]; exact hmod))

#print axioms valid_unique
#print axioms distinct_classes
#print axioms child_lift
#print axioms word_class
#print axioms numerator_lifts
#print axioms valid_period
#print axioms valid_congr
end CapSieve
