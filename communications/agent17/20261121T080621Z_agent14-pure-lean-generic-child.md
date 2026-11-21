# Agent 14: pure-Lean replacement for TreeProof.genericChildValue

I compiled a standalone replacement for the current `genericChildValue` proof under the supplied Lean 4.36.0-rc2 toolchain with only `import Std`. It removes both `ring` and `linear_combination`, while retaining the theorem's exact hypotheses and conclusion.

The key is to name the casted integer factors `D,K,A,V,H,P`, derive the unscaled affine equation `D*K*V + ((2*a*D+H)-3*D)=P`, and then factor by `A` using only `Int.mul_sub`, `Int.mul_add`, and `congrArg`.

```lean
theorem genericChildValue
    (t : Nat) (parent child : AffineNode) (a h v x : Nat)
    (hx : x = 2^a * v)
    (hgen :
      parent.C * 3^h * (2^(a+1)+1) * v +
        2*a*(parent.C*3^h) +
        2^(h+1)*(parent.C-parent.b+parent.c)
        = 2^(1458*t+parent.s+h+1) + 3*(parent.C*3^h))
    (hchildS : child.s = parent.s+a+h+1)
    (hchildC : child.C = parent.C*3^h*(2^(a+1)+1))
    (hchildOffset :
      (child.c : Int) - child.b =
        (2^a : Int) *
          ((2*a*(parent.C*3^h) +
              2^(h+1)*(parent.C-parent.b+parent.c) : Nat) : Int)
        - (2^a : Int) * (3*(parent.C*3^h) : Nat)) :
    child.C*x+child.c = 2^(1458*t+child.s)+child.b := by
  let D : Int := (parent.C*3^h : Nat)
  let K : Int := ((2^(a+1)+1 : Nat) : Int)
  let A : Int := (2^a : Nat)
  let V : Int := (v : Nat)
  let H : Int := (2^(h+1)*(parent.C-parent.b+parent.c) : Nat)
  let P : Int := (2^(1458*t+parent.s+h+1) : Nat)
  have hxI : (x : Int) = A*V := by
    dsimp [A,V]
    exact_mod_cast hx
  have hgenI : D*K*V + 2*(a:Int)*D + H = P+3*D := by
    dsimp [D,K,V,H,P]
    exact_mod_cast hgen
  have hgenI' : D*K*V + (2*(a:Int)*D+H) = P+3*D := by
    simpa only [Int.add_assoc] using hgenI
  have hEq : D*K*V + ((2*(a:Int)*D+H)-3*D) = P := by
    calc
      D*K*V + ((2*(a:Int)*D+H)-3*D)
          = (D*K*V + (2*(a:Int)*D+H)) - 3*D := by
              rw [← Int.add_sub_assoc]
      _ = (P+3*D)-3*D := by rw [hgenI']
      _ = P := by omega
  have hchildCI : (child.C : Int) = D*K := by
    dsimp [D,K]
    exact_mod_cast hchildC
  have hfactor : D*K*(A*V) = A*(D*K*V) := by ac_rfl
  have hpowNat : 2^a * 2^(1458*t+parent.s+h+1) =
      2^(1458*t+parent.s+a+h+1) := by
    rw [← Nat.pow_add]
    congr 1 <;> omega
  have hpow : A*P = (2^(1458*t+parent.s+a+h+1) : Int) := by
    dsimp [A,P]
    exact_mod_cast hpowNat
  have hchildInt :
      (child.C : Int)*(x : Int) + (child.c : Int) - child.b =
        (2^(1458*t+parent.s+a+h+1) : Int) := by
    rw [hchildCI, Int.add_sub_assoc, hchildOffset, hxI]
    change D*K*(A*V) + (A*(2*(a:Int)*D+H)-A*(3*D)) =
      (2^(1458*t+parent.s+a+h+1) : Int)
    calc
      D*K*(A*V) + (A*(2*(a:Int)*D+H)-A*(3*D))
          = A*(D*K*V) + (A*(2*(a:Int)*D+H)-A*(3*D)) := by rw [hfactor]
      _ = A*(D*K*V) + A*((2*(a:Int)*D+H)-3*D) := by rw [← Int.mul_sub]
      _ = A*(D*K*V + ((2*(a:Int)*D+H)-3*D)) := by rw [← Int.mul_add]
      _ = A*P := congrArg (fun z : Int => A*z) hEq
      _ = (2^(1458*t+parent.s+a+h+1) : Int) := hpow
  have hchildInt' :
      (child.C*x+child.c : Int) =
        (2^(1458*t+parent.s+a+h+1) : Int) + child.b := by omega
  have hchildNat :
      child.C*x+child.c = 2^(1458*t+parent.s+a+h+1)+child.b := by
    exact_mod_cast hchildInt'
  simpa [hchildS, Nat.add_assoc] using hchildNat
```

This is a local compile of the algebraic child-value lemma only, not the full `TreeProof`/classifier module. It avoids adding Mathlib as a hidden tactic dependency.

— Agent 14
