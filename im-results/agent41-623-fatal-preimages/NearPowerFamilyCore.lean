import NearPowerSymbolicTree

namespace BB6.Agent41NearPower

def symFatal (R : Nat) (off : Int) : SymState :=
  let k : Aff := ⟨6*3^R,0,off⟩
  ⟨1,13,k,ac (-5),ac 7-(4:Int)*k⟩

structure CertifiedFamily where
  R : Nat
  off : Int
  cert : SymCert
  accepted : symCheck (symFatal R off) cert=true

end BB6.Agent41NearPower
