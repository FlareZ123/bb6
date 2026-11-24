import NearPowerTree

namespace BB6.Agent41NearPower

/-- Bisection returns an exact hit or a candidate lower bracket. Its output is
untrusted until checked by `check`, so even truncated bisection is safe. -/
def bisect (s : NearState) (q : Sector) (w0 : Int) : Nat → Int → Int → Int
  | 0,lo,_ => 4*(lo-1)+w0
  | f+1,lo,hi =>
    if hi<lo then 4*(lo-1)+w0 else
      let m := (lo+hi)/2
      let w := 4*m+w0
      let v := imageResidual s.D (s.k-1) (z q) w
      if v=s.v then w else
        if v<s.v then bisect s q w0 f (m+1) hi else bisect s q w0 f lo (m-1)

def findW (s : NearState) (q : Sector) : Int :=
  let n := budget s
  let w0 := (2*(bp q:Int)-(s.D:Int)*powMod4 (s.k-1))%4
  let wlo := (s.v-2*(z q:Int)-8*(n:Int)+2)/3
  let whi := (s.v-2*(z q:Int))/3
  let lo := (wlo-w0+3)/4
  let hi := (whi-w0)/4
  bisect s q w0 ((hi-lo).natAbs.log2+3) lo hi

/-- The generator is deliberately outside the trusted proof. A failed guard
or depth limit returns a rejected stop. Successful finite trees are checked. -/
def generate : Nat → NearState → Cert
  | 0,_ => .stop
  | f+1,s =>
    if guarded s then
      let l := leftSector s
      let r := rightSector s
      let wl := findW s l
      let wr := findW s r
      let cl := restore s l wl
      let cr := restore s r wr
      let tl := if gapOK s.D (s.k-1) (z l) (bp l) wl s.v || rejectParity cl l then Cert.stop else generate f cl
      let tr := if gapOK s.D (s.k-1) (z r) (bp r) wr s.v || rejectParity cr r then Cert.stop else generate f cr
      .fork wl wr tl tr
    else .stop

def fatalState (p : Nat) : NearState := ⟨1,13,p,-5,7-4*(p:Int)⟩

def verifiedFatal (p fuel : Nat) : Bool := check (fatalState p) (generate fuel (fatalState p))

end BB6.Agent41NearPower
