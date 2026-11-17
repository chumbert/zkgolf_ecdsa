import Solution.Projected.Gadgets
import Challenge.Instances.ECDSA_P256_Projected.Interface

/-! Proof-friendly projected-signature circuit.
Operation-for-operation identical to `Baseline.Projected.Offset.main`
(measured 9,267 = 4,631 allocations + 4,636 rows). -/
namespace Solution.Projected

open Challenge.Instances.ECDSA_P256_Projected.Interface

def main (inp : Var Input Fp) : C Unit := do
  let ry ← hint 0
  let hx ← hint 1
  let hy ← hint 2
  let q := ⟨inp.pkX,inp.pkY⟩
  let r := ⟨inp.r,ry⟩
  let h := ⟨hx,hy⟩
  isOnCurve q.x q.y
  isOnCurve r.x r.y
  isOnCurve hx hy
  let _ ← nonzero inp.pkX
  let _ ← nonzero inp.r
  let negS := cst (Challenge.Specs.ECDSAP256.n : Fp) - inp.s
  let _ ← nonzero negS
  let pre ← originalTable q r
  let qr := pre.getD 2 ⟨cst 0,cst 0⟩
  let mut eb : Array E := #[]
  let mut rb : Array E := #[]
  let mut sb : Array E := #[]
  let mut ee := cst 0
  let mut rr := cst 0
  let mut ss := cst 0
  for i in [0:256] do
    let be ← hint (11+3*i)
    let br ← hint (12+3*i)
    let bs ← hint (13+3*i)
    assertBool be
    assertBool br
    assertBool bs
    eb := eb.push be
    rb := rb.push br
    sb := sb.push bs
    ee := ee + sc ((2 : Fp)^i) be
    rr := rr + sc ((2 : Fp)^i) br
    ss := ss + sc ((2 : Fp)^i) bs
  Circuit.assertZero (ee-inp.digest)
  Circuit.assertZero (rr-inp.r)
  Circuit.assertZero (ss-negS)
  assertLtOrder (fun i => rb.getD i (cst 0))
  assertLtOrder (fun i => sb.getD i (cst 0))
  -- E = H + eG, with a nonzero constant offset in every fixed-base window.
  let shift := fixedShift
  let mut ep ← affAdd h ⟨cst shift.1,cst (-shift.2)⟩
  let tables := fixedTables
  for i in [0:128] do
    let t ← muxConst4 (eb.getD (2*i) (cst 0)) (eb.getD (2*i+1) (cst 0))
      (tables.getD i #[])
    ep ← affAdd ep t
  -- Alternating offsets allow both ELM denominators to be avoided by choosing H.
  let hh ← affDouble h
  let hhh ← affAdd hh h
  let mut plus : Array (Point E) := #[hhh]
  let nhhh := ⟨hhh.x,-hhh.y⟩
  let mut minus : Array (Point E) := #[nhhh]
  for t in #[q,r,qr] do
    plus := plus.push (← affAdd hhh t)
    minus := minus.push (← affAdd nhhh t)
  let mut acc := ⟨hx,-hy⟩
  for j in [0:256] do
    let i := 255-j
    let tab := if j%2 == 0 then plus else minus
    let t ← mux4 (rb.getD i (cst 0)) (sb.getD i (cst 0))
      (tab.getD 0 h) (tab.getD 1 h) (tab.getD 2 h) (tab.getD 3 h)
    if j == 255 then
      elmTo acc t ⟨ep.x,-ep.y⟩
    else
      acc ← elm acc t

end Solution.Projected
