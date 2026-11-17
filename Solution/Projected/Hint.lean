import Solution.Projected.Types

/-! Hint-row layout for the projected-signature circuit.
`hint i` = `.hintGet "offset" 1 (const i) 0`:
0 = ry, 1,2 = H = (hx,hy), 3..10 = pre[0..7],
11+3i, 12+3i, 13+3i = (e_i, r_i, t_i) for i = 0..255 (LSB first, weight 2^i). -/
namespace Solution.Projected

def hint (i : Nat) : C E :=
  Circuit.witnessField (.hintGet "offset" 1 (.const i.toUInt64) ⟨0, by decide⟩)

end Solution.Projected
