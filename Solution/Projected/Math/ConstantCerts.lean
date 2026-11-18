import Solution.Projected.Certs.CertsFinal

/-! P-256 constant certificates: the fixed-base table, the shift point, and
small multiples of G, assembled from the generated Certs modules. -/
namespace Solution.Projected

open Challenge.Specs.ECDSAP256

/-- Offset-candidate count: at least the catalogue size + 1 (1040). -/
def N_H : ℕ := 1050

theorem table_pt (i : Fin 128) (d : Fin 4) :
    ∃ h, pt (tableX i d) (tableY i d) h = ((4 + d.val) * 4^i.val) • G :=
  table_pt_aux i d

theorem shift_pt : ∃ h, pt shiftX shiftY h = (4 * ((4^128 - 1) / 3)) • G :=
  shift_pt_aux

theorem small_multiples_ne_zero : ∀ m, 0 < m → m < 4 * N_H → m • G ≠ 0 :=
  small_multiples_ne_zero_aux

end Solution.Projected

#print axioms Solution.Projected.table_pt
#print axioms Solution.Projected.shift_pt
#print axioms Solution.Projected.small_multiples_ne_zero
