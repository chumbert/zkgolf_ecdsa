import Solution.Projected.Certs.CertsFinal
import Solution.Projected.Math.ShiftCert
import Solution.Projected.Math.SmallMultiples

/-! P-256 constant certificates: the fixed-base table, the shift point, and
small multiples of G, assembled from the generated Certs modules. -/
namespace Solution.Projected

open Challenge.Specs.ECDSAP256

-- N_H and small_multiples_ne_zero are now imported from SmallMultiples
-- (previously redeclared here)

theorem table_pt (i : Fin 128) (d : Fin 4) :
    ∃ h, pt (tableX i d) (tableY i d) h = ((4 + d.val) * 4^i.val) • G :=
  table_pt_aux i d

-- shift_pt is imported from ShiftCert (not redeclared here)

end Solution.Projected

#print axioms Solution.Projected.table_pt
#print axioms Solution.Projected.shift_pt
#print axioms Solution.Projected.small_multiples_ne_zero
