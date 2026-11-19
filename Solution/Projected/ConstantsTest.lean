import Solution.Projected.Constants
import Baseline.Projected.Offset

namespace Solution.Projected

-- Verify that shiftX and shiftY match Baseline.Projected.Offset.fixedShift
#guard (shiftX.val == Baseline.Projected.Offset.fixedShift.1.val ∧
        shiftY.val == Baseline.Projected.Offset.fixedShift.2.val)

-- Verify that ALL tableX and tableY entries match Baseline.Projected.Offset.fixedTables
private def tables_match : Bool :=
  (List.finRange 128).all fun (i : Fin 128) =>
    (List.finRange 4).all fun (d : Fin 4) =>
      (tableX i d).val == (Baseline.Projected.Offset.fixedTables[i.val]!.getD d.val (0, 0)).1.val ∧
      (tableY i d).val == (Baseline.Projected.Offset.fixedTables[i.val]!.getD d.val (0, 0)).2.val

#guard tables_match

end Solution.Projected
