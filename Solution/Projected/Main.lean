import Solution.Projected.Export

def main (args : List String) : IO UInt32 := do
  if args.contains "--constants-check" then
    if ← Solution.Projected.Check.constantsCheck then
      IO.println "constants check: literal tables equal Offset.fixedTables/fixedShift"
      return 0
    else
      IO.println "constants check FAILED"
      return 1
  if args.head? == some "--export" then
    let directory := System.FilePath.mk (args[1]?.getD "Solution/Projected/generated")
    Solution.Projected.Export.exportTo directory
    return 0
  Solution.Projected.Check.run args
