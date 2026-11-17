import Solution.Projected.Export

def main (args : List String) : IO UInt32 := do
  if args.head? == some "--export" then
    let directory := System.FilePath.mk (args[1]?.getD "Solution/Projected/generated")
    Solution.Projected.Export.exportTo directory
    return 0
  Solution.Projected.Check.run args
