/-
# Executable entry point for the standard P-256 ECDSA circuit diagnostics

Kept in its own module so that `StandardECDSA.Check` (the library of
diagnostics, imported by the regression suite) does not declare a root-level
`main`, which would clash with the entry point of any other executable that
imports it.

Task T18/T19/T20.
-/
import StandardECDSA.Check

def main (args : List String) : IO UInt32 := StandardECDSA.Check.run args
