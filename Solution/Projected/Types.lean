import Clean.Circuit
import Clean.Utils.Tactics.ProvableStructDeriving

namespace Solution.Projected

/-- A point with coordinates in field F. -/
structure Point (F : Type) where
  x : F
  y : F
  deriving ProvableStruct

/-- A table of 4 points. -/
structure Table4 (F : Type) where
  p0 : Point F
  p1 : Point F
  p2 : Point F
  p3 : Point F
  deriving ProvableStruct

/-- Input for the `affAdd` gadget. -/
structure AffAddInput (F : Type) where
  P : Point F
  Q : Point F
  deriving ProvableStruct

/-- Input for the `elm` gadget. -/
structure ElmInput (F : Type) where
  A : Point F
  T : Point F
  deriving ProvableStruct

/-- Input for the `elmTo` gadget. -/
structure ElmToInput (F : Type) where
  A : Point F
  T : Point F
  target : Point F
  deriving ProvableStruct

/-- Input for the `mux4` gadget. -/
structure Mux4Input (F : Type) where
  b0 : F
  b1 : F
  table : Table4 F
  deriving ProvableStruct

/-- Input for the `muxConst4` gadget (table index `i` is a parameter). -/
structure MuxConst4Input (F : Type) where
  b0 : F
  b1 : F
  deriving ProvableStruct

/-- Input for the `originalTable` gadget. -/
structure OriginalTableInput (F : Type) where
  Q : Point F
  R : Point F
  pre : Vector F 8
  deriving ProvableStruct

/-- Input for the `ltOrder` gadget. -/
structure LtOrderInput (F : Type) where
  bits : Vector F 256
  deriving ProvableStruct

end Solution.Projected
