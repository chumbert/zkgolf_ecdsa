/-
# Shifted-table phase: `±3H` plus `Q` and `R`

Ported from the pinned `circuit_baseline` revision
(`3a1bd20749ae0b6400a158651dba64a2c5fc58ff`), `Baseline/Projected/Offset.lean`,
with the plan §3A modification: the *original* Longfellow table (which needed
affine coordinates of the unshifted `Q + R`) is deleted, and only the two
shifted tables are built.

For each sign `ε ∈ {+1, -1}`:

```text
P0 = [3ε]H
P1 = P0 + Q
P2 = P0 + R
P3 = P1 + R
table_ε = [P0, P1, P2, P3]
```

This uses six ordinary affine additions and never asks for affine coordinates
of unshifted `Q + R`, so it works when `Q + R = O` or `Q = R`, provided the
chosen offset avoids the actual addition denominators.  Table order matches
`rBit + 2·tBit`.

Cost: `affDouble` (4/4) + `affAdd` (4/4) for `2H` and `3H`, plus six `affAdd`
(24/24) = 32 allocations and 32 rows.

Task T12 (table half).
-/

import StandardECDSA.Gadgets.Affine

namespace StandardECDSA.Phases

open StandardECDSA.Gadgets

/-- The two shifted tables, indexed by `rBit + 2·tBit`.  The eight entries are
named fields (rather than arrays) so that the degree/`localLength` certificates
for the ladder can be stated without any `Array.getD` default. -/
structure Tables where
  /-- `3H` -/
  p0 : Pt
  /-- `3H + Q` -/
  p1 : Pt
  /-- `3H + R` -/
  p2 : Pt
  /-- `3H + Q + R` -/
  p3 : Pt
  /-- `-3H` -/
  m0 : Pt
  /-- `-3H + Q` -/
  m1 : Pt
  /-- `-3H + R` -/
  m2 : Pt
  /-- `-3H + Q + R` -/
  m3 : Pt

/-- The four table entries used at ladder step `j`: the `+` table for even `j`,
the `-` table for odd `j`. -/
def Tables.x0 (t : Tables) (j : ℕ) : Pt := if j % 2 == 0 then t.p0 else t.m0
/-- Second entry of the table selected at step `j`. -/
def Tables.x1 (t : Tables) (j : ℕ) : Pt := if j % 2 == 0 then t.p1 else t.m1
/-- Third entry of the table selected at step `j`. -/
def Tables.x2 (t : Tables) (j : ℕ) : Pt := if j % 2 == 0 then t.p2 else t.m2
/-- Fourth entry of the table selected at step `j`. -/
def Tables.x3 (t : Tables) (j : ℕ) : Pt := if j % 2 == 0 then t.p3 else t.m3

/-- All eight table entries have wire (degree-one) coordinates. -/
def Tables.Wires (t : Tables) : Prop :=
  (deg t.p0.1 = 1 ∧ deg t.p0.2 = 1) ∧ (deg t.p1.1 = 1 ∧ deg t.p1.2 = 1) ∧
  (deg t.p2.1 = 1 ∧ deg t.p2.2 = 1) ∧ (deg t.p3.1 = 1 ∧ deg t.p3.2 = 1) ∧
  (deg t.m0.1 = 1 ∧ deg t.m0.2 = 1) ∧ (deg t.m1.1 = 1 ∧ deg t.m1.2 = 1) ∧
  (deg t.m2.1 = 1 ∧ deg t.m2.2 = 1) ∧ (deg t.m3.1 = 1 ∧ deg t.m3.2 = 1)

theorem Tables.Wires.x0 {t : Tables} (h : t.Wires) (j : ℕ) :
    deg (t.x0 j).1 = 1 ∧ deg (t.x0 j).2 = 1 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  unfold Tables.x0
  split <;> assumption

theorem Tables.Wires.x1 {t : Tables} (h : t.Wires) (j : ℕ) :
    deg (t.x1 j).1 = 1 ∧ deg (t.x1 j).2 = 1 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  unfold Tables.x1
  split <;> assumption

theorem Tables.Wires.x2 {t : Tables} (h : t.Wires) (j : ℕ) :
    deg (t.x2 j).1 = 1 ∧ deg (t.x2 j).2 = 1 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  unfold Tables.x2
  split <;> assumption

theorem Tables.Wires.x3 {t : Tables} (h : t.Wires) (j : ℕ) :
    deg (t.x3 j).1 = 1 ∧ deg (t.x3 j).2 = 1 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  unfold Tables.x3
  split <;> assumption

/-- Build both shifted tables from `H`, `Q` and `R`. -/
def shiftedTables (h q r : Pt) : C Tables := do
  let hh ← affDouble h
  let hhh ← affAdd hh h
  let nhhh := negPt hhh
  let p1 ← affAdd hhh q
  let p2 ← affAdd hhh r
  let p3 ← affAdd p1 r
  let m1 ← affAdd nhhh q
  let m2 ← affAdd nhhh r
  let m3 ← affAdd m1 r
  return { p0 := hhh, p1 := p1, p2 := p2, p3 := p3,
           m0 := nhhh, m1 := m1, m2 := m2, m3 := m3 }

end StandardECDSA.Phases
