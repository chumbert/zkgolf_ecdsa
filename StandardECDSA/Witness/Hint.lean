/-
# The concrete prover hint built from a witness seed (gap G2, step 1)

`StandardECDSA/Witness/Seed.lean` fixes the *typed* 772-field seed layout, and
`StandardECDSA/Witness/Correctness.lean` proves that `generateSeed` produces an
admissible seed for every standard-valid input.  What was still missing is the
*concrete* `ProverHint` that the circuit actually reads: the circuit's `hint i`
leaf is

```
Circuit.witnessField (.hintGet hintKey 1 (.const i.toUInt64) ⟨0, _⟩)
```

(`StandardECDSA/Main.lean`), i.e. it reads row `i` of the single-column hint table
`env.hint hintKey 1`.  This module flattens a `Seed` into that table.

## Row layout

The 772 cells are laid out exactly as the circuit reads them:

| hint index | cell |
|---|---|
| `0` | `ry` |
| `1` | `hx` |
| `2` | `hy` |
| `3` | `overflow` |
| `4 + 3·j` | `digestBits j` |
| `5 + 3·j` | `rBits j` |
| `6 + 3·j` | `tBits j` |

for `j : Fin 256`.  The three interleaved bit vectors are the `bitVec 4 3`,
`bitVec 5 3` and `bitVec 6 3` stages of `bitsPhase`, whose `k`-th body reads hint
row `base + stride·k`.

## Main results

* `seedCells` — the 772-cell list, with `seedCells_length` and one
  `seedCells_getElem?_*` lemma per block;
* `seedHint` — the `ProverHint Fp` whose `hintKey` table is `seedCells`;
* `seedHint_getElem` — the value read by the circuit's `hintGet` leaf at row `i`
  is `(seedCells s).getD i 0`.

Gap G2 of `docs/m6-report.md`.
-/
import StandardECDSA.Main
import StandardECDSA.Witness.Seed

namespace StandardECDSA.Witness

open StandardECDSA
open StandardECDSA.Gadgets

/-! ## The 772-cell list -/

/-- The `j`-th digest bit, extended by `0` outside `Fin 256`. -/
def seedBitD (s : Seed) (j : Nat) : K := if h : j < 256 then s.digestBits ⟨j, h⟩ else 0

/-- The `j`-th bit of `r`, extended by `0` outside `Fin 256`. -/
def seedBitR (s : Seed) (j : Nat) : K := if h : j < 256 then s.rBits ⟨j, h⟩ else 0

/-- The `j`-th bit of `t = n - s`, extended by `0` outside `Fin 256`. -/
def seedBitT (s : Seed) (j : Nat) : K := if h : j < 256 then s.tBits ⟨j, h⟩ else 0

/-- The first `m` interleaved `(digest, r, t)` bit triples. -/
def seedTriples (s : Seed) : Nat → List K
  | 0 => []
  | m + 1 => seedTriples s m ++ [seedBitD s m, seedBitR s m, seedBitT s m]

/-- The 772 hint cells of a seed, in the order the circuit reads them. -/
def seedCells (s : Seed) : List K :=
  [s.ry, s.hx, s.hy, s.overflow] ++ seedTriples s 256

theorem seedTriples_length (s : Seed) (m : Nat) : (seedTriples s m).length = 3 * m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [seedTriples, List.length_append, ih, List.length_cons, List.length_nil]
    omega

/-- The seed flattens to exactly 772 hint cells. -/
theorem seedCells_length (s : Seed) : (seedCells s).length = 772 := by
  simp only [seedCells, List.length_append, List.length_cons, List.length_nil,
    seedTriples_length]

theorem seedTriples_getElem? (s : Seed) (m j : Nat) (hj : j < m) :
    (seedTriples s m)[3 * j]? = some (seedBitD s j) ∧
      (seedTriples s m)[3 * j + 1]? = some (seedBitR s j) ∧
      (seedTriples s m)[3 * j + 2]? = some (seedBitT s j) := by
  induction m with
  | zero => omega
  | succ m ih =>
    simp only [seedTriples]
    have hlen : (seedTriples s m).length = 3 * m := seedTriples_length s m
    rcases Nat.lt_or_ge j m with h | h
    · obtain ⟨h1, h2, h3⟩ := ih h
      rw [List.getElem?_append_left (by rw [hlen]; omega),
        List.getElem?_append_left (by rw [hlen]; omega),
        List.getElem?_append_left (by rw [hlen]; omega)]
      exact ⟨h1, h2, h3⟩
    · have hje : j = m := by omega
      rw [List.getElem?_append_right (by rw [hlen]; omega),
        List.getElem?_append_right (by rw [hlen]; omega),
        List.getElem?_append_right (by rw [hlen]; omega)]
      rw [hlen]
      rw [show 3 * j - 3 * m = 0 from by omega,
        show 3 * j + 1 - 3 * m = 1 from by omega,
        show 3 * j + 2 - 3 * m = 2 from by omega]
      subst hje
      exact ⟨rfl, rfl, rfl⟩

/-! ## The four scalar cells -/

theorem seedCells_getElem?_ry (s : Seed) : (seedCells s)[0]? = some s.ry := by
  show ([s.ry, s.hx, s.hy, s.overflow] ++ seedTriples s 256)[0]? = some s.ry
  rw [List.getElem?_append_left (by simp)]
  rfl

theorem seedCells_getElem?_hx (s : Seed) : (seedCells s)[1]? = some s.hx := by
  show ([s.ry, s.hx, s.hy, s.overflow] ++ seedTriples s 256)[1]? = some s.hx
  rw [List.getElem?_append_left (by simp)]
  rfl

theorem seedCells_getElem?_hy (s : Seed) : (seedCells s)[2]? = some s.hy := by
  show ([s.ry, s.hx, s.hy, s.overflow] ++ seedTriples s 256)[2]? = some s.hy
  rw [List.getElem?_append_left (by simp)]
  rfl

theorem seedCells_getElem?_ov (s : Seed) : (seedCells s)[3]? = some s.overflow := by
  show ([s.ry, s.hx, s.hy, s.overflow] ++ seedTriples s 256)[3]? = some s.overflow
  rw [List.getElem?_append_left (by simp)]
  rfl

/-! ## The three interleaved bit vectors -/

theorem seedCells_getElem?_digest (s : Seed) (j : Fin 256) :
    (seedCells s)[4 + 3 * j.val]? = some (s.digestBits j) := by
  show ([s.ry, s.hx, s.hy, s.overflow] ++ seedTriples s 256)[4 + 3 * j.val]? = _
  rw [List.getElem?_append_right (by simp only [List.length_cons, List.length_nil]; omega)]
  simp only [List.length_cons, List.length_nil]
  rw [show 4 + 3 * j.val - (1 + (1 + (1 + (1 + 0)))) = 3 * j.val from by omega]
  obtain ⟨h1, -, -⟩ := seedTriples_getElem? s 256 j.val j.isLt
  rw [h1, show seedBitD s j.val = s.digestBits j from by
    simp only [seedBitD, dite_eq_left j.isLt]]

theorem seedCells_getElem?_r (s : Seed) (j : Fin 256) :
    (seedCells s)[5 + 3 * j.val]? = some (s.rBits j) := by
  show ([s.ry, s.hx, s.hy, s.overflow] ++ seedTriples s 256)[5 + 3 * j.val]? = _
  rw [List.getElem?_append_right (by simp only [List.length_cons, List.length_nil]; omega)]
  simp only [List.length_cons, List.length_nil]
  rw [show 5 + 3 * j.val - (1 + (1 + (1 + (1 + 0)))) = 3 * j.val + 1 from by omega]
  obtain ⟨-, h2, -⟩ := seedTriples_getElem? s 256 j.val j.isLt
  rw [h2, show seedBitR s j.val = s.rBits j from by
    simp only [seedBitR, dite_eq_left j.isLt]]

theorem seedCells_getElem?_t (s : Seed) (j : Fin 256) :
    (seedCells s)[6 + 3 * j.val]? = some (s.tBits j) := by
  show ([s.ry, s.hx, s.hy, s.overflow] ++ seedTriples s 256)[6 + 3 * j.val]? = _
  rw [List.getElem?_append_right (by simp only [List.length_cons, List.length_nil]; omega)]
  simp only [List.length_cons, List.length_nil]
  rw [show 6 + 3 * j.val - (1 + (1 + (1 + (1 + 0)))) = 3 * j.val + 2 from by omega]
  obtain ⟨-, -, h3⟩ := seedTriples_getElem? s 256 j.val j.isLt
  rw [h3, show seedBitT s j.val = s.tBits j from by
    simp only [seedBitT, dite_eq_left j.isLt]]

/-! ## The cells as `getD` values -/

theorem seedCells_getD_ry (s : Seed) : (seedCells s).getD 0 0 = s.ry := by
  rw [List.getD_eq_getElem?_getD, seedCells_getElem?_ry]; rfl

theorem seedCells_getD_hx (s : Seed) : (seedCells s).getD 1 0 = s.hx := by
  rw [List.getD_eq_getElem?_getD, seedCells_getElem?_hx]; rfl

theorem seedCells_getD_hy (s : Seed) : (seedCells s).getD 2 0 = s.hy := by
  rw [List.getD_eq_getElem?_getD, seedCells_getElem?_hy]; rfl

theorem seedCells_getD_ov (s : Seed) : (seedCells s).getD 3 0 = s.overflow := by
  rw [List.getD_eq_getElem?_getD, seedCells_getElem?_ov]; rfl

theorem seedCells_getD_digest (s : Seed) (j : Fin 256) :
    (seedCells s).getD (4 + 3 * j.val) 0 = s.digestBits j := by
  rw [List.getD_eq_getElem?_getD, seedCells_getElem?_digest]; rfl

theorem seedCells_getD_r (s : Seed) (j : Fin 256) :
    (seedCells s).getD (5 + 3 * j.val) 0 = s.rBits j := by
  rw [List.getD_eq_getElem?_getD, seedCells_getElem?_r]; rfl

theorem seedCells_getD_t (s : Seed) (j : Fin 256) :
    (seedCells s).getD (6 + 3 * j.val) 0 = s.tBits j := by
  rw [List.getD_eq_getElem?_getD, seedCells_getElem?_t]; rfl

/-! ## The concrete hint provider -/

/-- The concrete `ProverHint` of a seed: the `hintKey` table has one row per hint
cell, each row being a single-column vector. -/
def seedHint (s : Seed) : ProverHint Fp :=
  fun key n =>
    if key = hintKey then
      ((seedCells s).map (fun x => Vector.ofFn (fun _ : Fin n => x))).toArray
    else #[]

theorem seedHint_apply (s : Seed) (n : Nat) :
    seedHint s hintKey n
      = ((seedCells s).map (fun x => Vector.ofFn (fun _ : Fin n => x))).toArray := by
  simp only [seedHint, ite_true]

/-- Row `i` of the concrete hint table is the constant vector of the `i`-th cell. -/
theorem seedHint_getD (s : Seed) (i : Nat) (hi : i < 772) :
    (seedHint s hintKey 1)[i]?.getD default
      = Vector.ofFn (fun _ : Fin 1 => (seedCells s).getD i 0) := by
  have hlen : i < (seedCells s).length := by rw [seedCells_length]; exact hi
  rw [seedHint_apply]
  rw [List.getElem?_toArray, List.getElem?_map, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hlen]
  rfl

/-- **The value the circuit's `hintGet` leaf reads at row `i`.** -/
theorem seedHint_getElem (s : Seed) (i : Nat) (hi : i < 772) (c : Fin 1) :
    ((seedHint s hintKey 1)[i]?.getD default)[c] = (seedCells s).getD i 0 := by
  rw [seedHint_getD s i hi]
  simp

end StandardECDSA.Witness
