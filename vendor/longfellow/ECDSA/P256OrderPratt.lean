import ECDSA.PowMod

/-!
# Pratt certificate for the P-256 group order `n`

`n` is the order of the P-256 generator.  The certificate below is a
recursive Lucas/Pratt certificate: for each prime `q` in the chain we give a
witness `a` with `a^(q-1) = 1` and `a^((q-1)/p) != 1` for every prime `p | q-1`,
together with the factorisation of `q-1` into already certified primes.

Generated mechanically; every step is re-checked by the kernel (`decide` on
`powMod`), so the advice cannot be wrong without the proof failing.
-/

public section

namespace ECDSA

set_option maxRecDepth 40000
set_option exponentiation.threshold 300

theorem prime_5 : Nat.Prime 5 := by
  refine lucas_primality 5 ((2 : ℕ) : ZMod 5) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 5 - 1 = ([2, 2] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_nil _⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_7 : Nat.Prime 7 := by
  refine lucas_primality 7 ((3 : ℕ) : ZMod 7) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 7 - 1 = ([2, 3] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_three, List.forall_mem_nil _⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_11 : Nat.Prime 11 := by
  refine lucas_primality 11 ((2 : ℕ) : ZMod 11) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 11 - 1 = ([2, 5] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨prime_5, List.forall_mem_nil _⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_13 : Nat.Prime 13 := by
  refine lucas_primality 13 ((2 : ℕ) : ZMod 13) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 13 - 1 = ([2, 2, 3] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_three, List.forall_mem_nil _⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_17 : Nat.Prime 17 := by
  refine lucas_primality 17 ((3 : ℕ) : ZMod 17) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 17 - 1 = ([2, 2, 2, 2] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_nil _⟩⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_19 : Nat.Prime 19 := by
  refine lucas_primality 19 ((2 : ℕ) : ZMod 19) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 19 - 1 = ([2, 3, 3] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_three, List.forall_mem_cons.mpr ⟨Nat.prime_three, List.forall_mem_nil _⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_29 : Nat.Prime 29 := by
  refine lucas_primality 29 ((2 : ℕ) : ZMod 29) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 29 - 1 = ([2, 2, 7] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨prime_7, List.forall_mem_nil _⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_31 : Nat.Prime 31 := by
  refine lucas_primality 31 ((3 : ℕ) : ZMod 31) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 31 - 1 = ([2, 3, 5] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_three, List.forall_mem_cons.mpr ⟨prime_5, List.forall_mem_nil _⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_37 : Nat.Prime 37 := by
  refine lucas_primality 37 ((2 : ℕ) : ZMod 37) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 37 - 1 = ([2, 2, 3, 3] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_three, List.forall_mem_cons.mpr ⟨Nat.prime_three, List.forall_mem_nil _⟩⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_41 : Nat.Prime 41 := by
  refine lucas_primality 41 ((6 : ℕ) : ZMod 41) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 41 - 1 = ([2, 2, 2, 5] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨prime_5, List.forall_mem_nil _⟩⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_43 : Nat.Prime 43 := by
  refine lucas_primality 43 ((3 : ℕ) : ZMod 43) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 43 - 1 = ([2, 3, 7] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_three, List.forall_mem_cons.mpr ⟨prime_7, List.forall_mem_nil _⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_71 : Nat.Prime 71 := by
  refine lucas_primality 71 ((7 : ℕ) : ZMod 71) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 71 - 1 = ([2, 5, 7] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨prime_5, List.forall_mem_cons.mpr ⟨prime_7, List.forall_mem_nil _⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_97 : Nat.Prime 97 := by
  refine lucas_primality 97 ((5 : ℕ) : ZMod 97) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 97 - 1 = ([2, 2, 2, 2, 2, 3] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_three, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_127 : Nat.Prime 127 := by
  refine lucas_primality 127 ((3 : ℕ) : ZMod 127) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 127 - 1 = ([2, 3, 3, 7] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_three, List.forall_mem_cons.mpr ⟨Nat.prime_three, List.forall_mem_cons.mpr ⟨prime_7, List.forall_mem_nil _⟩⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_131 : Nat.Prime 131 := by
  refine lucas_primality 131 ((2 : ℕ) : ZMod 131) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 131 - 1 = ([2, 5, 13] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨prime_5, List.forall_mem_cons.mpr ⟨prime_13, List.forall_mem_nil _⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_151 : Nat.Prime 151 := by
  refine lucas_primality 151 ((6 : ℕ) : ZMod 151) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 151 - 1 = ([2, 3, 5, 5] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_three, List.forall_mem_cons.mpr ⟨prime_5, List.forall_mem_cons.mpr ⟨prime_5, List.forall_mem_nil _⟩⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_229 : Nat.Prime 229 := by
  refine lucas_primality 229 ((6 : ℕ) : ZMod 229) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 229 - 1 = ([2, 2, 3, 19] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_three, List.forall_mem_cons.mpr ⟨prime_19, List.forall_mem_nil _⟩⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_263 : Nat.Prime 263 := by
  refine lucas_primality 263 ((5 : ℕ) : ZMod 263) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 263 - 1 = ([2, 131] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨prime_131, List.forall_mem_nil _⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_311 : Nat.Prime 311 := by
  refine lucas_primality 311 ((17 : ℕ) : ZMod 311) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 311 - 1 = ([2, 5, 31] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨prime_5, List.forall_mem_cons.mpr ⟨prime_31, List.forall_mem_nil _⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_337 : Nat.Prime 337 := by
  refine lucas_primality 337 ((10 : ℕ) : ZMod 337) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 337 - 1 = ([2, 2, 2, 2, 3, 7] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_three, List.forall_mem_cons.mpr ⟨prime_7, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_373 : Nat.Prime 373 := by
  refine lucas_primality 373 ((2 : ℕ) : ZMod 373) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 373 - 1 = ([2, 2, 3, 31] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_three, List.forall_mem_cons.mpr ⟨prime_31, List.forall_mem_nil _⟩⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_727 : Nat.Prime 727 := by
  refine lucas_primality 727 ((5 : ℕ) : ZMod 727) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 727 - 1 = ([2, 3, 11, 11] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_three, List.forall_mem_cons.mpr ⟨prime_11, List.forall_mem_cons.mpr ⟨prime_11, List.forall_mem_nil _⟩⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_1201 : Nat.Prime 1201 := by
  refine lucas_primality 1201 ((11 : ℕ) : ZMod 1201) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 1201 - 1 = ([2, 2, 2, 2, 3, 5, 5] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_three, List.forall_mem_cons.mpr ⟨prime_5, List.forall_mem_cons.mpr ⟨prime_5, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_1297 : Nat.Prime 1297 := by
  refine lucas_primality 1297 ((10 : ℕ) : ZMod 1297) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 1297 - 1 = ([2, 2, 2, 2, 3, 3, 3, 3] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_three, List.forall_mem_cons.mpr ⟨Nat.prime_three, List.forall_mem_cons.mpr ⟨Nat.prime_three, List.forall_mem_cons.mpr ⟨Nat.prime_three, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_1511 : Nat.Prime 1511 := by
  refine lucas_primality 1511 ((11 : ℕ) : ZMod 1511) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 1511 - 1 = ([2, 5, 151] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨prime_5, List.forall_mem_cons.mpr ⟨prime_151, List.forall_mem_nil _⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_3023 : Nat.Prime 3023 := by
  refine lucas_primality 3023 ((5 : ℕ) : ZMod 3023) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 3023 - 1 = ([2, 1511] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨prime_1511, List.forall_mem_nil _⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_3407 : Nat.Prime 3407 := by
  refine lucas_primality 3407 ((5 : ℕ) : ZMod 3407) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 3407 - 1 = ([2, 13, 131] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨prime_13, List.forall_mem_cons.mpr ⟨prime_131, List.forall_mem_nil _⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_9547 : Nat.Prime 9547 := by
  refine lucas_primality 9547 ((2 : ℕ) : ZMod 9547) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 9547 - 1 = ([2, 3, 37, 43] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_three, List.forall_mem_cons.mpr ⟨prime_37, List.forall_mem_cons.mpr ⟨prime_43, List.forall_mem_nil _⟩⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_16879 : Nat.Prime 16879 := by
  refine lucas_primality 16879 ((3 : ℕ) : ZMod 16879) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 16879 - 1 = ([2, 3, 29, 97] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_three, List.forall_mem_cons.mpr ⟨prime_29, List.forall_mem_cons.mpr ⟨prime_97, List.forall_mem_nil _⟩⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_17449 : Nat.Prime 17449 := by
  refine lucas_primality 17449 ((14 : ℕ) : ZMod 17449) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 17449 - 1 = ([2, 2, 2, 3, 727] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_three, List.forall_mem_cons.mpr ⟨prime_727, List.forall_mem_nil _⟩⟩⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_38189 : Nat.Prime 38189 := by
  refine lucas_primality 38189 ((2 : ℕ) : ZMod 38189) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 38189 - 1 = ([2, 2, 9547] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨prime_9547, List.forall_mem_nil _⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_104471 : Nat.Prime 104471 := by
  refine lucas_primality 104471 ((11 : ℕ) : ZMod 104471) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 104471 - 1 = ([2, 5, 31, 337] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨prime_5, List.forall_mem_cons.mpr ⟨prime_31, List.forall_mem_cons.mpr ⟨prime_337, List.forall_mem_nil _⟩⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_126241 : Nat.Prime 126241 := by
  refine lucas_primality 126241 ((7 : ℕ) : ZMod 126241) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 126241 - 1 = ([2, 2, 2, 2, 2, 3, 5, 263] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_three, List.forall_mem_cons.mpr ⟨prime_5, List.forall_mem_cons.mpr ⟨prime_263, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_155317 : Nat.Prime 155317 := by
  refine lucas_primality 155317 ((5 : ℕ) : ZMod 155317) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 155317 - 1 = ([2, 2, 3, 7, 43, 43] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_three, List.forall_mem_cons.mpr ⟨prime_7, List.forall_mem_cons.mpr ⟨prime_43, List.forall_mem_cons.mpr ⟨prime_43, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_3969899 : Nat.Prime 3969899 := by
  refine lucas_primality 3969899 ((2 : ℕ) : ZMod 3969899) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 3969899 - 1 = ([2, 19, 104471] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨prime_19, List.forall_mem_cons.mpr ⟨prime_104471, List.forall_mem_nil _⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_9350987 : Nat.Prime 9350987 := by
  refine lucas_primality 9350987 ((2 : ℕ) : ZMod 9350987) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 9350987 - 1 = ([2, 17, 229, 1201] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨prime_17, List.forall_mem_cons.mpr ⟨prime_229, List.forall_mem_cons.mpr ⟨prime_1201, List.forall_mem_nil _⟩⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_187019741 : Nat.Prime 187019741 := by
  refine lucas_primality 187019741 ((2 : ℕ) : ZMod 187019741) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 187019741 - 1 = ([2, 2, 5, 9350987] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨prime_5, List.forall_mem_cons.mpr ⟨prime_9350987, List.forall_mem_nil _⟩⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_191039911 : Nat.Prime 191039911 := by
  refine lucas_primality 191039911 ((3 : ℕ) : ZMod 191039911) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 191039911 - 1 = ([2, 3, 5, 41, 155317] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_three, List.forall_mem_cons.mpr ⟨prime_5, List.forall_mem_cons.mpr ⟨prime_41, List.forall_mem_cons.mpr ⟨prime_155317, List.forall_mem_nil _⟩⟩⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_311245691 : Nat.Prime 311245691 := by
  refine lucas_primality 311245691 ((2 : ℕ) : ZMod 311245691) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 311245691 - 1 = ([2, 5, 7, 17, 29, 29, 311] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨prime_5, List.forall_mem_cons.mpr ⟨prime_7, List.forall_mem_cons.mpr ⟨prime_17, List.forall_mem_cons.mpr ⟨prime_29, List.forall_mem_cons.mpr ⟨prime_29, List.forall_mem_cons.mpr ⟨prime_311, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_622491383 : Nat.Prime 622491383 := by
  refine lucas_primality 622491383 ((5 : ℕ) : ZMod 622491383) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 622491383 - 1 = ([2, 311245691] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨prime_311245691, List.forall_mem_nil _⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_1002328039319 : Nat.Prime 1002328039319 := by
  refine lucas_primality 1002328039319 ((19 : ℕ) : ZMod 1002328039319) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 1002328039319 - 1 = ([2, 126241, 3969899] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨prime_126241, List.forall_mem_cons.mpr ⟨prime_3969899, List.forall_mem_nil _⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_208150935158385979 : Nat.Prime 208150935158385979 := by
  refine lucas_primality 208150935158385979 ((2 : ℕ) : ZMod 208150935158385979) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 208150935158385979 - 1 = ([2, 3, 11, 43, 127, 3023, 191039911] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_three, List.forall_mem_cons.mpr ⟨prime_11, List.forall_mem_cons.mpr ⟨prime_43, List.forall_mem_cons.mpr ⟨prime_127, List.forall_mem_cons.mpr ⟨prime_3023, List.forall_mem_cons.mpr ⟨prime_191039911, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_2624747550333869278416773953 : Nat.Prime 2624747550333869278416773953 := by
  refine lucas_primality 2624747550333869278416773953 ((7 : ℕ) : ZMod 2624747550333869278416773953) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 2624747550333869278416773953 - 1 = ([2, 2, 2, 2, 2, 2, 3, 3, 1297, 16879, 208150935158385979] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_three, List.forall_mem_cons.mpr ⟨Nat.prime_three, List.forall_mem_cons.mpr ⟨prime_1297, List.forall_mem_cons.mpr ⟨prime_16879, List.forall_mem_cons.mpr ⟨prime_208150935158385979, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

theorem prime_115792089210356248762697446949407573529996955224135760342422259061068512044369 : Nat.Prime 115792089210356248762697446949407573529996955224135760342422259061068512044369 := by
  refine lucas_primality 115792089210356248762697446949407573529996955224135760342422259061068512044369 ((7 : ℕ) : ZMod 115792089210356248762697446949407573529996955224135760342422259061068512044369) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 115792089210356248762697446949407573529996955224135760342422259061068512044369 - 1 = ([2, 2, 2, 2, 3, 71, 131, 373, 3407, 17449, 38189, 187019741, 622491383, 1002328039319, 2624747550333869278416773953] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod (List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_two, List.forall_mem_cons.mpr ⟨Nat.prime_three, List.forall_mem_cons.mpr ⟨prime_71, List.forall_mem_cons.mpr ⟨prime_131, List.forall_mem_cons.mpr ⟨prime_373, List.forall_mem_cons.mpr ⟨prime_3407, List.forall_mem_cons.mpr ⟨prime_17449, List.forall_mem_cons.mpr ⟨prime_38189, List.forall_mem_cons.mpr ⟨prime_187019741, List.forall_mem_cons.mpr ⟨prime_622491383, List.forall_mem_cons.mpr ⟨prime_1002328039319, List.forall_mem_cons.mpr ⟨prime_2624747550333869278416773953, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

end ECDSA

end
