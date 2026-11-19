/-
# Axiom audit for the standard P-256 ECDSA submission

Every public proof root of the standard-ECDSA development is audited here.  The
fail-closed checker `scripts/check_standard_ecdsa_axioms.py` runs this file and
rejects any root that depends on an axiom outside

    { propext, Classical.choice, Quot.sound }.

The roots are grouped as in the plan's T20 acceptance list:

* **end-to-end** — the four exported theorems of `StandardECDSA/Main.lean` plus
  the exact cost certificate;
* **specification** — the standard-ECDSA specification and its equivalence with
  the signature-point predicate;
* **offset existence** — the 1,040-candidate / 1,039-slot counting argument;
* **witness generation** — the honest seed generator;
* **group order** — the P-256 group-order certificates;
* **fixed tables** — the 128×4 fixed-base table and the shift point;
* **phase semantics** — the three arithmetic phases' group-level specs;
* **phase cost** — the per-phase and per-stage allocation/row certificates.

Task T20.
-/

import StandardECDSA.Main
import StandardECDSA.Cost
import StandardECDSA.Math.SignatureEquation
import StandardECDSA.Math.OffsetCandidates
import StandardECDSA.Witness.Correctness
import StandardECDSA.Math.GroupOrder
import StandardECDSA.Math.FixedTables
import StandardECDSA.Phases.FixedBaseSemantics
import StandardECDSA.Phases.TableSemantics
import StandardECDSA.Phases.LadderSemantics
import StandardECDSA.Phases.Cost

/-! ## End-to-end -/

#print axioms StandardECDSA.main_soundness
#print axioms StandardECDSA.main_complete_with_seed
#print axioms StandardECDSA.main_completeness
#print axioms StandardECDSA.main_accepts_iff_standard
#print axioms StandardECDSA.main_cost

/-! ## Specification -/

#print axioms StandardECDSA.Math.standard_iff_signaturePoint
#print axioms StandardECDSA.Math.x_mod_order_iff_lift
#print axioms StandardECDSA.Math.signature_equation_iff

/-! ## Offset existence -/

#print axioms StandardECDSA.Math.offsetCandidate_injective
#print axioms StandardECDSA.Math.exists_goodOffset
#print axioms StandardECDSA.Math.findGoodOffset_spec

/-! ## Witness generation -/

#print axioms StandardECDSA.Witness.generateSeed_complete

/-! ## Group order -/

#print axioms StandardECDSA.Math.n_prime
#print axioms StandardECDSA.Math.addOrderOf_Gpt
#print axioms StandardECDSA.Math.card_eq_n
#print axioms StandardECDSA.Math.nsmul_eq_zero
#print axioms StandardECDSA.Math.nsmul_injective_of_lt

/-! ## Fixed tables -/

#print axioms StandardECDSA.Math.FixedTables.mulG_toMathlib
#print axioms StandardECDSA.Math.FixedTables.mulG_affine_some
#print axioms StandardECDSA.Math.FixedTables.fixedTables_get
#print axioms StandardECDSA.Math.FixedTables.fixedShift_eq

/-! ## Phase semantics -/

#print axioms StandardECDSA.Phases.fixedBase_spec
#print axioms StandardECDSA.Phases.shiftedTables_spec
#print axioms StandardECDSA.Phases.jointLadder_spec

/-! ## Phase and stage cost -/

#print axioms StandardECDSA.Phases.fixedBase_cost
#print axioms StandardECDSA.Phases.shiftedTables_cost
#print axioms StandardECDSA.Phases.jointLadder_cost
#print axioms StandardECDSA.curvePhase_cost
#print axioms StandardECDSA.bitsPhase_cost
#print axioms StandardECDSA.cmpPhase_cost
