/-
# `CompleteWitness` for the honest environment (task G2-c)

`Witness/CompleteWitnessOfULWC.lean` proves all 30 fields of `CompleteWitness`
from the environment's local witnesses, the input embedding, standard validity
and a good offset for the concrete family `famOf` — but it takes the six ladder
fields as a hypothesis (`LadderWitness`) so that the large ladder statement gets
its own elaboration budget.  `Witness/LadderWitness.lean` discharges that
hypothesis from `jointLadder_denominators_of_ulwc`.

This module puts the two together: `CompleteWitness_of_ulwc` has no
`LadderWitness` hypothesis.

No new axioms, no `native_decide`, no `sorry`.
-/
import StandardECDSA.Witness.LadderWitness

namespace StandardECDSA

open Circuit
open StandardECDSA.Gadgets
open StandardECDSA.Phases
open StandardECDSA.Math
open StandardECDSA.Witness
open StandardECDSA.Math.FixedTables
open WeierstrassCurve

set_option linter.constructorNameAsVariable false in
/-- **`CompleteWitness` for the honest environment.**  All 30 fields follow from
the environment's local witnesses, the input embedding, standard validity and a
good offset for the concrete family `famOf`. -/
theorem CompleteWitness_of_ulwc (inp : Var Input Fp) (env : ProverEnvironment Fp) (n : Nat)
    (pkX pkY digestLo digestHi r s : K) (fam : BadFamily Grp) (hm : fam.m < 1294)
    (hhint : env.hint = seedHint (generateSeed pkX pkY digestLo digestHi r s fam hm))
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n))
    (hIn : InputEmbedding inp env pkX pkY digestLo digestHi r s)
    (hstd : standardVerify pkX pkY digestLo digestHi r s)
    (hlo : digestLo.val < 2 ^ 128) (hhi : digestHi.val < 2 ^ 128)
    (H : AffinePoint K) (hH : H.IsOnCurve params)
    (hHX : H.X = Expression.eval env.toEnvironment (seedPhase inp n).1.hx)
    (hHY : H.Y = Expression.eval env.toEnvironment (seedPhase inp n).1.hy)
    (hQnsE : NS (Expression.eval env.toEnvironment inp.pkX)
      (Expression.eval env.toEnvironment inp.pkY))
    (hRnsE : NS (Expression.eval env.toEnvironment (shR inp n).1)
      (Expression.eval env.toEnvironment (shR inp n).2))
    (hgood : GoodOffset H hH (famOf env.toEnvironment (fbEb inp n) (fbRb inp n) (fbSb inp n)
      (Affine.Point.some (Expression.eval env.toEnvironment inp.pkX)
        (Expression.eval env.toEnvironment inp.pkY) hQnsE)
      (Affine.Point.some (Expression.eval env.toEnvironment (shR inp n).1)
        (Expression.eval env.toEnvironment (shR inp n).2) hRnsE))) :
    CompleteWitness inp env n :=
  CompleteWitness_of_ulwc_core inp env n pkX pkY digestLo digestHi r s fam hm hhint hw hIn
    hstd hlo hhi H hH hHX hHY hQnsE hRnsE hgood
    (main_ladder_denominators inp env n pkX pkY digestLo digestHi r s fam hm hhint hw hIn
      hstd hlo hhi H hH hHX hHY hQnsE hRnsE hgood)

end StandardECDSA
