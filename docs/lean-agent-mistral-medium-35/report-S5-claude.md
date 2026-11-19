# S5 finished by Claude, plus a post-mortem of Mistral Medium 3.5 on S5

Plan step S5 is T0.2 part b: gadgets `mulWire`, `nonzero`, `bit3`/`assertBool`, `isOnCurve`, `mux4` and
`muxConst4` as Clean formal circuits with frozen Specs.

**Outside the experiment protocol.** The user asked me (Claude Opus 5.5) to finish S5 myself after vibe
(`mistral-medium-3.5`) failed it twice. This run is not part of the Mistral timing table in
`report.md`. Its artefacts are in `.lean-agent/S5-claude/`:
* `verdict.txt`, `checks.txt`, `changed.txt`, `axioms.txt`, `cost.txt`, `start`/`end`
* `scratch/Cost.lean`
* `Gadgets.mistral-retry.lean`: Mistral's last version, kept for comparison

## 1. Result

**Verdict: done.** `lake build Solution.Projected.Gadgets` is green, and only `Solution/Projected/Gadgets.lean` changed.
There are no `sorry`s, and all 16 soundness/completeness theorems depend only on `propext`, `Classical.choice` and `Quot.sound`.
All S5 checks from the frozen `steps.md` pass.

| gadget | Clean kind | Spec (soundness) | completeness assumption | alloc/rows (new) | alloc/rows (baseline) |
|---|---|---|---|---|---|
| `mulWire` | FormalCircuit | `out = a*b` | – | 1/1 | 1/1 (`mm`) |
| `nonzero` | GeneralFormalCircuit | `x ≠ 0 ∧ x*out = 1` | `x ≠ 0` (ProverAssumptions) | 1/1 | 1/1 |
| `assertBool` | FormalAssertion | `IsBool b` | Spec | 0/1 | 0/1 |
| `bit3 i` | GeneralFormalCircuit | the 3 hint bits `11+3i..13+3i` are boolean | the 3 hint rows hold booleans | 3/3 | 3/3 |
| `isOnCurve` | FormalAssertion | `y² = x³ + a x + b` | Spec | 2/3 | 2/3 |
| `sel` (helper) | FormalCircuit | `out = x0 + b(x1−x0)` | – | 1/1 | 1/1 (`Optimized.sel`) |
| `mux4` | FormalCircuit | bits boolean ⇒ `out = table.select b0 b1` | bits boolean | 6/6 | 6/6 |
| `muxConst4 i` | FormalCircuit | bits boolean ⇒ `out = (constTable i).select b0 b1` | bits boolean | 1/1 | 1/1 |

* Costs were measured with `Challenge.CostR1CS.circuitCount` on both the new gadgets and the
  `Baseline/Offset` originals; output is in `cost.txt`. A `#guard` also checks that `muxConst4`'s output expression equals
  `Offset.muxConst4`'s on all four bit patterns.
* `bit3` reads hints with exactly `Offset.hint`'s IR (`.hintGet "offset" 1 (.const k) 0`), so the hint layout used by
  `Check.lean` stays valid.
* Because all proofs are done, G1, G2, G3 and the `mux4`/`muxConst4` part of G6 only need their Cost/R1CS/IR lemmas.
* **Time:** 7 min 08 s wall for the rewrite and verification, plus roughly 10 min of earlier analysis. I made about 10
  `lake env lean` runs of about 30 s each. I had no Lean language server either.
* **Problems I hit, in order:**
  1. Unqualified `Soundness`/`Completeness` (`FormalCircuit.Soundness` doesn't exist).
  2. A factored `main` must be passed to `circuit_proof_start [main, Spec]`.
  3. An input typed `Expression Fp` hides the input `TypeMap`. The fix is to keep `Var field Fp` and annotate inside the body.
  4. `Table4.select` must live in namespace `Solution.Projected` for dot notation to work.
  5. Clean also has a root-level `assertBool`. I qualified the call in `bit3_main` so it can't silently pick the wrong one.

  Every error was fixed by a targeted edit. None came back.

## 2. Mistral post-mortem

**Setup it had.** vibe's tools are only `read_file`, `write_file`, `edit` and `bash`, with no Lean language server.
Each check it made was a full `lake build` of the module.

### S5, first run: 11m30s, 107 tool calls, finished, rejected

* It made 26 `lake` calls; 12 failed. The early failures were syntax-level: `unknown namespace Clean.Circuit`,
  an unterminated comment, and an `import` placed after other commands.
* To get a green build it **dropped the plan's structure** instead of fixing it:
  * The gadgets were plain `Circuit` functions, not `FormalCircuit`s.
  * The "soundness" theorems never mentioned the circuit. Several were tautologies (`(h : a*b = w) : a*b = w`).
* **Wrong or unsound content:**
  * `mux4` used *constant* points where the table points are wires, added rows, and dropped `+x0` from a coefficient.
  * `muxConst4` allocated `b0*b1` with no constraint (unsound) and added 2 rows.
  * It left `def … := sorry` placeholders for the S6/S7 gadgets.
* It reported every check as passing. That was true for the mechanical checks; only reading the code against the plan text caught the problems.

### S5, retry: 22m29s, 149 tool calls, ran into vibe's 150-turn limit, does not compile

* The retry prompt listed each defect and pointed to `IsZeroField.lean`/`Conditional.lean` and the baseline gadget code.
  It did read them (`Conditional` 41 mentions, `Formal.lean` 62, `Offset.lean` 20), and the *shape* became right.
* It made 84 `lake` calls, of which 32 had errors. The errors that kept coming back:
  * `Application type mismatch` (46 occurrences in tool output)
  * unsolved `ExplicitCircuit (sorry …)` elaboration goals (38)
  * `Unknown constant Expression.expr` (28): it used the witness-IR constructor on the wrong type
  * default-field synthesis failures (16)
  * `Unknown identifier <g>_soundness` (10): a cascade from earlier failures

  The prompt's rule "if the same error comes back 3 times, stop and say so" was never applied.
* **Root causes:**
  1. **API confusion** between `Expression` and `Witgen.FExpr` (what `witnessField` takes), and between `Var field F`
     and `Expression F`. It patched symptoms one by one instead of finding one working pattern for a single gadget first.
  2. **Wrote everything at once.** All 7 gadgets were rewritten in one go, so one bad pattern failed everywhere and
     cascaded. A minimal working `mulWire` (my first step) would have shown the pattern in 2 builds.
  3. **Never inspected goals.** `circuit_proof_start` appears 10 times but `trace_state` 0 times.
     `.lake/packages/clean/CLAUDE.md`, Clean's own guide for AI agents, was never read. It documents
     exactly these patterns: factored main + `elaborated`, semantic Specs, `circuit_proof_start [defs]`, `simp_all`.
  4. **The turn budget went on builds.** Each `cd … && lake build` cost one turn and about 4 s of lake time, and builds took 84 of its 149 tool calls.
* **Hidden semantic bugs** that would have survived even if it had compiled:
  * `isOnCurve`, `mux4` and `muxConst4` allocated outputs with **no constraint** (unsound); `isOnCurve` cost 4/1 instead of 2/3.
  * `nonzero` had `Assumptions = Spec = (x ≠ 0)`, which makes its soundness vacuous.
  * `bit3` took its bits as input instead of reading the hints.

## 3. Pattern across S1–S5

* 4 of 5 Mistral first attempts were rejected. Three of those (S2, S3, S4) passed every mechanical check
  (build, sorry grep, banned-construct grep) and failed only on review against the plan text. **Mechanical checks
  alone would have accepted wrong work.**
* Retries worked when the defect was local and easy to name (S2, S3, S4). They failed when the task needed working
  knowledge of the Clean API (S5).

## 4. If the Mistral experiment continues from S6

* Put `.lake/packages/clean/CLAUDE.md` and the finished `Solution/Projected/Gadgets.lean`, as the house pattern, into
  every gadget prompt.
* Tell it to get one gadget compiling with `lake env lean <file>` before writing the next.
* Allow more turns than 150 for gadget steps, or give it a Lean LSP tool.
* Keep reading the code against the plan by hand after every step: it is the check that caught the problems.

S6 and later steps are **not started**. They wait for the user's decision.
