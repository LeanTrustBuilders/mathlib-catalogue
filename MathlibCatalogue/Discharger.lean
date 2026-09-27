import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# How the catalogue's domains are shown to hold

The well-definedness analyzer ([LeanTrustBuilders/well-defined](https://github.com/LeanTrustBuilders/well-defined))
checks each use of a definition with a declared domain against what is in scope where it sits. Its
default dischargers (`fun_prop`, `positivity`, `infer_instance`, …) know nothing of the facts that
make a function integrable in probability theory: a random variable in L², a martingale's values, a
set integral of an integrable function, a stopped process with bounded stopping times.

`mathlib_catalogue_discharger` is those facts, for the domains this catalogue declares: CI names it
as a discharger (`trust-extract welldefined --discharger mathlib_catalogue_discharger`). It is a
`solve_by_elim` over them, so what it proves is proved, and what it misses stays open rather than
being guessed.
-/

open MeasureTheory

/-- The facts behind the catalogue's domains in probability theory, as a discharger for the
well-definedness analyzer. -/
macro "mathlib_catalogue_discharger" : tactic => `(tactic| solve_by_elim (maxDepth := 6)
  [MeasureTheory.Integrable.restrict, MeasureTheory.Integrable.integrableOn,
   MeasureTheory.MemLp.integrable, MeasureTheory.MemLp.integrable_sq,
   MeasureTheory.Submartingale.integrable, MeasureTheory.Supermartingale.integrable,
   MeasureTheory.Martingale.integrable, MeasureTheory.integrable_condExp,
   MeasureTheory.integrable_stoppedValue, MeasureTheory.Filtration.le,
   le_trans, one_le_two, le_refl])

section Checks

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}

example [IsFiniteMeasure μ] {X : Ω → ℝ} (h : MemLp X 2 μ) : Integrable X μ := by
  mathlib_catalogue_discharger

example {s : Set Ω} {ℱ : Filtration ℕ m₀} {f : ℕ → Ω → ℝ} (hf : Submartingale f ℱ μ) (j : ℕ) :
    Integrable (f j) (μ.restrict s) := by mathlib_catalogue_discharger

example {ℱ : Filtration ℕ m₀} (n : ℕ) : ℱ n ≤ m₀ := by mathlib_catalogue_discharger

end Checks
