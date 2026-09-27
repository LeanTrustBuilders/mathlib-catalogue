import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import TrustAnnotations

/-!
# Measure theory: the Bochner integral, conditional expectation, the Radon–Nikodym derivative

Three of the definitions most of Mathlib's probability theory rests on, and where junk values and
choices of representative matter most: an integral of a non-integrable function is `0`, and so is a
conditional expectation or a Radon–Nikodym derivative whenever it is not defined; and where they are
defined, the last two are one function among those equal to it almost everywhere.

* **Domains**, declared on Mathlib's definitions: where each is meant to apply.
* **What they are determined up to** (`@[up_to]`): almost-everywhere equality.
* **Characterizations** stated by one theorem each, with no predicate: the integral of a real
  function by the textbook formula, conditional expectation and the Radon–Nikodym derivative by
  Mathlib's uniqueness theorems.

Mathlib's own theorems cannot carry an annotation from outside Mathlib, so the characterizations,
and the specification lemmas that show conditional expectation has its property, are restatements
here, each proved by the Mathlib lemma it restates.
-/

open MeasureTheory
open scoped ENNReal

/-! ## Domains -/

attribute [domain (Integrable f μ) "a Bochner integral of a non-integrable function is 0 \
(`integral_undef`)"] MeasureTheory.integral

attribute [domain (∃ hm : m ≤ m₀, SigmaFinite (μ.trim hm) ∧ Integrable f μ) "the zero function \
when m is not a sub-σ-algebra of m₀, when μ is not σ-finite on it, or when f is not integrable \
(`condExp_of_not_le`, `condExp_of_not_sigmaFinite`, `condExp_of_not_integrable`)"]
  MeasureTheory.condExp

attribute [domain (μ.HaveLebesgueDecomposition ν) "the zero function when μ has no Lebesgue \
decomposition with respect to ν (`rnDeriv_of_not_haveLebesgueDecomposition`)"]
  MeasureTheory.Measure.rnDeriv

/-! ## What they are determined up to -/

attribute [up_to (· =ᵐ[μ] ·) "one version of the conditional expectation among the functions equal \
to it μ-almost everywhere; its value at a point means nothing"] MeasureTheory.condExp

attribute [up_to (· =ᵐ[ν] ·) "one density among the functions equal to it ν-almost everywhere; its \
value at a point means nothing"] MeasureTheory.Measure.rnDeriv

namespace MathlibCatalogue

/-! ## The Bochner integral of a real function: the textbook definition -/

/-- **The integral of an integrable real function is the Lebesgue integral of its positive part minus
that of its negative part.** This moves trust from Bochner's construction, through simple functions
and the completion of `L¹`, to the Lebesgue integral of nonnegative functions. -/
@[characterization MeasureTheory.integral "the textbook definition: the integral of the positive \
part minus that of the negative part"]
theorem eq_integral_iff {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {f : α → ℝ}
    (hf : Integrable f μ) (x : ℝ) :
    x = ∫ a, f a ∂μ ↔
      x = (∫⁻ a, ENNReal.ofReal (f a) ∂μ).toReal - (∫⁻ a, ENNReal.ofReal (-f a) ∂μ).toReal := by
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]

/-! ## Conditional expectation: its defining property -/

section
variable {α E : Type*} {m m₀ : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E] {f : α → E}

omit [CompleteSpace E] in
/-- Mathlib's `stronglyMeasurable_condExp`: it uses only the information in `m`. -/
@[specifies MeasureTheory.condExp "it uses only the information in m: it is m-measurable"]
theorem aestronglyMeasurable_condExp : AEStronglyMeasurable[m] (μ[f | m]) μ :=
  stronglyMeasurable_condExp.aestronglyMeasurable

/-- Mathlib's `integrable_condExp`: it is integrable, on every set. -/
@[specifies MeasureTheory.condExp "it is integrable, on every set"]
theorem integrableOn_condExp {s : Set α} : IntegrableOn (μ[f | m]) s μ :=
  integrable_condExp.integrableOn

/-- Mathlib's `setIntegral_condExp`: it has the integrals of `f` over every `m`-measurable set. -/
@[specifies MeasureTheory.condExp "it has the integrals of f over every m-measurable set"]
theorem setIntegral_condExp (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)] (hf : Integrable f μ)
    {s : Set α} (hs : MeasurableSet[m] s) : ∫ x in s, (μ[f | m]) x ∂μ = ∫ x in s, f x ∂μ :=
  MeasureTheory.setIntegral_condExp hm hf hs

/-- **Conditional expectation is the unique `m`-measurable function with the integrals of `f` over
`m`-measurable sets**, up to a.e. equality: Mathlib's `ae_eq_condExp_of_forall_setIntegral_eq`. -/
@[characterization "the defining property: m-measurable, integrable on the m-measurable sets of \
finite measure, with the integrals of f over them"]
theorem ae_eq_condExp (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)] {g : α → E} (hf : Integrable f μ)
    (hg_int_finite : ∀ s, MeasurableSet[m] s → μ s < ∞ → IntegrableOn g s μ)
    (hg_eq : ∀ s : Set α, MeasurableSet[m] s → μ s < ∞ → ∫ x in s, g x ∂μ = ∫ x in s, f x ∂μ)
    (hgm : AEStronglyMeasurable[m] g μ) : g =ᵐ[μ] μ[f | m] :=
  ae_eq_condExp_of_forall_setIntegral_eq hm hf hg_int_finite hg_eq hgm

end

/-! ## The Radon–Nikodym derivative: the density of the absolutely continuous part -/

section
variable {α : Type*} {m : MeasurableSpace α} {μ ν : Measure α}

/-- Mathlib's `measurable_rnDeriv`. -/
@[specifies MeasureTheory.Measure.rnDeriv "it is measurable"]
theorem measurable_rnDeriv : Measurable (μ.rnDeriv ν) :=
  Measure.measurable_rnDeriv μ ν

/-- **The Lebesgue decomposition**: `μ` is a measure singular with respect to `ν`, plus `ν` with
density `rnDeriv μ ν`. Mathlib's `mutuallySingular_singularPart` and `haveLebesgueDecomposition_add`,
together. -/
@[specifies MeasureTheory.Measure.rnDeriv "the Lebesgue decomposition: μ is a part singular with \
respect to ν plus ν with this density"]
theorem exists_singular_add_withDensity_rnDeriv [μ.HaveLebesgueDecomposition ν] :
    ∃ s : Measure α, s ⟂ₘ ν ∧ μ = s + ν.withDensity (μ.rnDeriv ν) :=
  ⟨μ.singularPart ν, Measure.mutuallySingular_singularPart μ ν, Measure.haveLebesgueDecomposition_add μ ν⟩

/-- **The Radon–Nikodym derivative is the unique measurable density of the absolutely continuous part
of `μ` with respect to `ν`**, up to `ν`-almost everywhere equality: Mathlib's `eq_rnDeriv`, with the
singular part stated as existing. That `rnDeriv μ ν` itself has the property needs the Lebesgue
decomposition, which the characterization records as where it holds. -/
@[characterization "the density of the part of μ absolutely continuous with respect to ν, the rest \
being singular"]
theorem ae_eq_rnDeriv [SigmaFinite ν] {f : α → ℝ≥0∞} (hf : Measurable f)
    (h : ∃ s : Measure α, s ⟂ₘ ν ∧ μ = s + ν.withDensity f) : f =ᵐ[ν] μ.rnDeriv ν := by
  obtain ⟨s, hs, hadd⟩ := h
  exact Measure.eq_rnDeriv hf hs hadd

end

end MathlibCatalogue
