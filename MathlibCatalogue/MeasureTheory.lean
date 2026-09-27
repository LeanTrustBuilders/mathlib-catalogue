import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import TrustAnnotations

/-!
# Measure theory: the Bochner integral and conditional expectation

Two of the definitions most of Mathlib's probability theory rests on, and the two where a junk value
matters most: an integral of a non-integrable function is `0`, and so is a conditional expectation
whenever it is not defined.

* **Domains**, declared on Mathlib's definitions: where each is meant to apply.
* **Characterizations** stated by one theorem each, with no predicate: the integral of a real
  function by the textbook formula, and conditional expectation by Mathlib's uniqueness theorem.

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

end MathlibCatalogue
