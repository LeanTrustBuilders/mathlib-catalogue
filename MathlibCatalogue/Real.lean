import Mathlib.Algebra.Order.CompleteField
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import TrustAnnotations

/-!
# The real numbers

Mathlib constructs `ℝ` from Cauchy sequences of rationals. What it is meant to be is the
conditionally complete linearly ordered field, which any two of are isomorphic, by a unique
isomorphism (`ConditionallyCompleteLinearOrderedField.inducedOrderRingIso`, `uniqueOrderRingHom`).
The characterization below states that, so that a reader can take `ℝ` through its axioms instead of
its construction.

The isomorphism is also said to preserve `0`, `1`, `-`, `⁻¹`, `<`, `max`, `min` and the casts, which
it does as any isomorphism of ordered fields would: Mathlib defines each of them on `ℝ` by its own
instance, on the Cauchy sequences, and an instance the statement does not name is not pinned down
by it. A reader taking `ℝ` from this characterization leaves out the construction of each one named.
-/

namespace MathlibCatalogue

/-- **`ℝ` is the conditionally complete linearly ordered field**: any conditionally complete
linearly ordered field is isomorphic to it as an ordered ring, by an isomorphism that preserves the
operations Mathlib defines on `ℝ` separately. -/
@[characterization Real "the conditionally complete linearly ordered field, unique up to a unique \
isomorphism of ordered fields"]
theorem real_orderRingIso (K : Type*) [Field K] [ConditionallyCompleteLinearOrder K]
    [IsStrictOrderedRing K] :
    ∃ e : K ≃+*o ℝ, e 0 = 0 ∧ e 1 = 1 ∧ (∀ x, e (-x) = -e x) ∧ (∀ x, e x⁻¹ = (e x)⁻¹) ∧
      (∀ x y, x < y ↔ e x < e y) ∧ (∀ x y, e (max x y) = max (e x) (e y)) ∧
      (∀ x y, e (min x y) = min (e x) (e y)) ∧ (∀ n : ℕ, e n = n) ∧ (∀ z : ℤ, e z = z) ∧
      (∀ q : ℚ, e q = q) ∧ (∀ q : ℚ≥0, e q = q) := by
  let e := ConditionallyCompleteLinearOrderedField.inducedOrderRingIso K ℝ
  exact ⟨e, map_zero e, map_one e, map_neg e, map_inv₀ e, fun _ _ => e.toOrderIso.lt_iff_lt.symm,
    fun _ _ => e.toOrderIso.monotone.map_max, fun _ _ => e.toOrderIso.monotone.map_min,
    map_natCast e, map_intCast e, map_ratCast e, map_nnratCast e⟩

end MathlibCatalogue
