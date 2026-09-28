import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import TrustAnnotations

/-!
# The logarithm, and the moments of a random variable

Where `Real.log` is meant to apply, and the moments and generating functions of a random variable
defined from it and from the integral. Mathlib defines each everywhere, with a default value outside
the textbook's domain:
* `Real.log 0 = 0`, and `Real.log x = Real.log |x|` for `x < 0`;
* `moment`, `centralMoment` and `mgf` are integrals, so `0` for a random variable with no such
  moment;
* `cgf` is the logarithm of `mgf`, so `0` wherever `mgf` is `0`.

With their domains declared, the well-definedness analyzer checks their bodies, each use of the
integral and of the logarithm under the definition's own domain, and each use of them in a
statement.
-/

open MeasureTheory ProbabilityTheory

attribute [domain (0 < x) "log 0 = 0 and log x = log |x| for x < 0, by convention (`Real.log_zero`, \
`Real.log_abs`)"] Real.log

attribute [domain (Integrable (X ^ p) μ) "0 when X ^ p is not integrable"]
  ProbabilityTheory.moment

attribute [domain (Integrable X μ ∧ Integrable ((X - fun _ => ∫ x, X x ∂μ) ^ p) μ) "0 when X, or \
its p-th power centred, is not integrable"] ProbabilityTheory.centralMoment

attribute [domain (Integrable (fun ω => Real.exp (t * X ω)) μ) "0 where exp (t X) is not \
integrable"] ProbabilityTheory.mgf

attribute [domain (Integrable (fun ω => Real.exp (t * X ω)) μ ∧ μ ≠ 0) "0 where the moment \
generating function is 0: where exp (t X) is not integrable, or for the zero measure \
(`log 0 = 0`)"] ProbabilityTheory.cgf
