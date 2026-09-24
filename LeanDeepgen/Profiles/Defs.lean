import Mathlib
import Architect
import LeanDeepgen.Setting.Covering

/-!
# The entropy integral (definition)

The Dudley-type entropy integral `entropyIntegral D A = ∫_0^D √(log N(A, ε)) dε` of a set `A`
in a pseudo-emetric space up to scale `D`, where `log N(A, ε) = metricEntropy ε A`
(`LeanDeepgen.Setting.Covering`).  In the paper,
`V_k(S) = ∫_0^{D_k(S)} √(log N(B(k,F), d_S, ε)) dε` is
`entropyIntegral (empDiam S (wordBall F k)) (wordBall F k)` on the empirical space of the
sample `S`.

This module only contains the definition (it is imported by the assumption module
`LeanDeepgen.Setting.Assumptions` for the variance term `var(k,n)`); its properties and the
four variance profiles are in `LeanDeepgen.Profiles.Profiles`.
-/

open scoped NNReal ENNReal Real
open MeasureTheory intervalIntegral Metric

namespace LeanDeepgen

variable {Y : Type*} [PseudoEMetricSpace Y]

@[blueprint "def:entropy-integral"
  (statement := /-- The entropy integral of $A$ up to scale $D$ is
    $\mathsf V(D, A) = \int_0^{D} \sqrt{\log N(A, \varepsilon)}\,d\varepsilon$.
    In the paper, $\mathsf V_k(S) = \int_0^{D_k(S)} \sqrt{\log N(B(k,F), d_S, \varepsilon)}\,
    d\varepsilon$ with $D_k(S) = \operatorname{diam}_S B(k,F)$ is
    $\mathsf V(\operatorname{diam}_S B(k,F), B(k,F))$ for the empirical pseudometric $d_S$. -/)]
noncomputable def entropyIntegral (D : ℝ) (A : Set Y) : ℝ :=
  ∫ ε in (0 : ℝ)..D, √(metricEntropy (Real.toNNReal ε) A)

end LeanDeepgen
