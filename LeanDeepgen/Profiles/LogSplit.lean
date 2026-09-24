import Mathlib
import Architect
import FoML.ToMathlib.SqrtLogIntegral

/-!
# The log-splitting lemma

Elementary estimates behind the variance profiles (paper Lemma `lem:log-split`):
for `0 < D̄`, `k ≥ 0` and `0 < ε ≤ D̄`,
`log (1 + k/ε) ≤ log (1 + k/D̄) + log (D̄/ε)`, and
`∫_0^{D̄} √(log (D̄/ε)) dε = D̄ Γ(3/2) = (√π/2) D̄`.

The logarithmic inequality is proved here; the integral (`integral_sqrt_log_div`,
`integral_Ioo_sqrt_log_div`, `intervalIntegrable_sqrt_log_div`, `Gamma_three_halves`) and the
subadditivity of the square root (`sqrt_add_le`, `sqrt_add_add_le`) are Mathlib-generic and live
in `FoML.ToMathlib.SqrtLogIntegral` (re-exported here through the import).
-/

open FoML.ToMathlib

namespace LeanDeepgen

/-! ### The logarithmic inequality -/

@[blueprint "lem:log-split-ineq"
  (statement := /-- For $\overline D > 0$, $k \ge 0$ and $0 < \varepsilon \le \overline D$,
    $\log\bigl(1 + \tfrac{k}{\varepsilon}\bigr)
      \le \log\bigl(1 + \tfrac{k}{\overline D}\bigr) + \log\tfrac{\overline D}{\varepsilon}$. -/)]
theorem log_one_add_div_le {D k ε : ℝ} (hD : 0 < D) (hk : 0 ≤ k) (hε : 0 < ε)
    (hεD : ε ≤ D) :
    Real.log (1 + k / ε) ≤ Real.log (1 + k / D) + Real.log (D / ε) := by
  /-- $(1 + k/\overline D)(\overline D/\varepsilon) = \overline D/\varepsilon + k/\varepsilon
    \ge 1 + k/\varepsilon$ since $\overline D/\varepsilon \ge 1$; take logarithms. -/
  have h1 : 1 ≤ D / ε := (one_le_div hε).2 hεD
  have h2 : 1 + k / ε ≤ (1 + k / D) * (D / ε) := by
    have : (1 + k / D) * (D / ε) = D / ε + k / ε := by field_simp
    rw [this]; linarith
  calc Real.log (1 + k / ε) ≤ Real.log ((1 + k / D) * (D / ε)) :=
        Real.log_le_log (by positivity) h2
    _ = Real.log (1 + k / D) + Real.log (D / ε) := Real.log_mul (by positivity) (by positivity)

end LeanDeepgen
