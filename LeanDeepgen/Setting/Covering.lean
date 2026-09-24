import Mathlib
import Architect
import FoML.ToMathlib.CoveringNumber

/-!
# Covering numbers and metric entropy

Thin wrapper around Mathlib's `Metric.coveringNumber` (radius `ε : ℝ≥0`, covers by closed balls,
values in `ℕ∞`): the metric entropy `log N(A, ε)`. The packing/covering duality
(`packing_covering`, `covering_two_mul_le_external`), the attainment of the external covering
number (`exists_isCover_encard_eq_externalCoveringNumber`) and subadditivity under unions
(`externalCoveringNumber_union_le`) are Mathlib-generic and live in
`FoML.ToMathlib.CoveringNumber` (re-exported here through the import).
-/

open scoped NNReal ENNReal
open Metric

open FoML.ToMathlib

namespace LeanDeepgen

variable {X : Type*} [PseudoEMetricSpace X]

@[blueprint "def:metric-entropy"
  (statement := /-- The metric entropy of $A$ at scale $\varepsilon$ is $\log N(A, \varepsilon)$,
    where $N(A,\varepsilon)$ is the (internal) covering number of $A$ by closed
    $\varepsilon$-balls (with the convention $\log \infty = \log 0 = 0$ in Lean). -/)]
noncomputable def metricEntropy (ε : ℝ≥0) (A : Set X) : ℝ :=
  Real.log (coveringNumber ε A : ℝ≥0∞).toReal

end LeanDeepgen
