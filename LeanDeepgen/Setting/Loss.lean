import Mathlib
import Architect

/-!
# Loss, risk and empirical risk

A bounded Lipschitz loss `ℓ : ℝ × Y → [0, b]`, `β`-Lipschitz in its first argument, the
population risk `L[f] = 𝔼 ℓ(f(X), Y)`, the empirical risk `L̂[f] = n⁻¹ ∑ ℓ(f(xᵢ), yᵢ)`,
`η`-empirical minimizers and the model error `ε_model = inf_{ℋ} L − inf_{𝒞} L`.
-/

open MeasureTheory

namespace LeanDeepgen

@[blueprint "def:loss"
  (statement := /-- A loss is a function $\ell : \mathbb R \times \mathcal Y \to [0, b]$ which is
    $\beta_\ell$-Lipschitz in its first argument:
    $|\ell(a, y) - \ell(a', y)| \le \beta_\ell |a - a'|$. -/)]
structure BoundedLipschitzLoss (Y : Type*) where
  /-- The loss function. -/
  ℓ : ℝ → Y → ℝ
  /-- The upper bound $b$ of the loss. -/
  b : ℝ
  /-- The Lipschitz constant $\beta_\ell$ in the first argument. -/
  β : ℝ
  nonneg : ∀ a y, 0 ≤ ℓ a y
  le_b : ∀ a y, ℓ a y ≤ b
  lip : ∀ a a' y, |ℓ a y - ℓ a' y| ≤ β * |a - a'|

variable {X Y : Type*}

@[blueprint "def:emp-risk"
  (statement := /-- The empirical risk on a sample $D = ((x_1,y_1),\dots,(x_n,y_n))$ is
    $\hat L[f] = \frac1n \sum_{i=1}^n \ell(f(x_i), y_i)$. -/)]
noncomputable def empRisk (L : BoundedLipschitzLoss Y) {n : ℕ} (D : Fin n → X × Y)
    (f : X → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, L.ℓ (f (D i).1) (D i).2

@[blueprint "def:risk"
  (statement := /-- The (population) risk under a distribution $P$ on
    $\mathcal X \times \mathcal Y$ is $L[f] = \mathbb E_{(X,Y) \sim P}\, \ell(f(X), Y)$. -/)]
noncomputable def risk [MeasurableSpace X] [MeasurableSpace Y] (L : BoundedLipschitzLoss Y)
    (P : Measure (X × Y)) (f : X → ℝ) : ℝ :=
  ∫ z, L.ℓ (f z.1) z.2 ∂P

@[blueprint "def:emp-minimizer"
  (statement := /-- $f$ is an $\eta$-empirical minimizer over $\mathcal H$ if $f \in \mathcal H$ and
    $\hat L[f] \le \inf_{g \in \mathcal H} \hat L[g] + \eta$. -/)]
def IsEmpMinimizer (L : BoundedLipschitzLoss Y) {n : ℕ} (D : Fin n → X × Y) (𝓗 : Set (X → ℝ))
    (η : ℝ) (f : X → ℝ) : Prop :=
  f ∈ 𝓗 ∧ ∀ g ∈ 𝓗, empRisk L D f ≤ empRisk L D g + η

@[blueprint "def:err-model"
  (statement := /-- The model error (approximation term) of $\mathcal H$ relative to a target class
    $\mathcal C$ is $\varepsilon_{\mathrm{model}}
    = \inf_{f \in \mathcal H} L[f] - \inf_{c \in \mathcal C} L[c]$. -/)]
noncomputable def modelError [MeasurableSpace X] [MeasurableSpace Y] (L : BoundedLipschitzLoss Y)
    (P : Measure (X × Y)) (𝓗 𝒞 : Set (X → ℝ)) : ℝ :=
  sInf (risk L P '' 𝓗) - sInf (risk L P '' 𝒞)

end LeanDeepgen
