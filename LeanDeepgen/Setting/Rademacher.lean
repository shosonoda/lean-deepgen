import Mathlib
import Architect
import FoML

/-!
# Rademacher complexity (via FoML)

We connect the paper's Rademacher complexities to the library `FoML` (lean-rademacher).
There, Rademacher signs are `σ : Signs n = Fin n → {-1, 1}`, the expectation over the uniform
distribution on `{±1}ⁿ` is the average over the `2^n` sign patterns, and a function class is
indexed: `F : ι → 𝒳 → ℝ`.

For a set `G : Set (X → ℝ)` we index by the subtype `G` itself. The paper's
`R̂_S(G) = 𝔼_σ sup_{g ∈ G} n⁻¹ ∑ᵢ σᵢ g(xᵢ)` (no absolute value) is FoML's
`empiricalRademacherComplexity_without_abs`; the population version `R_n(G)` is FoML's
`rademacherComplexity`, which is the expectation of the *absolute* version
`𝔼_σ sup_{g ∈ G} |n⁻¹ ∑ᵢ σᵢ g(xᵢ)|` (all high-probability bounds in FoML are stated for it; it
dominates the one-sided version, see `empRademacher_le_abs`).
-/

open MeasureTheory

namespace LeanDeepgen

variable {X : Type*}

@[blueprint "def:emp-rademacher"
  (statement := /-- The empirical Rademacher complexity of $G \subseteq \mathbb R^{\mathcal X}$
    on the sample $S = (x_1,\dots,x_n)$ is
    $\hat{\mathfrak R}_S(G) = \mathbb E_\sigma \sup_{g \in G} \frac1n \sum_{i=1}^n \sigma_i g(x_i)
    = 2^{-n} \sum_{\sigma \in \{\pm1\}^n} \sup_{g \in G} \frac1n \sum_{i=1}^n \sigma_i g(x_i)$
    (no absolute value). In Lean this is FoML's
    `empiricalRademacherComplexity\_without\_abs` for the class indexed by $G$ itself. -/)]
noncomputable def empRademacher {n : ℕ} (S : Fin n → X) (G : Set (X → ℝ)) : ℝ :=
  empiricalRademacherComplexity_without_abs n (fun g : G => (g : X → ℝ)) S

@[blueprint "def:rademacher"
  (statement := /-- The (population) Rademacher complexity is
    $\mathfrak R_n(G) = \mathbb E_{S \sim P^{\otimes n}} \hat{\mathfrak R}_S(G)$.
    In Lean we take FoML's `rademacherComplexity`, i.e. the expectation over $S \sim P^{\otimes n}$
    of the absolute version
    $\mathbb E_\sigma \sup_{g \in G} \bigl|\frac1n \sum_i \sigma_i g(x_i)\bigr|
    \ge \hat{\mathfrak R}_S(G)$; this is the quantity for which FoML's deviation bounds are
    stated, and it dominates the paper's $\mathfrak R_n(G)$. -/)]
noncomputable def rademacherComplexity [MeasurableSpace X] (P : Measure X) (n : ℕ)
    (G : Set (X → ℝ)) : ℝ :=
  _root_.rademacherComplexity n (fun g : G => (g : X → ℝ)) P id

variable {n : ℕ} {S : Fin n → X} {G G₁ G₂ : Set (X → ℝ)}

@[blueprint "lem:emp-rademacher-mono"
  (statement := /-- If $G_1 \subseteq G_2$, $G_1 \ne \emptyset$ and the Rademacher averages
    $\{\frac1n\sum_i \sigma_i g(x_i) : g \in G_2\}$ are bounded above for every sign pattern
    $\sigma$, then $\hat{\mathfrak R}_S(G_1) \le \hat{\mathfrak R}_S(G_2)$. -/)]
theorem empRademacher_mono (h : G₁ ⊆ G₂) (hne : G₁.Nonempty)
    (hbdd : ∀ σ : Signs n,
      BddAbove (Set.range fun g : G₂ =>
        normalizedRademacherSum n (fun g : G₂ => (g : X → ℝ)) S σ g)) :
    empRademacher S G₁ ≤ empRademacher S G₂ := by
  /-- Compare the suprema termwise for each sign pattern $\sigma$: every element of $G_1$ is an
    element of $G_2$. -/
  haveI : Nonempty G₁ := hne.to_subtype
  unfold empRademacher empiricalRademacherComplexity_without_abs
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => ?_) (by positivity)
  refine ciSup_le fun g => ?_
  exact le_ciSup (hbdd σ) (⟨(g : X → ℝ), h g.2⟩ : G₂)

@[blueprint "lem:emp-rademacher-le-abs"
  (statement := /-- If $|g(x_i)| \le C$ for all $g \in G$ and $i \le n$, then the one-sided
    empirical Rademacher complexity is dominated by the absolute one:
    $\hat{\mathfrak R}_S(G) \le \mathbb E_\sigma \sup_{g \in G}
    \bigl|\frac1n \sum_i \sigma_i g(x_i)\bigr|$. -/)]
theorem empRademacher_le_abs {C : ℝ} (hC : 0 ≤ C) (hG : ∀ g ∈ G, ∀ i, |g (S i)| ≤ C) :
    empRademacher S G ≤ empiricalRademacherComplexity n (fun g : G => (g : X → ℝ)) S :=
  empiricalRademacherComplexity_without_abs_le_empiricalRademacherComplexity n
    (fun g : G => (g : X → ℝ)) S C hC fun g i => hG g g.2 i

end LeanDeepgen
