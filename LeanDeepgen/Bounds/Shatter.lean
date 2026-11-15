import Mathlib
import Architect
import FoML
import LeanDeepgen.Setting.Hypothesis
import LeanDeepgen.Setting.Rademacher
import LeanDeepgen.Bounds.Sudakov

/-!
# Rademacher complexity of a class that shatters the sample

A class `G ⊆ ℝ^𝒳` *shatters* the sample `S = (x_1, …, x_n)` at the levels `a₀ ≤ a₁` when every
two-valued labeling `c ∈ {0,1}^n` is realized: some `g ∈ G` has `g(x_i) = a_{c_i}` for all `i`.

* `empRademacher_ge_of_shatter` (`lem:shatter-rademacher-general`): then
  `R̂_S(G) ≥ (a₁ − a₀)/2`, provided the Rademacher averages over `G` are bounded above.  For a
  sign pattern `σ` take the labeling `c_i = 1` exactly when `σ_i = 1`; the supremum over `G` is
  at least the value at the corresponding `g`, which is `n⁻¹ ∑ᵢ σᵢ a_{c_i}`.  Pairing `σ` with
  `−σ`, the two values add up to `a₁ − a₀`, so the average over the `2^n` sign patterns is
  `(a₁ − a₀)/2`.
* `lem_shatter_rademacher` (`lem:shatter-rademacher`, the statement of the paper): the same
  bound when the class is uniformly bounded on the sample (this gives the boundedness of the
  Rademacher averages).
* `empRademacher_compClass_ge_of_shatter` (`lem:shatter-rademacher-comp`): the form for a
  composite class `H ∘ B`: one output layer `h ∈ H` and, for every labeling, a hidden map
  `f ∈ B` with `h(f(x_i)) = a_{c_i}`.

As everywhere in this library, the general Lean statement carries the hypothesis that for every
sign pattern the Rademacher averages over the class are bounded above: Lean's `⨆` of an unbounded
real family is `0`, so the statement would be false without it.  The paper's lemma assumes that
the class is bounded on the sample, which implies it.  The hypothesis `a₀ ≤ a₁` is the natural
reading (it makes the bound nonnegative); the proof does not use it.
-/

open scoped NNReal ENNReal

namespace LeanDeepgen

variable {X : Type*} {n : ℕ}

set_option linter.unusedVariables false in
@[blueprint "lem:shatter-rademacher-general"
  (statement := /-- \textbf{(A shattered sample has Rademacher complexity at least half the
    margin, general form.)} Let $S = (x_1, \dots, x_n)$ with $n \ge 1$,
    $G \subseteq \mathbb R^{\mathcal X}$ and $a_0 \le a_1$. Suppose that $G$ realizes every
    two-valued labeling of the sample: for every $c \in \{0,1\}^n$ there is $g \in G$ with
    $g(x_i) = a_{c_i}$ for all $i$. Suppose moreover that for every sign pattern $\sigma$ the
    Rademacher averages $\{\frac1n \sum_i \sigma_i g(x_i) : g \in G\}$ are bounded above (as in
    \texttt{lem:emp-rademacher-mono}). Then
    $$\hat{\mathfrak R}_S(G) \ge \frac{a_1 - a_0}{2}.$$
    (This is \texttt{lem:shatter-rademacher} with the boundedness of $G$ on the sample replaced
    by the weaker hypothesis on the Rademacher averages; the hypothesis $a_0 \le a_1$ is not
    used in the proof.) -/)]
theorem empRademacher_ge_of_shatter (hn : 0 < n) (S : Fin n → X) (G : Set (X → ℝ))
    {a₀ a₁ : ℝ} (ha : a₀ ≤ a₁)
    (hshatter : ∀ c : Fin n → Bool, ∃ g ∈ G, ∀ i, g (S i) = if c i then a₁ else a₀)
    (hbdd : ∀ σ : Signs n, BddAbove (Set.range fun g : G =>
      normalizedRademacherSum n (fun g : G => (g : X → ℝ)) S σ g)) :
    (a₁ - a₀) / 2 ≤ empRademacher S G := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsign : ∀ (σ : Signs n) (i : Fin n), (σ i : ℤ) = -1 ∨ (σ i : ℤ) = 1 := fun σ i => by
    have h := (σ i).2
    rw [Finset.mem_insert, Finset.mem_singleton] at h
    exact h
  /-- Step 1. For a sign pattern $\sigma$ let $\psi(\sigma) := \frac1n \sum_i \sigma_i a_{c_i}$
    with $c_i = 1$ exactly when $\sigma_i = 1$. The labeling $c$ is realized by some
    $g \in G$, so $\psi(\sigma) \le \sup_{g \in G} \frac1n \sum_i \sigma_i g(x_i)$. -/
  set ψ : Signs n → ℝ := fun σ =>
    (n : ℝ)⁻¹ * ∑ i : Fin n, (σ i : ℝ) * (if (σ i : ℤ) = 1 then a₁ else a₀) with hψ
  have hle : ∀ σ : Signs n,
      ψ σ ≤ ⨆ g : G, (n : ℝ)⁻¹ * ∑ i : Fin n, (σ i : ℝ) * (g : X → ℝ) (S i) := by
    intro σ
    obtain ⟨g, hg, hgS⟩ := hshatter fun i => decide ((σ i : ℤ) = 1)
    have h := le_ciSup (hbdd σ) ⟨g, hg⟩
    have hval : normalizedRademacherSum n (fun g : G => (g : X → ℝ)) S σ ⟨g, hg⟩ = ψ σ := by
      simp only [normalizedRademacherSum, hψ, hgS, decide_eq_true_eq]
    rw [hval] at h
    exact h
  /-- Step 2. $\psi(\sigma) + \psi(-\sigma) = a_1 - a_0$: the $i$-th terms add up to
    $a_1 - a_0$ for either value of $\sigma_i$. -/
  have hpair : ∀ σ : Signs n, ψ σ + ψ (FoML.ToFoML.negSigns σ) = a₁ - a₀ := by
    intro σ
    have hterm : ∀ i : Fin n,
        (σ i : ℝ) * (if (σ i : ℤ) = 1 then a₁ else a₀) +
          (FoML.ToFoML.negSigns σ i : ℝ) *
            (if (FoML.ToFoML.negSigns σ i : ℤ) = 1 then a₁ else a₀) = a₁ - a₀ := by
      intro i
      have hneg : (FoML.ToFoML.negSigns σ i : ℤ) = -(σ i : ℤ) := rfl
      rw [hneg]
      rcases hsign σ i with h | h <;> rw [h] <;> norm_num <;> ring
    simp only [hψ]
    rw [← mul_add, ← Finset.sum_add_distrib, Finset.sum_congr rfl fun i _ => hterm i,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hn', one_mul]
  /-- Step 3. Reindexing by $\sigma \mapsto -\sigma$,
    $2 \sum_\sigma \psi(\sigma) = \sum_\sigma (\psi(\sigma) + \psi(-\sigma)) = 2^n (a_1 - a_0)$. -/
  have hsum : ∑ σ : Signs n, ψ σ = (Fintype.card (Signs n) : ℝ) * ((a₁ - a₀) / 2) := by
    have hflip : ∑ σ : Signs n, ψ (FoML.ToFoML.negSigns σ) = ∑ σ : Signs n, ψ σ :=
      Function.Bijective.sum_comp FoML.ToFoML.negSigns_involutive.bijective ψ
    have h2 : ∑ σ : Signs n, (ψ σ + ψ (FoML.ToFoML.negSigns σ)) =
        (Fintype.card (Signs n) : ℝ) * (a₁ - a₀) := by
      rw [Finset.sum_congr rfl fun σ _ => hpair σ, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
    rw [Finset.sum_add_distrib, hflip] at h2
    linarith
  /-- Step 4. Average the inequality of Step 1 over the sign patterns. -/
  have hcard : (0 : ℝ) < Fintype.card (Signs n) := by
    rw [Signs.card]; positivity
  calc (a₁ - a₀) / 2
      = (Fintype.card (Signs n) : ℝ)⁻¹ * ∑ σ : Signs n, ψ σ := by
        rw [hsum, inv_mul_cancel_left₀ hcard.ne']
    _ ≤ empRademacher S G := by
        unfold empRademacher empiricalRademacherComplexity_without_abs
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => hle σ) (by positivity)

@[blueprint "lem:shatter-rademacher"
  (statement := /-- \textbf{(Rademacher complexity of a shattered sample.)} Let $G$ be a class
    of real-valued functions that is bounded on the sample $S = (x_1, \dots, x_n)$, $n \ge 1$
    (there is $C$ with $|g(x_i)| \le C$ for all $g \in G$ and $i \le n$), and let
    $a_0 \le a_1$. If for every $c \in \{0,1\}^n$ there is $g \in G$ with $g(x_i) = a_{c_i}$
    for all $i$, then
    $$\hat{\mathfrak R}_S(G) \ge \frac{a_1 - a_0}{2}.$$
    (The boundedness on the sample gives the hypothesis of
    \texttt{lem:shatter-rademacher-general} that the Rademacher averages are bounded
    above.) -/)]
theorem lem_shatter_rademacher (hn : 0 < n) (S : Fin n → X) (G : Set (X → ℝ))
    {a₀ a₁ C : ℝ} (ha : a₀ ≤ a₁)
    (hshatter : ∀ c : Fin n → Bool, ∃ g ∈ G, ∀ i, g (S i) = if c i then a₁ else a₀)
    (hC : ∀ g ∈ G, ∀ i, |g (S i)| ≤ C) :
    (a₁ - a₀) / 2 ≤ empRademacher S G :=
  empRademacher_ge_of_shatter hn S G ha hshatter (bddAbove_normalizedRademacherSum_of_bounded hC)

@[blueprint "lem:shatter-rademacher-comp"
  (statement := /-- \textbf{(Shattered sample, composite class.)} Let $H \subseteq
    \mathbb R^{\mathcal X}$ be an output-layer class, $B \subseteq \mathcal X^{\mathcal X}$ a
    hidden class, $h \in H$ and $a_0 \le a_1$. If for every labeling $c \in \{0,1\}^n$ there is
    $f \in B$ with $h(f(x_i)) = a_{c_i}$ for all $i$, and $|g(x_i)| \le C$ for all
    $g \in H \circ B$ and $i \le n$, then
    $\hat{\mathfrak R}_S(H \circ B) \ge (a_1 - a_0)/2$. -/)]
theorem empRademacher_compClass_ge_of_shatter (hn : 0 < n) (S : Fin n → X) (H : Set (X → ℝ))
    (B : Set (X → X)) {h : X → ℝ} (hh : h ∈ H) {a₀ a₁ C : ℝ} (ha : a₀ ≤ a₁)
    (hshatter : ∀ c : Fin n → Bool, ∃ f ∈ B, ∀ i, h (f (S i)) = if c i then a₁ else a₀)
    (hC : ∀ g ∈ compClass H B, ∀ i, |g (S i)| ≤ C) :
    (a₁ - a₀) / 2 ≤ empRademacher S (compClass H B) := by
  /-- Apply \texttt{lem:shatter-rademacher} to $G = H \circ B$ with the functions
    $h \circ f$. -/
  refine lem_shatter_rademacher hn S (compClass H B) ha (fun c => ?_) hC
  obtain ⟨f, hf, hfS⟩ := hshatter c
  exact ⟨h ∘ f, ⟨h, hh, f, hf, rfl⟩, hfS⟩

end LeanDeepgen
