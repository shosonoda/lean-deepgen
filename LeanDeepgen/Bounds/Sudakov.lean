import Mathlib
import Architect
import FoML
import LeanDeepgen.Setting.WordBall
import LeanDeepgen.Setting.Metrics
import LeanDeepgen.Setting.Hypothesis
import LeanDeepgen.Setting.Rademacher
import LeanDeepgen.Setting.Assumptions
import FoML.ToFoML.BernoulliSudakov

/-!
# Conditional Sudakov-type lower bound

Assumption `ass:readout-realization-main`, Theorem `thm:sudakov-type` (= `thm:sudakov`,
Appendix E) and its corollaries `cor:sudakov-rates` and `cor:matching` (i), (ii), which are
proved from the theorem by substitution.

**Proof status.** The paper's proof (transport a `2ε`-packing of `B(k,F)` through `Ψ_k`, apply
the Bernoulli–Sudakov minoration `thm:bernoulli-sudakov` of
`FoML.ToFoML.BernoulliSudakov` to the transported finite class) is formalised as
`sudakov_type`, for an **arbitrary** hidden class `B ⊆ 𝒳^𝒳` (the word-ball structure of `B(k,F)`
is not used; the paper's form is the specialization `sudakov_type_wordBall`); all results of this
file are unconditional, `FoML.ToFoML.bernoulli_sudakov` being fully proved. Compared
with the paper, the Lean statement of `sudakov_type` (and hence of every corollary) carries one
extra hypothesis: for every sign pattern `σ` the Rademacher sums `{n⁻¹ ∑ᵢ σᵢ g(xᵢ) : g ∈ H ∘ B}` are
bounded above (e.g. `ℋ_k` is uniformly bounded on the sample, `sudakov_type_of_bounded`). This is
needed because Lean's `⨆` over a set of reals that is not bounded above is `0`
(`Real.iSup_of_not_bddAbove`), so without it the statement would be false for an unbounded output
class such as `H = ℝ^𝒳`. (In the paper the class `H` is implicitly bounded.)

The universal constant `c` is quantified as `∃ c > 0, ∀ X S H F k κ R_out, …`, i.e. it depends on
nothing. The paper's `sup_{ε>0}` on the right-hand side is equivalent to a statement for every
`ε > 0`, which is how we state it. The packing number is Mathlib's `Metric.packingNumber`
(`ℕ∞`-valued); the Lean statement uses `(packingNumber …).toReal`, which is `0` when the packing
number is infinite (the `ℕ∞` value is cast to `ℝ≥0∞` and then to `ℝ`), so in that (impossible
under the assumption) case the Lean statement is a weaker (trivial) inequality than the paper's —
no finiteness hypothesis is added.

The assumption `ReadoutRealization` (`ass:readout-realization-main`) is defined in
`LeanDeepgen.Setting.Assumptions`.
-/

open scoped NNReal ENNReal

namespace LeanDeepgen

section Nonneg

variable {X : Type*} {n : ℕ} {S : Fin n → X} {G : Set (X → ℝ)}

@[blueprint "lem:emp-rademacher-nonneg"
  (statement := /-- If $G \ne \emptyset$ and for every sign pattern $\sigma$ the Rademacher
    averages $\{\frac1n\sum_i \sigma_i g(x_i) : g \in G\}$ are bounded above, then
    $\hat{\mathfrak R}_S(G) \ge 0$. -/)]
theorem empRademacher_nonneg (hne : G.Nonempty)
    (hbdd : ∀ σ : Signs n, BddAbove (Set.range fun g : G =>
      normalizedRademacherSum n (fun g : G => (g : X → ℝ)) S σ g)) :
    0 ≤ empRademacher S G := by
  /-- Apply \texttt{lem:rademacher-avg-sup-nonneg} to the family $(g(x_i))_i$, $g \in G$. -/
  haveI : Nonempty G := hne.to_subtype
  exact FoML.ToFoML.rademacherAvgSup_nonneg (fun g : G => fun i => (g : X → ℝ) (S i)) hbdd

@[blueprint "lem:bdd-above-of-bounded"
  (statement := /-- If $|g(x_i)| \le C$ for all $g \in G$ and $i \le n$, then for every sign
    pattern $\sigma$ the Rademacher averages $\{\frac1n\sum_i \sigma_i g(x_i) : g \in G\}$ are
    bounded above (by $|C|$). -/)]
theorem bddAbove_normalizedRademacherSum_of_bounded {C : ℝ}
    (hG : ∀ g ∈ G, ∀ i, |g (S i)| ≤ C) (σ : Signs n) :
    BddAbove (Set.range fun g : G =>
      normalizedRademacherSum n (fun g : G => (g : X → ℝ)) S σ g) := by
  refine ⟨|C|, ?_⟩
  rintro _ ⟨g, rfl⟩
  change (n : ℝ)⁻¹ * ∑ k, (σ k : ℝ) * (g : X → ℝ) (S k) ≤ |C|
  calc (n : ℝ)⁻¹ * ∑ k, (σ k : ℝ) * (g : X → ℝ) (S k) ≤ (n : ℝ)⁻¹ * ∑ _k : Fin n, |C| := by
        gcongr with k
        calc (σ k : ℝ) * (g : X → ℝ) (S k) ≤ |(σ k : ℝ) * (g : X → ℝ) (S k)| := le_abs_self _
          _ = |(g : X → ℝ) (S k)| := by rw [abs_mul, abs_sigma, one_mul]
          _ ≤ C := hG g g.2 k
          _ ≤ |C| := le_abs_self C
    _ = (n : ℝ)⁻¹ * (n * |C|) := by simp
    _ ≤ |C| := by
        rcases Nat.eq_zero_or_pos n with h | h
        · subst h; simp
        · rw [inv_mul_cancel_left₀ (by positivity)]

end Nonneg

@[blueprint "thm:sudakov-type"
  (statement := /-- \textbf{Conditional Sudakov-type lower bound.} There is a universal constant
    $c > 0$ such that the following holds. Let $(\mathcal X, d)$ be a pseudometric space,
    $S = (x_1,\dots,x_n)$ a sample with $n \ge 1$, $H$ an output-layer class,
    $B \subseteq \mathcal X^{\mathcal X}$ an arbitrary hidden class, and suppose Assumption
    \texttt{ass:readout-realization-main} holds for $B$ with constants
    $\kappa, R_{\mathrm{out}} > 0$. Then for every $\varepsilon > 0$,
    $$\hat{\mathfrak R}_S(H \circ B) \ge c \min\Bigl\{\kappa \varepsilon
    \sqrt{\frac{\log M(B, d_S, 2\varepsilon)}{n}},\
    \frac{\kappa^2 \varepsilon^2}{R_{\mathrm{out}}} \Bigr\},$$
    equivalently the bound with $\sup_{\varepsilon > 0}$ on the right. (In Lean
    $\log M$ is read as $0$ when $M = \infty$, which only weakens the inequality.)
    This generalizes the paper, which states the bound for the word ball $B = B(k,F)$
    (\texttt{thm:sudakov-type-wordball}); the word-ball structure is not used in the proof,
    and $B = \emptyset$ is allowed (both sides are then $0$).
    In Lean we add the hypothesis that, for every sign pattern, the Rademacher averages over
    $H \circ B$ are bounded above (equivalently, that the supremum defining
    $\hat{\mathfrak R}_S(H \circ B)$ is finite); without it the Lean statement is false because
    an unbounded supremum evaluates to $0$. The proof is complete modulo the Bernoulli–Sudakov
    minoration \texttt{thm:bernoulli-sudakov}.
    Proof: take a maximal $2\varepsilon$-packing $g_1, \dots, g_M$ of $B$ for $d_S$
    ($M = M(B, d_S, 2\varepsilon)$; if $M = \infty$ the right-hand side is $0$ in Lean and the
    claim is \texttt{lem:emp-rademacher-nonneg}); the transported vectors
    $u_j = (h_{g_j}(g_j(x_i)))_i$ are $2\kappa\varepsilon$-separated in $\|\cdot\|_S$ and
    bounded by $R_{\mathrm{out}}$, so \texttt{thm:bernoulli-sudakov} gives
    $\mathbb E_\sigma \max_j \frac1n\sum_i \sigma_i u_{j,i} \ge c\min\{2\kappa\varepsilon
    \sqrt{\log M/n}, 4\kappa^2\varepsilon^2/R_{\mathrm{out}}\}$, and the left-hand side is at
    most $\hat{\mathfrak R}_S(H \circ B)$ since $\{h_{g_j} \circ g_j\} \subseteq
    H \circ B$. -/)]
theorem sudakov_type :
    ∃ c : ℝ, 0 < c ∧ ∀ (𝒳 : Type u) [PseudoMetricSpace 𝒳] (n : ℕ) (S : Fin n → 𝒳)
      (H : Set (𝒳 → ℝ)) (B : Set (𝒳 → 𝒳)) (κ Rout : ℝ),
      0 < κ → 0 < Rout → 0 < n → ReadoutRealization S H B κ Rout →
      (∀ σ : Signs n, BddAbove (Set.range fun g : compClass H B =>
        normalizedRademacherSum n (fun g : compClass H B => (g : 𝒳 → ℝ)) S σ g)) →
      ∀ ε : ℝ≥0, 0 < ε →
        c * min (κ * ε * Real.sqrt (Real.log
              (Metric.packingNumber (X := EmpSpace S) (2 * ε) B : ℝ≥0∞).toReal / n))
            (κ ^ 2 * ε ^ 2 / Rout) ≤
          empRademacher S (compClass H B) := by
  obtain ⟨c, hc, hmin⟩ := FoML.ToFoML.bernoulli_sudakov
  refine ⟨c, hc, fun 𝒳 _ n S H B κ Rout hκ hR hn hreal hbdd ε hε => ?_⟩
  obtain ⟨hf, hfH, hfsep, hfbdd⟩ := hreal
  rcases B.eq_empty_or_nonempty with hB | ⟨g₀, hg₀⟩
  · -- empty hidden class: both sides are `0`
    have hemp : compClass H B = ∅ := by
      rw [hB]
      ext u
      simp [compClass]
    have hP0 : Metric.packingNumber (X := EmpSpace S) (2 * ε) B = 0 := by
      rw [hB]
      exact Metric.packingNumber_empty _
    rw [hemp, hP0]
    simp only [ENat.toENNReal_zero, ENNReal.toReal_zero, Real.log_zero, zero_div,
      Real.sqrt_zero, mul_zero]
    rw [min_eq_left (by positivity), mul_zero]
    unfold empRademacher empiricalRademacherComplexity_without_abs
    haveI : IsEmpty ((∅ : Set (𝒳 → ℝ))) := Set.isEmpty_coe_sort.mpr rfl
    simp only [iSup_of_empty', Real.sSup_empty, Finset.sum_const_zero, mul_zero, le_refl]
  have hne : (compClass H B).Nonempty :=
    ⟨hf g₀ ∘ g₀, hf g₀, hfH g₀ hg₀, g₀, hg₀, rfl⟩
  have hε' : (0 : ℝ) < ε := NNReal.coe_pos.mpr hε
  by_cases hP : Metric.packingNumber (X := EmpSpace S) (2 * ε) B = ⊤
  · -- infinite packing number: the right-hand side is `0`
    rw [hP, ENat.toENNReal_top, ENNReal.toReal_top, Real.log_zero, zero_div, Real.sqrt_zero,
      mul_zero, min_eq_left (by positivity), mul_zero]
    exact empRademacher_nonneg hne hbdd
  -- a maximal `2ε`-separated subset `C ⊆ B`, enumerated by `Fin M`
  obtain ⟨C, hCA, hCfin, hCsep, hCcard⟩ := Metric.exists_set_encard_eq_packingNumber hP
  haveI : Fintype C := hCfin.fintype
  set M := Fintype.card C with hM
  have hCne : C.Nonempty := by
    rw [← Set.encard_pos, hCcard]
    exact Metric.packingNumber_pos_iff.mpr ⟨g₀, hg₀⟩
  haveI : Nonempty (Fin M) := ⟨⟨0, Fintype.card_pos_iff.mpr hCne.to_subtype⟩⟩
  let e : Fin M ≃ C := (Fintype.equivFin C).symm
  let g : Fin M → (𝒳 → 𝒳) := fun j => (e j : EmpSpace S)
  have hg : ∀ j, g j ∈ B := fun j => hCA (e j).2
  -- the transported vectors
  let u : Fin M → Fin n → ℝ := fun j i => hf (g j) (g j (S i))
  have hPM : (Metric.packingNumber (X := EmpSpace S) (2 * ε) B : ℝ≥0∞).toReal = M := by
    rw [← hCcard, Set.encard_eq_coe_toFinset_card, Set.toFinset_card, ENat.toENNReal_coe,
      ENNReal.toReal_natCast]
  -- separation: `‖u j − u l‖_S ≥ κ d_S(g j, g l) > 2κε`
  have hsep : ∀ j l, j ≠ l →
      2 * κ * ε ≤ Real.sqrt ((1 / (n : ℝ)) * ∑ i, |u j i - u l i| ^ 2) := by
    intro j l hjl
    have hne' : (e j : EmpSpace S) ≠ e l := fun h => hjl (e.injective (Subtype.ext h))
    have h1 : ((2 * ε : ℝ≥0) : ℝ≥0∞) < edist (e j : EmpSpace S) (e l) :=
      hCsep (e j).2 (e l).2 hne'
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)] at h1
    have h2 := hfsep (g j) (hg j) (g l) (hg l)
    have h3 : empNorm S (hf (g j) ∘ g j) (hf (g l) ∘ g l) =
        Real.sqrt ((1 / (n : ℝ)) * ∑ i, |u j i - u l i| ^ 2) := rfl
    rw [← h3]
    calc 2 * κ * ε = κ * ((2 * ε : ℝ≥0) : ℝ) := by push_cast; ring
      _ ≤ κ * empDist S (g j) (g l) := mul_le_mul_of_nonneg_left h1.le hκ.le
      _ ≤ _ := h2
  -- boundedness: `|u j i| ≤ ‖h_{g j} ∘ g j‖_{S,∞} ≤ R_out`
  have hbdd' : ∀ j i, |u j i| ≤ Rout := by
    intro j i
    exact (le_ciSup (Set.finite_range fun i => |(hf (g j) ∘ g j) (S i)|).bddAbove i).trans
      (hfbdd (g j) (hg j))
  -- the minoration for the transported class
  have hmain := hmin n M u (2 * κ * ε) Rout hn (by positivity) hR hsep hbdd'
  -- the transported class is a subclass of `H ∘ B`
  have hcmp : (Fintype.card (Signs n) : ℝ)⁻¹ *
      ∑ σ : Signs n, ⨆ j, (n : ℝ)⁻¹ * ∑ i : Fin n, (σ i : ℝ) * u j i ≤
        empRademacher S (compClass H B) := by
    unfold empRademacher empiricalRademacherComplexity_without_abs
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => ?_) (by positivity)
    refine ciSup_le fun j => ?_
    have hmem : hf (g j) ∘ g j ∈ compClass H B :=
      ⟨hf (g j), hfH _ (hg j), g j, hg j, rfl⟩
    exact le_ciSup (hbdd σ) ⟨hf (g j) ∘ g j, hmem⟩
  -- adjust the constants: `min {κε√, κ²ε²/R} ≤ min {2κε√, (2κε)²/R}`
  rw [hPM]
  refine le_trans ?_ (hmain.trans hcmp)
  refine mul_le_mul_of_nonneg_left (min_le_min ?_ ?_) hc.le
  · have : 0 ≤ κ * ε * Real.sqrt (Real.log M / n) := by positivity
    rw [show 2 * κ * (ε : ℝ) * Real.sqrt (Real.log M / n) =
      2 * (κ * ε * Real.sqrt (Real.log M / n)) by ring]
    linarith
  · refine div_le_div_of_nonneg_right ?_ hR.le
    nlinarith [mul_pos hκ hε']

@[blueprint "thm:sudakov-type-wordball"
  (statement := /-- \textbf{Conditional Sudakov-type lower bound for word balls (the paper's
    form).} There is a universal constant $c > 0$ such that, for $F$ a hidden-layer class,
    $k \ge 0$ and Assumption \texttt{ass:readout-realization-main} for $B_k = B(k,F)$ with
    constants $\kappa, R_{\mathrm{out}} > 0$ (and the boundedness hypothesis of
    \texttt{thm:sudakov-type}), for every $\varepsilon > 0$,
    $$\hat{\mathfrak R}_S(\mathcal H_k) \ge c \min\Bigl\{\kappa \varepsilon
    \sqrt{\frac{\log M(B_k, d_S, 2\varepsilon)}{n}},\
    \frac{\kappa^2 \varepsilon^2}{R_{\mathrm{out}}} \Bigr\}.$$
    Proof: \texttt{thm:sudakov-type} with $B = B(k,F)$, since
    $\mathcal H_k = H \circ B(k,F)$. -/)]
theorem sudakov_type_wordBall :
    ∃ c : ℝ, 0 < c ∧ ∀ (𝒳 : Type u) [PseudoMetricSpace 𝒳] (n : ℕ) (S : Fin n → 𝒳)
      (H : Set (𝒳 → ℝ)) (F : Set (𝒳 → 𝒳)) (k : ℕ) (κ Rout : ℝ),
      0 < κ → 0 < Rout → 0 < n → ReadoutRealization S H (wordBall F k) κ Rout →
      (∀ σ : Signs n, BddAbove (Set.range fun g : hypothesisClass H F k =>
        normalizedRademacherSum n (fun g : hypothesisClass H F k => (g : 𝒳 → ℝ)) S σ g)) →
      ∀ ε : ℝ≥0, 0 < ε →
        c * min (κ * ε * Real.sqrt (Real.log
              (Metric.packingNumber (X := EmpSpace S) (2 * ε) (wordBall F k) : ℝ≥0∞).toReal / n))
            (κ ^ 2 * ε ^ 2 / Rout) ≤
          empRademacher S (hypothesisClass H F k) := by
  obtain ⟨c, hc, hmain⟩ := sudakov_type.{u}
  exact ⟨c, hc, fun 𝒳 _ n S H F k κ Rout hκ hR hn hreal hbdd ε hε =>
    hmain 𝒳 n S H (wordBall F k) κ Rout hκ hR hn hreal hbdd ε hε⟩

@[blueprint "cor:sudakov-type-bounded"
  (statement := /-- \textbf{Conditional Sudakov-type lower bound for a bounded hypothesis
    class.} Under the hypotheses of \texttt{thm:sudakov-type}, the boundedness hypothesis
    holds as soon as $\mathcal H_k$ is uniformly bounded on the sample,
    $|g(x_i)| \le C$ for all $g \in \mathcal H_k$ and $i \le n$; hence the same lower bound. -/)]
theorem sudakov_type_of_bounded :
    ∃ c : ℝ, 0 < c ∧ ∀ (𝒳 : Type u) [PseudoMetricSpace 𝒳] (n : ℕ) (S : Fin n → 𝒳)
      (H : Set (𝒳 → ℝ)) (F : Set (𝒳 → 𝒳)) (k : ℕ) (κ Rout C : ℝ),
      0 < κ → 0 < Rout → 0 < n → ReadoutRealization S H (wordBall F k) κ Rout →
      (∀ g ∈ hypothesisClass H F k, ∀ i, |g (S i)| ≤ C) →
      ∀ ε : ℝ≥0, 0 < ε →
        c * min (κ * ε * Real.sqrt (Real.log
              (Metric.packingNumber (X := EmpSpace S) (2 * ε) (wordBall F k) : ℝ≥0∞).toReal / n))
            (κ ^ 2 * ε ^ 2 / Rout) ≤
          empRademacher S (hypothesisClass H F k) := by
  obtain ⟨c, hc, hmain⟩ := sudakov_type_wordBall.{u}
  exact ⟨c, hc, fun 𝒳 _ n S H F k κ Rout C hκ hR hn hreal hC ε hε =>
    hmain 𝒳 n S H F k κ Rout hκ hR hn hreal
      (bddAbove_normalizedRademacherSum_of_bounded hC) ε hε⟩

@[blueprint "lem:sudakov-rates-of-log-le"
  (statement := /-- (Substitution step.) There is a universal constant $c > 0$ such that under
    Assumption \texttt{ass:readout-realization-main} for $B_k$ and the boundedness hypothesis of
    \texttt{thm:sudakov-type}, for every $\varepsilon_0 > 0$ and
    every $q \ge 0$ with $q \le \log M(B_k, d_S, 2\varepsilon_0)$,
    $\hat{\mathfrak R}_S(\mathcal H_k) \ge c \min\{\kappa \varepsilon_0 \sqrt{q/n},\
    \kappa^2 \varepsilon_0^2 / R_{\mathrm{out}}\}$. -/)]
theorem sudakov_rates_of_log_le :
    ∃ c : ℝ, 0 < c ∧ ∀ (𝒳 : Type u) [PseudoMetricSpace 𝒳] (n : ℕ) (S : Fin n → 𝒳)
      (H : Set (𝒳 → ℝ)) (F : Set (𝒳 → 𝒳)) (k : ℕ) (κ Rout : ℝ),
      0 < κ → 0 < Rout → 0 < n → ReadoutRealization S H (wordBall F k) κ Rout →
      (∀ σ : Signs n, BddAbove (Set.range fun g : hypothesisClass H F k =>
        normalizedRademacherSum n (fun g : hypothesisClass H F k => (g : 𝒳 → ℝ)) S σ g)) →
      ∀ (ε₀ : ℝ≥0) (q : ℝ), 0 < ε₀ → 0 ≤ q →
        q ≤ Real.log
          (Metric.packingNumber (X := EmpSpace S) (2 * ε₀) (wordBall F k) : ℝ≥0∞).toReal →
        c * min (κ * ε₀ * Real.sqrt (q / n)) (κ ^ 2 * ε₀ ^ 2 / Rout) ≤
          empRademacher S (hypothesisClass H F k) := by
  /-- Monotonicity of $q \mapsto \kappa \varepsilon_0 \sqrt{q/n}$ in
    \texttt{thm:sudakov-type-wordball}. -/
  obtain ⟨c, hc, hmain⟩ := sudakov_type_wordBall.{u}
  refine ⟨c, hc, fun 𝒳 _ n S H F k κ Rout hκ hR hn hreal hbdd ε₀ q hε₀ hq hlog => ?_⟩
  refine le_trans ?_ (hmain 𝒳 n S H F k κ Rout hκ hR hn hreal hbdd ε₀ hε₀)
  refine mul_le_mul_of_nonneg_left (min_le_min ?_ le_rfl) hc.le
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (mul_nonneg hκ.le ε₀.coe_nonneg)
  gcongr

@[blueprint "cor:sudakov-rates"
  (statement := /-- \textbf{Rates under fixed-scale packing lower bounds (exponential).} There is
    a universal constant $c > 0$ such that under Assumption
    \texttt{ass:readout-realization-main} for $B_k$: if
    $M(B_k, d_S, 2\varepsilon_0) \ge e^{\alpha k}$ for some $\varepsilon_0, \alpha > 0$, then
    $$\hat{\mathfrak R}_S(\mathcal H_k) \ge c \min\Bigl\{\kappa \varepsilon_0 \sqrt{\alpha k / n},\
    \kappa^2 \varepsilon_0^2 / R_{\mathrm{out}}\Bigr\}.$$ -/)]
theorem sudakov_rates_exp :
    ∃ c : ℝ, 0 < c ∧ ∀ (𝒳 : Type u) [PseudoMetricSpace 𝒳] (n : ℕ) (S : Fin n → 𝒳)
      (H : Set (𝒳 → ℝ)) (F : Set (𝒳 → 𝒳)) (k : ℕ) (κ Rout : ℝ),
      0 < κ → 0 < Rout → 0 < n → ReadoutRealization S H (wordBall F k) κ Rout →
      (∀ σ : Signs n, BddAbove (Set.range fun g : hypothesisClass H F k =>
        normalizedRademacherSum n (fun g : hypothesisClass H F k => (g : 𝒳 → ℝ)) S σ g)) →
      ∀ (ε₀ : ℝ≥0) (α : ℝ), 0 < ε₀ → 0 < α →
        Real.exp (α * k) ≤
          (Metric.packingNumber (X := EmpSpace S) (2 * ε₀) (wordBall F k) : ℝ≥0∞).toReal →
        c * min (κ * ε₀ * Real.sqrt (α * k / n)) (κ ^ 2 * ε₀ ^ 2 / Rout) ≤
          empRademacher S (hypothesisClass H F k) := by
  /-- $\alpha k = \log e^{\alpha k} \le \log M$. -/
  obtain ⟨c, hc, hmain⟩ := sudakov_rates_of_log_le.{u}
  refine ⟨c, hc, fun 𝒳 _ n S H F k κ Rout hκ hR hn hreal hbdd ε₀ α hε₀ hα hpack => ?_⟩
  refine hmain 𝒳 n S H F k κ Rout hκ hR hn hreal hbdd ε₀ (α * k) hε₀ (by positivity) ?_
  rw [Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos _) hpack)]
  exact hpack

@[blueprint "cor:sudakov-rates-poly"
  (statement := /-- \textbf{Rates under fixed-scale packing lower bounds (polynomial).} There is
    a universal constant $c > 0$ such that under Assumption
    \texttt{ass:readout-realization-main} for $B_k$: if $k \ge 1$ and
    $M(B_k, d_S, 2\varepsilon_0) \ge k^{\beta}$ for some $\varepsilon_0, \beta > 0$, then
    $$\hat{\mathfrak R}_S(\mathcal H_k) \ge c \min\Bigl\{\kappa \varepsilon_0
    \sqrt{\beta \log k / n},\ \kappa^2 \varepsilon_0^2 / R_{\mathrm{out}}\Bigr\}.$$ -/)]
theorem sudakov_rates_poly :
    ∃ c : ℝ, 0 < c ∧ ∀ (𝒳 : Type u) [PseudoMetricSpace 𝒳] (n : ℕ) (S : Fin n → 𝒳)
      (H : Set (𝒳 → ℝ)) (F : Set (𝒳 → 𝒳)) (k : ℕ) (κ Rout : ℝ),
      0 < κ → 0 < Rout → 0 < n → ReadoutRealization S H (wordBall F k) κ Rout →
      (∀ σ : Signs n, BddAbove (Set.range fun g : hypothesisClass H F k =>
        normalizedRademacherSum n (fun g : hypothesisClass H F k => (g : 𝒳 → ℝ)) S σ g)) →
      ∀ (ε₀ : ℝ≥0) (β : ℝ), 0 < ε₀ → 0 < β → 1 ≤ k →
        (k : ℝ) ^ β ≤
          (Metric.packingNumber (X := EmpSpace S) (2 * ε₀) (wordBall F k) : ℝ≥0∞).toReal →
        c * min (κ * ε₀ * Real.sqrt (β * Real.log k / n)) (κ ^ 2 * ε₀ ^ 2 / Rout) ≤
          empRademacher S (hypothesisClass H F k) := by
  /-- $\beta \log k = \log k^\beta \le \log M$. -/
  obtain ⟨c, hc, hmain⟩ := sudakov_rates_of_log_le.{u}
  refine ⟨c, hc, fun 𝒳 _ n S H F k κ Rout hκ hR hn hreal hbdd ε₀ β hε₀ hβ hk hpack => ?_⟩
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hlogk : 0 ≤ Real.log k := Real.log_nonneg hk'
  refine hmain 𝒳 n S H F k κ Rout hκ hR hn hreal hbdd ε₀ (β * Real.log k) hε₀
    (mul_nonneg hβ.le hlogk) ?_
  rw [← Real.log_rpow (by linarith)]
  exact Real.log_le_log (Real.rpow_pos_of_pos (by linarith) β) hpack

@[blueprint "lem:first-branch-le"
  (statement := /-- For $\kappa, \varepsilon_0, R_{\mathrm{out}} > 0$, $n \ge 1$ and $q \ge 0$,
    the first branch of the minimum is the smaller one as soon as
    $n \ge R_{\mathrm{out}}^2 q / (\kappa^2 \varepsilon_0^2)$:
    $\kappa \varepsilon_0 \sqrt{q/n} \le \kappa^2 \varepsilon_0^2 / R_{\mathrm{out}}$. -/)]
theorem first_branch_le {κ ε₀ Rout q : ℝ} {n : ℕ} (hκ : 0 < κ) (hε₀ : 0 < ε₀) (hR : 0 < Rout)
    (hn : 0 < n) (_hq : 0 ≤ q) (hthr : Rout ^ 2 * q / (κ ^ 2 * ε₀ ^ 2) ≤ n) :
    κ * ε₀ * Real.sqrt (q / n) ≤ κ ^ 2 * ε₀ ^ 2 / Rout := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hκε : 0 ≤ κ * ε₀ := (mul_pos hκ hε₀).le
  have h1 : q / n ≤ (κ * ε₀ / Rout) ^ 2 := by
    rw [div_le_iff₀ hn', div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hthr
    nlinarith [hthr]
  calc κ * ε₀ * Real.sqrt (q / n) ≤ κ * ε₀ * (κ * ε₀ / Rout) := by
        refine mul_le_mul_of_nonneg_left ?_ hκε
        calc Real.sqrt (q / n) ≤ Real.sqrt ((κ * ε₀ / Rout) ^ 2) := Real.sqrt_le_sqrt h1
          _ = κ * ε₀ / Rout := Real.sqrt_sq (div_nonneg hκε hR.le)
    _ = κ ^ 2 * ε₀ ^ 2 / Rout := by ring

@[blueprint "cor:matching"
  (statement := /-- \textbf{Matching depth dependence (i).} There is a universal constant $c > 0$
    such that under Assumption \texttt{ass:readout-realization-main} for $B_k$ (constants
    $\kappa, R_{\mathrm{out}}$), the boundedness hypothesis of \texttt{thm:sudakov-type} and
    $\varepsilon_0 > 0$: if
    $M(B_k, d_S, 2\varepsilon_0) \ge e^{\alpha k}$ for some $\alpha > 0$, then
    $\hat{\mathfrak R}_S(\mathcal H_k) \ge c\, \kappa \varepsilon_0 \sqrt{\alpha k / n}$
    whenever $n \ge R_{\mathrm{out}}^2 \alpha k / (\kappa^2 \varepsilon_0^2)$. -/)]
theorem matching_exp :
    ∃ c : ℝ, 0 < c ∧ ∀ (𝒳 : Type u) [PseudoMetricSpace 𝒳] (n : ℕ) (S : Fin n → 𝒳)
      (H : Set (𝒳 → ℝ)) (F : Set (𝒳 → 𝒳)) (k : ℕ) (κ Rout : ℝ),
      0 < κ → 0 < Rout → 0 < n → ReadoutRealization S H (wordBall F k) κ Rout →
      (∀ σ : Signs n, BddAbove (Set.range fun g : hypothesisClass H F k =>
        normalizedRademacherSum n (fun g : hypothesisClass H F k => (g : 𝒳 → ℝ)) S σ g)) →
      ∀ (ε₀ : ℝ≥0) (α : ℝ), 0 < ε₀ → 0 < α →
        Real.exp (α * k) ≤
          (Metric.packingNumber (X := EmpSpace S) (2 * ε₀) (wordBall F k) : ℝ≥0∞).toReal →
        Rout ^ 2 * (α * k) / (κ ^ 2 * ε₀ ^ 2) ≤ n →
        c * (κ * ε₀ * Real.sqrt (α * k / n)) ≤ empRademacher S (hypothesisClass H F k) := by
  /-- Substitute $\varepsilon = \varepsilon_0$; the threshold on $n$ makes the first branch of
    the minimum the smaller one. -/
  obtain ⟨c, hc, hmain⟩ := sudakov_rates_exp.{u}
  refine ⟨c, hc, fun 𝒳 _ n S H F k κ Rout hκ hR hn hreal hbdd ε₀ α hε₀ hα hpack hthr => ?_⟩
  have h := hmain 𝒳 n S H F k κ Rout hκ hR hn hreal hbdd ε₀ α hε₀ hα hpack
  rwa [min_eq_left (first_branch_le hκ (NNReal.coe_pos.mpr hε₀) hR hn (by positivity) hthr)]
    at h

@[blueprint "cor:matching-ii"
  (statement := /-- \textbf{Matching depth dependence (ii).} There is a universal constant
    $c > 0$ such that under Assumption \texttt{ass:readout-realization-main} for $B_k$ (constants
    $\kappa, R_{\mathrm{out}}$), the boundedness hypothesis of \texttt{thm:sudakov-type},
    $k \ge 1$ and $\varepsilon_0 > 0$: if
    $M(B_k, d_S, 2\varepsilon_0) \ge k^{\beta}$ for some $\beta > 0$, then
    $\hat{\mathfrak R}_S(\mathcal H_k) \ge c\, \kappa \varepsilon_0 \sqrt{\beta \log k / n}$
    whenever $n \ge R_{\mathrm{out}}^2 \beta \log k / (\kappa^2 \varepsilon_0^2)$. -/)]
theorem matching_poly :
    ∃ c : ℝ, 0 < c ∧ ∀ (𝒳 : Type u) [PseudoMetricSpace 𝒳] (n : ℕ) (S : Fin n → 𝒳)
      (H : Set (𝒳 → ℝ)) (F : Set (𝒳 → 𝒳)) (k : ℕ) (κ Rout : ℝ),
      0 < κ → 0 < Rout → 0 < n → ReadoutRealization S H (wordBall F k) κ Rout →
      (∀ σ : Signs n, BddAbove (Set.range fun g : hypothesisClass H F k =>
        normalizedRademacherSum n (fun g : hypothesisClass H F k => (g : 𝒳 → ℝ)) S σ g)) →
      ∀ (ε₀ : ℝ≥0) (β : ℝ), 0 < ε₀ → 0 < β → 1 ≤ k →
        (k : ℝ) ^ β ≤
          (Metric.packingNumber (X := EmpSpace S) (2 * ε₀) (wordBall F k) : ℝ≥0∞).toReal →
        Rout ^ 2 * (β * Real.log k) / (κ ^ 2 * ε₀ ^ 2) ≤ n →
        c * (κ * ε₀ * Real.sqrt (β * Real.log k / n)) ≤
          empRademacher S (hypothesisClass H F k) := by
  obtain ⟨c, hc, hmain⟩ := sudakov_rates_poly.{u}
  refine ⟨c, hc, fun 𝒳 _ n S H F k κ Rout hκ hR hn hreal hbdd ε₀ β hε₀ hβ hk hpack hthr => ?_⟩
  have h := hmain 𝒳 n S H F k κ Rout hκ hR hn hreal hbdd ε₀ β hε₀ hβ hk hpack
  have hlogk : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk)
  rwa [min_eq_left (first_branch_le hκ (NNReal.coe_pos.mpr hε₀) hR hn
    (mul_nonneg hβ.le hlogk) hthr)] at h

end LeanDeepgen
