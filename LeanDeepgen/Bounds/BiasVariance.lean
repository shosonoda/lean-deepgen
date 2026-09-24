import Mathlib
import Architect
import FoML
import LeanDeepgen.Setting.Hypothesis
import LeanDeepgen.Setting.Loss
import LeanDeepgen.Setting.Rademacher
import LeanDeepgen.Setting.Assumptions
import FoML.ToFoML.Contraction
import FoML.ToFoML.UniformFunSeparable
import FoML.ToFoML.OneSidedDeviation

/-!
# Implementation-agnostic bias–variance decomposition

The paper's Theorem `thm:bv-general` (Appendix B) and its specialization `thm:bv` (Section 3.1).

The statements are in the "probability of the bad event" form used by FoML: for the sample
`D ~ P^{⊗n}`, the `P^{⊗n}`-measure of the set of samples on which the bound fails is at most `δ`.

## Constants

The paper states the bounds with `4 β_ℓ R̂_S(𝓗)` (excess risk), `2 β_ℓ R̂_S(𝓗)` (gap) and an
unspecified universal constant `C` in the deviation term `C b √(log(1/δ)/n)`. We recover the
paper's Rademacher constants exactly and make the deviation constant explicit. The proof goes
through the one-sided uniform-deviation chain of `FoML.ToFoML.OneSidedDeviation`
(one-sided symmetrization `𝔼 sup_f (L̂ f − L f) ≤ 2 R_n^{no-abs}`, McDiarmid, concentration of the
observed one-sided complexity) applied to the loss class `ℓ ∘ 𝓗` and to its negative `−ℓ ∘ 𝓗`
(union bound, `δ/2` each), together with the one-sided contraction inequality
`FoML.ToFoML.empiricalRademacherComplexity_without_abs_contraction`, which gives
`R̂_𝒟(±ℓ ∘ 𝓗) ≤ β_ℓ R̂_S(𝓗)` with constant exactly `β_ℓ` (no factor `2`, no singleton term).
Hence, with `ε_δ := b √(2 log(4/δ)/n)`:

* uniform deviation: `sup_{f∈𝓗} |L[f] − L̂[f]| ≤ 2 β_ℓ R̂_S(𝓗) + 3 ε_δ`;
* excess risk: `L[ĥ] − L_𝒞 ≤ β_L ε_imp + ε_model + η + 4 β_ℓ R̂_S(𝓗) + 6 ε_δ`;
* generalization gap: `L[h] − L̂[h] ≤ (β_L + β_L̂) ε_imp + 2 β_ℓ R̂_S(𝓗) + 3 ε_δ`.

The `log(4/δ)` (instead of `log(1/δ)`) comes from the two union bounds (two one-sided events, each
split into a deviation event and a lower-tail event for the observed complexity); the factor `3`
is FoML's `2 R̂_S + 3ε` threshold for the observed-complexity version.

## Additional hypothesis

We assume that `𝓗` is pointwise bounded (`∀ x, ∃ M, ∀ f ∈ 𝓗, |f x| ≤ M`); this guarantees that
the suprema defining `R̂_S(𝓗)` are suprema of bounded sets (otherwise Lean's `⨆` takes the junk
value `0` and the statement is meaningless).

The population-complexity variant ("the same bounds hold with `R̂_S` replaced by `R_n`") is
omitted for now.

The definitions used in the statements (`IsSupSeparable`, the index type `SupIndex 𝓗` and the
loss class `lossClass L 𝓗`) live in `LeanDeepgen.Setting.Assumptions`.
-/

open MeasureTheory
open scoped ENNReal UniformConvergence

namespace LeanDeepgen

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

@[blueprint "lem:risk-lipschitz"
  (statement := /-- If $\ell$ is $\beta_\ell$-Lipschitz in its first argument (with
    $\beta_\ell \ge 0$), $f, g$ are measurable and $\sup_x |f(x) - g(x)| \le c$, then
    $|L[f] - L[g]| \le \beta_\ell c$. -/)]
theorem abs_risk_sub_risk_le (P : Measure (X × Y)) [IsProbabilityMeasure P]
    (L : BoundedLipschitzLoss Y) (hℓ : Measurable (Function.uncurry L.ℓ)) (hβ : 0 ≤ L.β)
    {f g : X → ℝ} (hf : Measurable f) (hg : Measurable g) {c : ℝ} (hc : ∀ x, |f x - g x| ≤ c) :
    |risk L P f - risk L P g| ≤ L.β * c := by
  /-- Both loss integrands are bounded and measurable, hence integrable; the difference of the
    integrals is the integral of the pointwise difference, which is bounded by
    $\beta_\ell |f(x) - g(x)| \le \beta_\ell c$. -/
  have hmf : Measurable fun z : X × Y => L.ℓ (f z.1) z.2 :=
    hℓ.comp ((hf.comp measurable_fst).prodMk measurable_snd)
  have hmg : Measurable fun z : X × Y => L.ℓ (g z.1) z.2 :=
    hℓ.comp ((hg.comp measurable_fst).prodMk measurable_snd)
  have hbound : ∀ u : X → ℝ, ∀ z : X × Y, ‖L.ℓ (u z.1) z.2‖ ≤ L.b := fun u z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (L.nonneg _ _)]; exact L.le_b _ _
  have hif : Integrable (fun z : X × Y => L.ℓ (f z.1) z.2) P :=
    Integrable.of_bound hmf.aestronglyMeasurable L.b (Filter.Eventually.of_forall (hbound f))
  have hig : Integrable (fun z : X × Y => L.ℓ (g z.1) z.2) P :=
    Integrable.of_bound hmg.aestronglyMeasurable L.b (Filter.Eventually.of_forall (hbound g))
  unfold risk
  rw [← integral_sub hif hig, ← Real.norm_eq_abs]
  have := norm_integral_le_of_norm_le_const (μ := P)
    (f := fun z : X × Y => L.ℓ (f z.1) z.2 - L.ℓ (g z.1) z.2) (C := L.β * c)
    (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]
      exact (L.lip _ _ _).trans (mul_le_mul_of_nonneg_left (hc _) hβ))
  simpa [probReal_univ] using this

omit [MeasurableSpace X] [MeasurableSpace Y] in
@[blueprint "lem:emp-risk-lipschitz"
  (statement := /-- If $\ell$ is $\beta_\ell$-Lipschitz in its first argument (with
    $\beta_\ell \ge 0$) and $\sup_x |f(x) - g(x)| \le c$ with $c \ge 0$, then
    $|\hat L[f] - \hat L[g]| \le \beta_\ell c$ for every sample. -/)]
theorem abs_empRisk_sub_empRisk_le (L : BoundedLipschitzLoss Y) (hβ : 0 ≤ L.β) {n : ℕ}
    (D : Fin n → X × Y) {f g : X → ℝ} {c : ℝ} (hc0 : 0 ≤ c) (hc : ∀ x, |f x - g x| ≤ c) :
    |empRisk L D f - empRisk L D g| ≤ L.β * c := by
  /-- Termwise bound $|\ell(f(x_i),y_i) - \ell(g(x_i),y_i)| \le \beta_\ell c$ and average. -/
  unfold empRisk
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ))]
  calc (1 / (n : ℝ)) * |∑ i, (L.ℓ (f (D i).1) (D i).2 - L.ℓ (g (D i).1) (D i).2)|
      ≤ (1 / (n : ℝ)) * ∑ i, |L.ℓ (f (D i).1) (D i).2 - L.ℓ (g (D i).1) (D i).2| := by
        gcongr; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (1 / (n : ℝ)) * ∑ _i : Fin n, L.β * c := by
        gcongr with i
        exact (L.lip _ _ _).trans (mul_le_mul_of_nonneg_left (hc _) hβ)
    _ = (1 / (n : ℝ)) * ((n : ℝ) * (L.β * c)) := by simp
    _ ≤ L.β * c := by
        rcases Nat.eq_zero_or_pos n with h | h
        · subst h
          simp only [CharP.cast_eq_zero, div_zero, zero_mul, mul_zero]
          positivity
        · rw [one_div, inv_mul_cancel_left₀ (by exact_mod_cast h.ne')]

section General

variable {n : ℕ} (P : Measure (X × Y)) [IsProbabilityMeasure P] (L : BoundedLipschitzLoss Y)
  {𝓗 𝒞 : Set (X → ℝ)} (ι : (X → ℝ) → (X → ℝ)) (dT : (X → ℝ) → (X → ℝ) → ℝ)
  {βL βLhat εimp η δ : ℝ}

/-! ### Deterministic part -/

omit [IsProbabilityMeasure P] in
@[blueprint "lem:bv-deterministic"
  (statement := /-- \textbf{Deterministic excess-risk bound.} Fix a sample $\mathcal D$ and
    suppose $|L[f] - \hat L[f]| \le \Delta_0$ for every $f \in \mathcal H$. If
    $d_T(\iota f, f) \le \varepsilon_{\mathrm{imp}}$ and
    $|L[\iota f] - L[f]| \le \beta_L\, d_T(\iota f, f)$ for all $f \in \mathcal H$
    ($\beta_L \ge 0$), then every $\eta$-empirical minimizer $\hat f \in \mathcal H$ satisfies,
    with $\hat h = \iota(\hat f)$,
    $L[\hat h] - \inf_{\mathcal C} L \le \beta_L \varepsilon_{\mathrm{imp}}
    + \varepsilon_{\mathrm{model}} + \eta + 2\Delta_0$. -/)]
theorem excessRisk_le_of_uniform_deviation {D : Fin n → X × Y} {Δ₀ : ℝ}
    (hdev : ∀ f ∈ 𝓗, |risk L P f - empRisk L D f| ≤ Δ₀) (hβL : 0 ≤ βL)
    (himp : ∀ f ∈ 𝓗, dT (ι f) f ≤ εimp)
    (hL : ∀ f ∈ 𝓗, |risk L P (ι f) - risk L P f| ≤ βL * dT (ι f) f)
    {fhat : X → ℝ} (hfhat : IsEmpMinimizer L D 𝓗 η fhat) :
    risk L P (ι fhat) - sInf (risk L P '' 𝒞) ≤
      βL * εimp + modelError L P 𝓗 𝒞 + η + 2 * Δ₀ := by
  /-- $L[\hat h] \le L[\hat f] + \beta_L \varepsilon_{\mathrm{imp}}$ and, for every
    $f \in \mathcal H$, $L[\hat f] \le \hat L[\hat f] + \Delta_0 \le \hat L[f] + \eta + \Delta_0
    \le L[f] + \eta + 2\Delta_0$; take the infimum over $f$. -/
  obtain ⟨hmem, hmin⟩ := hfhat
  have h1 : risk L P (ι fhat) ≤ risk L P fhat + βL * εimp := by
    have := (abs_le.mp (hL fhat hmem)).2
    have := mul_le_mul_of_nonneg_left (himp fhat hmem) hβL
    linarith
  have h2 : ∀ f ∈ 𝓗, risk L P fhat ≤ risk L P f + 2 * Δ₀ + η := by
    intro f hf
    have := (abs_le.mp (hdev fhat hmem)).2
    have := (abs_le.mp (hdev f hf)).1
    have := hmin f hf
    linarith
  have h3 : risk L P fhat - 2 * Δ₀ - η ≤ sInf (risk L P '' 𝓗) := by
    refine le_csInf ⟨_, fhat, hmem, rfl⟩ ?_
    rintro _ ⟨f, hf, rfl⟩
    linarith [h2 f hf]
  unfold modelError
  linarith

omit [IsProbabilityMeasure P] in
@[blueprint "lem:bv-deterministic-gap"
  (statement := /-- \textbf{Deterministic gap bound.} Fix a sample $\mathcal D$ and suppose
    $|L[f] - \hat L[f]| \le \Delta_0$ for every $f \in \mathcal H$. Under the implementation
    hypotheses ($d_T(\iota f, f) \le \varepsilon_{\mathrm{imp}}$,
    $|L[\iota f] - L[f]| \le \beta_L d_T(\iota f,f)$,
    $|\hat L[\iota f] - \hat L[f]| \le \beta_{\hat L} d_T(\iota f, f)$), every $f \in \mathcal H$
    satisfies $L[\iota f] - \hat L[\iota f] \le (\beta_L + \beta_{\hat L})
    \varepsilon_{\mathrm{imp}} + \Delta_0$. -/)]
theorem gap_le_of_uniform_deviation {D : Fin n → X × Y} {Δ₀ : ℝ}
    (hdev : ∀ f ∈ 𝓗, |risk L P f - empRisk L D f| ≤ Δ₀) (hβL : 0 ≤ βL) (hβLhat : 0 ≤ βLhat)
    (himp : ∀ f ∈ 𝓗, dT (ι f) f ≤ εimp)
    (hL : ∀ f ∈ 𝓗, |risk L P (ι f) - risk L P f| ≤ βL * dT (ι f) f)
    (hLhat : ∀ f ∈ 𝓗, |empRisk L D (ι f) - empRisk L D f| ≤ βLhat * dT (ι f) f)
    {f : X → ℝ} (hf : f ∈ 𝓗) :
    risk L P (ι f) - empRisk L D (ι f) ≤ (βL + βLhat) * εimp + Δ₀ := by
  have := (abs_le.mp (hL f hf)).2
  have := (abs_le.mp (hLhat f hf)).1
  have := (abs_le.mp (hdev f hf)).2
  have := mul_le_mul_of_nonneg_left (himp f hf) hβL
  have := mul_le_mul_of_nonneg_left (himp f hf) hβLhat
  linarith

/-! ### The loss class indexed by `𝓗` with the uniform-convergence topology -/

omit [MeasurableSpace X] [MeasurableSpace Y] in
@[blueprint "lem:bv-emp-rademacher-reindex"
  (statement := /-- The one-sided empirical Rademacher complexity of the class
    $\{(x,y) \mapsto f(x) : f \in \mathcal H\}$ on the labelled sample $\mathcal D$ equals
    $\hat{\mathfrak R}_S(\mathcal H)$ on the inputs $S = (x_1,\dots,x_n)$. -/)]
theorem empRademacher_eq_supIndex (D : Fin n → X × Y) :
    empiricalRademacherComplexity_without_abs n
        (fun h : SupIndex 𝓗 => fun z : X × Y => UniformFun.toFun h.1 z.1) D =
      empRademacher (fun i => (D i).1) 𝓗 := by
  have hsurj : Function.Surjective
      (fun h : SupIndex 𝓗 => (⟨UniformFun.toFun h.1, h.2⟩ : 𝓗)) :=
    fun g => ⟨⟨UniformFun.ofFun g.1, g.2⟩, rfl⟩
  have := empiricalRademacherComplexity_without_abs_reindex_eq_of_surjective
    (fun g : 𝓗 => fun z : X × Y => (g : X → ℝ) z.1)
    (fun h : SupIndex 𝓗 => (⟨UniformFun.toFun h.1, h.2⟩ : 𝓗)) hsurj D
  exact this

omit [MeasurableSpace X] [MeasurableSpace Y] in
@[blueprint "lem:bv-loss-rademacher"
  (statement := /-- \textbf{One-sided Rademacher complexity of the loss class.} Let
    $\mathcal H \ne \emptyset$ be pointwise bounded and $\ell : \mathbb R \times \mathcal Y \to
    \mathbb R$ be $\beta_\ell$-Lipschitz in its first argument ($\beta_\ell \ge 0$). Then on every
    sample $\mathcal D = ((x_i,y_i))_i$ with $S = (x_i)_i$,
    $$\hat{\mathfrak R}_{\mathcal D}(\ell \circ \mathcal H) \le \beta_\ell
    \hat{\mathfrak R}_S(\mathcal H) \quad\text{and}\quad
    \hat{\mathfrak R}_{\mathcal D}(-\ell \circ \mathcal H) \le \beta_\ell
    \hat{\mathfrak R}_S(\mathcal H),$$
    where $\hat{\mathfrak R}$ is the one-sided (no absolute value) empirical Rademacher
    complexity. Proof: the one-sided contraction \texttt{lem:contraction-without-abs} applied to
    $\psi(z,u) = \pm\ell(u,y)$, which is $\beta_\ell$-Lipschitz in $u$ (no vanishing condition
    at $u = 0$ is needed). -/)]
theorem empiricalRademacherComplexity_without_abs_lossClass_le (hβ : 0 ≤ L.β)
    (h𝓗ne : 𝓗.Nonempty) (h𝓗b : ∀ x, ∃ M : ℝ, ∀ f ∈ 𝓗, |f x| ≤ M) (D : Fin n → X × Y) :
    empiricalRademacherComplexity_without_abs n (lossClass L 𝓗) D ≤
        L.β * empRademacher (fun i => (D i).1) 𝓗 ∧
      empiricalRademacherComplexity_without_abs n (fun h z => -lossClass L 𝓗 h z) D ≤
        L.β * empRademacher (fun i => (D i).1) 𝓗 := by
  haveI : Nonempty (SupIndex 𝓗) := h𝓗ne.elim fun f hf => ⟨⟨UniformFun.ofFun f, hf⟩⟩
  set F' : SupIndex 𝓗 → X × Y → ℝ := fun h z => UniformFun.toFun h.1 z.1 with hF'
  -- uniform bound of `𝓗` on the sample
  choose M hM using h𝓗b
  set b' : ℝ := ∑ k : Fin n, |M (D k).1| with hb'
  have hb'0 : 0 ≤ b' := Finset.sum_nonneg fun k _ => abs_nonneg _
  have hF'b : ∀ (h : SupIndex 𝓗) (k : Fin n), |F' h (D k)| ≤ b' := by
    intro h k
    refine ((hM _ _ h.2).trans (le_abs_self _)).trans ?_
    exact Finset.single_le_sum (f := fun k : Fin n => |M (D k).1|)
      (fun k _ => abs_nonneg _) (Finset.mem_univ k)
  have hR : empiricalRademacherComplexity_without_abs n F' D =
      empRademacher (fun i => (D i).1) 𝓗 := empRademacher_eq_supIndex D
  constructor
  · have := FoML.ToFoML.empiricalRademacherComplexity_without_abs_contraction n F'
      (fun z u => L.ℓ u z.2) D hβ hb'0 hF'b (fun z u v => L.lip u v z.2)
    rw [hR] at this
    exact this
  · have := FoML.ToFoML.empiricalRademacherComplexity_without_abs_contraction n F'
      (fun z u => -L.ℓ u z.2) D hβ hb'0 hF'b
      (fun z u v => by rw [neg_sub_neg, abs_sub_comm u v]; exact L.lip v u z.2)
    rw [hR] at this
    exact this

/-! ### The uniform deviation bound -/

@[blueprint "lem:bv-uniform-deviation-onesided"
  (statement := /-- \textbf{Uniform deviation for a sup-separable Lipschitz-loss class.}
    Let $n \ge 1$, $\mathcal H$ be a sup-norm separable, pointwise bounded class of measurable
    functions, $\ell : \mathbb R \times \mathcal Y \to [0,b]$ measurable and $\beta_\ell$-Lipschitz
    in its first argument ($b > 0$, $\beta_\ell \ge 0$), $\delta \in (0,1)$. Then with probability
    at least $1 - \delta$ over $\mathcal D \sim P^{\otimes n}$,
    $$\sup_{f \in \mathcal H} |L[f] - \hat L[f]| \le 2 \beta_\ell \hat{\mathfrak R}_S(\mathcal H)
    + 3 b \sqrt{\tfrac{2\log(4/\delta)}{n}}.$$
    Proof: apply the two-sided bound \texttt{lem:two-sided-tail-empirical} (one-sided
    symmetrization for $\ell\circ\mathcal H$ and $-\ell\circ\mathcal H$) with
    $C(\mathcal D) = \beta_\ell \hat{\mathfrak R}_S(\mathcal H)$ from
    \texttt{lem:bv-loss-rademacher} and $\varepsilon = b\sqrt{2\log(4/\delta)/n}$, so that
    $4\exp(-n\varepsilon^2/(2b^2)) = \delta$; the topology on $\mathcal H$ is the
    uniform-convergence topology, which is separable and first countable by
    \texttt{lem:sup-dense-separableSpace}, and evaluations are continuous. -/)]
theorem uniform_deviation_bound (hn : 0 < n) (hℓ : Measurable (Function.uncurry L.ℓ))
    (hb : 0 < L.b) (hβ : 0 ≤ L.β) (h𝓗 : ∀ f ∈ 𝓗, Measurable f) (hsep : IsSupSeparable 𝓗)
    (h𝓗b : ∀ x, ∃ M : ℝ, ∀ f ∈ 𝓗, |f x| ≤ M) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ((Measure.pi fun _ : Fin n => P) {D | ¬ ∀ f ∈ 𝓗,
        |risk L P f - empRisk L D f| ≤
          2 * L.β * empRademacher (fun i => (D i).1) 𝓗
            + 3 * L.b * Real.sqrt (2 * Real.log (4 / δ) / n)}).toReal ≤ δ := by
  rcases 𝓗.eq_empty_or_nonempty with h𝓗e | h𝓗ne
  · subst h𝓗e
    simp only [Set.mem_empty_iff_false, IsEmpty.forall_iff, implies_true, not_true_eq_false,
      Set.setOf_false, measure_empty, ENNReal.toReal_zero]
    exact hδ.le
  obtain ⟨Dn, hDc, -, hDd⟩ := hsep
  haveI : Nonempty (SupIndex 𝓗) := h𝓗ne.elim fun f hf => ⟨⟨UniformFun.ofFun f, hf⟩⟩
  haveI : TopologicalSpace.SeparableSpace (SupIndex 𝓗) :=
    FoML.ToMathlib.separableSpace_preimage_toFun_of_sup_dense hDc hDd
  haveI : Nonempty (X × Y) := nonempty_of_isProbabilityMeasure P
  set G := lossClass L 𝓗 with hG
  have hGmeas : ∀ h : SupIndex 𝓗, Measurable (G h) := fun h =>
    hℓ.comp (((h𝓗 _ h.2).comp measurable_fst).prodMk measurable_snd)
  have hGb : ∀ (h : SupIndex 𝓗) (z : X × Y), |G h z| ≤ L.b := fun h z => by
    change |L.ℓ (UniformFun.toFun h.1 z.1) z.2| ≤ L.b
    rw [abs_of_nonneg (L.nonneg _ _)]; exact L.le_b _ _
  have hlip : ∀ y : Y, LipschitzWith (Real.toNNReal L.β) fun u : ℝ => L.ℓ u y := fun y =>
    LipschitzWith.of_dist_le_mul fun u v => by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hβ]; exact L.lip u v y
  have hGcont : ∀ z : X × Y, Continuous fun h : SupIndex 𝓗 => G h z := fun z =>
    (hlip z.2).continuous.comp
      ((FoML.ToMathlib.continuous_toFun_apply (β := ℝ) z.1).comp continuous_subtype_val)
  set C : (Fin n → X × Y) → ℝ := fun D => L.β * empRademacher (fun i => (D i).1) 𝓗 with hC
  have hC1 : ∀ D : Fin n → X × Y, empiricalRademacherComplexity_without_abs n G D ≤ C D :=
    fun D => (empiricalRademacherComplexity_without_abs_lossClass_le L hβ h𝓗ne h𝓗b D).1
  have hC2 : ∀ D : Fin n → X × Y,
      empiricalRademacherComplexity_without_abs n (fun h z => -G h z) D ≤ C D :=
    fun D => (empiricalRademacherComplexity_without_abs_lossClass_le L hβ h𝓗ne h𝓗b D).2
  set ε : ℝ := L.b * Real.sqrt (2 * Real.log (4 / δ) / n) with hε
  have hε0 : 0 ≤ ε := by positivity
  have htail := FoML.ToFoML.twoSided_deviation_tail_bound_separable_of_sample_empirical_le (μ := P)
    hn G hGmeas id measurable_id C hb hGb hGcont hC1 hC2 hε0
  have hδ' : 4 * (-ε ^ 2 * n / (2 * L.b ^ 2)).exp = δ :=
    mul_exp_neg_confidenceRadius_sq hn (κ := 4) (b := L.b) (δ := δ) (by norm_num) hb hδ
      (by linarith)
  rw [hδ'] at htail
  refine le_trans ?_ htail
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun D hD => ?_)
  simp only [Set.mem_setOf_eq, not_forall, not_le] at hD
  obtain ⟨f, hf, hfD⟩ := hD
  refine ⟨⟨UniformFun.ofFun f, hf⟩, ?_⟩
  have hemp : (n : ℝ)⁻¹ * ∑ k : Fin n, L.ℓ (f (D k).1) (D k).2 = empRisk L D f := by
    unfold empRisk; rw [one_div]
  have h1 : 2 * C D + 3 * ε = 2 * L.β * empRademacher (fun i => (D i).1) 𝓗
      + 3 * L.b * Real.sqrt (2 * Real.log (4 / δ) / n) := by
    simp only [hC, hε]; ring
  change 2 * C D + 3 * ε < |risk L P f - (n : ℝ)⁻¹ * ∑ k : Fin n, L.ℓ (f (D k).1) (D k).2|
  rw [hemp, h1]
  exact hfD

/-! ### Main theorems -/

set_option linter.unusedVariables false in
@[blueprint "thm:bv-general"
  (statement := /-- \textbf{General bias--variance decomposition (excess risk).}
    Let $\mathcal H$ be a sup-norm separable, pointwise bounded class of measurable functions
    $\mathcal X \to \mathbb R$, $\mathcal C$ a nonempty class of measurable benchmark functions,
    and $\ell : \mathbb R \times \mathcal Y \to [0,b]$ measurable and $\beta_\ell$-Lipschitz in
    its first argument ($b > 0$, $\beta_\ell \ge 0$). Let $\iota$ be an implementation map, $d_T$
    a nonnegative function (pseudo-metric) and assume, for constants
    $\beta_L, \beta_{\hat L} \ge 0$ and $\varepsilon_{\mathrm{imp}} \ge 0$ (any upper bound for
    $\sup_{f\in\mathcal H} d_T(\iota f, f)$),
    that for every $f \in \mathcal H$: $d_T(\iota f, f) \le \varepsilon_{\mathrm{imp}}$,
    $|L[\iota f] - L[f]| \le \beta_L d_T(\iota f, f)$ and
    $|\hat L[\iota f] - \hat L[f]| \le \beta_{\hat L} d_T(\iota f, f)$ for every sample.
    Let $n \ge 1$, $\eta \ge 0$ and $\delta \in (0,1)$. Then with probability at least $1 - \delta$
    over $\mathcal D \sim P^{\otimes n}$, every $\eta$-empirical minimizer $\hat f \in \mathcal H$
    satisfies, with $\hat h := \iota(\hat f)$,
    $$L[\hat h] - \inf_{c \in \mathcal C} L[c] \le \beta_L \varepsilon_{\mathrm{imp}}
    + \varepsilon_{\mathrm{model}} + \eta + 4 \beta_\ell \hat{\mathfrak R}_S(\mathcal H)
    + 6 b \sqrt{\tfrac{2 \log(4/\delta)}{n}}.$$
    The Rademacher constant $4\beta_\ell$ is the paper's; the deviation constant is explicit
    ($C b\sqrt{\log(1/\delta)/n}$ in the paper, with unspecified universal $C$, becomes
    $6b\sqrt{2\log(4/\delta)/n}$, from \texttt{lem:bv-uniform-deviation-onesided}). The
    pointwise boundedness of $\mathcal H$ makes $\hat{\mathfrak R}_S(\mathcal H)$ a genuine
    supremum. -/)]
theorem bv_general (hn : 0 < n) (hℓ : Measurable (Function.uncurry L.ℓ)) (hb : 0 < L.b)
    (hβ : 0 ≤ L.β) (h𝓗 : ∀ f ∈ 𝓗, Measurable f) (hsep : IsSupSeparable 𝓗)
    (h𝓗b : ∀ x, ∃ M : ℝ, ∀ f ∈ 𝓗, |f x| ≤ M)
    (h𝒞 : 𝒞.Nonempty) (h𝒞m : ∀ c ∈ 𝒞, Measurable c)
    (hdT : ∀ f g, 0 ≤ dT f g) (hβL : 0 ≤ βL) (hβLhat : 0 ≤ βLhat) (hεimp : 0 ≤ εimp)
    (himp : ∀ f ∈ 𝓗, dT (ι f) f ≤ εimp)
    (hL : ∀ f ∈ 𝓗, |risk L P (ι f) - risk L P f| ≤ βL * dT (ι f) f)
    (hLhat : ∀ f ∈ 𝓗, ∀ D : Fin n → X × Y,
      |empRisk L D (ι f) - empRisk L D f| ≤ βLhat * dT (ι f) f)
    (hη : 0 ≤ η) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ((Measure.pi fun _ : Fin n => P) {D | ¬ ∀ fhat, IsEmpMinimizer L D 𝓗 η fhat →
        risk L P (ι fhat) - sInf (risk L P '' 𝒞) ≤
          βL * εimp + modelError L P 𝓗 𝒞 + η
            + 4 * L.β * empRademacher (fun i => (D i).1) 𝓗
            + 6 * L.b * Real.sqrt (2 * Real.log (4 / δ) / n)}).toReal ≤ δ := by
  /-- On the complement of the bad event of \texttt{lem:bv-uniform-deviation-onesided}, apply
    \texttt{lem:bv-deterministic} with $\Delta_0 = 2\beta_\ell\hat{\mathfrak R}_S(\mathcal H)
    + 3b\sqrt{2\log(4/\delta)/n}$. -/
  refine le_trans ?_ (uniform_deviation_bound P L hn hℓ hb hβ h𝓗 hsep h𝓗b hδ hδ1)
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun D hD => ?_)
  simp only [Set.mem_setOf_eq] at hD ⊢
  intro hdev
  apply hD
  intro fhat hfhat
  have := excessRisk_le_of_uniform_deviation P L ι dT (𝒞 := 𝒞) hdev hβL himp hL hfhat
  linarith

set_option linter.unusedVariables false in
@[blueprint "thm:bv-general-gap"
  (statement := /-- \textbf{General bias--variance decomposition (generalization gap).}
    Under the hypotheses of \texttt{thm:bv-general}, with probability at least $1-\delta$ over
    $\mathcal D \sim P^{\otimes n}$, \emph{every} $f \in \mathcal H$ (in particular every
    $\eta$-empirical minimizer $\hat f$) satisfies, with $h := \iota(f)$,
    $$L[h] - \hat L[h] \le (\beta_L + \beta_{\hat L}) \varepsilon_{\mathrm{imp}}
    + 2 \beta_\ell \hat{\mathfrak R}_S(\mathcal H) + 3 b \sqrt{\tfrac{2 \log(4/\delta)}{n}}.$$
    (The paper states this for the $\eta$-empirical minimizer only, with
    $2\beta_\ell\hat{\mathfrak R}_S(\mathcal H) + Cb\sqrt{\log(1/\delta)/n}$; its proof gives it
    for every $f \in \mathcal H$, which is what we state. The deviation constant is explicit, see
    \texttt{thm:bv-general}.) -/)]
theorem bv_general_gap (hn : 0 < n) (hℓ : Measurable (Function.uncurry L.ℓ)) (hb : 0 < L.b)
    (hβ : 0 ≤ L.β) (h𝓗 : ∀ f ∈ 𝓗, Measurable f) (hsep : IsSupSeparable 𝓗)
    (h𝓗b : ∀ x, ∃ M : ℝ, ∀ f ∈ 𝓗, |f x| ≤ M)
    (hdT : ∀ f g, 0 ≤ dT f g) (hβL : 0 ≤ βL) (hβLhat : 0 ≤ βLhat) (hεimp : 0 ≤ εimp)
    (himp : ∀ f ∈ 𝓗, dT (ι f) f ≤ εimp)
    (hL : ∀ f ∈ 𝓗, |risk L P (ι f) - risk L P f| ≤ βL * dT (ι f) f)
    (hLhat : ∀ f ∈ 𝓗, ∀ D : Fin n → X × Y,
      |empRisk L D (ι f) - empRisk L D f| ≤ βLhat * dT (ι f) f)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ((Measure.pi fun _ : Fin n => P) {D | ¬ ∀ f ∈ 𝓗,
        risk L P (ι f) - empRisk L D (ι f) ≤
          (βL + βLhat) * εimp + 2 * L.β * empRademacher (fun i => (D i).1) 𝓗
            + 3 * L.b * Real.sqrt (2 * Real.log (4 / δ) / n)}).toReal ≤ δ := by
  refine le_trans ?_ (uniform_deviation_bound P L hn hℓ hb hβ h𝓗 hsep h𝓗b hδ hδ1)
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun D hD => ?_)
  simp only [Set.mem_setOf_eq] at hD ⊢
  intro hdev
  apply hD
  intro f hf
  have := gap_le_of_uniform_deviation P L ι dT hdev hβL hβLhat himp hL (hLhat · · D) hf
  linarith

end General

section Specialization

variable {n : ℕ} (P : Measure (X × Y)) [IsProbabilityMeasure P] (L : BoundedLipschitzLoss Y)
  {H : Set (X → ℝ)} {F : Set (X → X)} {k : ℕ} {𝒞 : Set (X → ℝ)} (ι : (X → ℝ) → (X → ℝ))
  {εimp η δ : ℝ}

omit [MeasurableSpace X] in
@[blueprint "lem:impl-error-pointwise"
  (statement := /-- If $\varepsilon_{\mathrm{imp}} = \sup_{f \in \mathcal H} \|f - \iota f\|_\infty
    \le \varepsilon$ with $\varepsilon \ge 0$, then $|\iota f(x) - f(x)| \le \varepsilon$ for all
    $f \in \mathcal H$, $x \in \mathcal X$. -/)]
theorem abs_sub_le_of_implError_le {𝓗 : Set (X → ℝ)} (hεimp : 0 ≤ εimp)
    (himp : implError ι 𝓗 ≤ ENNReal.ofReal εimp) {f : X → ℝ} (hf : f ∈ 𝓗) (x : X) :
    |ι f x - f x| ≤ εimp := by
  have h1 : ENNReal.ofReal |f x - ι f x| ≤ implError ι 𝓗 := by
    unfold implError
    exact le_iSup₂_of_le f hf (le_iSup (fun x => ENNReal.ofReal |f x - ι f x|) x)
  rw [abs_sub_comm]
  exact (ENNReal.ofReal_le_ofReal_iff hεimp).mp (h1.trans himp)

@[blueprint "thm:bv"
  (statement := /-- \textbf{Implementation-free bias--variance decomposition.}
    Fix $k \ge 0$, $\eta \ge 0$, $n \ge 1$. Assume $\mathcal H_k = H \circ B(k,F)$ consists of
    measurable functions, is sup-norm separable and pointwise bounded, $\mathcal C$ is a nonempty
    class of measurable benchmarks, the loss $\ell : \mathbb R \times \mathcal Y \to [0,b]$ is
    measurable and
    $\beta_\ell$-Lipschitz in its first argument ($b > 0$, $\beta_\ell \ge 0$), the implementation
    map $\iota$ produces measurable functions, and
    $\varepsilon_{\mathrm{imp}}(k) = \sup_{f \in \mathcal H_k} \|f - \iota f\|_\infty
    \le \varepsilon_{\mathrm{imp}}$ for a real $\varepsilon_{\mathrm{imp}} \ge 0$.
    Then for every $\delta \in (0,1)$, with probability at least $1-\delta$ over
    $\mathcal D \sim P^{\otimes n}$, every $\eta$-empirical minimizer $\hat f \in \mathcal H_k$
    satisfies, with $\hat h := \iota(\hat f)$,
    $$L[\hat h] - \inf_{c \in \mathcal C} L[c] \le \beta_\ell \varepsilon_{\mathrm{imp}}
    + \varepsilon_{\mathrm{model}}(k) + \eta + 4 \beta_\ell \hat{\mathfrak R}_S(\mathcal H_k)
    + 6 b \sqrt{\tfrac{2\log(4/\delta)}{n}}.$$
    This is \texttt{thm:bv-general} with $d_T(f,g) = \|f - g\|_\infty$ and
    $\beta_L = \beta_{\hat L} = \beta_\ell$ (the loss is $\beta_\ell$-Lipschitz); the Rademacher
    constant $4\beta_\ell$ is the paper's and the deviation constant is explicit (as in
    \texttt{thm:bv-general}); $\mathcal H_k$ is assumed pointwise bounded. -/)]
theorem bv (hn : 0 < n) (hℓ : Measurable (Function.uncurry L.ℓ)) (hb : 0 < L.b) (hβ : 0 ≤ L.β)
    (h𝓗 : ∀ f ∈ hypothesisClass H F k, Measurable f)
    (hsep : IsSupSeparable (hypothesisClass H F k))
    (h𝓗b : ∀ x, ∃ M : ℝ, ∀ f ∈ hypothesisClass H F k, |f x| ≤ M)
    (h𝒞 : 𝒞.Nonempty) (h𝒞m : ∀ c ∈ 𝒞, Measurable c)
    (hι : ∀ f ∈ hypothesisClass H F k, Measurable (ι f))
    (hεimp : 0 ≤ εimp) (himp : implError ι (hypothesisClass H F k) ≤ ENNReal.ofReal εimp)
    (hη : 0 ≤ η) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ((Measure.pi fun _ : Fin n => P) {D | ¬ ∀ fhat,
        IsEmpMinimizer L D (hypothesisClass H F k) η fhat →
        risk L P (ι fhat) - sInf (risk L P '' 𝒞) ≤
          L.β * εimp + modelError L P (hypothesisClass H F k) 𝒞 + η
            + 4 * L.β * empRademacher (fun i => (D i).1) (hypothesisClass H F k)
            + 6 * L.b * Real.sqrt (2 * Real.log (4 / δ) / n)}).toReal ≤ δ := by
  /-- Apply the general theorem with $d_T(f,g) = \sup_x |f(x) - g(x)|$; the Lipschitz transfer
    lemmas give $\beta_L = \beta_{\hat L} = \beta_\ell$. -/
  set 𝓗k := hypothesisClass H F k with h𝓗k
  have hpt : ∀ f ∈ 𝓗k, ∀ x, |ι f x - f x| ≤ εimp :=
    fun f hf x => abs_sub_le_of_implError_le ι hεimp himp hf x
  set dT : (X → ℝ) → (X → ℝ) → ℝ := fun f g => ⨆ x, |f x - g x| with hdT_def
  have hdT0 : ∀ f g, 0 ≤ dT f g := fun f g => Real.iSup_nonneg fun x => abs_nonneg _
  have hle : ∀ f ∈ 𝓗k, ∀ x, |ι f x - f x| ≤ dT (ι f) f := fun f hf x =>
    le_ciSup ⟨εimp, by rintro _ ⟨y, rfl⟩; exact hpt f hf y⟩ x
  have himp' : ∀ f ∈ 𝓗k, dT (ι f) f ≤ εimp := fun f hf => Real.iSup_le (hpt f hf) hεimp
  exact bv_general P L ι dT hn hℓ hb hβ h𝓗 hsep h𝓗b h𝒞 h𝒞m hdT0 hβ hβ hεimp himp'
    (fun f hf => abs_risk_sub_risk_le P L hℓ hβ (hι f hf) (h𝓗 f hf) (hle f hf))
    (fun f hf D => abs_empRisk_sub_empRisk_le L hβ D (hdT0 _ _) (hle f hf)) hη hδ hδ1

@[blueprint "thm:bv-gap"
  (statement := /-- \textbf{Implementation-free generalization gap.} Under the hypotheses of
    \texttt{thm:bv}, with probability at least $1-\delta$ over $\mathcal D \sim P^{\otimes n}$,
    every $f \in \mathcal H_k$ (in particular every $\eta$-empirical minimizer) satisfies, with
    $h := \iota(f)$,
    $$L[h] - \hat L[h] \le 2 \beta_\ell \varepsilon_{\mathrm{imp}}
    + 2 \beta_\ell \hat{\mathfrak R}_S(\mathcal H_k) + 3 b \sqrt{\tfrac{2\log(4/\delta)}{n}}.$$
    (The Rademacher constant $2\beta_\ell$ is the paper's; the deviation constant is explicit,
    as in \texttt{thm:bv-general-gap}.) -/)]
theorem bv_gap (hn : 0 < n) (hℓ : Measurable (Function.uncurry L.ℓ)) (hb : 0 < L.b)
    (hβ : 0 ≤ L.β) (h𝓗 : ∀ f ∈ hypothesisClass H F k, Measurable f)
    (hsep : IsSupSeparable (hypothesisClass H F k))
    (h𝓗b : ∀ x, ∃ M : ℝ, ∀ f ∈ hypothesisClass H F k, |f x| ≤ M)
    (hι : ∀ f ∈ hypothesisClass H F k, Measurable (ι f))
    (hεimp : 0 ≤ εimp) (himp : implError ι (hypothesisClass H F k) ≤ ENNReal.ofReal εimp)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ((Measure.pi fun _ : Fin n => P) {D | ¬ ∀ f ∈ hypothesisClass H F k,
        risk L P (ι f) - empRisk L D (ι f) ≤
          2 * L.β * εimp + 2 * L.β * empRademacher (fun i => (D i).1) (hypothesisClass H F k)
            + 3 * L.b * Real.sqrt (2 * Real.log (4 / δ) / n)}).toReal ≤ δ := by
  set 𝓗k := hypothesisClass H F k with h𝓗k
  have hpt : ∀ f ∈ 𝓗k, ∀ x, |ι f x - f x| ≤ εimp :=
    fun f hf x => abs_sub_le_of_implError_le ι hεimp himp hf x
  set dT : (X → ℝ) → (X → ℝ) → ℝ := fun f g => ⨆ x, |f x - g x| with hdT_def
  have hdT0 : ∀ f g, 0 ≤ dT f g := fun f g => Real.iSup_nonneg fun x => abs_nonneg _
  have hle : ∀ f ∈ 𝓗k, ∀ x, |ι f x - f x| ≤ dT (ι f) f := fun f hf x =>
    le_ciSup ⟨εimp, by rintro _ ⟨y, rfl⟩; exact hpt f hf y⟩ x
  have himp' : ∀ f ∈ 𝓗k, dT (ι f) f ≤ εimp := fun f hf => Real.iSup_le (hpt f hf) hεimp
  have := bv_general_gap P L ι dT hn hℓ hb hβ h𝓗 hsep h𝓗b hdT0 hβ hβ hεimp himp'
    (fun f hf => abs_risk_sub_risk_le P L hℓ hβ (hι f hf) (h𝓗 f hf) (hle f hf))
    (fun f hf D => abs_empRisk_sub_empRisk_le L hβ D (hdT0 _ _) (hle f hf)) hδ hδ1
  convert this using 6
  ring_nf

end Specialization

end LeanDeepgen
