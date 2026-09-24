import Mathlib
import Architect
import FoML
import LeanDeepgen.Setting.WordBall
import LeanDeepgen.Setting.Metrics
import LeanDeepgen.Setting.Hypothesis
import LeanDeepgen.Setting.Loss
import LeanDeepgen.Setting.Rademacher
import LeanDeepgen.Growth.Exponential
import LeanDeepgen.Growth.Saturation
import LeanDeepgen.Bounds.BiasVariance
import LeanDeepgen.Bounds.HiddenOutput
import LeanDeepgen.Bounds.Variance
import LeanDeepgen.Examples.Readout

/-!
# Shared glue for the worked examples: rigorous regime propositions

The worked examples of the paper (chain of thought, App. `sec:app-cot`; unrolled solvers,
App. `sec:app-ode`) state their regime propositions informally ("`≲`, up to depth-independent
terms").  This module collects the general ingredients needed to turn them into rigorous
high-probability bounds obtained from `thm:bv` (with the identity implementation map),
`thm:hidden-decomp-depth` and the profiles:

* `lem:approx-transfer`: the paper's inequality `(eq:approx-transfer)`
  $\varepsilon_{\mathrm{model}} \le \beta_\ell \sup_{c \in \mathcal C}\inf_{f \in \mathcal H}
  \|f - c\|_\infty$ (stated with an $\varepsilon$-slack so that it applies to uniform closures);
* the linear readout class $H_R(\Phi) = \{\langle w, \Phi(\cdot)\rangle : \|w\| \le R\}$
  (`def:linear-readouts`): sub-Gaussian increments with $A_H = 1$ (`lem:linear-readouts-sg`),
  the Rademacher bound $\hat{\mathfrak R}_S(H_R(\Phi)) \le R\sup\|\Phi\|/\sqrt n$
  (`lem:linear-readouts-rademacher`, via FoML's Hilbert-predictor bound), Lipschitz and
  boundedness properties;
* the hypotheses of `thm:bv` for classes $H_R(\Phi) \circ \mathfrak F$: measurability,
  pointwise boundedness and sup-norm separability (`lem:comp-linear-readouts-separable`, from a
  countable uniformly dense subset of $\mathfrak F$, which exists when $\mathfrak F$ is finite or
  totally bounded in $d_\infty$);
* `thm:bv-id-bounds`: `thm:bv-general` with $\iota = \mathrm{id}$, a deterministic Rademacher
  bound and a bias bound plugged in;
* `lem:truncation-bias`: the truncation argument of the paper's Sec. `sec:examples-regime`
  (contractive layers, Lipschitz readouts): every element of the uniform closure of
  $H \circ \langle F\rangle$ is within $L_H c^k D_{\mathcal X}$ of $\mathcal H_k$;
* the explicit balancing depths for the EL regime with saturated variance
  ($k = \lceil \log n / (2\log(1/\theta))\rceil$ gives $\theta^k \le n^{-1/2}$,
  `lem:el-balance-depth`) and for the PL regime ($k = \lceil\sqrt n\rceil$ gives
  $1/k \le n^{-1/2}$, `lem:pl-balance-depth`).
-/

open MeasureTheory Metric
open scoped NNReal ENNReal UniformConvergence RealInnerProductSpace

namespace LeanDeepgen

/-! ### Approximation transfer -/

section ApproxTransfer

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

@[blueprint "lem:risk-nonneg"
  (statement := /-- $L[f] \ge 0$ since the loss is nonnegative. -/)]
theorem risk_nonneg (L : BoundedLipschitzLoss Y) (P : Measure (X × Y)) (f : X → ℝ) :
    0 ≤ risk L P f :=
  integral_nonneg fun _ => L.nonneg _ _

@[blueprint "lem:approx-transfer"
  (statement := /-- \textbf{(Approximation transfer, `eq:approx-transfer`.)} Let $\ell$ be
    $\beta_\ell$-Lipschitz in its first argument, $\mathcal H$ and $\mathcal C \ne \emptyset$
    classes of measurable functions, and $B \in \mathbb R$. If every $c \in \mathcal C$ is
    uniformly approximable from $\mathcal H$ within $B + \varepsilon$ for every
    $\varepsilon > 0$ (in particular if $\sup_{c \in \mathcal C}\inf_{f \in \mathcal H}
    \|f - c\|_\infty \le B$), then
    $$\varepsilon_{\mathrm{model}} = \inf_{\mathcal H} L - \inf_{\mathcal C} L
      \le \beta_\ell\, B .$$ -/)]
theorem modelError_le_of_approx (P : Measure (X × Y)) [IsProbabilityMeasure P]
    (L : BoundedLipschitzLoss Y) (hℓ : Measurable (Function.uncurry L.ℓ)) (hβ : 0 ≤ L.β)
    {𝓗 𝒞 : Set (X → ℝ)} (h𝓗 : ∀ f ∈ 𝓗, Measurable f) (h𝒞m : ∀ c ∈ 𝒞, Measurable c)
    (h𝒞 : 𝒞.Nonempty) {B : ℝ}
    (happ : ∀ c ∈ 𝒞, ∀ ε > (0 : ℝ), ∃ f ∈ 𝓗, ∀ x, |f x - c x| ≤ B + ε) :
    modelError L P 𝓗 𝒞 ≤ L.β * B := by
  /-- For $c \in \mathcal C$ and $\varepsilon > 0$ pick $f \in \mathcal H$ with
    $\|f - c\|_\infty \le B + \varepsilon$; then $\inf_{\mathcal H} L \le L[f] \le L[c] +
    \beta_\ell (B + \varepsilon)$ by `lem:risk-lipschitz`. Let $\varepsilon \to 0$ and take the
    infimum over $c$. -/
  unfold modelError
  have hbdd : BddBelow (risk L P '' 𝓗) := ⟨0, by rintro _ ⟨f, -, rfl⟩; exact risk_nonneg L P f⟩
  have key : ∀ c ∈ 𝒞, sInf (risk L P '' 𝓗) ≤ risk L P c + L.β * B := by
    intro c hc
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨f, hf, hfc⟩ := happ c hc (ε / (L.β + 1)) (by positivity)
    have h1 : sInf (risk L P '' 𝓗) ≤ risk L P f := csInf_le hbdd ⟨f, hf, rfl⟩
    have h2 := abs_risk_sub_risk_le P L hℓ hβ (h𝓗 f hf) (h𝒞m c hc) hfc
    have h3 : L.β * (ε / (L.β + 1)) ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    linarith [(abs_le.1 h2).2]
  have : sInf (risk L P '' 𝓗) - L.β * B ≤ sInf (risk L P '' 𝒞) := by
    refine le_csInf (h𝒞.image _) ?_
    rintro _ ⟨c, hc, rfl⟩
    linarith [key c hc]
  linarith

end ApproxTransfer

/-! ### The linear readout class -/

section LinearReadouts

variable {X : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

@[blueprint "lem:linear-readouts-abs-le"
  (statement := /-- For $h = \langle w, \Phi(\cdot)\rangle \in H_R(\Phi)$,
    $|h(x)| \le R\,\|\Phi(x)\|$. -/)]
theorem abs_le_of_mem_linearReadouts {Φ : X → E} {R : ℝ} {h : X → ℝ}
    (hh : h ∈ linearReadouts Φ R) (x : X) : |h x| ≤ R * ‖Φ x‖ := by
  obtain ⟨w, hw, rfl⟩ := hh
  exact (abs_real_inner_le_norm w (Φ x)).trans (mul_le_mul_of_nonneg_right hw (norm_nonneg _))

@[blueprint "lem:linear-readouts-lipschitz"
  (statement := /-- If $\Phi$ is $L_\Phi$-Lipschitz and $R \ge 0$ then every
    $h \in H_R(\Phi)$ is $R L_\Phi$-Lipschitz. -/)]
theorem lipschitzWith_of_mem_linearReadouts [PseudoMetricSpace X] {Φ : X → E} {LΦ : ℝ≥0}
    (hΦ : LipschitzWith LΦ Φ) {R : ℝ} (hR : 0 ≤ R) {h : X → ℝ} (hh : h ∈ linearReadouts Φ R) :
    LipschitzWith (R.toNNReal * LΦ) h := by
  obtain ⟨w, hw, rfl⟩ := hh
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, ← inner_sub_right, NNReal.coe_mul, Real.coe_toNNReal _ hR]
  calc |⟪w, Φ x - Φ y⟫| ≤ ‖w‖ * ‖Φ x - Φ y‖ := abs_real_inner_le_norm _ _
    _ ≤ R * (LΦ * dist x y) := by
        gcongr
        rw [← dist_eq_norm]
        exact hΦ.dist_le_mul x y
    _ = R * LΦ * dist x y := by ring

@[blueprint "lem:linear-readouts-eq-hilbert-smul"
  (statement := /-- For $R > 0$, $H_R(\Phi) = H_1(R\,\Phi)$: the radius can be absorbed into the
    feature map. -/)]
theorem linearReadouts_eq_hilbertReadoutClass_smul (Φ : X → E) {R : ℝ} (hR : 0 < R) :
    linearReadouts Φ R = hilbertReadoutClass (fun x => R • Φ x) := by
  ext h
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨R⁻¹ • w, ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR), inv_mul_le_iff₀ hR, mul_one]
      exact hw
    · funext x
      simp [real_inner_smul_left, real_inner_smul_right, hR.ne']
  · rintro ⟨w, hw, rfl⟩
    refine ⟨R • w, ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR]
      nlinarith [norm_nonneg w]
    · funext x
      simp only [real_inner_smul_left, real_inner_smul_right]

@[blueprint "lem:linear-readouts-sg"
  (statement := /-- (`prop:hilbert-sg` for the radius-$R$ class.) If $\Phi$ is
    $L_\Phi$-Lipschitz and $R > 0$, then $H_R(\Phi)$ satisfies the sub-Gaussian increment
    condition `ass:sg-increment-main` with $A_H = 1$ and $L = R L_\Phi$, for every hidden-layer
    class $\mathfrak F$. -/)]
theorem linearReadouts_sg [PseudoMetricSpace X] {n : ℕ} (S : Fin n → X) (Φ : X → E)
    {LΦ : ℝ≥0} (hΦ : LipschitzWith LΦ Φ) {R : ℝ} (hR : 0 < R) (𝔉 : Set (X → X)) :
    SubGaussianIncrements S (linearReadouts Φ R) 𝔉 1 ((R.toNNReal * LΦ : ℝ≥0) : ℝ) := by
  /-- $H_R(\Phi) = H_1(R\Phi)$ and $R\Phi$ is $RL_\Phi$-Lipschitz. -/
  rw [linearReadouts_eq_hilbertReadoutClass_smul Φ hR]
  refine hilbert_sg (E := E) S (fun x => R • Φ x) (L := R.toNNReal * LΦ) ?_ 𝔉
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hR, NNReal.coe_mul,
    Real.coe_toNNReal _ hR.le, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hR.le
  rw [← dist_eq_norm]
  exact hΦ.dist_le_mul x y

@[blueprint "lem:bdd-rademacher-of-bound"
  (statement := /-- If $|g(x)| \le C$ for all $g \in G$ and $x$ ($C \ge 0$), then the Rademacher
    averages $\{\frac1n\sum_i \sigma_i g(x_i) : g \in G\}$ are bounded above by $C$, for every
    sample and sign pattern. -/)]
theorem bddAbove_range_normalizedRademacherSum_of_bound {G : Set (X → ℝ)} {n : ℕ}
    (S : Fin n → X) {C : ℝ} (hC : 0 ≤ C) (hG : ∀ g ∈ G, ∀ x, |g x| ≤ C) (σ : Signs n) :
    BddAbove (Set.range fun g : G =>
      normalizedRademacherSum n (fun g : G => (g : X → ℝ)) S σ g) := by
  refine ⟨C, ?_⟩
  rintro _ ⟨g, rfl⟩
  exact (le_abs_self _).trans
    (FoML.ToFoML.abs_normalizedRademacherSum_le_of_bound (fun g : G => (g : X → ℝ)) S hC
      (fun g k => hG g g.2 _) σ g)

@[blueprint "lem:linear-readouts-rademacher"
  (statement := /-- \textbf{(Rademacher complexity of the linear readout class.)} If
    $\|\Phi(x)\| \le M$ for all $x$ ($R, M \ge 0$), then for every sample $S$ of size $n$,
    $$\hat{\mathfrak R}_S(H_R(\Phi)) \le \frac{R\,M}{\sqrt n} .$$
    (Proof: $\hat{\mathfrak R}_S(H_R(\Phi)) \le R\,\mathbb E_\sigma\|n^{-1}\sum_i\sigma_i
    \Phi(x_i)\| \le R\sqrt{\sum_i\|\Phi(x_i)\|^2}/n \le RM/\sqrt n$, via FoML's
    \texttt{hilbertPredictor\_empiricalRademacherComplexity\_le}.) -/)]
theorem empRademacher_linearReadouts_le {n : ℕ} (S : Fin n → X) (Φ : X → E) {R M : ℝ}
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hΦ : ∀ x, ‖Φ x‖ ≤ M) :
    empRademacher S (linearReadouts Φ R) ≤ R * M / Real.sqrt n := by
  have hb : ∀ g ∈ linearReadouts Φ R, ∀ i, |g (S i)| ≤ R * M := fun g hg i =>
    (abs_le_of_mem_linearReadouts hg _).trans (mul_le_mul_of_nonneg_left (hΦ _) hR)
  refine (empRademacher_le_abs (by positivity) hb).trans ?_
  haveI : Nonempty (Metric.closedBall (0 : E) R) := (Metric.nonempty_closedBall.mpr hR).to_subtype
  let e : Metric.closedBall (0 : E) R → linearReadouts Φ R := fun w =>
    ⟨fun x => ⟪(w : E), Φ x⟫, w, mem_closedBall_zero_iff.1 w.2, rfl⟩
  have he : Function.Surjective e := by
    rintro ⟨g, w, hw, rfl⟩
    exact ⟨⟨w, mem_closedBall_zero_iff.2 hw⟩, rfl⟩
  have hre := empiricalRademacherComplexity_reindex_eq_of_surjective
    (fun g : linearReadouts Φ R => (g : X → ℝ)) e he S
  rw [← hre]
  have hfoml := hilbertPredictor_empiricalRademacherComplexity_le (H := E) R hR (Φ ∘ S)
  refine hfoml.trans ?_
  have hsum : ∑ k : Fin n, ‖Φ (S k)‖ ^ 2 ≤ n * M ^ 2 := by
    calc ∑ k : Fin n, ‖Φ (S k)‖ ^ 2 ≤ ∑ _k : Fin n, M ^ 2 :=
          Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _) (hΦ _) 2
      _ = n * M ^ 2 := by simp
  have hsqrt : Real.sqrt (∑ k : Fin n, ‖Φ (S k)‖ ^ 2) ≤ Real.sqrt n * M := by
    rw [← Real.sqrt_sq hM, ← Real.sqrt_mul (Nat.cast_nonneg n)]
    exact Real.sqrt_le_sqrt hsum
  calc R * (n : ℝ)⁻¹ * Real.sqrt (∑ k : Fin n, ‖(Φ ∘ S) k‖ ^ 2)
      ≤ R * (n : ℝ)⁻¹ * (Real.sqrt n * M) := by
        gcongr
        exact hsqrt
    _ = R * M / Real.sqrt n := by
        rcases Nat.eq_zero_or_pos n with hn | hn
        · subst hn; simp
        · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
          have hs : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 hn'
          have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn'.le
          have h2 : (n : ℝ)⁻¹ * Real.sqrt n = (Real.sqrt n)⁻¹ := by
            rw [inv_eq_one_div, inv_eq_one_div, eq_div_iff hs.ne', mul_assoc, hsq,
              one_div_mul_cancel hn'.ne']
          calc R * (n : ℝ)⁻¹ * (Real.sqrt n * M) = R * M * ((n : ℝ)⁻¹ * Real.sqrt n) := by ring
            _ = R * M / Real.sqrt n := by rw [h2, div_eq_mul_inv]

end LinearReadouts

/-! ### Finiteness of word balls -/

@[blueprint "lem:wordball-finite"
  (statement := /-- If $F$ is finite then every word ball $B(k,F)$ is finite. -/)]
theorem wordBall_finite {X : Type*} {F : Set (X → X)} (hF : F.Finite) (k : ℕ) :
    (wordBall F k).Finite := by
  induction k with
  | zero => exact Set.finite_singleton _
  | succ k ih => exact ih.union (hF.image2 _ ih)

/-! ### Hypotheses of `thm:bv` for `H_R(Φ) ∘ 𝔉` -/

section CompClass

variable {X : Type*} [PseudoMetricSpace X] {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]

@[blueprint "lem:comp-linear-readouts-measurable"
  (statement := /-- If $\Phi$ is continuous and every $f \in \mathfrak F$ is continuous, then
    every element of $H_R(\Phi) \circ \mathfrak F$ is (Borel) measurable. -/)]
theorem measurable_of_mem_compClass_linearReadouts [MeasurableSpace X] [OpensMeasurableSpace X]
    {Φ : X → E} (hΦ : Continuous Φ) {R : ℝ} {𝔉 : Set (X → X)} (h𝔉 : ∀ f ∈ 𝔉, Continuous f)
    {g : X → ℝ} (hg : g ∈ compClass (linearReadouts Φ R) 𝔉) : Measurable g := by
  obtain ⟨h, ⟨w, -, rfl⟩, f, hf, rfl⟩ := hg
  exact ((continuous_const.inner hΦ).comp (h𝔉 f hf)).measurable

omit [PseudoMetricSpace X] in
@[blueprint "lem:comp-linear-readouts-bounded"
  (statement := /-- If $\|\Phi\| \le M$ and $R \ge 0$ then $|g(x)| \le RM$ for every
    $g \in H_R(\Phi) \circ \mathfrak F$ and every $x$. -/)]
theorem abs_le_of_mem_compClass_linearReadouts {Φ : X → E} {M : ℝ} (hΦ : ∀ x, ‖Φ x‖ ≤ M)
    {R : ℝ} (hR : 0 ≤ R) {𝔉 : Set (X → X)} {g : X → ℝ}
    (hg : g ∈ compClass (linearReadouts Φ R) 𝔉) (x : X) : |g x| ≤ R * M := by
  obtain ⟨h, hh, f, hf, rfl⟩ := hg
  exact (abs_le_of_mem_linearReadouts hh _).trans (mul_le_mul_of_nonneg_left (hΦ _) hR)

@[blueprint "def:countable-uniform-dense"
  (statement := /-- A hidden-layer class $\mathfrak F$ has a countable uniformly dense subset
    if there is a countable $D \subseteq \mathfrak F$ such that every $f \in \mathfrak F$ is
    within uniform distance $\varepsilon$ of some $g \in D$, for every $\varepsilon > 0$. -/)]
def HasCountableUniformDense (𝔉 : Set (X → X)) : Prop :=
  ∃ D ⊆ 𝔉, D.Countable ∧ ∀ f ∈ 𝔉, ∀ ε > (0 : ℝ), ∃ g ∈ D, ∀ x, dist (f x) (g x) ≤ ε

@[blueprint "lem:countable-dense-of-finite"
  (statement := /-- A finite hidden-layer class has a countable uniformly dense subset
    (itself). -/)]
theorem hasCountableUniformDense_of_finite {𝔉 : Set (X → X)} (h : 𝔉.Finite) :
    HasCountableUniformDense 𝔉 :=
  ⟨𝔉, subset_rfl, h.countable, fun f hf ε hε => ⟨f, hf, fun x => by simp [hε.le]⟩⟩

@[blueprint "lem:countable-dense-of-totallyBounded"
  (statement := /-- A hidden-layer class which is totally bounded in $d_\infty$ has a countable
    uniformly dense subset (it is separable in the pseudo-metrizable space
    $(\mathcal X^{\mathcal X}, d_\infty)$). -/)]
theorem hasCountableUniformDense_of_totallyBounded {𝔉 : Set (X → X)}
    (h : TotallyBounded (α := UnifMaps X) 𝔉) : HasCountableUniformDense 𝔉 := by
  obtain ⟨D, hD𝔉, hDc, hdense⟩ :=
    (TotallyBounded.isSeparable h).exists_countable_dense_subset
  refine ⟨D, hD𝔉, hDc, fun f hf ε hε => ?_⟩
  have hmem : toUnifMaps f ∈ closure (X := UnifMaps X) D := hdense hf
  obtain ⟨g, hg, hfg⟩ := EMetric.mem_closure_iff.1 hmem (ENNReal.ofReal ε)
    (ENNReal.ofReal_pos.2 hε)
  refine ⟨g, hg, fun x => ?_⟩
  have h1 : edist (f x) (g x) ≤ ENNReal.ofReal ε :=
    (edist_le_uniformDist x).trans (by rw [← edist_toUnifMaps]; exact hfg.le)
  exact (edist_le_ofReal hε.le).1 h1

@[blueprint "lem:comp-linear-readouts-separable"
  (statement := /-- \textbf{(Sup-norm separability of $H_R(\Phi) \circ \mathfrak F$.)} Let
    $\mathcal H$ be a separable real inner product space, $\Phi : \mathcal X \to \mathcal H$ be
    $L_\Phi$-Lipschitz with $\|\Phi\| \le M$, $R \ge 0$, and let $\mathfrak F$ have a countable
    uniformly dense subset. Then $H_R(\Phi) \circ \mathfrak F$ is sup-norm separable: the
    countable set $\{\langle w, \Phi(g(\cdot))\rangle : w \in W,\ g \in D\}$, with $W$ a
    countable dense subset of the ball of radius $R$, is uniformly dense, since
    $|\langle w, \Phi(f x)\rangle - \langle w', \Phi(g x)\rangle| \le \|w - w'\| M +
    R L_\Phi\, d(f x, g x)$. -/)]
theorem isSupSeparable_compClass_linearReadouts [TopologicalSpace.SeparableSpace E]
    {Φ : X → E} {LΦ : ℝ≥0} (hΦ : LipschitzWith LΦ Φ) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x, ‖Φ x‖ ≤ M) {R : ℝ} (hR : 0 ≤ R) {𝔉 : Set (X → X)}
    (h𝔉 : HasCountableUniformDense 𝔉) :
    IsSupSeparable (compClass (linearReadouts Φ R) 𝔉) := by
  obtain ⟨D, hD𝔉, hDc, hdense⟩ := h𝔉
  obtain ⟨W, hWb, hWc, hWd⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace
      (Metric.closedBall (0 : E) R)).exists_countable_dense_subset
  refine ⟨Set.image2 (fun (w : E) (f : X → X) => fun x => ⟪w, Φ (f x)⟫) W D,
    hWc.image2 hDc _, ?_, ?_⟩
  · rintro _ ⟨w, hw, f, hf, rfl⟩
    exact ⟨_, ⟨w, mem_closedBall_zero_iff.1 (hWb hw), rfl⟩, f, hD𝔉 hf, rfl⟩
  · rintro _ ⟨h, ⟨w, hw, rfl⟩, f, hf, rfl⟩ ε hε
    obtain ⟨w', hw', hww'⟩ := Metric.mem_closure_iff.1 (hWd (mem_closedBall_zero_iff.2 hw))
      (ε / (2 * (M + 1))) (by positivity)
    obtain ⟨g, hg, hfg⟩ := hdense f hf (ε / (2 * (R * LΦ + 1))) (by positivity)
    refine ⟨_, ⟨w', hw', g, hg, rfl⟩, fun x => ?_⟩
    have hw'R : ‖w'‖ ≤ R := mem_closedBall_zero_iff.1 (hWb hw')
    have e1 : |⟪w, Φ (f x)⟫ - ⟪w', Φ (f x)⟫| ≤ ε / 2 := by
      rw [← inner_sub_left]
      refine (abs_real_inner_le_norm _ _).trans ?_
      have hd : ‖w - w'‖ ≤ ε / (2 * (M + 1)) := by rw [← dist_eq_norm]; exact hww'.le
      calc ‖w - w'‖ * ‖Φ (f x)‖ ≤ ε / (2 * (M + 1)) * M := by gcongr; exact hM _
        _ ≤ ε / 2 := by
            rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith
    have e2 : |⟪w', Φ (f x)⟫ - ⟪w', Φ (g x)⟫| ≤ ε / 2 := by
      rw [← inner_sub_right]
      refine (abs_real_inner_le_norm _ _).trans ?_
      have hd : ‖Φ (f x) - Φ (g x)‖ ≤ LΦ * (ε / (2 * (R * LΦ + 1))) := by
        rw [← dist_eq_norm]
        exact (hΦ.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left (hfg x) LΦ.coe_nonneg)
      calc ‖w'‖ * ‖Φ (f x) - Φ (g x)‖ ≤ R * (LΦ * (ε / (2 * (R * LΦ + 1)))) := by gcongr
        _ ≤ ε / 2 := by
            rw [← mul_assoc, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith [mul_nonneg hR LΦ.coe_nonneg]
    calc |⟪w, Φ (f x)⟫ - ⟪w', Φ (g x)⟫|
        ≤ |⟪w, Φ (f x)⟫ - ⟪w', Φ (f x)⟫| + |⟪w', Φ (f x)⟫ - ⟪w', Φ (g x)⟫| :=
          abs_sub_le _ _ _
      _ ≤ ε / 2 + ε / 2 := add_le_add e1 e2
      _ = ε := by ring

@[blueprint "lem:totallyBounded-empSpace-of-unifMaps"
  (statement := /-- A class which is totally bounded in $d_\infty$ is totally bounded in $d_S$
    for every sample $S$ (the identity is $1$-Lipschitz, `lem:to-emp-space-lipschitz`). -/)]
theorem totallyBounded_empSpace_of_unifMaps {n : ℕ} (S : Fin n → X) {A : Set (X → X)}
    (hA : TotallyBounded (α := UnifMaps X) A) : TotallyBounded (α := EmpSpace S) A := by
  have h := hA.image (lipschitzWith_toEmpSpace S).uniformContinuous
  have himg : toEmpSpace S '' A = A := Set.image_id' A
  rwa [himg] at h

end CompClass

/-! ### Measurability of uniform limits -/

@[blueprint "lem:measurable-of-mem-closure-uniform"
  (statement := /-- Every element of the uniform closure of a class of measurable functions is
    measurable (a uniform limit of measurable functions is a pointwise limit). -/)]
theorem measurable_of_mem_closure_uniformFun {X : Type*} [MeasurableSpace X]
    {𝒢 : Set (X → ℝ)} (h𝒢 : ∀ g ∈ 𝒢, Measurable g) {g : X → ℝ}
    (hg : g ∈ closure (X := X →ᵤ ℝ) 𝒢) : Measurable g := by
  have hg' : UniformFun.ofFun g ∈ closure (X := X →ᵤ ℝ) 𝒢 := hg
  obtain ⟨u, hu, hlim⟩ := (mem_closure_iff_seq_limit (X := X →ᵤ ℝ)).1 hg'
  have hpt : Filter.Tendsto (fun n x => UniformFun.toFun (u n) x) Filter.atTop (nhds g) := by
    rw [tendsto_pi_nhds]
    intro x
    exact (UniformFun.tendsto_iff_tendstoUniformly.1 hlim).tendsto_at x
  exact measurable_of_tendsto_metrizable (fun i => h𝒢 _ (hu i)) hpt

/-! ### `thm:bv` with the identity implementation and explicit bounds -/

section BVId

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

omit [MeasurableSpace X] [MeasurableSpace Y] in
@[blueprint "def:bv-dev"
  (statement := /-- The estimation-plus-deviation term of `thm:bv` (with the constants of
    `thm:bv-general`), as a function of an upper bound $B$ for
    $\hat{\mathfrak R}_S(\mathcal H)$:
    $$\mathrm{dev}_{\ell,n,\delta}(B) := 4\beta_\ell B + 6\,b\sqrt{\tfrac{2\log(4/\delta)}{n}} .$$
    (All regime propositions below are stated in terms of this quantity, so that the constants of
    `thm:bv` enter in one place only.) -/)]
noncomputable def bvDev (L : BoundedLipschitzLoss Y) (n : ℕ) (δ B : ℝ) : ℝ :=
  4 * L.β * B + 6 * L.b * Real.sqrt (2 * Real.log (4 / δ) / n)

omit [MeasurableSpace X] [MeasurableSpace Y] in
@[blueprint "lem:bv-dev-mono"
  (statement := /-- $B \mapsto \mathrm{dev}_{\ell,n,\delta}(B)$ is nondecreasing when
    $\beta_\ell \ge 0$. -/)]
theorem bvDev_mono (L : BoundedLipschitzLoss Y) (hβ : 0 ≤ L.β) (n : ℕ) (δ : ℝ) {B B' : ℝ}
    (h : B ≤ B') : bvDev L n δ B ≤ bvDev L n δ B' := by
  unfold bvDev
  have := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 4 * L.β)
  linarith

@[blueprint "thm:bv-id-bounds"
  (statement := /-- \textbf{(`thm:bv` with $\iota = \mathrm{id}$ and explicit bounds.)} Let
    $\mathcal H$ be a sup-norm separable, pointwise bounded class of measurable functions,
    $\mathcal C \ne \emptyset$ a class of measurable benchmarks, $\ell$ measurable, bounded by
    $b > 0$ and $\beta_\ell$-Lipschitz, $n \ge 1$, $\eta \ge 0$, $\delta \in (0,1)$. Suppose
    $\hat{\mathfrak R}_S(\mathcal H) \le B$ for every sample $S$ of size $n$ and
    $\varepsilon_{\mathrm{model}} \le \mathrm{bias}$. Then with probability at least $1 - \delta$
    over $\mathcal D \sim P^{\otimes n}$, every $\eta$-empirical minimizer $\hat f \in \mathcal H$
    satisfies
    $$L[\hat f] - \inf_{\mathcal C} L \le \mathrm{bias} + \eta + \mathrm{dev}_{\ell,n,\delta}(B)
      = \mathrm{bias} + \eta + 4\beta_\ell B + 6\, b\sqrt{\tfrac{2\log(4/\delta)}{n}} .$$ -/)]
theorem bv_id_of_bounds {n : ℕ} (P : Measure (X × Y)) [IsProbabilityMeasure P]
    (L : BoundedLipschitzLoss Y) {𝓗 𝒞 : Set (X → ℝ)} {η δ B bias : ℝ}
    (hn : 0 < n) (hℓ : Measurable (Function.uncurry L.ℓ)) (hb : 0 < L.b) (hβ : 0 ≤ L.β)
    (h𝓗 : ∀ f ∈ 𝓗, Measurable f) (hsep : IsSupSeparable 𝓗)
    (h𝓗b : ∀ x, ∃ M : ℝ, ∀ f ∈ 𝓗, |f x| ≤ M)
    (h𝒞 : 𝒞.Nonempty) (h𝒞m : ∀ c ∈ 𝒞, Measurable c)
    (hR : ∀ S : Fin n → X, empRademacher S 𝓗 ≤ B) (hbias : modelError L P 𝓗 𝒞 ≤ bias)
    (hη : 0 ≤ η) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ((Measure.pi fun _ : Fin n => P) {D | ¬ ∀ fhat, IsEmpMinimizer L D 𝓗 η fhat →
        risk L P fhat - sInf (risk L P '' 𝒞) ≤ bias + η + bvDev L n δ B}).toReal ≤ δ := by
  /-- `thm:bv-general` with $\iota = \mathrm{id}$, $d_T = 0$, $\varepsilon_{\mathrm{imp}} = 0$,
    then monotonicity of the bad event. -/
  have h := bv_general P L id (fun _ _ => 0) (βL := 0) (βLhat := 0) (εimp := 0) hn hℓ hb hβ h𝓗
    hsep h𝓗b h𝒞 h𝒞m (fun _ _ => le_rfl) le_rfl le_rfl le_rfl (fun _ _ => le_rfl)
    (fun f _ => by simp) (fun f _ D => by simp) hη hδ hδ1
  refine le_trans ?_ h
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun D hD => ?_)
  simp only [Set.mem_setOf_eq] at hD ⊢
  intro hall
  apply hD
  intro fhat hfhat
  have h1 := hall fhat hfhat
  simp only [id, zero_mul, zero_add] at h1
  have hR' := mul_le_mul_of_nonneg_left (hR fun i => (D i).1) (by positivity : (0 : ℝ) ≤ 4 * L.β)
  unfold bvDev
  linarith

end BVId

/-! ### The truncation argument for contractive layers -/

section Truncation

variable {X : Type*} [PseudoMetricSpace X] {H : Set (X → ℝ)} {F : Set (X → X)}

@[blueprint "lem:truncation-bias-exact"
  (statement := /-- \textbf{(Truncation, Sec. `sec:examples-regime`.)} Let every $h \in H$ be
    $L_H$-Lipschitz, every $f \in F$ be $c$-Lipschitz, and $d(x,y) \le D_{\mathcal X}$ on
    $\mathcal X$. Then every $g = h \circ w \in H \circ \langle F\rangle$ is within uniform
    distance $L_H c^k D_{\mathcal X}$ of $\mathcal H_k = H \circ B(k,F)$: if $w = w_2 \circ w_1$
    with $|w_2| = k$ then $|h(w_2(w_1 x)) - h(w_2 x)| \le L_H c^k d(w_1 x, x)$. -/)]
theorem exists_approx_of_mem_compClass_semigroupClosure {LH : ℝ≥0}
    (hH : ∀ h ∈ H, LipschitzWith LH h) {c : ℝ≥0} (hF : ∀ f ∈ F, LipschitzWith c f) {Dx : ℝ}
    (hX : ∀ x y : X, dist x y ≤ Dx) (k : ℕ) {g : X → ℝ}
    (hg : g ∈ compClass H (semigroupClosure F)) :
    ∃ f ∈ hypothesisClass H F k, ∀ x, |f x - g x| ≤ LH * (c : ℝ) ^ k * Dx := by
  obtain ⟨h, hh, w, hw, rfl⟩ := hg
  obtain ⟨m, hwm⟩ := Set.mem_iUnion.1 hw
  obtain ⟨l, -, hwl⟩ := mem_wordBall_iff.1 hwm
  rcases le_or_gt l k with hlk | hlk
  · refine ⟨h ∘ w, ⟨h, hh, w, wordBall_mono hlk (words_subset_wordBall hwl), rfl⟩, fun x => ?_⟩
    simp only [sub_self, abs_zero]
    have := hX x x
    rw [dist_self] at this
    positivity
  · obtain ⟨w₂, hw₂, w₁, hw₁, rfl⟩ := exists_comp_of_mem_words_add (n := k) (L := l - k)
      (by rwa [show k + (l - k) = l by omega])
    refine ⟨h ∘ w₂, ⟨h, hh, w₂, words_subset_wordBall hw₂, rfl⟩, fun x => ?_⟩
    simp only [Function.comp_apply]
    have hw₂l := (lipschitzWith_pow_of_mem_words hF hw₂).dist_le_mul x (w₁ x)
    rw [NNReal.coe_pow] at hw₂l
    calc |h (w₂ x) - h (w₂ (w₁ x))| ≤ LH * dist (w₂ x) (w₂ (w₁ x)) := by
          rw [← Real.dist_eq]; exact (hH h hh).dist_le_mul _ _
      _ ≤ LH * ((c : ℝ) ^ k * dist x (w₁ x)) := by gcongr
      _ ≤ LH * ((c : ℝ) ^ k * Dx) := by gcongr; exact hX _ _
      _ = LH * (c : ℝ) ^ k * Dx := by ring

@[blueprint "lem:truncation-bias"
  (statement := /-- \textbf{(Truncation for the uniform closure.)} Under the hypotheses of
    `lem:truncation-bias-exact`, every $g$ in the uniform closure
    $\overline{H \circ \langle F\rangle}^{\,d_\infty}$ satisfies, for every $\varepsilon > 0$,
    $\inf_{f \in \mathcal H_k}\|f - g\|_\infty \le L_H c^k D_{\mathcal X} + \varepsilon$. -/)]
theorem exists_approx_of_mem_closure_compClass_semigroupClosure {LH : ℝ≥0}
    (hH : ∀ h ∈ H, LipschitzWith LH h) {c : ℝ≥0} (hF : ∀ f ∈ F, LipschitzWith c f) {Dx : ℝ}
    (hX : ∀ x y : X, dist x y ≤ Dx) (k : ℕ) {g : X → ℝ}
    (hg : g ∈ closure (X := X →ᵤ ℝ) (compClass H (semigroupClosure F))) :
    ∀ ε > (0 : ℝ), ∃ f ∈ hypothesisClass H F k, ∀ x, |f x - g x| ≤ LH * (c : ℝ) ^ k * Dx + ε := by
  intro ε hε
  obtain ⟨g', hg', hgg'⟩ := EMetric.mem_closure_iff.1 hg (ENNReal.ofReal ε)
    (ENNReal.ofReal_pos.2 hε)
  obtain ⟨f, hf, hfg'⟩ := exists_approx_of_mem_compClass_semigroupClosure hH hF hX k hg'
  refine ⟨f, hf, fun x => ?_⟩
  have h1 : dist (g x) (g' x) ≤ ε := by
    have := UniformFun.edist_le.1 hgg'.le x
    exact (edist_le_ofReal hε.le).1 this
  rw [Real.dist_eq] at h1
  calc |f x - g x| ≤ |f x - g' x| + |g' x - g x| := abs_sub_le _ _ _
    _ ≤ LH * (c : ℝ) ^ k * Dx + ε := add_le_add (hfg' x) (by rwa [abs_sub_comm])

end Truncation

/-! ### The saturated entropy integral -/

section SatVinf

variable {X : Type*} [PseudoMetricSpace X]

@[blueprint "def:sat-vinf"
  (statement := /-- The depth-independent entropy integral of `cor:profile-p1`:
    $\mathsf V_\infty(F) := \int_0^{\mathrm{diam}(\mathcal X)}
    \sqrt{\log N^{\mathrm{ext}}(\overline{\langle F\rangle}, d_\infty, \varepsilon/2)}\,
    d\varepsilon$. -/)]
noncomputable def satVinf (F : Set (X → X)) : ℝ :=
  ∫ ε in (0 : ℝ)..Metric.diam (Set.univ : Set X),
    √(Real.log (externalCoveringNumber (X := UnifMaps X) (ε.toNNReal / 2)
      (closure (X := UnifMaps X) (semigroupClosure F)) : ℝ≥0∞).toReal)

@[blueprint "def:sat-integrable"
  (statement := /-- The paper's condition $\mathsf V_\infty(F) < \infty$: the majorant
    $\varepsilon \mapsto \sqrt{\log N^{\mathrm{ext}}(\overline{\langle F\rangle}, d_\infty,
    \varepsilon/2)}$ is interval-integrable on $[0, \mathrm{diam}(\mathcal X)]$. -/)]
def SatIntegrable (F : Set (X → X)) : Prop :=
  IntervalIntegrable (fun ε : ℝ => √(Real.log (externalCoveringNumber (X := UnifMaps X)
    (ε.toNNReal / 2) (closure (X := UnifMaps X) (semigroupClosure F)) : ℝ≥0∞).toReal))
    volume 0 (Metric.diam (Set.univ : Set X))

end SatVinf

/-! ### Balancing depths with saturated variance -/

@[blueprint "lem:el-balance-depth"
  (statement := /-- \textbf{(EL balance with saturated variance.)} For $0 < \theta < 1$ and
    $n \ge 1$, the depth $k := \lceil \log n / (2\log(1/\theta))\rceil$ satisfies
    $\theta^k \le n^{-1/2}$: the bias $\theta^k$ is balanced against the saturated variance
    $n^{-1/2}$, and $k = \frac{\log n}{2\log(1/\theta)} + O(1)$. -/)]
theorem pow_ceil_log_div_le_one_div_sqrt {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {n : ℝ}
    (hn : 1 ≤ n) : θ ^ ⌈Real.log n / (2 * Real.log (1 / θ))⌉₊ ≤ 1 / Real.sqrt n := by
  /-- $k \log(1/\theta) \ge \tfrac12\log n = \log\sqrt n$, so $(1/\theta)^k \ge \sqrt n$. -/
  set k := ⌈Real.log n / (2 * Real.log (1 / θ))⌉₊
  have hb : 0 < Real.log (1 / θ) := Real.log_pos (one_lt_one_div hθ0 hθ1)
  have hn0 : 0 < n := by linarith
  have hk : Real.log n / (2 * Real.log (1 / θ)) ≤ k := Nat.le_ceil _
  rw [div_le_iff₀ (by positivity)] at hk
  have h1 : Real.sqrt n ≤ (1 / θ) ^ k := by
    rw [← Real.log_le_log_iff (Real.sqrt_pos.2 hn0) (pow_pos (one_div_pos.2 hθ0) _),
      Real.log_sqrt hn0.le, Real.log_pow]
    linarith
  rw [show θ ^ k = 1 / (1 / θ) ^ k by rw [one_div_pow, one_div_one_div]]
  exact one_div_le_one_div_of_le (Real.sqrt_pos.2 hn0) h1

@[blueprint "lem:pl-balance-depth"
  (statement := /-- \textbf{(PL balance with saturated variance, $p = 1$.)} For $n \ge 1$ the
    depth $k := \lceil\sqrt n\rceil \ge 1$ satisfies $1/k \le n^{-1/2}$: the bias $k^{-1}$ is
    balanced against the saturated variance $n^{-1/2}$, and $k \asymp n^{1/2}$. -/)]
theorem one_div_ceil_sqrt_le {n : ℝ} (hn : 1 ≤ n) :
    1 ≤ ⌈Real.sqrt n⌉₊ ∧ (1 : ℝ) / ⌈Real.sqrt n⌉₊ ≤ 1 / Real.sqrt n := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
  exact ⟨Nat.ceil_pos.2 hs, one_div_le_one_div_of_le hs (Nat.le_ceil _)⟩

end LeanDeepgen
