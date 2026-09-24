import Mathlib
import Architect
import LeanDeepgen.Setting.WordBall
import LeanDeepgen.Setting.Metrics
import LeanDeepgen.Setting.Covering
import LeanDeepgen.Growth.Lemmas
import LeanDeepgen.Growth.ArzelaAscoli
import LeanDeepgen.Growth.Saturation
import LeanDeepgen.Profiles.Profiles
import LeanDeepgen.Bounds.Variance
import LeanDeepgen.Examples.ChainOfThought
import LeanDeepgen.Examples.Regimes

/-!
# Worked example: unrolled iterative solvers and samplers (paper App. `sec:app-ode`)

The state space is a compact convex set `K` of a real inner product space `E`, used as the
subtype `↥K`. The Euclidean projection `Π_K` is not available in Mathlib as a packaged map, so
we *assume* a map `proj : E → E` with `proj x ∈ K`, `proj x = x` on `K` and `LipschitzWith 1 proj`
(`IsProjectionOnto`, `def:ode-projection`).

* Gradient steps `T_s x = Π_K(x + h s(x))` (`def:ode-grad-step`) and the contraction lemma
  `lem:fp-contraction`: if `s` is strongly monotone (`μ`) and satisfies the co-coercivity
  inequality of `μ`-strongly concave `Λ`-smooth gradients, then `T_s` is `(1 - hμ)`-Lipschitz
  for `0 < h ≤ 2/(μ+Λ)`. Consequences: the fixed-point class `F_fp` is non-expanding
  (`lem:fp-class-nonexpanding`), saturation via P1 (`lem:fp-saturation`), the explicit P1'
  entropy bound (`lem:fp-entropy-explicit`) and the saturated profile (`lem:fp-profile`).
* Euler layers `Π_K(x + h s(x,τ))` (`def:ode-euler-layer`) are `(1 + hΛ_s)`-Lipschitz
  (`lem:ode-layer-lipschitz`); a scheme of `n` steps is `∏(1 + h_i Λ_s) ≤ exp(Λ_s ∑ h_i)`-Lipschitz
  (`lem:ode-scheme-lipschitz`), so the scheme classes `B_T(k)` (`def:ode-scheme-ball`) are
  uniformly `exp(Λ_s T)`-Lipschitz, hence equicontinuous, totally bounded in `d_∞`, and their
  covering numbers are bounded uniformly in `k` (`lem:ode-saturation`); the entropy integral is
  bounded by the depth-independent integral of `prop:profiles`(i) (`lem:ode-saturation-profile`).

* Rigorous form of `prop:ode-fixedpoint` (EL regime): with the linear readout class
  `H_R(x) = {⟨w, x⟩ : ‖w‖ ≤ R}` on `K` and the teacher–student target class
  `cl(H_R ∘ ⟨F_fp⟩)`, the bias is at most `β_ℓ R D_K (1 - hμ)^k` (`lem:fp-bias`, truncation),
  the Rademacher complexity of `H_R ∘ B(k, F_fp)` at most `R M_K/√n + 12 R V_∞/√n`
  (`lem:fp-var`), and `thm:bv` gives the explicit high-probability bound `prop:ode-fixedpoint`;
  the depth `k = ⌈log n/(2 log(1/(1-hμ)))⌉` gives the balanced value `O(n^{-1/2})`
  (`cor:ode-fixedpoint-depth`).
* The Euler global error `lem:ode-euler-error`: one-step consistency
  `‖x(t₀+h) − x(t₀) − h s(x(t₀),t₀)‖ ≤ (Λ_s M_s + Λ_τ) h²/2` (`lem:ode-euler-local-error`, via the
  mean value inequality with a quadratic boundary) and the discrete Grönwall recursion
  `e_{i+1} ≤ (1 + hΛ_s) e_i + c h²/2` give `‖x(T) − y_k‖ ≤ C_E T²/k` with
  `C_E = (Λ_s M_s + Λ_τ) e^{Λ_s T}/2` for the explicit Euler iterates with `k` equal steps.
* Rigorous form of `prop:ode-horizon` (PL regime, `p = 1`): if the projection is inactive along
  the Euler steps (`K` is invariant under `x ↦ x + h s(x,τ)`), the equal-step scheme
  `T_{s,T/k,τ_k} ∘ ⋯ ∘ T_{s,T/k,τ_1}` coincides with the Euler iterates
  (`lem:ode-scheme-eq-euler`), the bias against the flow readouts `{⟨w, Φ_T(·)⟩}` is at most
  `β_ℓ R C_E T²/k` (`lem:ode-horizon-bias`), and `thm:bv` with `thm:hidden-decomp` on the scheme
  class gives `prop:ode-horizon`; the depth `k = ⌈√n⌉` gives the balanced value `O(n^{-1/2})`
  (`cor:ode-horizon-depth`).
-/

open scoped NNReal ENNReal UniformConvergence Topology RealInnerProductSpace
open Metric

open FoML.ToMathlib

namespace LeanDeepgen

/-! ### Empirical diameters on a compact state space -/

section EmpDiam

variable {X : Type*} [PseudoMetricSpace X]

@[blueprint "lem:ode-profile-saturation-generic"
  (statement := /-- (Saturated profile from total boundedness.) Let $\mathcal X$ be compact, let
    $G \subseteq \mathcal X^{\mathcal X}$ be totally bounded in $d_\infty$ and $A_k \subseteq G$
    for all $k$. With $N_\infty(\varepsilon) := N(\overline G, d_\infty, \varepsilon/2)
    < \infty$ and $\overline D := \mathrm{diam}(\mathcal X)$, if
    $\int_0^{\overline D}\sqrt{\log N_\infty(\varepsilon)}\,d\varepsilon < \infty$ then
    $\mathsf V(\mathrm{diam}_S(A_k), A_k) \le \int_0^{\overline D}
    \sqrt{\log N_\infty(\varepsilon)}\,d\varepsilon$ for every sample $S$ and every $k$
    (case (i) of `prop:profiles`). -/)]
theorem entropyIntegral_le_of_totallyBounded [CompactSpace X] {G : Set (X → X)}
    (hG : TotallyBounded (α := UnifMaps X) G) {A : ℕ → Set (X → X)} (hA : ∀ k, A k ⊆ G)
    {n : ℕ} (S : Fin n → X)
    (hint : IntervalIntegrable (fun ε : ℝ => √(Real.log (Metric.coveringNumber (X := UnifMaps X)
      (ε.toNNReal / 2) (closure (X := UnifMaps X) G) : ℝ≥0∞).toReal))
      MeasureTheory.volume 0 (Metric.diam (Set.univ : Set X))) (k : ℕ) :
    entropyIntegral (Y := EmpSpace S) (empDiam S (A k)) (A k) ≤
      ∫ ε in (0 : ℝ)..Metric.diam (Set.univ : Set X),
        √(Real.log (Metric.coveringNumber (X := UnifMaps X) (ε.toNNReal / 2)
          (closure (X := UnifMaps X) G) : ℝ≥0∞).toReal) := by
  /-- `prop:profiles-i` with $N(A_k, d_S, \varepsilon) \le N(A_k, d_\infty, \varepsilon)
    \le N(\overline G, d_\infty, \varepsilon/2)$ (`lem:covering-empSpace-le-unifMaps-internal` and
    Mathlib's `coveringNumber_subset_le`), which is finite since $\overline G$ is totally
    bounded, and $D_k(S) \le \mathrm{diam}(\mathcal X)$. -/
  refine profile_saturation (Y := EmpSpace S) (A := A) (D := fun k => empDiam S (A k))
    (Dbar := Metric.diam (Set.univ : Set X))
    (Ninf := fun ε => Metric.coveringNumber (X := UnifMaps X) (ε / 2) (closure (X := UnifMaps X) G))
    (fun k => empDiam_nonneg S _) (fun k => empDiam_le_diam_univ S _) (fun k ε => ?_)
    (fun ε hε => coveringNumber_ne_top_of_totallyBounded hG.closure (by positivity)) hint k
  exact (coveringNumber_empSpace_le S ε _).trans
    (coveringNumber_subset_le ((hA k).trans (subset_closure (X := UnifMaps X))))

@[blueprint "lem:ode-integrand-integrable-generic"
  (statement := /-- (Integrability of the entropy integrand from total boundedness.) Under the
    hypotheses of `lem:ode-profile-saturation-generic`, the entropy integrand
    $\varepsilon \mapsto \sqrt{\log N(A_k, d_S, \varepsilon)}$ is interval-integrable on
    $[0, \mathrm{diam}_S(A_k)]$ (it is dominated by the integrable majorant). -/)]
theorem intervalIntegrable_of_totallyBounded [CompactSpace X] {G : Set (X → X)}
    (hG : TotallyBounded (α := UnifMaps X) G) {A : ℕ → Set (X → X)} (hA : ∀ k, A k ⊆ G)
    {n : ℕ} (S : Fin n → X)
    (hint : IntervalIntegrable (fun ε : ℝ => √(Real.log (Metric.coveringNumber (X := UnifMaps X)
      (ε.toNNReal / 2) (closure (X := UnifMaps X) G) : ℝ≥0∞).toReal))
      MeasureTheory.volume 0 (Metric.diam (Set.univ : Set X))) (k : ℕ) :
    IntervalIntegrable (fun ε : ℝ => √(metricEntropy (X := EmpSpace S) ε.toNNReal (A k)))
      MeasureTheory.volume 0 (empDiam S (A k)) := by
  refine intervalIntegrable_sqrt_metricEntropy_of_le_of_le (empDiam_nonneg S _)
    (empDiam_le_diam_univ S _) hint fun ε hε => ?_
  refine Real.sqrt_le_sqrt (log_toReal_toENNReal_mono
    (coveringNumber_ne_top_of_totallyBounded hG.closure
      (div_pos (Real.toNNReal_pos.2 hε.1) two_pos)) ?_)
  exact (coveringNumber_empSpace_le S _ _).trans
    (coveringNumber_subset_le ((hA k).trans (subset_closure (X := UnifMaps X))))

end EmpDiam

/-! ### Projection and gradient steps -/

section GradStep

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

@[blueprint "def:ode-projection"
  (statement := /-- A map $\Pi_K : \mathbb R^d \to \mathbb R^d$ is a (Euclidean) projection
    onto $K$ if $\Pi_K(x) \in K$ for all $x$, $\Pi_K(x) = x$ for $x \in K$, and $\Pi_K$ is
    $1$-Lipschitz. (For a nonempty closed convex $K$ the nearest-point map has these
    properties; Mathlib provides only the existence of nearest points, so we take the
    projection and its properties as hypotheses.) -/)]
structure IsProjectionOnto (K : Set E) (proj : E → E) : Prop where
  mem : ∀ x, proj x ∈ K
  eq_of_mem : ∀ x ∈ K, proj x = x
  lipschitz : LipschitzWith 1 proj

variable {K : Set E} {proj : E → E}

@[blueprint "def:ode-grad-step"
  (statement := /-- The projected step of size $h$ along a vector field $s : K \to \mathbb R^d$:
    $T_s(x) := \Pi_K\bigl(x + h\,s(x)\bigr)$, a self-map of $K$. -/)]
def gradStep (hP : IsProjectionOnto K proj) (s : K → E) (h : ℝ) : K → K :=
  fun x => ⟨proj ((x : E) + h • s x), hP.mem _⟩

@[blueprint "lem:ode-grad-step-dist"
  (statement := /-- Since $\Pi_K$ is $1$-Lipschitz,
    $\|T_s(x) - T_s(y)\| \le \|(x - y) + h\,(s(x) - s(y))\|$. -/)]
theorem dist_gradStep_le (hP : IsProjectionOnto K proj) (s : K → E) (h : ℝ) (x y : K) :
    dist (gradStep hP s h x) (gradStep hP s h y) ≤ ‖((x : E) - y) + h • (s x - s y)‖ := by
  rw [Subtype.dist_eq]
  change dist (proj _) (proj _) ≤ _
  refine (hP.lipschitz.dist_le_mul _ _).trans ?_
  rw [NNReal.coe_one, one_mul, dist_eq_norm]
  apply le_of_eq
  congr 1
  rw [smul_sub]
  abel

@[blueprint "lem:ode-grad-step-zero"
  (statement := /-- A step of size $0$ is the identity: $T_{s,0} = \mathrm{id}$. -/)]
theorem gradStep_zero (hP : IsProjectionOnto K proj) (s : K → E) : gradStep hP s 0 = id := by
  funext x
  apply Subtype.ext
  simp [gradStep, hP.eq_of_mem _ x.2]

@[blueprint "def:fp-vector-field-class"
  (statement := /-- A vector field $s : K \to \mathbb R^d$ is \emph{$\mu$-strongly monotone
    and $\Lambda$-co-coercive} (the properties of $s = \nabla\phi$ for $\phi$
    $\mu$-strongly concave and $\Lambda$-smooth) if for all $x, y \in K$
    \[
      \langle x - y, s(x) - s(y)\rangle \le -\mu\|x-y\|^2, \qquad
      \langle x - y, s(x) - s(y)\rangle \le -\frac{\mu\Lambda}{\mu+\Lambda}\|x-y\|^2
        - \frac{1}{\mu+\Lambda}\|s(x)-s(y)\|^2 .
    \]
    (The first is the gradient characterization of strong concavity; the second is the standard
    consequence of strong concavity and smoothness. We take both as the definition.) -/)]
def StronglyConcaveSmooth (μ Λ : ℝ) (s : K → E) : Prop :=
  (∀ x y : K, ⟪(x : E) - y, s x - s y⟫ ≤ -μ * ‖(x : E) - y‖ ^ 2) ∧
  (∀ x y : K, ⟪(x : E) - y, s x - s y⟫ ≤
    -(μ * Λ / (μ + Λ)) * ‖(x : E) - y‖ ^ 2 - 1 / (μ + Λ) * ‖s x - s y‖ ^ 2)

@[blueprint "lem:fp-contraction"
  (statement := /-- \textbf{(Contraction of projected gradient steps.)} Let $0 < \mu \le
    \Lambda$, let $s$ be $\mu$-strongly monotone and $\Lambda$-co-coercive, and let
    $0 < h \le 2/(\mu+\Lambda)$. Then $T_s = \Pi_K(\cdot + h s(\cdot))$ is $\lambda$-Lipschitz
    on $K$ with $\lambda := 1 - h\mu \in [0,1)$. -/)]
theorem fp_contraction (hP : IsProjectionOnto K proj) {s : K → E} {μ Λ h : ℝ} (hμ : 0 < μ)
    (hμΛ : μ ≤ Λ) (hs : StronglyConcaveSmooth μ Λ s) (hh0 : 0 < h) (hh : h ≤ 2 / (μ + Λ)) :
    LipschitzWith (Real.toNNReal (1 - h * μ)) (gradStep hP s h) := by
  /-- Write $u = x - y$, $v = s(x) - s(y)$, $a = \|u\|$, $b = \|v\|$. Strong monotonicity and
    Cauchy–Schwarz give $\mu a \le b$. Then
    $\|u + hv\|^2 = a^2 + 2h\langle u,v\rangle + h^2 b^2
    \le a^2\bigl(1 - \tfrac{2h\mu\Lambda}{\mu+\Lambda}\bigr)
      + \bigl(h^2 - \tfrac{2h}{\mu+\Lambda}\bigr) b^2$
    and, since $h^2 - 2h/(\mu+\Lambda) \le 0$ and $b^2 \ge \mu^2 a^2$, this is at most
    $a^2\bigl(1 - \tfrac{2h\mu\Lambda}{\mu+\Lambda}\bigr)
      + \bigl(h^2 - \tfrac{2h}{\mu+\Lambda}\bigr)\mu^2 a^2 = (1 - h\mu)^2 a^2$.
    Finally $\Pi_K$ is $1$-Lipschitz. -/
  have hμΛ0 : 0 < μ + Λ := by linarith
  have h1μ : 0 ≤ 1 - h * μ := by
    have h1 : h * μ ≤ 2 / (μ + Λ) * μ := mul_le_mul_of_nonneg_right hh hμ.le
    have h2 : 2 / (μ + Λ) * μ ≤ 1 := by
      rw [div_mul_eq_mul_div, div_le_one hμΛ0]
      linarith
    linarith
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.coe_toNNReal _ h1μ, Subtype.dist_eq x y, dist_eq_norm]
  refine (dist_gradStep_le hP s h x y).trans ?_
  set u : E := (x : E) - y with hu
  set v : E := s x - s y with hv
  have hmono := hs.1 x y
  have hco := hs.2 x y
  rw [← hu, ← hv] at hmono hco
  set a := ‖u‖ with ha
  set b := ‖v‖ with hb
  have hab : μ * a ≤ b := by
    have h1 : μ * a * a ≤ b * a := by
      have h2 : -⟪u, v⟫ ≤ b * a := by
        have := abs_real_inner_le_norm u v
        rw [mul_comm] at this
        linarith [neg_abs_le ⟪u, v⟫]
      nlinarith
    rcases (norm_nonneg u).eq_or_lt with ha0 | ha0
    · rw [ha, ← ha0, mul_zero]; exact norm_nonneg _
    · exact le_of_mul_le_mul_right h1 ha0
  have hb2 : μ ^ 2 * a ^ 2 ≤ b ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hab 2
  have hc : h ^ 2 - 2 * h / (μ + Λ) ≤ 0 := by
    calc h ^ 2 - 2 * h / (μ + Λ) = h * (h - 2 / (μ + Λ)) := by ring
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hh0.le (by linarith)
  have h2h : 2 * h * ⟪u, v⟫ ≤
      2 * h * (-(μ * Λ / (μ + Λ)) * a ^ 2 - 1 / (μ + Λ) * b ^ 2) :=
    mul_le_mul_of_nonneg_left hco (by positivity)
  have h4 : (h ^ 2 - 2 * h / (μ + Λ)) * b ^ 2 ≤ (h ^ 2 - 2 * h / (μ + Λ)) * (μ ^ 2 * a ^ 2) :=
    mul_le_mul_of_nonpos_left hb2 hc
  have hid : a ^ 2 * (1 - 2 * h * μ * Λ / (μ + Λ)) +
      (h ^ 2 - 2 * h / (μ + Λ)) * (μ ^ 2 * a ^ 2) = ((1 - h * μ) * a) ^ 2 := by
    field_simp
    ring
  have hsq : ‖u + h • v‖ ^ 2 ≤ ((1 - h * μ) * a) ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hh0,
      ← ha, ← hb, ← hid]
    linear_combination h2h + h4
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg h1μ (norm_nonneg _)) two_ne_zero).1 hsq

@[blueprint "lem:ode-layer-lipschitz"
  (statement := /-- (Stability of one step.) If $s$ is $\Lambda_s$-Lipschitz and $h \ge 0$ then
    $x \mapsto \Pi_K(x + h s(x))$ is $(1 + h\Lambda_s)$-Lipschitz. -/)]
theorem lipschitzWith_gradStep_of_lipschitz (hP : IsProjectionOnto K proj) {s : K → E}
    {Λ : ℝ≥0} (hs : LipschitzWith Λ s) {h : ℝ} (hh : 0 ≤ h) :
    LipschitzWith (Real.toNNReal (1 + h * Λ)) (gradStep hP s h) := by
  /-- $\|(x-y) + h(s(x)-s(y))\| \le \|x-y\| + h\Lambda_s\|x-y\|$. -/
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.coe_toNNReal _ (by positivity)]
  refine (dist_gradStep_le hP s h x y).trans ?_
  calc ‖((x : E) - y) + h • (s x - s y)‖ ≤ ‖(x : E) - y‖ + ‖h • (s x - s y)‖ := norm_add_le _ _
    _ = dist x y + h * dist (s x) (s y) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh, ← dist_eq_norm, ← dist_eq_norm,
          Subtype.dist_eq]
    _ ≤ dist x y + h * (Λ * dist x y) := by gcongr; exact hs.dist_le_mul x y
    _ = (1 + h * Λ) * dist x y := by ring

end GradStep

/-! ### Fixed-point refinement -/

section FixedPoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {K : Set E} {proj : E → E}

@[blueprint "def:fp-class"
  (statement := /-- The fixed-point refinement class
    $F_{\rm fp} := \{T_s : x \mapsto \Pi_K(x + h s(x)) : s \in \mathcal S\}$ for a class
    $\mathcal S$ of vector fields on $K$ and a fixed step size $h$. -/)]
def fpClass (hP : IsProjectionOnto K proj) (𝒮 : Set (K → E)) (h : ℝ) : Set (K → K) :=
  (fun s => gradStep hP s h) '' 𝒮

@[blueprint "lem:fp-class-lipschitz"
  (statement := /-- Every $T \in F_{\rm fp}$ is $(1 - h\mu)$-Lipschitz, under the hypotheses of
    `lem:fp-contraction` for every $s \in \mathcal S$. -/)]
theorem lipschitzWith_of_mem_fpClass (hP : IsProjectionOnto K proj) {𝒮 : Set (K → E)}
    {μ Λ h : ℝ} (hμ : 0 < μ) (hμΛ : μ ≤ Λ) (h𝒮 : ∀ s ∈ 𝒮, StronglyConcaveSmooth μ Λ s)
    (hh0 : 0 < h) (hh : h ≤ 2 / (μ + Λ)) {T : K → K} (hT : T ∈ fpClass hP 𝒮 h) :
    LipschitzWith (Real.toNNReal (1 - h * μ)) T := by
  obtain ⟨s, hs, rfl⟩ := hT
  exact fp_contraction hP hμ hμΛ (h𝒮 s hs) hh0 hh

@[blueprint "lem:fp-class-nonexpanding"
  (statement := /-- Every $T \in F_{\rm fp}$ is non-expanding: $\mathrm{lip}\,F_{\rm fp} \le
    1 - h\mu \le 1$. -/)]
theorem lipschitzWith_one_of_mem_fpClass (hP : IsProjectionOnto K proj) {𝒮 : Set (K → E)}
    {μ Λ h : ℝ} (hμ : 0 < μ) (hμΛ : μ ≤ Λ) (h𝒮 : ∀ s ∈ 𝒮, StronglyConcaveSmooth μ Λ s)
    (hh0 : 0 < h) (hh : h ≤ 2 / (μ + Λ)) {T : K → K} (hT : T ∈ fpClass hP 𝒮 h) :
    LipschitzWith 1 T :=
  (lipschitzWith_of_mem_fpClass hP hμ hμΛ h𝒮 hh0 hh hT).weaken
    (by rw [← Real.toNNReal_one]; exact Real.toNNReal_le_toNNReal (by nlinarith))

@[blueprint "lem:fp-saturation"
  (statement := /-- \textbf{(Saturation for fixed-point refinement, `cond:p1`.)} If $K$ is
    compact then for every $\varepsilon > 0$ and every $k$,
    $N^{\mathrm{ext}}(B(k,F_{\rm fp}), d_\infty, \varepsilon) \le
    N^{\mathrm{ext}}(\overline{\langle F_{\rm fp}\rangle}, d_\infty, \varepsilon) < \infty$;
    in particular $\sup_k N^{\mathrm{ext}}(B(k,F_{\rm fp}), d_\infty, \varepsilon) < \infty$. -/)]
theorem fp_saturation (hK : IsCompact K) (hP : IsProjectionOnto K proj) {𝒮 : Set (K → E)}
    {μ Λ h : ℝ} (hμ : 0 < μ) (hμΛ : μ ≤ Λ) (h𝒮 : ∀ s ∈ 𝒮, StronglyConcaveSmooth μ Λ s)
    (hh0 : 0 < h) (hh : h ≤ 2 / (μ + Λ)) (ε : ℝ≥0) (hε : 0 < ε) (k : ℕ) :
    externalCoveringNumber (X := UnifMaps K) ε (wordBall (fpClass hP 𝒮 h) k) ≤
        externalCoveringNumber (X := UnifMaps K) ε
          (closure (X := UnifMaps K) (semigroupClosure (fpClass hP 𝒮 h))) ∧
      externalCoveringNumber (X := UnifMaps K) ε
        (closure (X := UnifMaps K) (semigroupClosure (fpClass hP 𝒮 h))) ≠ ⊤ := by
  /-- `cond:p1-2c` on the compact state space $K$ with non-expanding generators. -/
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  exact cond_p1_of_nonexpanding
    (fun _ hT => lipschitzWith_one_of_mem_fpClass hP hμ hμΛ h𝒮 hh0 hh hT) ε hε k

@[blueprint "lem:fp-entropy-explicit"
  (statement := /-- (Explicit entropy bound via `cond:p1-ucont`.) Assume moreover $h\mu < 1$
    and $K \ne \emptyset$, and let $\lambda = 1 - h\mu$,
    $m(\varepsilon) = \lceil \log_{1/\lambda}(2 D_K/\varepsilon)\rceil$ with
    $D_K = \mathrm{diam}(K)$. Then for every $\varepsilon > 0$ and every $k$ (generalizing the
    paper, which assumes $k \ge m(\varepsilon)$; see `cond:p1-ucont`),
    $$N^{\mathrm{ext}}(B(k,F_{\rm fp}), d_\infty, \varepsilon)
      \le N^{\mathrm{ext}}(K, \varepsilon/2)
      + \sum_{j < m(\varepsilon)} N^{\mathrm{ext}}(F_{\rm fp}^{\,j}, d_\infty, \varepsilon) .$$
    (In Lean the absorbing set is $K$ itself, with $L = 0$.) -/)]
theorem fp_entropy_explicit (hK : IsCompact K) (hKne : K.Nonempty) (hP : IsProjectionOnto K proj)
    {𝒮 : Set (K → E)} {μ Λ h : ℝ} (hμ : 0 < μ) (hμΛ : μ ≤ Λ)
    (h𝒮 : ∀ s ∈ 𝒮, StronglyConcaveSmooth μ Λ s) (hh0 : 0 < h) (hh : h ≤ 2 / (μ + Λ))
    (hhμ : h * μ < 1) (ε : ℝ≥0) (hε : 0 < ε) (k : ℕ) :
    externalCoveringNumber (X := UnifMaps K) ε (wordBall (fpClass hP 𝒮 h) k) ≤
      externalCoveringNumber (ε / 2) (Set.univ : Set K) +
        ∑ l ∈ Finset.range (memoryLength (Real.toNNReal (1 - h * μ)) 0 (Set.univ : Set K) ε),
          externalCoveringNumber (X := UnifMaps K) ε (words (fpClass hP 𝒮 h) l) := by
  /-- `cond:p1-ucont` with $c = 1 - h\mu \in (0,1)$, invariant set $A = K$ and bounded
    absorbing set $K$ (words of length $L = 0$). -/
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : Nonempty K := hKne.to_subtype
  have hc0 : 0 < Real.toNNReal (1 - h * μ) := Real.toNNReal_pos.2 (by linarith)
  have hc1 : Real.toNNReal (1 - h * μ) < 1 := by
    rw [← Real.toNNReal_one]
    exact (Real.toNNReal_lt_toNNReal_iff one_pos).2 (by nlinarith)
  exact cond_p1_ucont (fun _ hT => lipschitzWith_of_mem_fpClass hP hμ hμΛ h𝒮 hh0 hh hT) hc0 hc1
    Set.univ_nonempty (fun _ _ => Set.subset_univ _) (L := 0)
    isCompact_univ.isBounded (fun _ _ => Set.subset_univ _) ε hε k

@[blueprint "lem:fp-profile"
  (statement := /-- (Saturated variance profile for fixed-point refinement.) Under the
    hypotheses of `lem:fp-saturation`, with $N_\infty(\varepsilon) :=
    N(\overline{\langle F_{\rm fp}\rangle}, d_\infty, \varepsilon/2) < \infty$ and
    $D_K = \mathrm{diam}(K)$: if $\int_0^{D_K}\sqrt{\log N_\infty(\varepsilon)}\,d\varepsilon
    < \infty$ then $\mathsf V_k(S) \le \mathsf V_\infty :=
    \int_0^{D_K}\sqrt{\log N_\infty(\varepsilon)}\,d\varepsilon$ for all $k$ and all samples
    $S$ (case (i) of `prop:profiles`). -/)]
theorem fp_profile (hK : IsCompact K) (hP : IsProjectionOnto K proj) {𝒮 : Set (K → E)}
    {μ Λ h : ℝ} (hμ : 0 < μ) (hμΛ : μ ≤ Λ) (h𝒮 : ∀ s ∈ 𝒮, StronglyConcaveSmooth μ Λ s)
    (hh0 : 0 < h) (hh : h ≤ 2 / (μ + Λ)) {n : ℕ} (S : Fin n → K)
    (hint : IntervalIntegrable (fun ε : ℝ => √(Real.log (Metric.coveringNumber (X := UnifMaps K)
      (ε.toNNReal / 2) (closure (X := UnifMaps K) (semigroupClosure (fpClass hP 𝒮 h))) :
        ℝ≥0∞).toReal)) MeasureTheory.volume 0 (Metric.diam (Set.univ : Set K))) (k : ℕ) :
    entropyIntegral (Y := EmpSpace S) (empDiam S (wordBall (fpClass hP 𝒮 h) k))
        (wordBall (fpClass hP 𝒮 h) k) ≤
      ∫ ε in (0 : ℝ)..Metric.diam (Set.univ : Set K),
        √(Real.log (Metric.coveringNumber (X := UnifMaps K) (ε.toNNReal / 2)
          (closure (X := UnifMaps K) (semigroupClosure (fpClass hP 𝒮 h))) : ℝ≥0∞).toReal) := by
  /-- The non-expanding semigroup is equicontinuous, hence totally bounded in $d_\infty$
    (`thm:caa`); apply `lem:ode-profile-saturation-generic`. -/
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hG : TotallyBounded (α := UnifMaps K) (semigroupClosure (fpClass hP 𝒮 h)) :=
    totallyBounded_unifMaps_of_equicontinuous
      ((LipschitzWith.uniformEquicontinuous
        (fun g : semigroupClosure (fpClass hP 𝒮 h) => (g : K → K)) 1 fun g =>
          lipschitzWith_one_of_mem_semigroupClosure
            (fun _ hT => lipschitzWith_one_of_mem_fpClass hP hμ hμΛ h𝒮 hh0 hh hT)
            g.2).equicontinuous)
  exact entropyIntegral_le_of_totallyBounded hG (fun k => subset_semigroupClosure) S hint k

end FixedPoint

/-! ### Fixed-horizon integration: Euler schemes -/

section Euler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {K : Set E} {proj : E → E}

@[blueprint "def:ode-euler-layer"
  (statement := /-- An explicit Euler layer of step size $h$ at time stamp $\tau$ for a
    time-dependent vector field $s : K \times [0,T] \to \mathbb R^d$:
    $T_{s,h,\tau}(x) := \Pi_K\bigl(x + h\,s(x,\tau)\bigr)$. -/)]
def eulerLayer (hP : IsProjectionOnto K proj) (s : K → ℝ → E) (h τ : ℝ) : K → K :=
  gradStep hP (fun x => s x τ) h

@[blueprint "def:ode-euler-class"
  (statement := /-- The Euler layer class
    $F_T := \{T_{s,h,\tau} : s \in \mathcal S_T,\ h \in [0,h_0],\ \tau \in [0,T]\}$. -/)]
def eulerClass (hP : IsProjectionOnto K proj) (𝒮 : Set (K → ℝ → E)) (h₀ T : ℝ) : Set (K → K) :=
  {f | ∃ s ∈ 𝒮, ∃ h ∈ Set.Icc (0 : ℝ) h₀, ∃ τ ∈ Set.Icc (0 : ℝ) T, f = eulerLayer hP s h τ}

@[blueprint "lem:ode-euler-layer-lipschitz"
  (statement := /-- Each Euler layer with $h \ge 0$ and $\Lambda_s$-Lipschitz drift
    $s(\cdot,\tau)$ is $(1 + h\Lambda_s)$-Lipschitz. -/)]
theorem lipschitzWith_eulerLayer (hP : IsProjectionOnto K proj) {s : K → ℝ → E} {Λ : ℝ≥0}
    (hs : ∀ τ, LipschitzWith Λ (fun x => s x τ)) {h : ℝ} (hh : 0 ≤ h) (τ : ℝ) :
    LipschitzWith (Real.toNNReal (1 + h * Λ)) (eulerLayer hP s h τ) :=
  lipschitzWith_gradStep_of_lipschitz hP (hs τ) hh

@[blueprint "def:ode-scheme"
  (statement := /-- A scheme of $n$ steps with a single drift $s$, step sizes
    $h = (h_0, \dots, h_{n-1})$ and time stamps $\tau = (\tau_0, \dots, \tau_{n-1})$ is the
    composition $T_{s,h_{n-1},\tau_{n-1}} \circ \cdots \circ T_{s,h_0,\tau_0}$ (the empty
    scheme is $\mathrm{id}$). -/)]
def scheme (hP : IsProjectionOnto K proj) (s : K → ℝ → E) :
    (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ) → K → K
  | 0, _, _ => id
  | n + 1, h, τ =>
    eulerLayer hP s (h (Fin.last n)) (τ (Fin.last n)) ∘
      scheme hP s n (fun i => h i.castSucc) (fun i => τ i.castSucc)

@[blueprint "lem:ode-scheme-mem-wordball"
  (statement := /-- A scheme of $n$ steps with drift $s \in \mathcal S_T$, step sizes in
    $[0,h_0]$ and time stamps in $[0,T]$ belongs to $B(n, F_T)$. -/)]
theorem scheme_mem_wordBall (hP : IsProjectionOnto K proj) {𝒮 : Set (K → ℝ → E)} {h₀ T : ℝ}
    {s : K → ℝ → E} (hs : s ∈ 𝒮) :
    ∀ (n : ℕ) (h τ : Fin n → ℝ), (∀ i, h i ∈ Set.Icc (0 : ℝ) h₀) → (∀ i, τ i ∈ Set.Icc (0 : ℝ) T) →
      scheme hP s n h τ ∈ wordBall (eulerClass hP 𝒮 h₀ T) n
  | 0, _, _, _, _ => by simp [scheme]
  | n + 1, h, τ, hh, hτ =>
    mem_wordBall_succ_of_mem_of_mem ⟨s, hs, _, hh _, _, hτ _, rfl⟩
      (scheme_mem_wordBall hP hs n _ _ (fun i => hh _) (fun i => hτ _))

@[blueprint "lem:ode-scheme-lipschitz"
  (statement := /-- \textbf{(Stability of schemes.)} If $s(\cdot,\tau)$ is
    $\Lambda_s$-Lipschitz for every $\tau$ and $h_i \ge 0$, then the scheme with steps
    $h_0, \dots, h_{n-1}$ is
    $\prod_i(1 + h_i\Lambda_s) \le \exp(\Lambda_s\sum_i h_i)$-Lipschitz. -/)]
theorem lipschitzWith_scheme (hP : IsProjectionOnto K proj) {s : K → ℝ → E} {Λ : ℝ≥0}
    (hs : ∀ τ, LipschitzWith Λ (fun x => s x τ)) :
    ∀ (n : ℕ) (h τ : Fin n → ℝ), (∀ i, 0 ≤ h i) →
      LipschitzWith (Real.toNNReal (Real.exp (Λ * ∑ i, h i))) (scheme hP s n h τ)
  | 0, h, τ, _ => by
    /- The empty scheme is the identity and $\exp(0) = 1$. -/
    simp only [scheme, Finset.univ_eq_empty, Finset.sum_empty, mul_zero, Real.exp_zero,
      Real.toNNReal_one]
    exact LipschitzWith.id
  | n + 1, h, τ, hh => by
    /- Induction: $(1 + h_n\Lambda_s)\exp(\Lambda_s S) \le \exp(h_n\Lambda_s)\exp(\Lambda_s S)
      = \exp(\Lambda_s(S + h_n))$ by $1 + t \le e^t$. -/
    have ih := lipschitzWith_scheme hP hs n (fun i => h i.castSucc) (fun i => τ i.castSucc)
      (fun i => hh _)
    have hl := lipschitzWith_eulerLayer hP hs (hh (Fin.last n)) (τ (Fin.last n))
    refine (hl.comp ih).weaken ?_
    rw [← Real.toNNReal_mul (add_nonneg zero_le_one (mul_nonneg (hh _) Λ.coe_nonneg)),
      Fin.sum_univ_castSucc]
    refine Real.toNNReal_le_toNNReal ?_
    set S := ∑ i : Fin n, h i.castSucc
    rw [mul_add, Real.exp_add]
    have h1 : 1 + h (Fin.last n) * Λ ≤ Real.exp (Λ * h (Fin.last n)) := by
      have := Real.add_one_le_exp (Λ * h (Fin.last n))
      linarith [mul_comm (h (Fin.last n)) (Λ : ℝ)]
    calc (1 + h (Fin.last n) * Λ) * Real.exp (Λ * S)
        ≤ Real.exp (Λ * h (Fin.last n)) * Real.exp (Λ * S) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = Real.exp (Λ * S) * Real.exp (Λ * h (Fin.last n)) := mul_comm _ _

@[blueprint "def:ode-scheme-ball"
  (statement := /-- The class $B_T(k)$ of schemes of at most $k$ steps with a single drift
    $s \in \mathcal S_T$, step sizes $h_i \in [0,h_0]$, time stamps $\tau_i \in [0,T]$ and total
    time $\sum_i h_i \le T$ (it contains $\mathrm{id}$, the empty scheme). The consistency
    condition $\tau_i = \sum_{j<i}h_j$ of the paper is dropped; the bounds below hold for
    this larger class. -/)]
def schemeBall (hP : IsProjectionOnto K proj) (𝒮 : Set (K → ℝ → E)) (h₀ T : ℝ) (k : ℕ) :
    Set (K → K) :=
  {f | ∃ s ∈ 𝒮, ∃ n, n ≤ k ∧ ∃ h τ : Fin n → ℝ, (∀ i, h i ∈ Set.Icc (0 : ℝ) h₀) ∧
    (∀ i, τ i ∈ Set.Icc (0 : ℝ) T) ∧ ∑ i, h i ≤ T ∧ f = scheme hP s n h τ}

@[blueprint "def:ode-scheme-set"
  (statement := /-- All schemes: $\bigcup_k B_T(k)$. -/)]
def schemeSet (hP : IsProjectionOnto K proj) (𝒮 : Set (K → ℝ → E)) (h₀ T : ℝ) : Set (K → K) :=
  ⋃ k, schemeBall hP 𝒮 h₀ T k

@[blueprint "lem:ode-scheme-ball-mono"
  (statement := /-- $B_T(k) \subseteq B_T(k+1)$: the scheme classes are nested. -/)]
theorem schemeBall_mono (hP : IsProjectionOnto K proj) (𝒮 : Set (K → ℝ → E)) (h₀ T : ℝ) :
    Monotone (schemeBall hP 𝒮 h₀ T) := by
  intro k l hkl f hf
  obtain ⟨s, hs, n, hn, h, τ, hh, hτ, hsum, rfl⟩ := hf
  exact ⟨s, hs, n, hn.trans hkl, h, τ, hh, hτ, hsum, rfl⟩

@[blueprint "lem:ode-scheme-ball-subset-wordball"
  (statement := /-- $B_T(k) \subseteq B(k, F_T)$. -/)]
theorem schemeBall_subset_wordBall (hP : IsProjectionOnto K proj) (𝒮 : Set (K → ℝ → E))
    (h₀ T : ℝ) (k : ℕ) : schemeBall hP 𝒮 h₀ T k ⊆ wordBall (eulerClass hP 𝒮 h₀ T) k := by
  rintro f ⟨s, hs, n, hn, h, τ, hh, hτ, -, rfl⟩
  exact wordBall_mono hn (scheme_mem_wordBall hP hs n h τ hh hτ)

@[blueprint "lem:ode-scheme-set-lipschitz"
  (statement := /-- Every scheme in $\bigcup_k B_T(k)$ is $e^{\Lambda_s T}$-Lipschitz on $K$. -/)]
theorem lipschitzWith_of_mem_schemeSet (hP : IsProjectionOnto K proj) {𝒮 : Set (K → ℝ → E)}
    {Λ : ℝ≥0} (h𝒮 : ∀ s ∈ 𝒮, ∀ τ, LipschitzWith Λ (fun x => s x τ)) {h₀ T : ℝ} {f : K → K}
    (hf : f ∈ schemeSet hP 𝒮 h₀ T) : LipschitzWith (Real.toNNReal (Real.exp (Λ * T))) f := by
  /-- `lem:ode-scheme-lipschitz` and $\sum_i h_i \le T$. -/
  obtain ⟨_, ⟨k, rfl⟩, s, hs, n, -, h, τ, hh, -, hsum, rfl⟩ := hf
  refine (lipschitzWith_scheme hP (h𝒮 s hs) n h τ fun i => (hh i).1).weaken ?_
  exact Real.toNNReal_le_toNNReal (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hsum Λ.coe_nonneg))

@[blueprint "lem:ode-saturation"
  (statement := /-- \textbf{(Stability and saturation.)} Let $K$ be compact and let every drift
    $s \in \mathcal S_T$ be $\Lambda_s$-Lipschitz in $x$. Every scheme in $\bigcup_k B_T(k)$ is
    $e^{\Lambda_sT}$-Lipschitz on $K$. Consequently $\bigcup_k B_T(k)$ is equicontinuous on the
    compact set $K$, hence totally bounded in $d_\infty$ (`thm:caa`), and
    $$\sup_k N^{\mathrm{ext}}\bigl(B_T(k), d_\infty, \varepsilon\bigr)
      \le N^{\mathrm{ext}}\Bigl(\bigcup_k B_T(k), d_\infty, \varepsilon\Bigr)
      =: N_\infty(\varepsilon)
      < \infty \quad (\varepsilon > 0).$$ -/)]
theorem ode_saturation (hK : IsCompact K) (hP : IsProjectionOnto K proj) {𝒮 : Set (K → ℝ → E)}
    {Λ : ℝ≥0} (h𝒮 : ∀ s ∈ 𝒮, ∀ τ, LipschitzWith Λ (fun x => s x τ)) (h₀ T : ℝ) :
    TotallyBounded (α := UnifMaps K) (schemeSet hP 𝒮 h₀ T) ∧
    ∀ ε : ℝ≥0, 0 < ε → ∀ k,
      externalCoveringNumber (X := UnifMaps K) ε (schemeBall hP 𝒮 h₀ T k) ≤
          externalCoveringNumber (X := UnifMaps K) ε (schemeSet hP 𝒮 h₀ T) ∧
        externalCoveringNumber (X := UnifMaps K) ε (schemeSet hP 𝒮 h₀ T) ≠ ⊤ := by
  /-- A uniformly Lipschitz family is (uniformly) equicontinuous; Arzelà–Ascoli
    (`thm:caa-of-equicontinuous`) gives total boundedness in $d_\infty$, monotonicity of the
    external covering number and `lem:aa-external-covering-ne-top` the rest. -/
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have htb : TotallyBounded (α := UnifMaps K) (schemeSet hP 𝒮 h₀ T) :=
    totallyBounded_unifMaps_of_equicontinuous
      ((LipschitzWith.uniformEquicontinuous (fun f : schemeSet hP 𝒮 h₀ T => (f : K → K)) _
        fun f => lipschitzWith_of_mem_schemeSet hP h𝒮 f.2).equicontinuous)
  exact ⟨htb, fun ε hε k => ⟨externalCoveringNumber_mono_set (Set.subset_iUnion _ k),
    externalCoveringNumber_ne_top_of_totallyBounded htb hε⟩⟩

@[blueprint "lem:ode-saturation-profile"
  (statement := /-- (Saturated variance profile for Euler schemes.) Under the hypotheses of
    `lem:ode-saturation`, with $N_\infty(\varepsilon) := N(\overline{\bigcup_k B_T(k)},
    d_\infty, \varepsilon/2) < \infty$ and $D_K = \mathrm{diam}(K)$: if
    $\int_0^{D_K}\sqrt{\log N_\infty(\varepsilon)}\,d\varepsilon < \infty$ then
    $\mathsf V_k(S) \le \mathsf V_\infty := \int_0^{D_K}\sqrt{\log N_\infty(\varepsilon)}\,
    d\varepsilon$ for all $k$ and all samples $S$ (case (i) of `prop:profiles`). -/)]
theorem ode_saturation_profile (hK : IsCompact K) (hP : IsProjectionOnto K proj)
    {𝒮 : Set (K → ℝ → E)} {Λ : ℝ≥0} (h𝒮 : ∀ s ∈ 𝒮, ∀ τ, LipschitzWith Λ (fun x => s x τ))
    (h₀ T : ℝ) {n : ℕ} (S : Fin n → K)
    (hint : IntervalIntegrable (fun ε : ℝ => √(Real.log (Metric.coveringNumber (X := UnifMaps K)
      (ε.toNNReal / 2) (closure (X := UnifMaps K) (schemeSet hP 𝒮 h₀ T)) : ℝ≥0∞).toReal))
      MeasureTheory.volume 0 (Metric.diam (Set.univ : Set K))) (k : ℕ) :
    entropyIntegral (Y := EmpSpace S) (empDiam S (schemeBall hP 𝒮 h₀ T k))
        (schemeBall hP 𝒮 h₀ T k) ≤
      ∫ ε in (0 : ℝ)..Metric.diam (Set.univ : Set K),
        √(Real.log (Metric.coveringNumber (X := UnifMaps K) (ε.toNNReal / 2)
          (closure (X := UnifMaps K) (schemeSet hP 𝒮 h₀ T)) : ℝ≥0∞).toReal) := by
  /-- `lem:ode-profile-saturation-generic` with $G = \bigcup_k B_T(k)$. -/
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  exact entropyIntegral_le_of_totallyBounded (ode_saturation hK hP h𝒮 h₀ T).1
    (fun k => Set.subset_iUnion (schemeBall hP 𝒮 h₀ T) k) S hint k

end Euler

/-! ### Fixed-point refinement in the EL regime (`prop:ode-fixedpoint`) -/

section FixedPointRegime

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {K : Set E} {proj : E → E}

@[blueprint "def:ode-feature"
  (statement := /-- The identity feature map $K \hookrightarrow \mathbb R^d$, so that
    $H_R = \{x \mapsto \langle w, x\rangle : \|w\| \le R\}$ is the linear readout class
    $H_R(\Phi)$ with $\Phi = \mathrm{id}_K$. -/)]
def ambientFeature (K : Set E) : K → E := Subtype.val

omit [InnerProductSpace ℝ E] in
@[blueprint "lem:ode-feature-lipschitz"
  (statement := /-- $\mathrm{id}_K$ is $1$-Lipschitz and continuous. -/)]
theorem lipschitzWith_ambientFeature : LipschitzWith 1 (ambientFeature K) :=
  LipschitzWith.subtype_val K

@[blueprint "def:fp-target-class"
  (statement := /-- The teacher–student target class of the fixed-point example:
    $\mathcal C := \overline{H_R \circ \langle F_{\rm fp}\rangle}^{\,d_\infty}$, which contains
    the readouts $x \mapsto \langle w, x^\ast_s\rangle$ of the fixed points (limits of the
    refinement). -/)]
def fpTargetClass (hP : IsProjectionOnto K proj) (𝒮 : Set (K → E)) (h R : ℝ) : Set (K → ℝ) :=
  closure (X := K →ᵤ ℝ)
    (compClass (linearReadouts (ambientFeature K) R) (semigroupClosure (fpClass hP 𝒮 h)))

@[blueprint "lem:fp-one-sub-nonneg"
  (statement := /-- Under the step-size condition $0 < h \le 2/(\mu+\Lambda)$ with
    $0 < \mu \le \Lambda$, $0 \le 1 - h\mu$. -/)]
theorem one_sub_mul_nonneg_of_step {μ Λ h : ℝ} (hμ : 0 < μ) (hμΛ : μ ≤ Λ) (hh : h ≤ 2 / (μ + Λ)) :
    0 ≤ 1 - h * μ := by
  have hμΛ0 : 0 < μ + Λ := by linarith
  have h1 : h * μ ≤ 2 / (μ + Λ) * μ := mul_le_mul_of_nonneg_right hh hμ.le
  have h2 : 2 / (μ + Λ) * μ ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one hμΛ0]
    linarith
  linarith

@[blueprint "lem:fp-class-continuous"
  (statement := /-- Every element of $\langle F_{\rm fp}\rangle$ is $1$-Lipschitz, hence
    continuous. -/)]
theorem continuous_of_mem_semigroupClosure_fpClass (hP : IsProjectionOnto K proj)
    {𝒮 : Set (K → E)} {μ Λ h : ℝ} (hμ : 0 < μ) (hμΛ : μ ≤ Λ)
    (h𝒮 : ∀ s ∈ 𝒮, StronglyConcaveSmooth μ Λ s) (hh0 : 0 < h) (hh : h ≤ 2 / (μ + Λ))
    {f : K → K} (hf : f ∈ semigroupClosure (fpClass hP 𝒮 h)) : Continuous f :=
  (lipschitzWith_one_of_mem_semigroupClosure
    (fun _ hT => lipschitzWith_one_of_mem_fpClass hP hμ hμΛ h𝒮 hh0 hh hT) hf).continuous

@[blueprint "lem:fp-semigroup-totallyBounded"
  (statement := /-- For compact $K$, $\langle F_{\rm fp}\rangle$ is totally bounded in
    $d_\infty$ (Arzelà–Ascoli for the non-expanding semigroup). -/)]
theorem totallyBounded_semigroupClosure_fpClass (hK : IsCompact K) (hP : IsProjectionOnto K proj)
    {𝒮 : Set (K → E)} {μ Λ h : ℝ} (hμ : 0 < μ) (hμΛ : μ ≤ Λ)
    (h𝒮 : ∀ s ∈ 𝒮, StronglyConcaveSmooth μ Λ s) (hh0 : 0 < h) (hh : h ≤ 2 / (μ + Λ)) :
    TotallyBounded (α := UnifMaps K) (semigroupClosure (fpClass hP 𝒮 h)) := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hue := LipschitzWith.uniformEquicontinuous
    (fun g : semigroupClosure (fpClass hP 𝒮 h) => (g : K → K)) 1 fun g =>
      lipschitzWith_one_of_mem_semigroupClosure
        (fun _ hT => lipschitzWith_one_of_mem_fpClass hP hμ hμΛ h𝒮 hh0 hh hT) g.2
  exact totallyBounded_unifMaps_of_equicontinuous hue.equicontinuous

@[blueprint "lem:fp-var"
  (statement := /-- \textbf{(Estimation term for fixed-point refinement.)} Let $K$ be compact
    with $\|x\| \le M_K$ on $K$, $R > 0$, and assume $\mathsf V_\infty(F_{\rm fp}) < \infty$
    (`def:sat-integrable`). Then for every sample $S$ of size $n \ge 1$ and every depth $k$,
    $$\hat{\mathfrak R}_S(H_R \circ B(k, F_{\rm fp})) \le \frac{R M_K}{\sqrt n}
      + \frac{12 \cdot 1 \cdot R}{\sqrt n}\,\mathsf V_\infty(F_{\rm fp})$$
    (`cor:var-profiles-p1` with $A_H = 1$, $L = R$, and `lem:linear-readouts-rademacher`). -/)]
theorem fp_var (hK : IsCompact K) (hP : IsProjectionOnto K proj) {𝒮 : Set (K → E)}
    {μ Λ h : ℝ} (hμ : 0 < μ) (hμΛ : μ ≤ Λ) (h𝒮 : ∀ s ∈ 𝒮, StronglyConcaveSmooth μ Λ s)
    (hh0 : 0 < h) (hh : h ≤ 2 / (μ + Λ)) {n : ℕ} (hn : 0 < n) (S : Fin n → K) {R MK : ℝ}
    (hR : 0 < R) (hMK : 0 ≤ MK) (hK' : ∀ x : K, ‖(x : E)‖ ≤ MK)
    (hint : SatIntegrable (fpClass hP 𝒮 h)) (k : ℕ) :
    empRademacher S (hypothesisClass (linearReadouts (ambientFeature K) R) (fpClass hP 𝒮 h) k) ≤
      R * MK / √n + 12 * 1 * R / √n * satVinf (fpClass hP 𝒮 h) := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have h1 : ∀ T ∈ fpClass hP 𝒮 h, LipschitzWith 1 T :=
    fun _ hT => lipschitzWith_one_of_mem_fpClass hP hμ hμΛ h𝒮 hh0 hh hT
  have hF : Equicontinuous (fun f : semigroupClosure (fpClass hP 𝒮 h) => (f : K → K)) :=
    (LipschitzWith.uniformEquicontinuous
      (fun g : semigroupClosure (fpClass hP 𝒮 h) => (g : K → K)) 1 fun g =>
        lipschitzWith_one_of_mem_semigroupClosure h1 g.2).equicontinuous
  have hcoe : ((R.toNNReal * 1 : ℝ≥0) : ℝ) = R := by
    rw [NNReal.coe_mul, Real.coe_toNNReal _ hR.le, NNReal.coe_one, mul_one]
  have hL : (0 : ℝ) < ((R.toNNReal * 1 : ℝ≥0) : ℝ) := by rw [hcoe]; exact hR
  have hv := var_profile_p1 S (linearReadouts (ambientFeature K) R) hn k (AH := 1) one_pos hL
    (fun f _ σ => bddAbove_range_normalizedRademacherSum_of_bound (f ∘ S) (by positivity)
      (fun g hg x => (abs_le_of_mem_linearReadouts hg _).trans
        (mul_le_mul_of_nonneg_left (hK' _) hR.le)) σ)
    (totallyBounded_empSpace_of_unifMaps S
      ((totallyBounded_semigroupClosure_fpClass hK hP hμ hμΛ h𝒮 hh0 hh).subset
        subset_semigroupClosure))
    (linearReadouts_sg S (ambientFeature K) lipschitzWith_ambientFeature hR _) hF hint
  refine hv.trans ?_
  rw [hcoe]
  unfold satVinf
  gcongr
  exact empRademacher_linearReadouts_le S _ hR.le hMK hK'

variable [MeasurableSpace E] [BorelSpace E]

@[blueprint "lem:fp-class-measurable"
  (statement := /-- Every element of $H_R \circ B(k, F_{\rm fp})$ is Borel measurable. -/)]
theorem fp_class_measurable (hP : IsProjectionOnto K proj) {𝒮 : Set (K → E)} {μ Λ h : ℝ}
    (hμ : 0 < μ) (hμΛ : μ ≤ Λ) (h𝒮 : ∀ s ∈ 𝒮, StronglyConcaveSmooth μ Λ s) (hh0 : 0 < h)
    (hh : h ≤ 2 / (μ + Λ)) (R : ℝ) (k : ℕ) :
    ∀ g ∈ hypothesisClass (linearReadouts (ambientFeature K) R) (fpClass hP 𝒮 h) k,
      Measurable g :=
  fun _ hg => measurable_of_mem_compClass_linearReadouts lipschitzWith_ambientFeature.continuous
    (fun _ hf => continuous_of_mem_semigroupClosure_fpClass hP hμ hμΛ h𝒮 hh0 hh
      (subset_semigroupClosure hf)) hg

@[blueprint "lem:fp-target-measurable"
  (statement := /-- Every element of the target class $\mathcal C$ is measurable. -/)]
theorem fp_target_measurable (hP : IsProjectionOnto K proj) {𝒮 : Set (K → E)} {μ Λ h : ℝ}
    (hμ : 0 < μ) (hμΛ : μ ≤ Λ) (h𝒮 : ∀ s ∈ 𝒮, StronglyConcaveSmooth μ Λ s) (hh0 : 0 < h)
    (hh : h ≤ 2 / (μ + Λ)) (R : ℝ) : ∀ c ∈ fpTargetClass hP 𝒮 h R, Measurable c :=
  fun _ hc => measurable_of_mem_closure_uniformFun
    (fun _ hg => measurable_of_mem_compClass_linearReadouts
      lipschitzWith_ambientFeature.continuous
      (fun _ hf => continuous_of_mem_semigroupClosure_fpClass hP hμ hμΛ h𝒮 hh0 hh hf) hg) hc

omit [MeasurableSpace E] [BorelSpace E] in
@[blueprint "lem:fp-target-nonempty"
  (statement := /-- $\mathcal C \ne \emptyset$ for $R \ge 0$. -/)]
theorem fp_target_nonempty (hP : IsProjectionOnto K proj) (𝒮 : Set (K → E)) (h : ℝ) {R : ℝ}
    (hR : 0 ≤ R) : (fpTargetClass hP 𝒮 h R).Nonempty :=
  ⟨_, subset_closure (X := K →ᵤ ℝ) ⟨_, ⟨0, by simpa using hR, rfl⟩, id,
    subset_semigroupClosure (id_mem_wordBall (k := 0)), rfl⟩⟩

@[blueprint "lem:fp-bias"
  (statement := /-- \textbf{(Bias for fixed-point refinement.)} Let $K$ be compact with
    $D_K = \mathrm{diam}(K)$ and $R \ge 0$. Against the teacher–student class
    $\mathcal C = \overline{H_R \circ \langle F_{\rm fp}\rangle}^{\,d_\infty}$,
    $$\mathrm{bias}(k) = \varepsilon_{\mathrm{model}}(k) \le \beta_\ell\, R\, D_K\, (1 - h\mu)^k$$
    by the truncation argument `lem:truncation-bias` ($\mathrm{lip}(h) \le R$,
    $\mathrm{lip}(u) \le (1-h\mu)^k$ for $u \in F_{\rm fp}^{\,k}$) and `lem:approx-transfer`. -/)]
theorem fp_bias {Y : Type*} [MeasurableSpace Y] (hK : IsCompact K) (hP : IsProjectionOnto K proj)
    {𝒮 : Set (K → E)} {μ Λ h : ℝ} (hμ : 0 < μ) (hμΛ : μ ≤ Λ)
    (h𝒮 : ∀ s ∈ 𝒮, StronglyConcaveSmooth μ Λ s) (hh0 : 0 < h) (hh : h ≤ 2 / (μ + Λ))
    (P : Measure (K × Y)) [IsProbabilityMeasure P] (L : BoundedLipschitzLoss Y)
    (hℓ : Measurable (Function.uncurry L.ℓ)) (hβ : 0 ≤ L.β) {R : ℝ} (hR : 0 ≤ R) (k : ℕ) :
    modelError L P (hypothesisClass (linearReadouts (ambientFeature K) R) (fpClass hP 𝒮 h) k)
        (fpTargetClass hP 𝒮 h R) ≤
      L.β * (R * Metric.diam (Set.univ : Set K) * (1 - h * μ) ^ k) := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have h1μ : 0 ≤ 1 - h * μ := one_sub_mul_nonneg_of_step hμ hμΛ hh
  refine modelError_le_of_approx P L hℓ hβ (fp_class_measurable hP hμ hμΛ h𝒮 hh0 hh R k)
    (fp_target_measurable hP hμ hμΛ h𝒮 hh0 hh R) (fp_target_nonempty hP 𝒮 h hR)
    fun c hc ε hε => ?_
  have := exists_approx_of_mem_closure_compClass_semigroupClosure
    (H := linearReadouts (ambientFeature K) R) (LH := R.toNNReal * 1)
    (fun _ hh' => lipschitzWith_of_mem_linearReadouts lipschitzWith_ambientFeature hR hh')
    (c := Real.toNNReal (1 - h * μ))
    (fun _ hT => lipschitzWith_of_mem_fpClass hP hμ hμΛ h𝒮 hh0 hh hT)
    (Dx := Metric.diam (Set.univ : Set K))
    (fun x y => Metric.dist_le_diam_of_mem isCompact_univ.isBounded (Set.mem_univ x)
      (Set.mem_univ y)) k hc ε hε
  obtain ⟨f, hf, hfc⟩ := this
  refine ⟨f, hf, fun x => (hfc x).trans (le_of_eq ?_)⟩
  rw [NNReal.coe_mul, Real.coe_toNNReal _ hR, Real.coe_toNNReal _ h1μ, NNReal.coe_one]
  ring

@[blueprint "prop:ode-fixedpoint"
  (statement := /-- \textbf{(Fixed-point refinement, rigorous form.)} Let $K \subseteq \mathbb R^d$
    (a separable Hilbert space) be compact with $\|x\| \le M_K$ on $K$ and $D_K = \mathrm{diam}(K)$,
    let $F_{\rm fp}$ be the projected gradient steps of `lem:fp-contraction` with
    $0 < h \le 2/(\mu+\Lambda)$, $H = H_R$ ($R > 0$), and let the target class be
    $\mathcal C = \overline{H_R \circ \langle F_{\rm fp}\rangle}^{\,d_\infty}$. Assume
    $\mathsf V_\infty(F_{\rm fp}) < \infty$. For a measurable loss
    $\ell : \mathbb R \times \mathcal Y \to [0,b]$, $\beta_\ell$-Lipschitz in its first
    argument, $n \ge 1$, $\eta \ge 0$, $\delta \in (0,1)$: with probability at least $1 - \delta$
    over $\mathcal D \sim P^{\otimes n}$, every $\eta$-empirical minimizer
    $\hat h \in H_R \circ B(k, F_{\rm fp})$ satisfies
    $$L[\hat h] - \inf_{\mathcal C} L \le \beta_\ell R D_K (1 - h\mu)^k + \eta
      + \mathrm{dev}_{\ell,n,\delta}\Bigl(\frac{R M_K}{\sqrt n}
        + \frac{12 R}{\sqrt n}\,\mathsf V_\infty(F_{\rm fp})\Bigr),$$
    with $\mathrm{dev}_{\ell,n,\delta}(B) = 4\beta_\ell B + 6b\sqrt{2\log(4/\delta)/n}$
    (`def:bv-dev`): the EL regime with $\alpha = \log(1/(1-h\mu)) \ge h\mu$ and saturated
    variance. -/)]
theorem prop_ode_fixedpoint [TopologicalSpace.SeparableSpace E] {Y : Type*} [MeasurableSpace Y]
    (hK : IsCompact K) (hP : IsProjectionOnto K proj) {𝒮 : Set (K → E)} {μ Λ h : ℝ}
    (hμ : 0 < μ) (hμΛ : μ ≤ Λ) (h𝒮 : ∀ s ∈ 𝒮, StronglyConcaveSmooth μ Λ s) (hh0 : 0 < h)
    (hh : h ≤ 2 / (μ + Λ)) {n : ℕ} (hn : 0 < n) (P : Measure (K × Y)) [IsProbabilityMeasure P]
    (L : BoundedLipschitzLoss Y) (hℓ : Measurable (Function.uncurry L.ℓ)) (hb : 0 < L.b)
    (hβ : 0 ≤ L.β) {R MK : ℝ} (hR : 0 < R) (hMK : 0 ≤ MK) (hK' : ∀ x : K, ‖(x : E)‖ ≤ MK)
    (hint : SatIntegrable (fpClass hP 𝒮 h)) (k : ℕ) {η δ : ℝ} (hη : 0 ≤ η) (hδ : 0 < δ)
    (hδ1 : δ < 1) :
    ((Measure.pi fun _ : Fin n => P) {D | ¬ ∀ fhat,
        IsEmpMinimizer L D
          (hypothesisClass (linearReadouts (ambientFeature K) R) (fpClass hP 𝒮 h) k) η fhat →
        risk L P fhat - sInf (risk L P '' fpTargetClass hP 𝒮 h R) ≤
          L.β * (R * Metric.diam (Set.univ : Set K) * (1 - h * μ) ^ k) + η +
            bvDev L n δ (R * MK / √n + 12 * 1 * R / √n * satVinf (fpClass hP 𝒮 h))}
      ).toReal ≤ δ := by
  /- `thm:bv-id-bounds` with the class properties, `lem:fp-var` and `lem:fp-bias`. -/
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  exact bv_id_of_bounds P L hn hℓ hb hβ (fp_class_measurable hP hμ hμΛ h𝒮 hh0 hh R k)
    (isSupSeparable_compClass_linearReadouts lipschitzWith_ambientFeature hMK hK' hR.le
      (hasCountableUniformDense_of_totallyBounded
        ((totallyBounded_semigroupClosure_fpClass hK hP hμ hμΛ h𝒮 hh0 hh).subset
          subset_semigroupClosure)))
    (fun x => ⟨R * MK, fun _ hg => abs_le_of_mem_compClass_linearReadouts hK' hR.le hg x⟩)
    (fp_target_nonempty hP 𝒮 h hR.le) (fp_target_measurable hP hμ hμΛ h𝒮 hh0 hh R)
    (fun S => fp_var hK hP hμ hμΛ h𝒮 hh0 hh hn S hR hMK hK' hint k)
    (fp_bias hK hP hμ hμΛ h𝒮 hh0 hh P L hℓ hβ hR.le k) hη hδ hδ1

omit [MeasurableSpace E] [BorelSpace E] in
@[blueprint "lem:fp-balance"
  (statement := /-- \textbf{(EL balancing for fixed-point refinement.)} If $h\mu < 1$ and
    $n \ge 1$, the depth $k^\ast := \lceil \log n / (2\log(1/(1-h\mu)))\rceil
    = \frac{\log n}{2\log(1/(1-h\mu))} + O(1) \le \frac{\log n}{2h\mu} + O(1)$ satisfies
    $(1 - h\mu)^{k^\ast} \le n^{-1/2}$. -/)]
theorem fp_balance {μ h : ℝ} (hμ : 0 < μ) (hhμ : h * μ < 1) (hh0 : 0 < h) {n : ℕ}
    (hn : 1 ≤ n) :
    (1 - h * μ) ^ ⌈Real.log n / (2 * Real.log (1 / (1 - h * μ)))⌉₊ ≤ 1 / √n :=
  pow_ceil_log_div_le_one_div_sqrt (by linarith) (by nlinarith) (by exact_mod_cast hn)

@[blueprint "cor:ode-fixedpoint-depth"
  (statement := /-- \textbf{(Balanced value $O(n^{-1/2})$.)} Under the hypotheses of
    `prop:ode-fixedpoint` with $h\mu < 1$, at the depth
    $k^\ast = \lceil \log n / (2\log(1/(1-h\mu)))\rceil$,
    $$L[\hat h] - \inf_{\mathcal C} L \le \frac{\beta_\ell R D_K}{\sqrt n} + \eta
      + \mathrm{dev}_{\ell,n,\delta}\Bigl(\frac{R M_K + 12 R\,\mathsf V_\infty(F_{\rm fp})}
        {\sqrt n}\Bigr)$$
    with probability at least $1 - \delta$: the balanced value is of order $n^{-1/2}$. -/)]
theorem cor_ode_fixedpoint_depth [TopologicalSpace.SeparableSpace E] {Y : Type*}
    [MeasurableSpace Y] (hK : IsCompact K) (hP : IsProjectionOnto K proj) {𝒮 : Set (K → E)}
    {μ Λ h : ℝ} (hμ : 0 < μ) (hμΛ : μ ≤ Λ) (h𝒮 : ∀ s ∈ 𝒮, StronglyConcaveSmooth μ Λ s)
    (hh0 : 0 < h) (hh : h ≤ 2 / (μ + Λ)) (hhμ : h * μ < 1) {n : ℕ} (hn : 1 ≤ n)
    (P : Measure (K × Y)) [IsProbabilityMeasure P] (L : BoundedLipschitzLoss Y)
    (hℓ : Measurable (Function.uncurry L.ℓ)) (hb : 0 < L.b) (hβ : 0 ≤ L.β) {R MK : ℝ}
    (hR : 0 < R) (hMK : 0 ≤ MK) (hK' : ∀ x : K, ‖(x : E)‖ ≤ MK)
    (hint : SatIntegrable (fpClass hP 𝒮 h)) {η δ : ℝ} (hη : 0 ≤ η) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ((Measure.pi fun _ : Fin n => P) {D | ¬ ∀ fhat,
        IsEmpMinimizer L D (hypothesisClass (linearReadouts (ambientFeature K) R) (fpClass hP 𝒮 h)
          ⌈Real.log n / (2 * Real.log (1 / (1 - h * μ)))⌉₊) η fhat →
        risk L P fhat - sInf (risk L P '' fpTargetClass hP 𝒮 h R) ≤
          L.β * (R * Metric.diam (Set.univ : Set K)) / √n + η +
            bvDev L n δ ((R * MK + 12 * R * satVinf (fpClass hP 𝒮 h)) / √n)}
      ).toReal ≤ δ := by
  /- `prop:ode-fixedpoint` at $k^\ast$ and `lem:fp-balance`. -/
  refine le_trans ?_ (prop_ode_fixedpoint (n := n) hK hP hμ hμΛ h𝒮 hh0 hh
    (lt_of_lt_of_le Nat.one_pos hn) P L hℓ hb hβ hR hMK hK' hint
    ⌈Real.log n / (2 * Real.log (1 / (1 - h * μ)))⌉₊ hη hδ hδ1)
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun D hD => ?_)
  simp only [Set.mem_setOf_eq] at hD ⊢
  intro hall
  apply hD
  intro fhat hfhat
  have h1 := hall fhat hfhat
  have hlk := fp_balance hμ hhμ hh0 hn
  have hpos : 0 ≤ L.β * (R * Metric.diam (Set.univ : Set K)) :=
    mul_nonneg hβ (mul_nonneg hR.le Metric.diam_nonneg)
  have h2 : L.β * (R * Metric.diam (Set.univ : Set K) *
      (1 - h * μ) ^ ⌈Real.log n / (2 * Real.log (1 / (1 - h * μ)))⌉₊) ≤
      L.β * (R * Metric.diam (Set.univ : Set K)) / √n := by
    calc L.β * (R * Metric.diam (Set.univ : Set K) *
          (1 - h * μ) ^ ⌈Real.log n / (2 * Real.log (1 / (1 - h * μ)))⌉₊)
        = L.β * (R * Metric.diam (Set.univ : Set K)) *
          (1 - h * μ) ^ ⌈Real.log n / (2 * Real.log (1 / (1 - h * μ)))⌉₊ := by ring
      _ ≤ L.β * (R * Metric.diam (Set.univ : Set K)) * (1 / √n) :=
          mul_le_mul_of_nonneg_left hlk hpos
      _ = L.β * (R * Metric.diam (Set.univ : Set K)) / √n := by ring
  have h3 : R * MK / √n + 12 * 1 * R / √n * satVinf (fpClass hP 𝒮 h) =
      (R * MK + 12 * R * satVinf (fpClass hP 𝒮 h)) / √n := by ring
  rw [h3] at h1
  linarith

end FixedPointRegime

/-! ### The explicit Euler scheme: global error (`lem:ode-euler-error`) -/

section EulerError

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

@[blueprint "def:ode-euler-iter"
  (statement := /-- The explicit Euler iterates on the ambient space with constant step $h$
    from time $0$: $y_0 = x$, $y_{i+1} = y_i + h\,s(y_i, i h)$. -/)]
def eulerIter (s : E → ℝ → E) (h : ℝ) : ℕ → E → E
  | 0, x => x
  | i + 1, x => eulerIter s h i x + h • s (eulerIter s h i x) ((i : ℝ) * h)

@[blueprint "lem:ode-euler-local-error"
  (statement := /-- \textbf{(One-step consistency of the Euler scheme.)} Let $s$ be
    $\Lambda_s$-Lipschitz in $x$, $\Lambda_\tau$-Lipschitz in $\tau$ and bounded by $M_s$, and
    let $x$ solve $\dot x(t) = s(x(t), t)$ on $[t_0, t_0 + h]$ ($h \ge 0$). Then
    $$\|x(t_0 + h) - x(t_0) - h\,s(x(t_0), t_0)\| \le
      \frac{(\Lambda_s M_s + \Lambda_\tau)\,h^2}{2} .$$
    (The function $g(t) = x(t) - x(t_0) - (t - t_0) s(x(t_0),t_0)$ has
    $\|g'(t)\| \le \Lambda_s\|x(t) - x(t_0)\| + \Lambda_\tau (t - t_0) \le
    (\Lambda_s M_s + \Lambda_\tau)(t - t_0)$, and the mean value inequality with the quadratic
    boundary $B(t) = (\Lambda_s M_s + \Lambda_\tau)(t-t_0)^2/2$ gives the claim.) -/)]
theorem euler_local_error {s : E → ℝ → E} {Λs Λτ Ms : ℝ≥0}
    (hsx : ∀ τ, LipschitzWith Λs (fun x => s x τ)) (hsτ : ∀ x, LipschitzWith Λτ (s x))
    (hMs : ∀ x τ, ‖s x τ‖ ≤ Ms) {x : ℝ → E} {t₀ h : ℝ} (hh : 0 ≤ h)
    (hx : ∀ t ∈ Set.Icc t₀ (t₀ + h), HasDerivAt x (s (x t) t) t) :
    ‖x (t₀ + h) - x t₀ - h • s (x t₀) t₀‖ ≤ (Λs * Ms + Λτ) * h ^ 2 / 2 := by
  set v := s (x t₀) t₀ with hv
  set c : ℝ := Λs * Ms + Λτ with hc_def
  have hcont : ContinuousOn x (Set.Icc t₀ (t₀ + h)) := HasDerivAt.continuousOn hx
  -- `‖x t - x t₀‖ ≤ Ms (t - t₀)`
  have hA : ∀ t ∈ Set.Icc t₀ (t₀ + h), ‖x t - x t₀‖ ≤ Ms * (t - t₀) :=
    norm_image_sub_le_of_norm_deriv_right_le_segment hcont
      (fun t ht => (hx t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt)
      (fun t _ => hMs _ _)
  -- the defect `g`
  set g : ℝ → E := fun t => x t - x t₀ - (t - t₀) • v with hg_def
  have hg : ∀ t ∈ Set.Icc t₀ (t₀ + h), HasDerivAt g (s (x t) t - v) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => (t - t₀) • v) ((1 : ℝ) • v) t :=
      ((hasDerivAt_id' t).sub_const t₀).smul_const v
    rw [one_smul] at h1
    exact ((hx t ht).sub_const (x t₀)).sub h1
  have hgcont : ContinuousOn g (Set.Icc t₀ (t₀ + h)) := HasDerivAt.continuousOn hg
  have hB : ∀ t, HasDerivAt (fun t : ℝ => c * (t - t₀) ^ 2 / 2) (c * (t - t₀)) t := by
    intro t
    have := ((((hasDerivAt_id' t).sub_const t₀).pow 2).const_mul c).div_const 2
    refine this.congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one]
    ring
  have hbound : ∀ t ∈ Set.Ico t₀ (t₀ + h), ‖s (x t) t - v‖ ≤ c * (t - t₀) := by
    intro t ht
    have ht' : t ∈ Set.Icc t₀ (t₀ + h) := Set.Ico_subset_Icc_self ht
    have htt : 0 ≤ t - t₀ := by linarith [ht.1]
    calc ‖s (x t) t - v‖ ≤ ‖s (x t) t - s (x t₀) t‖ + ‖s (x t₀) t - s (x t₀) t₀‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ Λs * ‖x t - x t₀‖ + Λτ * |t - t₀| := by
          gcongr
          · have := (hsx t).dist_le_mul (x t) (x t₀)
            rwa [dist_eq_norm, dist_eq_norm] at this
          · have := (hsτ (x t₀)).dist_le_mul t t₀
            rwa [dist_eq_norm, Real.dist_eq] at this
      _ ≤ Λs * (Ms * (t - t₀)) + Λτ * (t - t₀) := by
          gcongr
          · exact hA t ht'
          · rw [abs_of_nonneg htt]
      _ = c * (t - t₀) := by rw [hc_def]; ring
  have hmain := image_norm_le_of_norm_deriv_right_le_deriv_boundary hgcont
    (fun t ht => (hg t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (by simp [hg_def]) hB hbound (Set.right_mem_Icc.2 (by linarith))
  simpa [hg_def] using hmain

@[blueprint "lem:ode-euler-error"
  (statement := /-- \textbf{(Global error of the explicit Euler scheme.)} Let $s$ be
    $\Lambda_s$-Lipschitz in $x$, $\Lambda_\tau$-Lipschitz in $\tau$ and bounded by $M_s$, let
    $x$ solve $\dot x(t) = s(x(t),t)$ on $[0,T]$ ($T \ge 0$), and let $y_0, \dots, y_k$ be the
    Euler iterates with $k \ge 1$ equal steps $h = T/k$ started at $y_0 = x(0)$. Then
    $$\|x(T) - y_k\| \le C_E\,\frac{T^2}{k}, \qquad
      C_E := \frac{(\Lambda_s M_s + \Lambda_\tau)\,e^{\Lambda_s T}}{2} .$$
    (Discrete Grönwall: $e_{i+1} \le (1 + h\Lambda_s) e_i + c h^2/2$ with
    $c = \Lambda_s M_s + \Lambda_\tau$, hence $e_k \le \frac{c h^2}{2}\sum_{j<k}(1+h\Lambda_s)^j
    \le \frac{c h^2}{2}\, k\, e^{\Lambda_s T}$.) -/)]
theorem euler_global_error {s : E → ℝ → E} {Λs Λτ Ms : ℝ≥0}
    (hsx : ∀ τ, LipschitzWith Λs (fun x => s x τ)) (hsτ : ∀ x, LipschitzWith Λτ (s x))
    (hMs : ∀ x τ, ‖s x τ‖ ≤ Ms) {T : ℝ} (hT : 0 ≤ T) {x : ℝ → E}
    (hx : ∀ t ∈ Set.Icc 0 T, HasDerivAt x (s (x t) t) t) {k : ℕ} (hk : 0 < k) :
    ‖x T - eulerIter s (T / k) k (x 0)‖ ≤
      (Λs * Ms + Λτ) * Real.exp (Λs * T) / 2 * T ^ 2 / k := by
  set h : ℝ := T / k with hh_def
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hh : 0 ≤ h := div_nonneg hT hk'.le
  have hkT : (k : ℝ) * h = T := by rw [hh_def]; field_simp
  set c : ℝ := Λs * Ms + Λτ with hc_def
  have hc : 0 ≤ c := by positivity
  set a : ℝ := 1 + h * Λs with ha_def
  have ha : 1 ≤ a := by
    have := mul_nonneg hh Λs.coe_nonneg
    linarith
  -- the discrete Grönwall recursion
  have hrec : ∀ i, i ≤ k → ‖x (i * h) - eulerIter s h i (x 0)‖ ≤
      c * h ^ 2 / 2 * ∑ j ∈ Finset.range i, a ^ j := by
    intro i
    induction i with
    | zero => intro _; simp [eulerIter]
    | succ i ih =>
      intro hik
      have ih' := ih (by omega)
      have hsub : ∀ t ∈ Set.Icc ((i : ℝ) * h) ((i : ℝ) * h + h), HasDerivAt x (s (x t) t) t := by
        intro t ht
        refine hx t ⟨by have := mul_nonneg (Nat.cast_nonneg i) hh; linarith [ht.1], ?_⟩
        have h2 : ((i : ℝ) + 1) * h ≤ k * h := by
          have : ((i : ℝ) + 1) ≤ k := by exact_mod_cast hik
          exact mul_le_mul_of_nonneg_right this hh
        linarith [ht.2]
      have hloc := euler_local_error hsx hsτ hMs hh hsub
      set y := eulerIter s h i (x 0) with hy
      have hstep : eulerIter s h (i + 1) (x 0) = y + h • s y (i * h) := rfl
      have hcast : ((i + 1 : ℕ) : ℝ) * h = (i : ℝ) * h + h := by push_cast; ring
      rw [hstep, hcast]
      have hlip : ‖s (x (i * h)) (i * h) - s y (i * h)‖ ≤ Λs * ‖x (i * h) - y‖ := by
        have := (hsx (i * h)).dist_le_mul (x (i * h)) y
        rwa [dist_eq_norm, dist_eq_norm] at this
      calc ‖x ((i : ℝ) * h + h) - (y + h • s y (i * h))‖
          = ‖(x ((i : ℝ) * h + h) - x (i * h) - h • s (x (i * h)) (i * h)) +
              ((x (i * h) - y) + h • (s (x (i * h)) (i * h) - s y (i * h)))‖ := by
            congr 1
            rw [smul_sub]
            abel
        _ ≤ ‖x ((i : ℝ) * h + h) - x (i * h) - h • s (x (i * h)) (i * h)‖ +
              (‖x (i * h) - y‖ + ‖h • (s (x (i * h)) (i * h) - s y (i * h))‖) :=
            (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
        _ ≤ c * h ^ 2 / 2 + (‖x (i * h) - y‖ + h * (Λs * ‖x (i * h) - y‖)) := by
            gcongr
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
            gcongr
        _ = c * h ^ 2 / 2 + a * ‖x (i * h) - y‖ := by rw [ha_def]; ring
        _ ≤ c * h ^ 2 / 2 + a * (c * h ^ 2 / 2 * ∑ j ∈ Finset.range i, a ^ j) := by
            gcongr
        _ = c * h ^ 2 / 2 * ∑ j ∈ Finset.range (i + 1), a ^ j := by
            rw [Finset.sum_range_succ', pow_zero]
            have : ∑ j ∈ Finset.range i, a ^ (j + 1) = a * ∑ j ∈ Finset.range i, a ^ j := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun j _ => by ring
            rw [this]
            ring
  have hfin := hrec k le_rfl
  rw [hkT] at hfin
  refine hfin.trans ?_
  have hexp : a ^ k ≤ Real.exp (Λs * T) := by
    calc a ^ k ≤ (Real.exp (h * Λs)) ^ k :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (h * Λs)]) k
      _ = Real.exp (Λs * T) := by
          rw [← Real.exp_nat_mul]
          congr 1
          linear_combination (Λs : ℝ) * hkT
  have hsum : ∑ j ∈ Finset.range k, a ^ j ≤ k * Real.exp (Λs * T) := by
    calc ∑ j ∈ Finset.range k, a ^ j ≤ ∑ _j ∈ Finset.range k, a ^ k :=
          Finset.sum_le_sum fun j hj => pow_le_pow_right₀ ha (Finset.mem_range.1 hj).le
      _ = k * a ^ k := by simp
      _ ≤ k * Real.exp (Λs * T) := by gcongr
  calc c * h ^ 2 / 2 * ∑ j ∈ Finset.range k, a ^ j
      ≤ c * h ^ 2 / 2 * (k * Real.exp (Λs * T)) := by gcongr
    _ = c * Real.exp (Λs * T) / 2 * T ^ 2 / k := by
        rw [hh_def]
        field_simp

end EulerError

/-! ### Fixed-horizon integration in the PL regime (`prop:ode-horizon`) -/

section HorizonRegime

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {K : Set E} {proj : E → E}

@[blueprint "def:ode-equal-scheme"
  (statement := /-- The equal-step scheme with $k$ Euler steps of size $h = T/k$ and time stamps
    $\tau_i = i h$: $T_{s,h,\tau_{k-1}} \circ \cdots \circ T_{s,h,\tau_0}$. -/)]
noncomputable def equalScheme (hP : IsProjectionOnto K proj) (s : K → ℝ → E) (T : ℝ) (k : ℕ) :
    K → K :=
  scheme hP s k (fun _ => T / k) (fun i => (i : ℝ) * (T / k))

@[blueprint "lem:ode-equal-scheme-mem"
  (statement := /-- For $s \in \mathcal S_T$, $T \ge 0$, $k \ge 1$ and $T/k \le h_0$, the
    equal-step scheme with $k$ steps belongs to $B_T(k)$. -/)]
theorem equalScheme_mem_schemeBall (hP : IsProjectionOnto K proj) {𝒮 : Set (K → ℝ → E)}
    {s : K → ℝ → E} (hs : s ∈ 𝒮) {h₀ T : ℝ} (hT : 0 ≤ T) {k : ℕ} (hk : 0 < k)
    (hkh : T / k ≤ h₀) : equalScheme hP s T k ∈ schemeBall hP 𝒮 h₀ T k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hh : 0 ≤ T / k := div_nonneg hT hk'.le
  refine ⟨s, hs, k, le_rfl, _, _, fun _ => ⟨hh, hkh⟩, fun i => ⟨by positivity, ?_⟩, ?_, rfl⟩
  · calc ((i : ℕ) : ℝ) * (T / k) ≤ k * (T / k) := by
          gcongr
          exact_mod_cast i.2.le
      _ = T := by field_simp
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_div_cancel₀ _ hk'.ne']

@[blueprint "lem:ode-scheme-eq-euler"
  (statement := /-- \textbf{(Inactive projection.)} Let $\tilde s : \mathbb R^d \times \mathbb R
    \to \mathbb R^d$ extend the drift $s$ from $K$, and suppose $K$ is invariant under the Euler
    steps, $x + h\,s(x,\tau) \in K$ for $x \in K$. Then the projection is inactive and the scheme
    with $k$ equal steps of size $h$ coincides with the Euler iterates:
    $T_{s,h,(k-1)h} \circ \cdots \circ T_{s,h,0}(x_0) = y_k(x_0)$. -/)]
theorem coe_scheme_eq_eulerIter (hP : IsProjectionOnto K proj) {s : K → ℝ → E}
    {s' : E → ℝ → E} (hs : ∀ (x : K) (τ : ℝ), s x τ = s' x τ) {h : ℝ}
    (hinv : ∀ (x : K) (τ : ℝ), (x : E) + h • s x τ ∈ K) (k : ℕ) (x₀ : K) :
    ((scheme hP s k (fun _ => h) (fun i => (i : ℝ) * h) x₀ : K) : E) = eulerIter s' h k x₀ := by
  induction k with
  | zero => rfl
  | succ n ih =>
    have hτ : (fun i : Fin n => (((Fin.castSucc i : Fin (n + 1)) : ℕ) : ℝ) * h) =
        fun i : Fin n => ((i : ℕ) : ℝ) * h := by
      funext i
      simp
    change ((eulerLayer hP s h (((Fin.last n : Fin (n + 1)) : ℕ) * h)
      (scheme hP s n (fun _ => h) (fun i => (((Fin.castSucc i : Fin (n + 1)) : ℕ) : ℝ) * h) x₀)
        : K) : E) = _
    rw [hτ]
    simp only [eulerLayer, gradStep, Fin.val_last, eulerIter]
    rw [hP.eq_of_mem _ (hinv _ _), hs, ih]

@[blueprint "def:ode-scheme-vinf"
  (statement := /-- The depth-independent entropy integral of `lem:ode-saturation-profile`:
    $\mathsf V_\infty := \int_0^{D_K}\sqrt{\log N(\overline{\bigcup_k B_T(k)}, d_\infty,
    \varepsilon/2)}\,d\varepsilon$. -/)]
noncomputable def schemeVinf (hP : IsProjectionOnto K proj) (𝒮 : Set (K → ℝ → E))
    (h₀ T : ℝ) : ℝ :=
  ∫ ε in (0 : ℝ)..Metric.diam (Set.univ : Set K),
    √(Real.log (Metric.coveringNumber (X := UnifMaps K) (ε.toNNReal / 2)
      (closure (X := UnifMaps K) (schemeSet hP 𝒮 h₀ T)) : ℝ≥0∞).toReal)

@[blueprint "def:ode-scheme-integrable"
  (statement := /-- The paper's condition $\int_0^{D_K}\sqrt{\log N_\infty(\varepsilon)}\,
    d\varepsilon < \infty$ for the scheme classes: the majorant is interval-integrable. -/)]
def SchemeIntegrable (hP : IsProjectionOnto K proj) (𝒮 : Set (K → ℝ → E)) (h₀ T : ℝ) : Prop :=
  IntervalIntegrable (fun ε : ℝ => √(Real.log (Metric.coveringNumber (X := UnifMaps K)
    (ε.toNNReal / 2) (closure (X := UnifMaps K) (schemeSet hP 𝒮 h₀ T)) : ℝ≥0∞).toReal))
    volume 0 (Metric.diam (Set.univ : Set K))

@[blueprint "lem:ode-horizon-var"
  (statement := /-- \textbf{(Estimation term for fixed-horizon schemes.)} Let $K$ be compact
    with $\|x\| \le M_K$ on $K$, every drift in $\mathcal S_T \ne \emptyset$ be
    $\Lambda_s$-Lipschitz in $x$, $T \ge 0$, $R > 0$, and assume the entropy condition of
    `lem:ode-saturation-profile`. Then for every sample $S$ of size $n \ge 1$ and every $k$,
    $$\hat{\mathfrak R}_S(H_R \circ B_T(k)) \le \frac{R M_K}{\sqrt n}
      + \frac{12 \cdot 1 \cdot R}{\sqrt n}\,\mathsf V_\infty$$
    (`thm:hidden-decomp` on the scheme class, `lem:ode-saturation-profile` and
    `lem:linear-readouts-rademacher`). -/)]
theorem horizon_var (hK : IsCompact K) (hP : IsProjectionOnto K proj) {𝒮 : Set (K → ℝ → E)}
    {Λs : ℝ≥0} (h𝒮 : ∀ s ∈ 𝒮, ∀ τ, LipschitzWith Λs (fun x => s x τ)) (h𝒮ne : 𝒮.Nonempty)
    {h₀ T : ℝ} (hT : 0 ≤ T) {n : ℕ} (hn : 0 < n) (S : Fin n → K) {R MK : ℝ} (hR : 0 < R)
    (hMK : 0 ≤ MK) (hK' : ∀ x : K, ‖(x : E)‖ ≤ MK) (hint : SchemeIntegrable hP 𝒮 h₀ T) (k : ℕ) :
    empRademacher S (compClass (linearReadouts (ambientFeature K) R) (schemeBall hP 𝒮 h₀ T k)) ≤
      R * MK / √n + 12 * 1 * R / √n * schemeVinf hP 𝒮 h₀ T := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  obtain ⟨s₀, hs₀⟩ := h𝒮ne
  have hid : id ∈ schemeBall hP 𝒮 h₀ T k :=
    ⟨s₀, hs₀, 0, Nat.zero_le _, finZeroElim, finZeroElim, fun i => i.elim0, fun i => i.elim0,
      by simp [hT], rfl⟩
  have htb := (ode_saturation hK hP h𝒮 h₀ T).1
  have hcoe : ((R.toNNReal * 1 : ℝ≥0) : ℝ) = R := by
    rw [NNReal.coe_mul, Real.coe_toNNReal _ hR.le, NNReal.coe_one, mul_one]
  have hL : (0 : ℝ) < ((R.toNNReal * 1 : ℝ≥0) : ℝ) := by rw [hcoe]; exact hR
  have hdec := hidden_decomp_id S (linearReadouts (ambientFeature K) R) hn
    (schemeBall hP 𝒮 h₀ T k)
    (schemeSet hP 𝒮 h₀ T) (AH := 1) one_pos hL
    (fun f _ σ => bddAbove_range_normalizedRademacherSum_of_bound (f ∘ S) (by positivity)
      (fun g hg x => (abs_le_of_mem_linearReadouts hg _).trans
        (mul_le_mul_of_nonneg_left (hK' _) hR.le)) σ)
    hid (totallyBounded_empSpace_of_unifMaps S (htb.subset (Set.subset_iUnion _ k)))
    (Set.subset_iUnion _ k)
    (linearReadouts_sg S (ambientFeature K) lipschitzWith_ambientFeature hR _)
    (intervalIntegrable_of_totallyBounded htb (fun k => Set.subset_iUnion (schemeBall hP 𝒮 h₀ T) k)
      S hint k)
  refine hdec.trans ?_
  rw [hcoe]
  have hprof := ode_saturation_profile hK hP h𝒮 h₀ T S hint k
  unfold entropyIntegral at hprof
  unfold schemeVinf
  gcongr
  exact empRademacher_linearReadouts_le S _ hR.le hMK hK'

@[blueprint "lem:ode-scheme-continuous"
  (statement := /-- Every scheme in $\bigcup_k B_T(k)$ is Lipschitz, hence continuous. -/)]
theorem continuous_of_mem_schemeSet (hP : IsProjectionOnto K proj) {𝒮 : Set (K → ℝ → E)}
    {Λs : ℝ≥0} (h𝒮 : ∀ s ∈ 𝒮, ∀ τ, LipschitzWith Λs (fun x => s x τ)) {h₀ T : ℝ} {f : K → K}
    (hf : f ∈ schemeSet hP 𝒮 h₀ T) : Continuous f :=
  (lipschitzWith_of_mem_schemeSet hP h𝒮 hf).continuous

variable [MeasurableSpace E] [BorelSpace E]

@[blueprint "lem:ode-horizon-class-measurable"
  (statement := /-- Every element of $H_R \circ B_T(k)$ is Borel measurable. -/)]
theorem horizon_class_measurable (hP : IsProjectionOnto K proj) {𝒮 : Set (K → ℝ → E)}
    {Λs : ℝ≥0} (h𝒮 : ∀ s ∈ 𝒮, ∀ τ, LipschitzWith Λs (fun x => s x τ)) (h₀ T : ℝ) (R : ℝ)
    (k : ℕ) :
    ∀ g ∈ compClass (linearReadouts (ambientFeature K) R) (schemeBall hP 𝒮 h₀ T k),
      Measurable g :=
  fun _ hg => measurable_of_mem_compClass_linearReadouts lipschitzWith_ambientFeature.continuous
    (fun _ hf => continuous_of_mem_schemeSet hP h𝒮 (Set.subset_iUnion _ k hf)) hg

@[blueprint "lem:ode-horizon-bias"
  (statement := /-- \textbf{(Bias for fixed-horizon integration.)} Let the target class be the
    readouts of the endpoint map of the exact flow of $s^\ast \in \mathcal S_T$:
    $\mathcal C = \{x_0 \mapsto \langle w, \Phi_T(x_0)\rangle : \|w\| \le R\}$, where for every
    $x_0 \in K$ the flow $\Phi_T(x_0) = x(T)$ is given by a solution of
    $\dot x = \tilde s(x, t)$, $x(0) = x_0$, for an extension $\tilde s$ of $s^\ast$ which is
    $\Lambda_s$-Lipschitz in $x$, $\Lambda_\tau$-Lipschitz in $\tau$ and bounded by $M_s$.
    Assume the projection is inactive along the Euler steps of size $T/k$ ($K$ is invariant),
    $k \ge 1$ and $T/k \le h_0$. Then
    $$\mathrm{bias}(k) = \varepsilon_{\mathrm{model}}(k) \le \beta_\ell\, R\, C_E\,\frac{T^2}{k},
      \qquad C_E = \frac{(\Lambda_s M_s + \Lambda_\tau)e^{\Lambda_s T}}{2},$$
    by `lem:ode-euler-error`, `lem:ode-scheme-eq-euler` and `lem:approx-transfer`. -/)]
theorem horizon_bias {Y : Type*} [MeasurableSpace Y] (hP : IsProjectionOnto K proj)
    {𝒮 : Set (K → ℝ → E)} {Λs : ℝ≥0} (h𝒮 : ∀ s ∈ 𝒮, ∀ τ, LipschitzWith Λs (fun x => s x τ))
    {h₀ T : ℝ} (hT : 0 ≤ T) {s : K → ℝ → E} (hs : s ∈ 𝒮) {s' : E → ℝ → E}
    (hss' : ∀ (x : K) (τ : ℝ), s x τ = s' x τ) {Λτ Ms : ℝ≥0}
    (hs'x : ∀ τ, LipschitzWith Λs (fun x => s' x τ)) (hs'τ : ∀ x, LipschitzWith Λτ (s' x))
    (hMs : ∀ x τ, ‖s' x τ‖ ≤ Ms) {flow : K → E} (hflowm : Measurable flow)
    (hflow : ∀ x₀ : K, ∃ x : ℝ → E, x 0 = x₀ ∧ (∀ t ∈ Set.Icc 0 T, HasDerivAt x (s' (x t) t) t) ∧
      flow x₀ = x T)
    {k : ℕ} (hk : 0 < k) (hkh : T / k ≤ h₀)
    (hinv : ∀ (x : K) (τ : ℝ), (x : E) + (T / k) • s x τ ∈ K)
    (P : Measure (K × Y)) [IsProbabilityMeasure P] (L : BoundedLipschitzLoss Y)
    (hℓ : Measurable (Function.uncurry L.ℓ)) (hβ : 0 ≤ L.β) {R : ℝ} (hR : 0 ≤ R) :
    modelError L P (compClass (linearReadouts (ambientFeature K) R) (schemeBall hP 𝒮 h₀ T k))
        (linearReadouts flow R) ≤
      L.β * (R * ((Λs * Ms + Λτ) * Real.exp (Λs * T) / 2 * T ^ 2 / k)) := by
  refine modelError_le_of_approx P L hℓ hβ (horizon_class_measurable hP h𝒮 h₀ T R k)
    (fun c hc => ?_) (⟨_, 0, by simpa using hR, rfl⟩ : (linearReadouts flow R).Nonempty)
    fun c hc ε hε => ?_
  · obtain ⟨w, -, rfl⟩ := hc
    exact (continuous_const.inner continuous_id).measurable.comp hflowm
  · obtain ⟨w, hw, rfl⟩ := hc
    refine ⟨fun x₀ => ⟪w, ambientFeature K (equalScheme hP s T k x₀)⟫,
      ⟨_, ⟨w, hw, rfl⟩, _, equalScheme_mem_schemeBall hP hs hT hk hkh, rfl⟩, fun x₀ => ?_⟩
    obtain ⟨x, hx0, hx, hxT⟩ := hflow x₀
    have herr := euler_global_error hs'x hs'τ hMs hT hx hk
    rw [hx0] at herr
    have hsch : ambientFeature K (equalScheme hP s T k x₀) = eulerIter s' (T / k) k x₀ :=
      coe_scheme_eq_eulerIter hP hss' hinv k x₀
    change |⟪w, ambientFeature K (equalScheme hP s T k x₀)⟫ - ⟪w, flow x₀⟫| ≤ _
    rw [hsch, hxT, ← inner_sub_right]
    refine le_trans ?_ (le_add_of_nonneg_right hε.le)
    calc |⟪w, eulerIter s' (T / k) k x₀ - x T⟫| ≤ ‖w‖ * ‖eulerIter s' (T / k) k x₀ - x T‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ R * ((Λs * Ms + Λτ) * Real.exp (Λs * T) / 2 * T ^ 2 / k) := by
          gcongr
          rw [norm_sub_rev]
          exact herr

@[blueprint "prop:ode-horizon"
  (statement := /-- \textbf{(Fixed-horizon integration, rigorous form, $p = 1$.)} Let
    $K \subseteq \mathbb R^d$ (a separable Hilbert space) be compact with $\|x\| \le M_K$ on $K$,
    let every drift in $\mathcal S_T$ be $\Lambda_s$-Lipschitz in $x$, $H = H_R$ ($R > 0$),
    and let the target class be the flow readouts $\mathcal C = \{\langle w, \Phi_T(\cdot)\rangle
    : \|w\| \le R\}$ of a teacher $s^\ast \in \mathcal S_T$ as in `lem:ode-horizon-bias`
    (projection inactive, $k \ge 1$, $T/k \le h_0$). Assume the entropy condition
    $\mathsf V_\infty < \infty$ of `lem:ode-saturation-profile`. For a measurable loss
    $\ell : \mathbb R \times \mathcal Y \to [0,b]$, $\beta_\ell$-Lipschitz in its first
    argument, $n \ge 1$, $\eta \ge 0$, $\delta \in (0,1)$: with probability at least $1 - \delta$
    over $\mathcal D \sim P^{\otimes n}$, every $\eta$-empirical minimizer
    $\hat h \in H_R \circ B_T(k)$ satisfies
    $$L[\hat h] - \inf_{\mathcal C} L \le \beta_\ell R C_E\,\frac{T^2}{k} + \eta
      + \mathrm{dev}_{\ell,n,\delta}\Bigl(\frac{R M_K}{\sqrt n}
        + \frac{12 R}{\sqrt n}\,\mathsf V_\infty\Bigr),$$
    with $C_E = (\Lambda_s M_s + \Lambda_\tau)e^{\Lambda_s T}/2$ and
    $\mathrm{dev}_{\ell,n,\delta}(B) = 4\beta_\ell B + 6b\sqrt{2\log(4/\delta)/n}$
    (`def:bv-dev`): the PL regime with $\beta = p = 1$ and saturated variance. -/)]
theorem prop_ode_horizon [TopologicalSpace.SeparableSpace E] {Y : Type*} [MeasurableSpace Y]
    (hK : IsCompact K) (hP : IsProjectionOnto K proj) {𝒮 : Set (K → ℝ → E)} {Λs : ℝ≥0}
    (h𝒮 : ∀ s ∈ 𝒮, ∀ τ, LipschitzWith Λs (fun x => s x τ)) {h₀ T : ℝ} (hT : 0 ≤ T)
    {s : K → ℝ → E} (hs : s ∈ 𝒮) {s' : E → ℝ → E} (hss' : ∀ (x : K) (τ : ℝ), s x τ = s' x τ)
    {Λτ Ms : ℝ≥0} (hs'x : ∀ τ, LipschitzWith Λs (fun x => s' x τ))
    (hs'τ : ∀ x, LipschitzWith Λτ (s' x)) (hMs : ∀ x τ, ‖s' x τ‖ ≤ Ms) {flow : K → E}
    (hflowm : Measurable flow)
    (hflow : ∀ x₀ : K, ∃ x : ℝ → E, x 0 = x₀ ∧ (∀ t ∈ Set.Icc 0 T, HasDerivAt x (s' (x t) t) t) ∧
      flow x₀ = x T)
    {k : ℕ} (hk : 0 < k) (hkh : T / k ≤ h₀)
    (hinv : ∀ (x : K) (τ : ℝ), (x : E) + (T / k) • s x τ ∈ K)
    {n : ℕ} (hn : 0 < n) (P : Measure (K × Y)) [IsProbabilityMeasure P]
    (L : BoundedLipschitzLoss Y) (hℓ : Measurable (Function.uncurry L.ℓ)) (hb : 0 < L.b)
    (hβ : 0 ≤ L.β) {R MK : ℝ} (hR : 0 < R) (hMK : 0 ≤ MK) (hK' : ∀ x : K, ‖(x : E)‖ ≤ MK)
    (hint : SchemeIntegrable hP 𝒮 h₀ T) {η δ : ℝ} (hη : 0 ≤ η) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ((Measure.pi fun _ : Fin n => P) {D | ¬ ∀ fhat,
        IsEmpMinimizer L D
          (compClass (linearReadouts (ambientFeature K) R) (schemeBall hP 𝒮 h₀ T k)) η fhat →
        risk L P fhat - sInf (risk L P '' linearReadouts flow R) ≤
          L.β * (R * ((Λs * Ms + Λτ) * Real.exp (Λs * T) / 2 * T ^ 2 / k)) + η +
            bvDev L n δ (R * MK / √n + 12 * 1 * R / √n * schemeVinf hP 𝒮 h₀ T)}
      ).toReal ≤ δ := by
  /- `thm:bv-id-bounds` with the class properties, `lem:ode-horizon-var` and
    `lem:ode-horizon-bias`. -/
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  exact bv_id_of_bounds P L hn hℓ hb hβ (horizon_class_measurable hP h𝒮 h₀ T R k)
    (isSupSeparable_compClass_linearReadouts lipschitzWith_ambientFeature hMK hK' hR.le
      (hasCountableUniformDense_of_totallyBounded
        ((ode_saturation hK hP h𝒮 h₀ T).1.subset (Set.subset_iUnion _ k))))
    (fun x => ⟨R * MK, fun _ hg => abs_le_of_mem_compClass_linearReadouts hK' hR.le hg x⟩)
    (⟨_, 0, by simpa using hR.le, rfl⟩ : (linearReadouts flow R).Nonempty)
    (fun c hc => by
      obtain ⟨w, -, rfl⟩ := hc
      exact (continuous_const.inner continuous_id).measurable.comp hflowm)
    (fun S => horizon_var hK hP h𝒮 ⟨s, hs⟩ hT hn S hR hMK hK' hint k)
    (horizon_bias hP h𝒮 hT hs hss' hs'x hs'τ hMs hflowm hflow hk hkh hinv P L hℓ hβ hR.le)
    hη hδ hδ1

omit [MeasurableSpace E] [BorelSpace E] in
@[blueprint "lem:ode-horizon-balance"
  (statement := /-- \textbf{(PL balancing with saturated variance, $p = 1$.)} For $n \ge 1$ the
    depth $k^\ast := \lceil\sqrt n\rceil \ge 1$ satisfies $1/k^\ast \le n^{-1/2}$, so
    $k^\ast \asymp n^{1/2} = n^{1/(2p)}$ balances the bias $k^{-1}$ against the saturated
    variance $n^{-1/2}$. -/)]
theorem horizon_balance {n : ℕ} (hn : 1 ≤ n) :
    0 < ⌈√(n : ℝ)⌉₊ ∧ (1 : ℝ) / ⌈√(n : ℝ)⌉₊ ≤ 1 / √n :=
  one_div_ceil_sqrt_le (by exact_mod_cast hn)

@[blueprint "cor:ode-horizon-depth"
  (statement := /-- \textbf{(Balanced value $O(n^{-1/2})$.)} Under the hypotheses of
    `prop:ode-horizon` with $k^\ast = \lceil\sqrt n\rceil$ (and $T/k^\ast \le h_0$, projection
    inactive at step size $T/k^\ast$),
    $$L[\hat h] - \inf_{\mathcal C} L \le \frac{\beta_\ell R C_E T^2}{\sqrt n} + \eta
      + \mathrm{dev}_{\ell,n,\delta}\Bigl(\frac{R M_K + 12 R\,\mathsf V_\infty}{\sqrt n}\Bigr)$$
    with probability at least $1 - \delta$: the balanced value is of order $n^{-1/2}$. -/)]
theorem cor_ode_horizon_depth [TopologicalSpace.SeparableSpace E] {Y : Type*} [MeasurableSpace Y]
    (hK : IsCompact K) (hP : IsProjectionOnto K proj) {𝒮 : Set (K → ℝ → E)} {Λs : ℝ≥0}
    (h𝒮 : ∀ s ∈ 𝒮, ∀ τ, LipschitzWith Λs (fun x => s x τ)) {h₀ T : ℝ} (hT : 0 ≤ T)
    {s : K → ℝ → E} (hs : s ∈ 𝒮) {s' : E → ℝ → E} (hss' : ∀ (x : K) (τ : ℝ), s x τ = s' x τ)
    {Λτ Ms : ℝ≥0} (hs'x : ∀ τ, LipschitzWith Λs (fun x => s' x τ))
    (hs'τ : ∀ x, LipschitzWith Λτ (s' x)) (hMs : ∀ x τ, ‖s' x τ‖ ≤ Ms) {flow : K → E}
    (hflowm : Measurable flow)
    (hflow : ∀ x₀ : K, ∃ x : ℝ → E, x 0 = x₀ ∧ (∀ t ∈ Set.Icc 0 T, HasDerivAt x (s' (x t) t) t) ∧
      flow x₀ = x T)
    {n : ℕ} (hn : 1 ≤ n) (hkh : T / ⌈√(n : ℝ)⌉₊ ≤ h₀)
    (hinv : ∀ (x : K) (τ : ℝ), (x : E) + (T / ⌈√(n : ℝ)⌉₊) • s x τ ∈ K)
    (P : Measure (K × Y)) [IsProbabilityMeasure P]
    (L : BoundedLipschitzLoss Y) (hℓ : Measurable (Function.uncurry L.ℓ)) (hb : 0 < L.b)
    (hβ : 0 ≤ L.β) {R MK : ℝ} (hR : 0 < R) (hMK : 0 ≤ MK) (hK' : ∀ x : K, ‖(x : E)‖ ≤ MK)
    (hint : SchemeIntegrable hP 𝒮 h₀ T) {η δ : ℝ} (hη : 0 ≤ η) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ((Measure.pi fun _ : Fin n => P) {D | ¬ ∀ fhat,
        IsEmpMinimizer L D (compClass (linearReadouts (ambientFeature K) R)
          (schemeBall hP 𝒮 h₀ T ⌈√(n : ℝ)⌉₊)) η fhat →
        risk L P fhat - sInf (risk L P '' linearReadouts flow R) ≤
          L.β * (R * ((Λs * Ms + Λτ) * Real.exp (Λs * T) / 2 * T ^ 2)) / √n + η +
            bvDev L n δ ((R * MK + 12 * R * schemeVinf hP 𝒮 h₀ T) / √n)}
      ).toReal ≤ δ := by
  /- `prop:ode-horizon` at $k^\ast = \lceil\sqrt n\rceil$ and `lem:ode-horizon-balance`. -/
  obtain ⟨hk, hkle⟩ := horizon_balance hn
  refine le_trans ?_ (prop_ode_horizon (n := n) hK hP h𝒮 hT hs hss' hs'x hs'τ hMs hflowm hflow
    hk hkh hinv (lt_of_lt_of_le Nat.one_pos hn) P L hℓ hb hβ hR hMK hK' hint hη hδ hδ1)
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun D hD => ?_)
  simp only [Set.mem_setOf_eq] at hD ⊢
  intro hall
  apply hD
  intro fhat hfhat
  have h1 := hall fhat hfhat
  have hpos : 0 ≤ L.β * (R * ((Λs * Ms + Λτ) * Real.exp (Λs * T) / 2 * T ^ 2)) := by positivity
  have h2 : L.β * (R * ((Λs * Ms + Λτ) * Real.exp (Λs * T) / 2 * T ^ 2 / ⌈√(n : ℝ)⌉₊)) ≤
      L.β * (R * ((Λs * Ms + Λτ) * Real.exp (Λs * T) / 2 * T ^ 2)) / √n := by
    calc L.β * (R * ((Λs * Ms + Λτ) * Real.exp (Λs * T) / 2 * T ^ 2 / ⌈√(n : ℝ)⌉₊))
        = L.β * (R * ((Λs * Ms + Λτ) * Real.exp (Λs * T) / 2 * T ^ 2)) *
          (1 / ⌈√(n : ℝ)⌉₊) := by ring
      _ ≤ L.β * (R * ((Λs * Ms + Λτ) * Real.exp (Λs * T) / 2 * T ^ 2)) * (1 / √n) :=
          mul_le_mul_of_nonneg_left hkle hpos
      _ = L.β * (R * ((Λs * Ms + Λτ) * Real.exp (Λs * T) / 2 * T ^ 2)) / √n := by ring
  have h3 : R * MK / √n + 12 * 1 * R / √n * schemeVinf hP 𝒮 h₀ T =
      (R * MK + 12 * R * schemeVinf hP 𝒮 h₀ T) / √n := by ring
  rw [h3] at h1
  linarith

end HorizonRegime

end LeanDeepgen
