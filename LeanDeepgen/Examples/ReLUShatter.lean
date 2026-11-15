import Mathlib
import Architect
import LeanDeepgen.Setting.WordBall
import LeanDeepgen.Setting.Metrics
import LeanDeepgen.Setting.Hypothesis
import LeanDeepgen.Setting.Rademacher
import LeanDeepgen.Growth.Envelope
import LeanDeepgen.Profiles.Profiles
import LeanDeepgen.Bounds.HiddenOutput
import LeanDeepgen.Bounds.Variance
import LeanDeepgen.Bounds.Shatter
import LeanDeepgen.Examples.ODE
import LeanDeepgen.Examples.Readout
import LeanDeepgen.Examples.Regimes
import LeanDeepgen.Examples.ReLU

/-!
# Worked example: deep ReLU networks shatter `k₁ B` points at depth `k₁ + B + 1`
(paper App. `sec:app-relu`, `prop:relu-shatter`)

The state space is the unit square `K = [0,1]²` of `E = ℝ² = EuclideanSpace ℝ (Fin 2)`
(`unitSquare`) with the coordinatewise clipping `Π_K` (`clipSquare`), a `1`-Lipschitz retraction
onto `K` (`isProjectionOnto_clipSquare`).  A state is written `(z, y)`: the *track* `z` is
coordinate `0` and the *register* `y` is coordinate `1`.

For a parameter `θ ∈ [0, 1/4]` the hidden layer is
`f_θ(z, y) = (clip(P(z) + s(z, y)), clip(4 relu(y) − 8 relu(y − 1/2) + θ ψ(z)))`
(`shatterBlock`, with `shatterP`, `shatterSort`, `shatterPsi`, `shatterTrack`,
`shatterRegister`).  It is a ReLU block `x ↦ Π_K(V_θ relu(W x + b) + c)` of width `11` with
`c = 0` (`shatterParam`, `reluBlock_shatterParam`): seven track units `relu(z − t)`, two register
units `relu(y)`, `relu(y − 1/2)`, and two sort units `relu(2z + y/4 − 17/16)`,
`relu(2z + y/4 − 19/16)`; only the output weights `V_θ` depend on `θ`.  Its weights satisfy
`‖W‖ ≤ 5`, `‖b‖ ≤ 2`, `‖V_θ‖ ≤ 17` (operator norms bounded by Frobenius norms,
`shatterParam_norms`) and the block is `‖V_θ‖ ‖W‖ ≤ 85`-Lipschitz
(`lipschitzWith_reluBlock_opNorm`), so `f_θ ∈ F_Λ = reluClass … w β_W β Λ` for every width
`w ≥ 11`, `β_W ≥ 17`, `β ≥ 2`, `Λ ≥ 85` (`shatterBlock_mem_reluClass`,
`shatterBlock_mem_reluClass_of_le`).

One layer acts on a state `(z, y) ∈ K` as follows (`shatterTrack_*`, `shatterRegister_*`):

* *wait*: `z ≤ 3/32`, `y = 0` gives `(2z, 0)`;
* *load*: `z ∈ [1/8, 3/16]`, `y = 0` gives `(2z, θ)`;
* *count*: `z ∈ [1/4, 3/8]` gives `(2z − 1/4, E(y))` with the shift
  `E(y) = clip(4 relu(y) − 8 relu(y − 1/2))` (`shatterShift`);
* *sort*: `z = 1/2` gives `z' = 3/4` if `y ≤ 1/4` and `z' = 7/8` if `y ≥ 3/4`;
* *hold*: `z ∈ [3/4, 1]` gives `z' = z`.

A word `c ∈ {0,1}^B` is stored in the parameter `θ(c) = code(c)/4` with
`code(c) = S_{c_1}(S_{c_2}(⋯ S_{c_B}(0)))`, `S_0(u) = u/4`, `S_1(u) = 1 − u/4` (`shatterS`,
`shatterCode`, `shatterTheta`); the shift `E` inverts `S_0` and `S_1` on `[0,1]`, so
`E^b(θ(c)) = S_{c_b}(code(c_{b+1}, …, c_B))` lies in `[0, 1/4]` or in `[3/4, 1]` according to the
letter `c_b` (`shatterShift_iterate_shatterTheta`).

The sample points are `x_{t,b} = (⅛ (1 + 2^{-b}) 2^{-(t-1)}, 0)` (`shatterPoint`, with `0`-based
indices).  Under any sequence of layers `f_{θ_1}, f_{θ_2}, …` with `θ_s ∈ [0, 1/4]` the point
`x_{t,b}` waits `t − 1` layers, loads `θ_t`, counts `b` layers (the register becomes
`E^b(θ_t)`), is sorted to `3/4` or `7/8`, and holds.  The orbit is first proved for real
sequences `(z_s, y_s)` satisfying the one-layer recursion (`shatter_orbit_wait`,
`shatter_orbit_count`, `shatter_orbit_hold`, `shatter_orbit_states`, `shatter_orbit_sink`,
`shatter_orbit`) and then read off for the composition `shatterNet θ s` of the first `s` layers
(`shatterNet_states`, `shatterNet_sink`).

* `prop_relu_shatter` (`prop:relu-shatter`) is the statement of the paper, the conjunction of
  its three parts: (i) membership, `shatterBlock_mem_reluClass_of_le` (`prop:relu-shatter-i`);
  (ii) shattering in terms of the parameters `θ_1, …, θ_{k₁+B+1} ∈ [0, 1/4]`,
  `prop_relu_shatter_params` (`prop:relu-shatter-ii`); (iii) the Rademacher lower bound,
  `prop_relu_shatter_rademacher` (`prop:relu-shatter-iii`).
* `prop_relu_shatter_labels` (`prop:relu-shatter-labels`), part (ii) in terms of the hidden
  class: for every `c ∈ {0,1}^{k₁ × B}` the composition `g ∈ B(k₁ + B + 1, F_Λ)` of the layers
  with parameters `θ_t = θ(c_{t,·})` (`shatterThetaSeq`, `shatterNet_shatterThetaSeq`) has
  first coordinate `g(x_{t,b})_0 = a_{c_{t,b}}` for all `t, b`, with `a_0 = 3/4`, `a_1 = 7/8`
  (`shatterSink`).
* `prop_relu_shatter_rademacher` (`prop:relu-shatter-iii`), part (iii): for `k ≥ k₁ + B + 1`,
  the linear output layers `H_R = {x ↦ ⟨u, x⟩ : ‖u‖ ≤ R}` and the sample `S = (x_{t,b})` of
  `n = k₁ B` points (`shatterSample`), `R̂_S(H_R ∘ B(k, F_Λ)) ≥ R/16`
  (`lem:shatter-rademacher-comp` with the output layer `x ↦ R x_0`).
* Both statements hold for every hidden-layer class `F` that contains the one-parameter family
  `{f_θ : θ ∈ [0, 1/4]}`: `prop_relu_shatter_labels_of_subset`
  (`prop:relu-shatter-labels-of-subset`) and `prop_relu_shatter_rademacher_of_subset`
  (`prop:relu-shatter-iii-of-subset`); the ReLU class is the special case `F = F_Λ`.
* `prop_relu_shatter_entropy` (`prop:relu-shatter-entropy`): consequently, by the hidden–output
  decomposition `thm:hidden-decomp-depth` (`A_H = 1`, `L = R`, here with `R = 1`) and
  `R̂_S(H_R) ≤ R√2/√n`, the entropy integral satisfies `V_k(S) ≥ √n/192 − √2/12`.  The
  total-boundedness and integrability hypotheses of the decomposition are proved for every
  class of Lipschitz layers with `log N(F, ε) ≤ p log(1 + C/ε)`
  (`totallyBounded_empSpace_wordBall_of_covering`, `sqrt_metricEntropy_wordBall_le_one_add`,
  `intervalIntegrable_wordBall_of_one_add`), in particular for `F_Λ`
  (`lem:relu-layer-covering`).  With `k₁ = B = ⌊(k−1)/2⌋` this is
  `V_k(S) ≥ ⌊(k−1)/2⌋/192 − √2/12`, linear in the depth
  (`prop_relu_shatter_entropy_linear`, `cor:relu-shatter-entropy-linear`).

## Conventions

The width is `11 + w'` in the explicit parameters (the last `w'` units are zero) and any
`w ≥ 11` in the statements.  Indices are `0`-based in Lean: `shatterPoint t b` is the paper's
`x_{t+1,b+1}`, and `shatterNet θ s` is the composition `f_{θ_{s-1}} ∘ ⋯ ∘ f_{θ_0}` of the first
`s` layers.
-/

open scoped NNReal ENNReal Real
open Metric MeasureTheory Set

namespace LeanDeepgen

local notation "E₂" => EuclideanSpace ℝ (Fin 2)

/-! ### Linear maps between the plane and `ℝ^w`, and the Lipschitz constant of a ReLU block -/

section PlaneMaps

variable {w : ℕ}

@[blueprint "def:relu-shatter-col-map"
  (statement := /-- The linear map $\mathbb R^2 \to \mathbb R^w$ with columns
    $\alpha, \gamma \in \mathbb R^w$: $(z, y) \mapsto z\,\alpha + y\,\gamma$, i.e. the matrix
    with rows $(\alpha_i, \gamma_i)$. -/)]
noncomputable def colMap (α γ : Fin w → ℝ) : E₂ →L[ℝ] EuclideanSpace ℝ (Fin w) :=
  (EuclideanSpace.proj (0 : Fin 2)).smulRight (WithLp.toLp 2 α : EuclideanSpace ℝ (Fin w)) +
    (EuclideanSpace.proj (1 : Fin 2)).smulRight (WithLp.toLp 2 γ : EuclideanSpace ℝ (Fin w))

@[blueprint "lem:relu-shatter-col-map-apply"
  (statement := /-- $(W x)_i = \alpha_i x_0 + \gamma_i x_1$ for the map
    `def:relu-shatter-col-map`. -/)]
theorem colMap_apply (α γ : Fin w → ℝ) (x : E₂) (i : Fin w) :
    colMap α γ x i = x 0 * α i + x 1 * γ i := by
  simp [colMap]

@[blueprint "def:relu-shatter-row-map"
  (statement := /-- The linear map $\mathbb R^w \to \mathbb R^2$ with rows
    $u, v \in \mathbb R^w$: $r \mapsto (\langle u, r\rangle, \langle v, r\rangle)$. -/)]
noncomputable def rowMap (u v : Fin w → ℝ) : EuclideanSpace ℝ (Fin w) →L[ℝ] E₂ :=
  (innerSL ℝ (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin w))).smulRight
      (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) +
    (innerSL ℝ (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin w))).smulRight
      (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))

@[blueprint "lem:relu-shatter-row-map-zero"
  (statement := /-- $(V r)_0 = \sum_i u_i r_i$ for the map `def:relu-shatter-row-map`. -/)]
theorem rowMap_apply_zero (u v : Fin w → ℝ) (r : EuclideanSpace ℝ (Fin w)) :
    rowMap u v r 0 = ∑ i, u i * r i := by
  simp [rowMap, PiLp.inner_apply, mul_comm]

@[blueprint "lem:relu-shatter-row-map-one"
  (statement := /-- $(V r)_1 = \sum_i v_i r_i$ for the map `def:relu-shatter-row-map`. -/)]
theorem rowMap_apply_one (u v : Fin w → ℝ) (r : EuclideanSpace ℝ (Fin w)) :
    rowMap u v r 1 = ∑ i, v i * r i := by
  simp [rowMap, PiLp.inner_apply, mul_comm]

@[blueprint "lem:relu-shatter-col-map-norm"
  (statement := /-- (Operator norm bounded by the Frobenius norm.) If
    $\sum_i \alpha_i^2 + \sum_i \gamma_i^2 \le C^2$ with $C \ge 0$ then the map
    `def:relu-shatter-col-map` has $\|W\|_{\rm op} \le C$: by the Cauchy--Schwarz inequality,
    $\|x_0\alpha + x_1\gamma\| \le |x_0|\|\alpha\| + |x_1|\|\gamma\| \le
    \sqrt{\|\alpha\|^2 + \|\gamma\|^2}\,\|x\|$. -/)]
theorem norm_colMap_le (α γ : Fin w → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∑ i, α i ^ 2 + ∑ i, γ i ^ 2 ≤ C ^ 2) : ‖colMap α γ‖ ≤ C := by
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun x => ?_
  set a : EuclideanSpace ℝ (Fin w) := WithLp.toLp 2 α with ha
  set g : EuclideanSpace ℝ (Fin w) := WithLp.toLp 2 γ with hg
  have hx : colMap α γ x = x 0 • a + x 1 • g := by
    simp [colMap, ha, hg]
  have hna : ‖a‖ ^ 2 = ∑ i, α i ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [ha]
  have hng : ‖g‖ ^ 2 = ∑ i, γ i ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [hg]
  have hnx : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_two]
  have h1 : ‖colMap α γ x‖ ≤ |x 0| * ‖a‖ + |x 1| * ‖g‖ := by
    rw [hx]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  refine h1.trans ?_
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
  have h2 : (|x 0| * ‖a‖ + |x 1| * ‖g‖) ^ 2 ≤ (x 0 ^ 2 + x 1 ^ 2) * (‖a‖ ^ 2 + ‖g‖ ^ 2) := by
    nlinarith [sq_nonneg (|x 0| * ‖g‖ - |x 1| * ‖a‖), sq_abs (x 0), sq_abs (x 1)]
  calc (|x 0| * ‖a‖ + |x 1| * ‖g‖) ^ 2 ≤ (x 0 ^ 2 + x 1 ^ 2) * (‖a‖ ^ 2 + ‖g‖ ^ 2) := h2
    _ ≤ ‖x‖ ^ 2 * C ^ 2 := by
        rw [hnx, hna, hng]
        exact mul_le_mul_of_nonneg_left h (by positivity)
    _ = (C * ‖x‖) ^ 2 := by ring

@[blueprint "lem:relu-shatter-row-map-norm"
  (statement := /-- (Operator norm bounded by the Frobenius norm.) If
    $\sum_i u_i^2 + \sum_i v_i^2 \le C^2$ with $C \ge 0$ then the map
    `def:relu-shatter-row-map` has $\|V\|_{\rm op} \le C$:
    $\|V r\|^2 = \langle u, r\rangle^2 + \langle v, r\rangle^2 \le (\|u\|^2 + \|v\|^2)\|r\|^2$. -/)]
theorem norm_rowMap_le (u v : Fin w → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∑ i, u i ^ 2 + ∑ i, v i ^ 2 ≤ C ^ 2) : ‖rowMap u v‖ ≤ C := by
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun r => ?_
  set a : EuclideanSpace ℝ (Fin w) := WithLp.toLp 2 u with ha
  set g : EuclideanSpace ℝ (Fin w) := WithLp.toLp 2 v with hg
  have hna : ‖a‖ ^ 2 = ∑ i, u i ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [ha]
  have hng : ‖g‖ ^ 2 = ∑ i, v i ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [hg]
  have h0 : rowMap u v r 0 = inner ℝ a r := by
    simp [rowMap, ha]
  have h1 : rowMap u v r 1 = inner ℝ g r := by
    simp [rowMap, hg]
  have hn : ‖rowMap u v r‖ ^ 2 = inner ℝ a r ^ 2 + inner ℝ g r ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_two, h0, h1]
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
  have ha' : inner ℝ a r ^ 2 ≤ ‖a‖ ^ 2 * ‖r‖ ^ 2 := by
    rw [← mul_pow, ← sq_abs (inner ℝ a r)]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm a r) 2
  have hg' : inner ℝ g r ^ 2 ≤ ‖g‖ ^ 2 * ‖r‖ ^ 2 := by
    rw [← mul_pow, ← sq_abs (inner ℝ g r)]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm g r) 2
  calc ‖rowMap u v r‖ ^ 2 = inner ℝ a r ^ 2 + inner ℝ g r ^ 2 := hn
    _ ≤ (‖a‖ ^ 2 + ‖g‖ ^ 2) * ‖r‖ ^ 2 := by linarith
    _ ≤ C ^ 2 * ‖r‖ ^ 2 := by
        rw [hna, hng]
        exact mul_le_mul_of_nonneg_right h (by positivity)
    _ = (C * ‖r‖) ^ 2 := by ring

@[blueprint "def:relu-shatter-plane-param"
  (statement := /-- The parameters of a ReLU block of width $w$ on $\mathbb R^2$ with input
    weights $(\alpha_i, \gamma_i)$, thresholds $t_i$, output weights $u_i$ (first coordinate)
    and $v_i$ (second coordinate), and $c = 0$: $W$ is `def:relu-shatter-col-map`,
    $b = (-t_i)_i$, $V$ is `def:relu-shatter-row-map`, so that
    $V\,\mathrm{relu}(Wx + b) = \bigl(\sum_i u_i\,\mathrm{relu}(\alpha_i z + \gamma_i y - t_i),
    \sum_i v_i\,\mathrm{relu}(\alpha_i z + \gamma_i y - t_i)\bigr)$ for $x = (z, y)$. -/)]
noncomputable def planeParam (α γ t u v : Fin w → ℝ) : ReLUParam E₂ w :=
  (colMap α γ, WithLp.toLp 2 (fun i => -t i), rowMap u v, 0)

@[blueprint "lem:relu-shatter-plane-param-block"
  (statement := /-- For the parameters `def:relu-shatter-plane-param` and $x = (z, y) \in K$,
    $f_\vartheta(x) = \Pi_K\bigl(\sum_i u_i \max\{\alpha_i z + \gamma_i y - t_i, 0\},
    \sum_i v_i \max\{\alpha_i z + \gamma_i y - t_i, 0\}\bigr)$. -/)]
theorem reluBlock_planeParam {K : Set E₂} {proj : E₂ → E₂} (hP : IsProjectionOnto K proj)
    (α γ t u v : Fin w → ℝ) (x : K) :
    (reluBlock hP (planeParam α γ t u v) x : E₂) =
      proj (WithLp.toLp 2
        ![∑ i, u i * max ((x : E₂) 0 * α i + (x : E₂) 1 * γ i - t i) 0,
          ∑ i, v i * max ((x : E₂) 0 * α i + (x : E₂) 1 * γ i - t i) 0]) := by
  change proj _ = proj _
  congr 1
  ext j
  fin_cases j
  · simp [planeParam, rowMap_apply_zero, colMap_apply, sub_eq_add_neg]
  · simp [planeParam, rowMap_apply_one, colMap_apply, sub_eq_add_neg]

end PlaneMaps

section BlockLipschitz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {K : Set E} {proj : E → E}
  {w : ℕ}

@[blueprint "lem:relu-shatter-block-lipschitz"
  (statement := /-- A ReLU block $f_\vartheta(x) = \Pi_K(V\,\mathrm{relu}(Wx + b) + c)$ is
    $\|V\|_{\rm op}\|W\|_{\rm op}$-Lipschitz: it is the composition of the $1$-Lipschitz maps
    $\Pi_K$ and $\mathrm{relu}$ with the affine maps $x \mapsto Wx + b$ and
    $r \mapsto Vr + c$. -/)]
theorem lipschitzWith_reluBlock_opNorm (hP : IsProjectionOnto K proj) (θ : ReLUParam E w) :
    LipschitzWith (‖θ.2.2.1‖₊ * ‖θ.1‖₊) (reluBlock hP θ) := by
  obtain ⟨W, b, V, c⟩ := θ
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have h1 : dist (reluBlock hP (W, b, V, c) x) (reluBlock hP (W, b, V, c) y) ≤
      dist (V (reluVec (W x + b)) + c) (V (reluVec (W y + b)) + c) := by
    have h := hP.lipschitz.dist_le_mul (V (reluVec (W x + b)) + c) (V (reluVec (W y + b)) + c)
    rw [NNReal.coe_one, one_mul] at h
    exact h
  refine h1.trans ?_
  rw [dist_add_right, dist_eq_norm, ← map_sub]
  have h2 : ‖reluVec (W x + b) - reluVec (W y + b)‖ ≤ ‖W‖ * dist x y := by
    have h := lipschitzWith_reluVec.dist_le_mul (W x + b) (W y + b)
    rw [NNReal.coe_one, one_mul, dist_add_right, dist_eq_norm, dist_eq_norm, ← map_sub] at h
    refine h.trans ((W.le_opNorm _).trans (le_of_eq ?_))
    rw [Subtype.dist_eq, dist_eq_norm]
  calc ‖V (reluVec (W x + b) - reluVec (W y + b))‖
      ≤ ‖V‖ * ‖reluVec (W x + b) - reluVec (W y + b)‖ := V.le_opNorm _
    _ ≤ ‖V‖ * (‖W‖ * dist x y) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = ((‖V‖₊ * ‖W‖₊ : ℝ≥0) : ℝ) * dist x y := by
        rw [NNReal.coe_mul, coe_nnnorm, coe_nnnorm, mul_assoc]

end BlockLipschitz

/-! ### The state space `[0,1]²` and its clipping -/

section Square

@[blueprint "def:relu-shatter-clip-square"
  (statement := /-- The coordinatewise clipping of $\mathbb R^2$ to the unit square:
    $\Pi_K(z, y) = (\mathrm{clip}(z), \mathrm{clip}(y))$ with
    $\mathrm{clip}(a) = \max\{0, \min\{1, a\}\}$ (`def:relu-clip-unit`). -/)]
noncomputable def clipSquare (x : E₂) : E₂ := WithLp.toLp 2 fun i => clipUnit (x i)

@[simp, blueprint "lem:relu-shatter-clip-square-apply"
  (statement := /-- $\Pi_K(x)_i = \mathrm{clip}(x_i)$. -/)]
theorem clipSquare_apply (x : E₂) (i : Fin 2) : clipSquare x i = clipUnit (x i) := rfl

@[blueprint "def:relu-shatter-unit-square"
  (statement := /-- The state space $K = [0,1]^2 \subseteq \mathbb R^2$. A state is written
    $(z, y)$: the \emph{track} $z$ is coordinate $0$ and the \emph{register} $y$ is
    coordinate $1$. -/)]
def unitSquare : Set E₂ := {x | ∀ i, x i ∈ Icc (0 : ℝ) 1}

@[blueprint "lem:relu-shatter-clip-square-projection"
  (statement := /-- $\Pi_K$ is a $1$-Lipschitz retraction of $\mathbb R^2$ (Euclidean norm)
    onto $K = [0,1]^2$ (`def:ode-projection`): it maps into $K$, is the identity on $K$, and
    $|\mathrm{clip}(a) - \mathrm{clip}(b)| \le |a - b|$ coordinatewise. -/)]
theorem isProjectionOnto_clipSquare : IsProjectionOnto unitSquare clipSquare where
  mem x i := isProjectionOnto_clipUnit.mem (x i)
  eq_of_mem x hx := by
    ext i
    exact clipUnit_of_mem (hx i)
  lipschitz := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [NNReal.coe_one, one_mul, EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
    change dist (clipUnit (x i)) (clipUnit (y i)) ^ 2 ≤ dist (x i) (y i) ^ 2
    have h := isProjectionOnto_clipUnit.lipschitz.dist_le_mul (x i) (y i)
    rw [NNReal.coe_one, one_mul] at h
    exact pow_le_pow_left₀ dist_nonneg h 2

@[blueprint "lem:relu-shatter-unit-square-norm"
  (statement := /-- $\|x\| \le \sqrt 2$ for $x \in K = [0,1]^2$. -/)]
theorem norm_le_sqrt_two_of_mem_unitSquare {x : E₂} (hx : x ∈ unitSquare) : ‖x‖ ≤ √2 := by
  obtain ⟨h00, h01⟩ := hx 0
  obtain ⟨h10, h11⟩ := hx 1
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  rw [Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  nlinarith

end Square

/-! ### The real functions of the block: `P`, `ψ`, `s`, the shift `E` and the two coordinates -/

section RealFunctions

@[blueprint "def:relu-shatter-P"
  (statement := /-- The track map
    $P(z) = 2\,\mathrm{relu}(z) - 4\,\mathrm{relu}(z - \tfrac3{16}) + 4\,\mathrm{relu}(z - \tfrac14)
    - \tfrac52\,\mathrm{relu}(z - \tfrac12) + \tfrac32\,\mathrm{relu}(z - \tfrac34)$. -/)]
noncomputable def shatterP (z : ℝ) : ℝ :=
  2 * max z 0 - 4 * max (z - 3 / 16) 0 + 4 * max (z - 1 / 4) 0 - 5 / 2 * max (z - 1 / 2) 0
    + 3 / 2 * max (z - 3 / 4) 0

@[blueprint "def:relu-shatter-psi"
  (statement := /-- The loading window
    $\psi(z) = 32\,\mathrm{relu}(z - \tfrac3{32}) - 32\,\mathrm{relu}(z - \tfrac18)
    - 16\,\mathrm{relu}(z - \tfrac3{16}) + 16\,\mathrm{relu}(z - \tfrac14)$. -/)]
noncomputable def shatterPsi (z : ℝ) : ℝ :=
  32 * max (z - 3 / 32) 0 - 32 * max (z - 1 / 8) 0 - 16 * max (z - 3 / 16) 0
    + 16 * max (z - 1 / 4) 0

@[blueprint "def:relu-shatter-sort"
  (statement := /-- The sorting term
    $s(z, y) = \mathrm{relu}\bigl(2(z - \tfrac12) + \tfrac14(y - \tfrac14)\bigr)
    - \mathrm{relu}\bigl(2(z - \tfrac12) + \tfrac14(y - \tfrac34)\bigr)$. -/)]
noncomputable def shatterSort (z y : ℝ) : ℝ :=
  max (2 * (z - 1 / 2) + 1 / 4 * (y - 1 / 4)) 0 - max (2 * (z - 1 / 2) + 1 / 4 * (y - 3 / 4)) 0

@[blueprint "def:relu-shatter-shift"
  (statement := /-- The shift of the register:
    $E(y) = \mathrm{clip}\bigl(4\,\mathrm{relu}(y) - 8\,\mathrm{relu}(y - \tfrac12)\bigr)$
    (the tent map on $[0,1]$). -/)]
noncomputable def shatterShift (y : ℝ) : ℝ := clipUnit (4 * max y 0 - 8 * max (y - 1 / 2) 0)

@[blueprint "def:relu-shatter-track"
  (statement := /-- The track coordinate of one layer:
    $(z, y) \mapsto \mathrm{clip}\bigl(P(z) + s(z, y)\bigr)$. -/)]
noncomputable def shatterTrack (z y : ℝ) : ℝ := clipUnit (shatterP z + shatterSort z y)

@[blueprint "def:relu-shatter-register"
  (statement := /-- The register coordinate of one layer with parameter $\theta$:
    $(z, y) \mapsto \mathrm{clip}\bigl(4\,\mathrm{relu}(y) - 8\,\mathrm{relu}(y - \tfrac12)
    + \theta\,\psi(z)\bigr)$. -/)]
noncomputable def shatterRegister (θ z y : ℝ) : ℝ :=
  clipUnit (4 * max y 0 - 8 * max (y - 1 / 2) 0 + θ * shatterPsi z)

/-! #### Facts 1–6 -/

@[blueprint "lem:relu-shatter-P-low"
  (statement := /-- (Fact 1.) $P(z) = 2z$ for $z \in [0, \tfrac3{16}]$. -/)]
theorem shatterP_of_le {z : ℝ} (h0 : 0 ≤ z) (h : z ≤ 3 / 16) : shatterP z = 2 * z := by
  unfold shatterP
  rw [max_eq_left h0, max_eq_right (by linarith), max_eq_right (by linarith),
    max_eq_right (by linarith), max_eq_right (by linarith)]
  ring

@[blueprint "lem:relu-shatter-P-mid"
  (statement := /-- (Facts 2 and 3.) $P(z) = 2z - \tfrac14$ for $z \in [\tfrac14, \tfrac12]$; in
    particular $P(\tfrac12) = \tfrac34$. -/)]
theorem shatterP_of_mem {z : ℝ} (h1 : 1 / 4 ≤ z) (h2 : z ≤ 1 / 2) :
    shatterP z = 2 * z - 1 / 4 := by
  unfold shatterP
  rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith),
    max_eq_right (by linarith), max_eq_right (by linarith)]
  ring

@[blueprint "lem:relu-shatter-P-high"
  (statement := /-- (Fact 4.) $P(z) = z - \tfrac18$ for $z \ge \tfrac34$. -/)]
theorem shatterP_of_ge {z : ℝ} (h : 3 / 4 ≤ z) : shatterP z = z - 1 / 8 := by
  unfold shatterP
  rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith),
    max_eq_left (by linarith), max_eq_left (by linarith)]
  ring

@[blueprint "lem:relu-shatter-sort-low"
  (statement := /-- (Facts 1 and 2.) $s(z, y) = 0$ for $z \le \tfrac38$ and $y \le 1$. -/)]
theorem shatterSort_of_le {z y : ℝ} (hz : z ≤ 3 / 8) (hy : y ≤ 1) : shatterSort z y = 0 := by
  unfold shatterSort
  rw [max_eq_right (by linarith), max_eq_right (by linarith), sub_zero]

@[blueprint "lem:relu-shatter-sort-half-zero"
  (statement := /-- (Fact 3.) $s(\tfrac12, y) = 0$ for $y \le \tfrac14$. -/)]
theorem shatterSort_half_of_le {y : ℝ} (hy : y ≤ 1 / 4) : shatterSort (1 / 2) y = 0 := by
  unfold shatterSort
  rw [max_eq_right (by linarith), max_eq_right (by linarith), sub_zero]

@[blueprint "lem:relu-shatter-sort-half-one"
  (statement := /-- (Fact 3.) $s(\tfrac12, y) = \tfrac18$ for $y \ge \tfrac34$. -/)]
theorem shatterSort_half_of_ge {y : ℝ} (hy : 3 / 4 ≤ y) : shatterSort (1 / 2) y = 1 / 8 := by
  unfold shatterSort
  rw [max_eq_left (by linarith), max_eq_left (by linarith)]
  ring

@[blueprint "lem:relu-shatter-sort-high"
  (statement := /-- (Fact 4.) $s(z, y) = \tfrac18$ for $z \ge \tfrac34$ and $y \ge 0$. -/)]
theorem shatterSort_of_ge {z y : ℝ} (hz : 3 / 4 ≤ z) (hy : 0 ≤ y) : shatterSort z y = 1 / 8 := by
  unfold shatterSort
  rw [max_eq_left (by linarith), max_eq_left (by linarith)]
  ring

@[blueprint "lem:relu-shatter-psi-low"
  (statement := /-- (Fact 5.) $\psi(z) = 0$ for $z \le \tfrac3{32}$. -/)]
theorem shatterPsi_of_le {z : ℝ} (h : z ≤ 3 / 32) : shatterPsi z = 0 := by
  unfold shatterPsi
  rw [max_eq_right (by linarith), max_eq_right (by linarith), max_eq_right (by linarith),
    max_eq_right (by linarith)]
  ring

@[blueprint "lem:relu-shatter-psi-window"
  (statement := /-- (Fact 5.) $\psi(z) = 1$ for $z \in [\tfrac18, \tfrac3{16}]$. -/)]
theorem shatterPsi_of_mem {z : ℝ} (h1 : 1 / 8 ≤ z) (h2 : z ≤ 3 / 16) : shatterPsi z = 1 := by
  unfold shatterPsi
  rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_right (by linarith),
    max_eq_right (by linarith)]
  ring

@[blueprint "lem:relu-shatter-psi-high"
  (statement := /-- (Fact 5.) $\psi(z) = 0$ for $z \ge \tfrac14$. -/)]
theorem shatterPsi_of_ge {z : ℝ} (h : 1 / 4 ≤ z) : shatterPsi z = 0 := by
  unfold shatterPsi
  rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith),
    max_eq_left (by linarith)]
  ring

@[blueprint "lem:relu-shatter-shift-low"
  (statement := /-- (Fact 6.) $E(u/4) = u$ for $u \in [0,1]$. -/)]
theorem shatterShift_div_four {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : shatterShift (u / 4) = u := by
  obtain ⟨h0, h1⟩ := hu
  unfold shatterShift
  rw [max_eq_left (by linarith), max_eq_right (by linarith)]
  rw [clipUnit_of_mem ⟨by linarith, by linarith⟩]
  ring

@[blueprint "lem:relu-shatter-shift-zero"
  (statement := /-- (Fact 6.) $E(0) = 0$. -/)]
theorem shatterShift_zero : shatterShift 0 = 0 := by
  have h := shatterShift_div_four (u := 0) ⟨le_rfl, zero_le_one⟩
  rwa [zero_div] at h

@[blueprint "lem:relu-shatter-shift-high"
  (statement := /-- (Fact 6.) $E(1 - u/4) = u$ for $u \in [0,1]$. -/)]
theorem shatterShift_one_sub {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    shatterShift (1 - u / 4) = u := by
  obtain ⟨h0, h1⟩ := hu
  unfold shatterShift
  rw [max_eq_left (by linarith), max_eq_left (by linarith)]
  rw [clipUnit_of_mem ⟨by linarith, by linarith⟩]
  ring

/-! #### One layer: wait, load, count, sort, hold -/

@[blueprint "lem:relu-shatter-track-double"
  (statement := /-- (Wait and load, track.) For $z \in [0, \tfrac3{16}]$ and $y \le 1$ the new
    track is $\mathrm{clip}(P(z) + s(z, y)) = 2z$. -/)]
theorem shatterTrack_of_le {z y : ℝ} (h0 : 0 ≤ z) (h : z ≤ 3 / 16) (hy : y ≤ 1) :
    shatterTrack z y = 2 * z := by
  rw [shatterTrack, shatterP_of_le h0 h, shatterSort_of_le (by linarith) hy, add_zero]
  exact clipUnit_of_mem ⟨by linarith, by linarith⟩

@[blueprint "lem:relu-shatter-register-wait"
  (statement := /-- (Wait, register.) For $z \le \tfrac3{32}$ and $y = 0$ the new register is
    $0$, for every $\theta$. -/)]
theorem shatterRegister_wait {θ z : ℝ} (h : z ≤ 3 / 32) : shatterRegister θ z 0 = 0 := by
  rw [shatterRegister, shatterPsi_of_le h, max_eq_left le_rfl, max_eq_right (by norm_num)]
  rw [clipUnit_of_mem ⟨by norm_num, by norm_num⟩]
  ring

@[blueprint "lem:relu-shatter-register-load"
  (statement := /-- (Load, register.) For $z \in [\tfrac18, \tfrac3{16}]$, $y = 0$ and
    $\theta \in [0, \tfrac14]$ the new register is $\theta$. -/)]
theorem shatterRegister_load {θ z : ℝ} (hθ : θ ∈ Icc (0 : ℝ) (1 / 4)) (h1 : 1 / 8 ≤ z)
    (h2 : z ≤ 3 / 16) : shatterRegister θ z 0 = θ := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  rw [shatterRegister, shatterPsi_of_mem h1 h2, max_eq_left le_rfl, max_eq_right (by norm_num)]
  rw [clipUnit_of_mem ⟨by linarith, by linarith⟩]
  ring

@[blueprint "lem:relu-shatter-track-count"
  (statement := /-- (Count, track.) For $z \in [\tfrac14, \tfrac38]$ and $y \le 1$ the new
    track is $2z - \tfrac14$. -/)]
theorem shatterTrack_count {z y : ℝ} (h1 : 1 / 4 ≤ z) (h2 : z ≤ 3 / 8) (hy : y ≤ 1) :
    shatterTrack z y = 2 * z - 1 / 4 := by
  rw [shatterTrack, shatterP_of_mem h1 (by linarith), shatterSort_of_le h2 hy, add_zero]
  exact clipUnit_of_mem ⟨by linarith, by linarith⟩

@[blueprint "lem:relu-shatter-register-count"
  (statement := /-- (Count, register.) For $z \ge \tfrac14$ the new register is $E(y)$, for
    every $\theta$. -/)]
theorem shatterRegister_count {θ z : ℝ} (h1 : 1 / 4 ≤ z) (y : ℝ) :
    shatterRegister θ z y = shatterShift y := by
  rw [shatterRegister, shatterPsi_of_ge h1, mul_zero, add_zero, shatterShift]

@[blueprint "lem:relu-shatter-track-sort-zero"
  (statement := /-- (Sort.) For $z = \tfrac12$ and $y \le \tfrac14$ the new track is
    $\tfrac34$. -/)]
theorem shatterTrack_sort_zero {y : ℝ} (hy : y ≤ 1 / 4) : shatterTrack (1 / 2) y = 3 / 4 := by
  rw [shatterTrack, shatterP_of_mem (by norm_num) le_rfl, shatterSort_half_of_le hy]
  rw [clipUnit_of_mem ⟨by norm_num, by norm_num⟩]
  norm_num

@[blueprint "lem:relu-shatter-track-sort-one"
  (statement := /-- (Sort.) For $z = \tfrac12$ and $y \ge \tfrac34$ the new track is
    $\tfrac78$. -/)]
theorem shatterTrack_sort_one {y : ℝ} (hy : 3 / 4 ≤ y) : shatterTrack (1 / 2) y = 7 / 8 := by
  rw [shatterTrack, shatterP_of_mem (by norm_num) le_rfl, shatterSort_half_of_ge hy]
  rw [clipUnit_of_mem ⟨by norm_num, by norm_num⟩]
  norm_num

@[blueprint "lem:relu-shatter-track-hold"
  (statement := /-- (Hold.) For $z \in [\tfrac34, 1]$ and $y \ge 0$ the new track is $z$; in
    particular the values $\tfrac34$ and $\tfrac78$ are kept by every layer. -/)]
theorem shatterTrack_hold {z y : ℝ} (h1 : 3 / 4 ≤ z) (h2 : z ≤ 1) (hy : 0 ≤ y) :
    shatterTrack z y = z := by
  rw [shatterTrack, shatterP_of_ge h1, shatterSort_of_ge h1 hy]
  rw [clipUnit_of_mem ⟨by linarith, by linarith⟩]
  ring

end RealFunctions

/-! ### The block as a ReLU block of width `11` and its membership in `F_Λ` -/

section Block

@[blueprint "def:relu-shatter-in-z"
  (statement := /-- Input weights of the $11 + w'$ units on the track $z$:
    $\alpha = (1,1,1,1,1,1,1;\ 0,0;\ 2,2;\ 0,\dots,0)$ (seven track units, two register units,
    two sort units, $w'$ zero units). -/)]
noncomputable def shatterInZ (w' : ℕ) : Fin (11 + w') → ℝ :=
  Fin.append ![1, 1, 1, 1, 1, 1, 1, 0, 0, 2, 2] 0

@[blueprint "def:relu-shatter-in-y"
  (statement := /-- Input weights of the units on the register $y$:
    $\gamma = (0,0,0,0,0,0,0;\ 1,1;\ \tfrac14,\tfrac14;\ 0,\dots,0)$. -/)]
noncomputable def shatterInY (w' : ℕ) : Fin (11 + w') → ℝ :=
  Fin.append ![0, 0, 0, 0, 0, 0, 0, 1, 1, 1 / 4, 1 / 4] 0

@[blueprint "def:relu-shatter-threshold"
  (statement := /-- Thresholds of the units ($b = -t$):
    $t = (0, \tfrac3{32}, \tfrac18, \tfrac3{16}, \tfrac14, \tfrac12, \tfrac34;\ 0, \tfrac12;\
    \tfrac{17}{16}, \tfrac{19}{16};\ 0,\dots,0)$. -/)]
noncomputable def shatterThreshold (w' : ℕ) : Fin (11 + w') → ℝ :=
  Fin.append ![0, 3 / 32, 1 / 8, 3 / 16, 1 / 4, 1 / 2, 3 / 4, 0, 1 / 2, 17 / 16, 19 / 16] 0

@[blueprint "def:relu-shatter-out-z"
  (statement := /-- Output weights for the track coordinate:
    $v^z = (2, 0, 0, -4, 4, -\tfrac52, \tfrac32;\ 0, 0;\ 1, -1;\ 0,\dots,0)$. -/)]
noncomputable def shatterOutZ (w' : ℕ) : Fin (11 + w') → ℝ :=
  Fin.append ![2, 0, 0, -4, 4, -5 / 2, 3 / 2, 0, 0, 1, -1] 0

@[blueprint "def:relu-shatter-out-y"
  (statement := /-- Output weights for the register coordinate, the only weights that depend
    on $\theta$: $v^y_\theta = (0, 32\theta, -32\theta, -16\theta, 16\theta, 0, 0;\ 4, -8;\
    0, 0;\ 0,\dots,0)$. -/)]
noncomputable def shatterOutY (w' : ℕ) (θ : ℝ) : Fin (11 + w') → ℝ :=
  Fin.append ![0, 32 * θ, -32 * θ, -16 * θ, 16 * θ, 0, 0, 4, -8, 0, 0] 0

@[blueprint "def:relu-shatter-param"
  (statement := /-- The parameters $\vartheta_\theta = (W, b, V_\theta, 0)$ of the block
    $f_\theta$ at width $11 + w'$ (`def:relu-shatter-plane-param` with the weights
    `def:relu-shatter-in-z`, `def:relu-shatter-in-y`, `def:relu-shatter-threshold`,
    `def:relu-shatter-out-z`, `def:relu-shatter-out-y`). Only $V_\theta$ depends on
    $\theta$. -/)]
noncomputable def shatterParam (w' : ℕ) (θ : ℝ) : ReLUParam E₂ (11 + w') :=
  planeParam (shatterInZ w') (shatterInY w') (shatterThreshold w') (shatterOutZ w')
    (shatterOutY w' θ)

@[blueprint "lem:relu-shatter-sum-z"
  (statement := /-- The unit sum of the track coordinate at width $11 + w'$ (the padding units
    vanish): $\sum_i v^z_i\,\mathrm{relu}(\alpha_i z + \gamma_i y - t_i) = P(z) + s(z, y)$. -/)]
theorem sum_shatterOutZ (w' : ℕ) (z y : ℝ) :
    ∑ i, shatterOutZ w' i *
        max (z * shatterInZ w' i + y * shatterInY w' i - shatterThreshold w' i) 0 =
      shatterP z + shatterSort z y := by
  have e1 : (2 : ℝ) * (z - 1 / 2) + 1 / 4 * (y - 1 / 4) = z * 2 + y * (1 / 4) - 17 / 16 := by ring
  have e2 : (2 : ℝ) * (z - 1 / 2) + 1 / 4 * (y - 3 / 4) = z * 2 + y * (1 / 4) - 19 / 16 := by ring
  rw [shatterSort, e1, e2]
  simp [shatterOutZ, shatterInZ, shatterInY, shatterThreshold, Fin.sum_univ_add,
    Fin.sum_univ_succ, shatterP]
  ring

@[blueprint "lem:relu-shatter-sum-y"
  (statement := /-- The unit sum of the register coordinate at width $11 + w'$:
    $\sum_i v^y_{\theta,i}\,\mathrm{relu}(\alpha_i z + \gamma_i y - t_i) = 4\,\mathrm{relu}(y)
    - 8\,\mathrm{relu}(y - \tfrac12) + \theta\,\psi(z)$. -/)]
theorem sum_shatterOutY (w' : ℕ) (θ z y : ℝ) :
    ∑ i, shatterOutY w' θ i *
        max (z * shatterInZ w' i + y * shatterInY w' i - shatterThreshold w' i) 0 =
      4 * max y 0 - 8 * max (y - 1 / 2) 0 + θ * shatterPsi z := by
  simp [shatterOutY, shatterInZ, shatterInY, shatterThreshold, Fin.sum_univ_add,
    Fin.sum_univ_succ, shatterPsi]
  ring

@[blueprint "def:relu-shatter-block"
  (statement := /-- The hidden layer with parameter $\theta$ on the state space $K = [0,1]^2$:
    $$f_\theta(z, y) = \Bigl(\mathrm{clip}\bigl(P(z) + s(z, y)\bigr),\
      \mathrm{clip}\bigl(4\,\mathrm{relu}(y) - 8\,\mathrm{relu}(y - \tfrac12)
      + \theta\,\psi(z)\bigr)\Bigr).$$ -/)]
noncomputable def shatterBlock (θ : ℝ) : unitSquare → unitSquare :=
  fun x => ⟨WithLp.toLp 2 ![shatterTrack ((x : E₂) 0) ((x : E₂) 1),
      shatterRegister θ ((x : E₂) 0) ((x : E₂) 1)],
    Fin.forall_fin_two.2 ⟨isProjectionOnto_clipUnit.mem _, isProjectionOnto_clipUnit.mem _⟩⟩

@[blueprint "lem:relu-shatter-block-zero"
  (statement := /-- The track coordinate of $f_\theta(z, y)$ is
    $\mathrm{clip}(P(z) + s(z, y))$. -/)]
theorem shatterBlock_apply_zero (θ : ℝ) (x : unitSquare) :
    (shatterBlock θ x : E₂) 0 = shatterTrack ((x : E₂) 0) ((x : E₂) 1) := rfl

@[blueprint "lem:relu-shatter-block-one"
  (statement := /-- The register coordinate of $f_\theta(z, y)$ is
    $\mathrm{clip}(4\,\mathrm{relu}(y) - 8\,\mathrm{relu}(y - \tfrac12) + \theta\,\psi(z))$. -/)]
theorem shatterBlock_apply_one (θ : ℝ) (x : unitSquare) :
    (shatterBlock θ x : E₂) 1 = shatterRegister θ ((x : E₂) 0) ((x : E₂) 1) := rfl

@[blueprint "lem:relu-shatter-block-relu"
  (statement := /-- (\textbf{$f_\theta$ is a ReLU block of width $11 + w'$.}) With the clipping
    $\Pi_K$ of the unit square and the parameters `def:relu-shatter-param`,
    $f_{\vartheta_\theta} = f_\theta$ on $K$: the closed form of the block in terms of $P$,
    $\psi$, $s$ and $\mathrm{clip}$. -/)]
theorem reluBlock_shatterParam (w' : ℕ) (θ : ℝ) :
    reluBlock isProjectionOnto_clipSquare (shatterParam w' θ) = shatterBlock θ := by
  funext x
  apply Subtype.ext
  rw [shatterParam, reluBlock_planeParam, sum_shatterOutZ, sum_shatterOutY]
  ext j
  fin_cases j <;> rfl

@[blueprint "lem:relu-shatter-block-relu-zero"
  (statement := /-- (Closed form of the ReLU block, track.) For $x = (z, y) \in K$, the first
    coordinate of $\Pi_K(V_\theta\,\mathrm{relu}(Wx + b))$ is
    $\mathrm{clip}\bigl(P(z) + s(z, y)\bigr)$. -/)]
theorem reluBlock_shatterParam_apply_zero (w' : ℕ) (θ : ℝ) (x : unitSquare) :
    (reluBlock isProjectionOnto_clipSquare (shatterParam w' θ) x : E₂) 0 =
      clipUnit (shatterP ((x : E₂) 0) + shatterSort ((x : E₂) 0) ((x : E₂) 1)) := by
  rw [reluBlock_shatterParam]
  rfl

@[blueprint "lem:relu-shatter-block-relu-one"
  (statement := /-- (Closed form of the ReLU block, register.) For $x = (z, y) \in K$, the
    second coordinate of $\Pi_K(V_\theta\,\mathrm{relu}(Wx + b))$ is
    $\mathrm{clip}\bigl(4\,\mathrm{relu}(y) - 8\,\mathrm{relu}(y - \tfrac12)
    + \theta\,\psi(z)\bigr)$. -/)]
theorem reluBlock_shatterParam_apply_one (w' : ℕ) (θ : ℝ) (x : unitSquare) :
    (reluBlock isProjectionOnto_clipSquare (shatterParam w' θ) x : E₂) 1 =
      clipUnit (4 * max ((x : E₂) 1) 0 - 8 * max ((x : E₂) 1 - 1 / 2) 0
        + θ * shatterPsi ((x : E₂) 0)) := by
  rw [reluBlock_shatterParam]
  rfl

@[blueprint "lem:relu-shatter-param-norms"
  (statement := /-- Weight norms of the representation of $f_\theta$, $\theta \in [0, \tfrac14]$:
    $\|W\|_{\rm op} \le \sqrt{15 + 17/8} \le 5$ (rows $(1,0)$ seven times, $(0,1)$ twice,
    $(2, \tfrac14)$ twice), $\|b\| \le 2$ ($\|b\|^2 = 3813/1024$),
    $\|V_\theta\|_{\rm op} \le \sqrt{\|v^z\|^2 + \|v^y_\theta\|^2}
    = \sqrt{46.5 + 2560\theta^2 + 80} \le 17$, and $c = 0$. -/)]
theorem shatterParam_norms (w' : ℕ) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) (1 / 4)) :
    ‖(shatterParam w' θ).1‖ ≤ 5 ∧ ‖(shatterParam w' θ).2.1‖ ≤ 2 ∧
      ‖(shatterParam w' θ).2.2.1‖ ≤ 17 ∧ ‖(shatterParam w' θ).2.2.2‖ = 0 := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine norm_colMap_le _ _ (by norm_num) ?_
    simp [shatterInZ, shatterInY, Fin.sum_univ_add, Fin.sum_univ_succ]
    norm_num
  · change ‖(WithLp.toLp 2 (fun i => -shatterThreshold w' i) :
      EuclideanSpace ℝ (Fin (11 + w')))‖ ≤ 2
    rw [EuclideanSpace.norm_eq, Real.sqrt_le_left (by norm_num)]
    simp [shatterThreshold, Fin.sum_univ_add, Fin.sum_univ_succ]
    norm_num
  · refine norm_rowMap_le _ _ (by norm_num) ?_
    simp [shatterOutZ, shatterOutY, Fin.sum_univ_add, Fin.sum_univ_succ]
    nlinarith [mul_nonneg hθ0 hθ0, mul_le_mul hθ1 hθ1 hθ0 (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  · exact norm_zero

@[blueprint "lem:relu-shatter-block-mem"
  (statement := /-- (\textbf{$f_\theta \in F_\Lambda$ at width $11 + w'$.}) For
    $\theta \in [0, \tfrac14]$, $\beta_W \ge 17$, $\beta \ge 2$ and $\Lambda \ge 85$, the block
    $f_\theta$ belongs to the class $F_\Lambda$ of ReLU blocks of width $11 + w'$ on
    $K = [0,1]^2$ with the clipping retraction: the weight norms are bounded by
    `lem:relu-shatter-param-norms` and the block is $\|V_\theta\|\|W\| \le 17 \cdot 5 = 85$
    Lipschitz by `lem:relu-shatter-block-lipschitz`. -/)]
theorem shatterBlock_mem_reluClass (w' : ℕ) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) (1 / 4))
    {βW β Λ : ℝ≥0} (hβW : 17 ≤ βW) (hβ : 2 ≤ β) (hΛ : 85 ≤ Λ) :
    shatterBlock θ ∈ reluClass isProjectionOnto_clipSquare (11 + w') βW β Λ := by
  have hβW' : (17 : ℝ) ≤ βW := by exact_mod_cast hβW
  have hβ' : (2 : ℝ) ≤ β := by exact_mod_cast hβ
  obtain ⟨h1, h2, h3, h4⟩ := shatterParam_norms w' hθ
  refine ⟨shatterParam w' θ, ⟨h1.trans (by linarith), h2.trans hβ', h3.trans hβW',
    h4.le.trans β.coe_nonneg, ?_⟩, reluBlock_shatterParam w' θ⟩
  refine (lipschitzWith_reluBlock_opNorm isProjectionOnto_clipSquare _).weaken ?_
  have hV : ‖(shatterParam w' θ).2.2.1‖₊ ≤ 17 := by exact_mod_cast h3
  have hW : ‖(shatterParam w' θ).1‖₊ ≤ 5 := by exact_mod_cast h1
  calc ‖(shatterParam w' θ).2.2.1‖₊ * ‖(shatterParam w' θ).1‖₊ ≤ 17 * 5 := mul_le_mul' hV hW
    _ = 85 := by norm_num
    _ ≤ Λ := hΛ

@[blueprint "prop:relu-shatter-i"
  (statement := /-- \textbf{(`prop:relu-shatter`(i), membership.)} Every $f_\theta$,
    $\theta \in [0, \tfrac14]$, is a ReLU block of width $11$
    (`lem:relu-shatter-block-relu`) and belongs to $F_\Lambda$ for every width $w \ge 11$,
    $\beta_W \ge 17$, $\beta \ge 2$ and $\Lambda \ge 85$ (pad the representation of
    `lem:relu-shatter-block-mem` with $w - 11$ zero units). -/)]
theorem shatterBlock_mem_reluClass_of_le {w : ℕ} (hw : 11 ≤ w) {θ : ℝ}
    (hθ : θ ∈ Icc (0 : ℝ) (1 / 4)) {βW β Λ : ℝ≥0} (hβW : 17 ≤ βW) (hβ : 2 ≤ β) (hΛ : 85 ≤ Λ) :
    shatterBlock θ ∈ reluClass isProjectionOnto_clipSquare w βW β Λ := by
  obtain ⟨w', rfl⟩ : ∃ w', w = 11 + w' := ⟨w - 11, by omega⟩
  exact shatterBlock_mem_reluClass w' hθ hβW hβ hΛ

end Block

/-! ### Codes: a word of `B` letters stored in one real parameter -/

section Codes

@[blueprint "def:relu-shatter-S"
  (statement := /-- The two inverse branches of the shift $E$:
    $S_0(u) = u/4$ and $S_1(u) = 1 - u/4$. -/)]
noncomputable def shatterS (a : Fin 2) (u : ℝ) : ℝ := if a = 0 then u / 4 else 1 - u / 4

@[blueprint "lem:relu-shatter-S-mem"
  (statement := /-- $S_a$ maps $[0,1]$ into $[0,1]$. -/)]
theorem shatterS_mem (a : Fin 2) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    shatterS a u ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := hu
  unfold shatterS
  split_ifs <;> constructor <;> linarith

@[blueprint "lem:relu-shatter-shift-S"
  (statement := /-- $E(S_a(u)) = u$ for $u \in [0,1]$ and $a \in \{0, 1\}$
    (Fact 6). -/)]
theorem shatterShift_shatterS (a : Fin 2) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    shatterShift (shatterS a u) = u := by
  unfold shatterS
  split_ifs
  · exact shatterShift_div_four hu
  · exact shatterShift_one_sub hu

@[blueprint "def:relu-shatter-code"
  (statement := /-- The code of a finite word $c = (c_1, \dots, c_B) \in \{0,1\}^B$:
    $\mathrm{code}(c) = S_{c_1}(S_{c_2}(\cdots S_{c_B}(0)))$, defined by recursion on the word:
    $\mathrm{code}(\emptyset) = 0$ and
    $\mathrm{code}(c_1, c_2, \dots) = S_{c_1}(\mathrm{code}(c_2, \dots))$. -/)]
noncomputable def shatterCode : List (Fin 2) → ℝ
  | [] => 0
  | a :: l => shatterS a (shatterCode l)

@[blueprint "lem:relu-shatter-code-mem"
  (statement := /-- $\mathrm{code}(c) \in [0,1]$. -/)]
theorem shatterCode_mem (l : List (Fin 2)) : shatterCode l ∈ Icc (0 : ℝ) 1 := by
  induction l with
  | nil => exact ⟨le_rfl, zero_le_one⟩
  | cons a l ih => exact shatterS_mem a ih

@[blueprint "lem:relu-shatter-shift-iterate-code"
  (statement := /-- The shift drops letters: $E^j(\mathrm{code}(c_1, \dots, c_B)) =
    \mathrm{code}(c_{j+1}, \dots, c_B)$ for every $j \ge 0$ (the empty word, of code $0$, for
    $j \ge B$). -/)]
theorem shatterShift_iterate_shatterCode (j : ℕ) (l : List (Fin 2)) :
    shatterShift^[j] (shatterCode l) = shatterCode (l.drop j) := by
  induction j generalizing l with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply]
    cases l with
    | nil =>
      have h := ih []
      simp only [shatterCode, List.drop_nil] at h ⊢
      rw [shatterShift_zero]
      exact h
    | cons a l =>
      rw [List.drop_succ_cons, ← ih l]
      congr 1
      exact shatterShift_shatterS a (shatterCode_mem l)

@[blueprint "def:relu-shatter-theta"
  (statement := /-- The parameter that stores the word $c$:
    $\theta(c) = \mathrm{code}(c)/4 \in [0, \tfrac14]$. -/)]
noncomputable def shatterTheta (l : List (Fin 2)) : ℝ := shatterCode l / 4

@[blueprint "lem:relu-shatter-theta-mem"
  (statement := /-- $\theta(c) \in [0, \tfrac14]$. -/)]
theorem shatterTheta_mem (l : List (Fin 2)) : shatterTheta l ∈ Icc (0 : ℝ) (1 / 4) := by
  obtain ⟨h0, h1⟩ := shatterCode_mem l
  unfold shatterTheta
  constructor <;> linarith

@[blueprint "lem:relu-shatter-shift-theta"
  (statement := /-- $E(\theta(c)) = \mathrm{code}(c)$. -/)]
theorem shatterShift_shatterTheta (l : List (Fin 2)) :
    shatterShift (shatterTheta l) = shatterCode l :=
  shatterShift_div_four (shatterCode_mem l)

@[blueprint "lem:relu-shatter-shift-iterate-theta"
  (statement := /-- (Reading the $b$-th letter.) For a word $c = (c_1, \dots, c_B)$ and
    $1 \le b \le B$, $E^{b}(\theta(c)) = \mathrm{code}(c_b, \dots, c_B)
    = S_{c_b}(\mathrm{code}(c_{b+1}, \dots, c_B))$, which lies in $[0, \tfrac14]$ if $c_b = 0$
    and in $[\tfrac34, 1]$ if $c_b = 1$. (In Lean the letters are indexed from $0$:
    $E^{b+1}(\theta(c)) = S_{c[b]}(\mathrm{code}(\mathrm{drop}_{b+1} c))$.) -/)]
theorem shatterShift_iterate_shatterTheta (l : List (Fin 2)) {b : ℕ} (hb : b < l.length) :
    shatterShift^[b + 1] (shatterTheta l) = shatterS l[b] (shatterCode (l.drop (b + 1))) := by
  rw [Function.iterate_succ_apply, shatterShift_shatterTheta, shatterShift_iterate_shatterCode,
    List.drop_eq_getElem_cons hb, shatterCode]

@[blueprint "def:relu-shatter-sink"
  (statement := /-- The two sinks of the track: $a_0 = \tfrac34$ and $a_1 = \tfrac78$. -/)]
noncomputable def shatterSink : Fin 2 → ℝ := ![3 / 4, 7 / 8]

end Codes

/-! ### The orbit of a sample point: wait, load, count, sort, hold -/

section Orbit

variable {θ z y : ℕ → ℝ}

@[blueprint "lem:relu-shatter-orbit-wait"
  (statement := /-- (Wait phase.) Let $(z_s, y_s)_{s \ge 0}$ be an orbit of the layers,
    $z_{s+1} = \mathrm{clip}(P(z_s) + s(z_s, y_s))$,
    $y_{s+1} = \mathrm{clip}(4\,\mathrm{relu}(y_s) - 8\,\mathrm{relu}(y_s - \tfrac12)
    + \theta_s\psi(z_s))$, started at $z_0 = a\,2^{-t}$, $y_0 = 0$ with
    $a \in [0, \tfrac3{16}]$. Then $z_s = a\,2^{-(t-s)}$ and $y_s = 0$ for all $s \le t$
    (the track doubles and the register stays empty, for arbitrary $\theta_s$). -/)]
theorem shatter_orbit_wait (hz : ∀ s, z (s + 1) = shatterTrack (z s) (y s))
    (hy : ∀ s, y (s + 1) = shatterRegister (θ s) (z s) (y s))
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 3 / 16) {t : ℕ} (hz0 : z 0 = a * (1 / 2) ^ t)
    (hy0 : y 0 = 0) (s d : ℕ) (hsd : s + d = t) : z s = a * (1 / 2) ^ d ∧ y s = 0 := by
  induction s generalizing d with
  | zero =>
    rw [zero_add] at hsd
    subst hsd
    exact ⟨hz0, hy0⟩
  | succ s ih =>
    obtain ⟨h1, h2⟩ := ih (d + 1) (by omega)
    have hd : (0 : ℝ) < (1 / 2) ^ d := by positivity
    have hd1 : ((1 : ℝ) / 2) ^ d ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hzs : z s = a * (1 / 2) ^ d / 2 := by rw [h1, pow_succ]; ring
    have hzs0 : 0 ≤ z s := by rw [hzs]; positivity
    have hzs1 : z s ≤ 3 / 32 := by
      rw [hzs]
      nlinarith
    constructor
    · rw [hz, h2, shatterTrack_of_le hzs0 (by linarith) zero_le_one, hzs]
      ring
    · rw [hy, h2, shatterRegister_wait hzs1]

@[blueprint "lem:relu-shatter-orbit-count"
  (statement := /-- (Count phase.) Let $(z_s, y_s)$ be an orbit of the layers with
    $y_s \le 1$ for all $s$, and suppose $z_{s_0} = \tfrac14 + \tfrac14 2^{-b}$. Then for
    $0 \le j \le b$, $z_{s_0+j} = \tfrac14 + \tfrac14 2^{-(b-j)}$ and
    $y_{s_0+j} = E^j(y_{s_0})$, for arbitrary $\theta_s$. -/)]
theorem shatter_orbit_count (hy1 : ∀ s, y s ≤ 1)
    (hz : ∀ s, z (s + 1) = shatterTrack (z s) (y s))
    (hy : ∀ s, y (s + 1) = shatterRegister (θ s) (z s) (y s))
    {s₀ b : ℕ} (hz0 : z s₀ = 1 / 4 + 1 / 4 * (1 / 2) ^ b)
    (j d : ℕ) (hjd : j + d = b) :
    z (s₀ + j) = 1 / 4 + 1 / 4 * (1 / 2) ^ d ∧ y (s₀ + j) = shatterShift^[j] (y s₀) := by
  induction j generalizing d with
  | zero =>
    rw [zero_add] at hjd
    subst hjd
    exact ⟨hz0, rfl⟩
  | succ j ih =>
    obtain ⟨h1, h2⟩ := ih (d + 1) (by omega)
    have hd : (0 : ℝ) < (1 / 2) ^ d := by positivity
    have hd1 : ((1 : ℝ) / 2) ^ d ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hzs : z (s₀ + j) = 1 / 4 + 1 / 8 * (1 / 2) ^ d := by rw [h1, pow_succ]; ring
    have hz1 : 1 / 4 ≤ z (s₀ + j) := by rw [hzs]; linarith
    have hz2 : z (s₀ + j) ≤ 3 / 8 := by rw [hzs]; linarith
    constructor
    · rw [← add_assoc, hz, shatterTrack_count hz1 hz2 (hy1 _), hzs]
      ring
    · rw [← add_assoc, hy, shatterRegister_count hz1, h2, Function.iterate_succ_apply']

@[blueprint "lem:relu-shatter-orbit-hold"
  (statement := /-- (Hold phase.) Let $(z_s, y_s)$ be an orbit of the layers with $y_s \ge 0$
    for all $s$. If $z_{s_0} \in [\tfrac34, 1]$ then $z_s = z_{s_0}$ for all $s \ge s_0$. -/)]
theorem shatter_orbit_hold (hy0 : ∀ s, 0 ≤ y s)
    (hz : ∀ s, z (s + 1) = shatterTrack (z s) (y s))
    {s₀ : ℕ} (h1 : 3 / 4 ≤ z s₀) (h2 : z s₀ ≤ 1) (m : ℕ) : z (s₀ + m) = z s₀ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [← add_assoc, hz, ih, shatterTrack_hold h1 h2 (hy0 _)]

@[blueprint "lem:relu-shatter-orbit-states"
  (statement := /-- \textbf{(Orbit of a sample point: wait, load, count.)} Let
    $\theta_s \in [0, \tfrac14]$ for all $s$ and let $(z_s, y_s)_{s \ge 0}$ be the orbit of
    the layers $f_{\theta_0}, f_{\theta_1}, \dots$ (layer $s$ maps $(z_s, y_s)$ to
    $(z_{s+1}, y_{s+1})$, with $y_s \le 1$) started at
    $z_0 = \tfrac18(1 + 2^{-(b+1)})\,2^{-t}$, $y_0 = 0$. Then, for arbitrary $\theta_s$:
    \begin{enumerate}
    \item (wait) the state is $(\tfrac18(1 + 2^{-(b+1)})2^{-(t-s)}, 0)$ after $s \le t$
      layers;
    \item (load) it is $(\tfrac14(1 + 2^{-(b+1)}), \theta_t)$ after $t+1$ layers;
    \item (count) it is $(\tfrac14 + \tfrac14 2^{-(b+1-j)}, E^j(\theta_t))$ after $t+1+j$
      layers, $0 \le j \le b+1$;
    \item in particular it is $(\tfrac12, E^{b+1}(\theta_t))$ after $t+b+2$ layers.
    \end{enumerate}
    (Indices are $0$-based; in the paper's $1$-based indices $t' = t+1$, $b' = b+1$ these are
    the states after $s \le t'-1$, $t'$, $t'+j$ and $t'+b'$ layers.) -/)]
theorem shatter_orbit_states (hθ : ∀ s, θ s ∈ Icc (0 : ℝ) (1 / 4)) (hy1 : ∀ s, y s ≤ 1)
    (hz : ∀ s, z (s + 1) = shatterTrack (z s) (y s))
    (hy : ∀ s, y (s + 1) = shatterRegister (θ s) (z s) (y s))
    {t b : ℕ} (hz0 : z 0 = 1 / 8 * (1 + (1 / 2) ^ (b + 1)) * (1 / 2) ^ t) (hy0 : y 0 = 0) :
    (∀ s d, s + d = t → z s = 1 / 8 * (1 + (1 / 2) ^ (b + 1)) * (1 / 2) ^ d ∧ y s = 0) ∧
    (z (t + 1) = 1 / 4 * (1 + (1 / 2) ^ (b + 1)) ∧ y (t + 1) = θ t) ∧
    (∀ j d, j + d = b + 1 →
      z (t + 1 + j) = 1 / 4 + 1 / 4 * (1 / 2) ^ d ∧ y (t + 1 + j) = shatterShift^[j] (θ t)) ∧
    (z (t + b + 2) = 1 / 2 ∧ y (t + b + 2) = shatterShift^[b + 1] (θ t)) := by
  have hb : (0 : ℝ) < (1 / 2) ^ (b + 1) := by positivity
  have hb1 : ((1 : ℝ) / 2) ^ (b + 1) ≤ 1 / 2 := by
    rw [pow_succ]
    have : ((1 : ℝ) / 2) ^ b ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  /-- Wait: after $t$ layers the state is $(\tfrac18(1 + 2^{-(b+1)}), 0)$, with track in
    $(\tfrac18, \tfrac3{16}]$ (`lem:relu-shatter-orbit-wait`). -/
  have hwait := shatter_orbit_wait hz hy (a := 1 / 8 * (1 + (1 / 2) ^ (b + 1)))
    (by positivity) (by linarith) hz0 hy0
  obtain ⟨hzt, hyt⟩ := hwait t 0 (add_zero t)
  rw [pow_zero, mul_one] at hzt
  /-- Load: layer $t$ writes $\theta_t$ into the register and doubles the track. -/
  have hzt1 : z (t + 1) = 1 / 4 + 1 / 4 * (1 / 2) ^ (b + 1) := by
    rw [hz, hyt, shatterTrack_of_le (by rw [hzt]; positivity) (by rw [hzt]; linarith)
      zero_le_one, hzt]
    ring
  have hyt1 : y (t + 1) = θ t := by
    rw [hy, hyt, shatterRegister_load (hθ t) (by rw [hzt]; linarith) (by rw [hzt]; linarith)]
  /-- Count: `lem:relu-shatter-orbit-count` started at depth $t+1$. -/
  have hcount : ∀ j d, j + d = b + 1 →
      z (t + 1 + j) = 1 / 4 + 1 / 4 * (1 / 2) ^ d ∧ y (t + 1 + j) = shatterShift^[j] (θ t) := by
    intro j d hjd
    have h := shatter_orbit_count hy1 hz hy hzt1 j d hjd
    rwa [hyt1] at h
  refine ⟨hwait, ⟨by rw [hzt1]; ring, hyt1⟩, hcount, ?_⟩
  have h := hcount (b + 1) 0 (add_zero _)
  rw [pow_zero, mul_one, show t + 1 + (b + 1) = t + b + 2 by omega] at h
  exact ⟨by rw [h.1]; norm_num, h.2⟩

@[blueprint "lem:relu-shatter-orbit-sink"
  (statement := /-- \textbf{(Orbit of a sample point: sort and hold.)} In the situation of
    `lem:relu-shatter-orbit-states` (with $y_s \in [0,1]$), for every depth $N \ge t + b + 3$
    the track is $z_N = \tfrac34$ if $E^{b+1}(\theta_t) \le \tfrac14$ and $z_N = \tfrac78$ if
    $E^{b+1}(\theta_t) \ge \tfrac34$: layer $t+b+2$ sorts the state $(\tfrac12,
    E^{b+1}(\theta_t))$ and all later layers hold the track. -/)]
theorem shatter_orbit_sink (hθ : ∀ s, θ s ∈ Icc (0 : ℝ) (1 / 4))
    (hy01 : ∀ s, y s ∈ Icc (0 : ℝ) 1) (hz : ∀ s, z (s + 1) = shatterTrack (z s) (y s))
    (hy : ∀ s, y (s + 1) = shatterRegister (θ s) (z s) (y s))
    {t b : ℕ} (hz0 : z 0 = 1 / 8 * (1 + (1 / 2) ^ (b + 1)) * (1 / 2) ^ t) (hy0 : y 0 = 0)
    {N : ℕ} (hN : t + b + 3 ≤ N) :
    (shatterShift^[b + 1] (θ t) ≤ 1 / 4 → z N = 3 / 4) ∧
      (3 / 4 ≤ shatterShift^[b + 1] (θ t) → z N = 7 / 8) := by
  obtain ⟨-, -, -, hzc, hyc⟩ := shatter_orbit_states hθ (fun s => (hy01 s).2) hz hy hz0 hy0
  obtain ⟨m, rfl⟩ : ∃ m, N = t + b + 2 + 1 + m := ⟨N - (t + b + 3), by omega⟩
  have hnext : z (t + b + 2 + 1) = shatterTrack (1 / 2) (shatterShift^[b + 1] (θ t)) := by
    rw [hz, hzc, hyc]
  constructor
  · intro h
    have hs : z (t + b + 2 + 1) = 3 / 4 := by rw [hnext, shatterTrack_sort_zero h]
    rw [shatter_orbit_hold (fun s => (hy01 s).1) hz (by rw [hs]) (by rw [hs]; norm_num) m, hs]
  · intro h
    have hs : z (t + b + 2 + 1) = 7 / 8 := by rw [hnext, shatterTrack_sort_one h]
    rw [shatter_orbit_hold (fun s => (hy01 s).1) hz (by rw [hs]; norm_num)
      (by rw [hs]; norm_num) m, hs]

@[blueprint "lem:relu-shatter-orbit"
  (statement := /-- \textbf{(Orbit of a sample point, code form.)} In the situation of
    `lem:relu-shatter-orbit-sink`, if $E^{b+1}(\theta_t) = S_a(u)$ with $u \in [0,1]$ and
    $a \in \{0,1\}$, then the track is $z_N = a_a$ (that is $\tfrac34$ for $a = 0$ and
    $\tfrac78$ for $a = 1$) for every $N \ge t + b + 3$, since $S_0(u) \le \tfrac14$ and
    $S_1(u) \ge \tfrac34$. In the paper's $1$-based indices $t' = t+1$, $b' = b+1$ this is
    depth $N \ge t' + b' + 1$. -/)]
theorem shatter_orbit (hθ : ∀ s, θ s ∈ Icc (0 : ℝ) (1 / 4)) (hy01 : ∀ s, y s ∈ Icc (0 : ℝ) 1)
    (hz : ∀ s, z (s + 1) = shatterTrack (z s) (y s))
    (hy : ∀ s, y (s + 1) = shatterRegister (θ s) (z s) (y s))
    {t b : ℕ} (hz0 : z 0 = 1 / 8 * (1 + (1 / 2) ^ (b + 1)) * (1 / 2) ^ t) (hy0 : y 0 = 0)
    (a : Fin 2) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (hcode : shatterShift^[b + 1] (θ t) = shatterS a u) {N : ℕ} (hN : t + b + 3 ≤ N) :
    z N = shatterSink a := by
  obtain ⟨h0, h1⟩ := shatter_orbit_sink hθ hy01 hz hy hz0 hy0 hN
  obtain ⟨hu0, hu1⟩ := hu
  by_cases ha : a = 0
  · subst ha
    rw [h0 (by rw [hcode, shatterS, if_pos rfl]; linarith)]
    simp [shatterSink]
  · have ha1 : a = 1 := Fin.eq_one_of_ne_zero a ha
    subst ha1
    rw [h1 (by rw [hcode, shatterS, if_neg ha]; linarith)]
    simp [shatterSink]

end Orbit

/-! ### The network, the sample points and the shattering theorem -/

section Shatter

@[blueprint "def:relu-shatter-net"
  (statement := /-- The composition of the first $s$ layers of the sequence
    $f_{\theta_0}, f_{\theta_1}, \dots$ (layer $0$ applied first):
    $g_0 = \mathrm{id}$, $g_{s+1} = f_{\theta_s} \circ g_s$. -/)]
noncomputable def shatterNet (θ : ℕ → ℝ) : ℕ → unitSquare → unitSquare
  | 0 => id
  | s + 1 => shatterBlock (θ s) ∘ shatterNet θ s

@[blueprint "lem:relu-shatter-net-mem"
  (statement := /-- If every layer $f_{\theta_s}$ belongs to a hidden-layer class $F$ then
    $f_{\theta_{s-1}} \circ \cdots \circ f_{\theta_0} \in B(s, F)$. -/)]
theorem shatterNet_mem_wordBall {F : Set (unitSquare → unitSquare)} {θ : ℕ → ℝ}
    (hθ : ∀ s, shatterBlock (θ s) ∈ F) (s : ℕ) : shatterNet θ s ∈ wordBall F s := by
  induction s with
  | zero => exact Set.mem_singleton _
  | succ s ih => exact mem_wordBall_succ_of_mem_of_mem (hθ s) ih

@[blueprint "lem:relu-shatter-point-track"
  (statement := /-- $\tfrac18(1 + 2^{-(b+1)})\,2^{-t} \in [0,1]$. -/)]
theorem shatterPoint_track_mem (t b : ℕ) :
    1 / 8 * (1 + (1 / 2 : ℝ) ^ (b + 1)) * (1 / 2) ^ t ∈ Icc (0 : ℝ) 1 := by
  have h1 : (0 : ℝ) < (1 / 2) ^ (b + 1) := by positivity
  have h2 : ((1 : ℝ) / 2) ^ (b + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h3 : (0 : ℝ) < (1 / 2) ^ t := by positivity
  have h4 : ((1 : ℝ) / 2) ^ t ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  constructor
  · positivity
  · nlinarith

@[blueprint "def:relu-shatter-point"
  (statement := /-- The sample points: for $t, b \ge 1$,
    $x_{t,b} = \bigl(\tfrac18(1 + 2^{-b})\,2^{-(t-1)},\ 0\bigr) \in K$. In Lean the indices are
    $0$-based: `shatterPoint t b` $= (\tfrac18(1 + 2^{-(b+1)})\,2^{-t}, 0)$ is the paper's
    $x_{t+1,b+1}$. -/)]
noncomputable def shatterPoint (t b : ℕ) : unitSquare :=
  ⟨WithLp.toLp 2 ![1 / 8 * (1 + (1 / 2 : ℝ) ^ (b + 1)) * (1 / 2) ^ t, 0],
    Fin.forall_fin_two.2 ⟨shatterPoint_track_mem t b, ⟨le_rfl, zero_le_one⟩⟩⟩

@[blueprint "lem:relu-shatter-net-states"
  (statement := /-- \textbf{(Orbit of $x_{t,b}$ under the network: wait, load, count.)} Let
    $\theta_s \in [0, \tfrac14]$ for all $s$ and write
    $(z_s, y_s) := (f_{\theta_{s-1}} \circ \cdots \circ f_{\theta_0})(x_{t+1,b+1})$ for the
    state after $s$ layers. Then $(z_s, y_s) = (\tfrac18(1 + 2^{-(b+1)})2^{-(t-s)}, 0)$ for
    $s \le t$; $(z_{t+1}, y_{t+1}) = (\tfrac14(1 + 2^{-(b+1)}), \theta_t)$;
    $(z_{t+1+j}, y_{t+1+j}) = (\tfrac14 + \tfrac14 2^{-(b+1-j)}, E^j(\theta_t))$ for
    $0 \le j \le b+1$; in particular $(z_{t+b+2}, y_{t+b+2}) = (\tfrac12, E^{b+1}(\theta_t))$
    (`lem:relu-shatter-orbit-states` applied to the two coordinates of the states). -/)]
theorem shatterNet_states {θ : ℕ → ℝ} (hθ : ∀ s, θ s ∈ Icc (0 : ℝ) (1 / 4)) (t b : ℕ) :
    (∀ s d, s + d = t →
      ((shatterNet θ s (shatterPoint t b) : unitSquare) : E₂) 0 =
          1 / 8 * (1 + (1 / 2) ^ (b + 1)) * (1 / 2) ^ d ∧
        ((shatterNet θ s (shatterPoint t b) : unitSquare) : E₂) 1 = 0) ∧
    (((shatterNet θ (t + 1) (shatterPoint t b) : unitSquare) : E₂) 0 =
          1 / 4 * (1 + (1 / 2) ^ (b + 1)) ∧
        ((shatterNet θ (t + 1) (shatterPoint t b) : unitSquare) : E₂) 1 = θ t) ∧
    (∀ j d, j + d = b + 1 →
      ((shatterNet θ (t + 1 + j) (shatterPoint t b) : unitSquare) : E₂) 0 =
          1 / 4 + 1 / 4 * (1 / 2) ^ d ∧
        ((shatterNet θ (t + 1 + j) (shatterPoint t b) : unitSquare) : E₂) 1 =
          shatterShift^[j] (θ t)) ∧
    (((shatterNet θ (t + b + 2) (shatterPoint t b) : unitSquare) : E₂) 0 = 1 / 2 ∧
      ((shatterNet θ (t + b + 2) (shatterPoint t b) : unitSquare) : E₂) 1 =
        shatterShift^[b + 1] (θ t)) :=
  shatter_orbit_states (z := fun s => ((shatterNet θ s (shatterPoint t b) : unitSquare) : E₂) 0)
    (y := fun s => ((shatterNet θ s (shatterPoint t b) : unitSquare) : E₂) 1) hθ
    (fun s => ((shatterNet θ s (shatterPoint t b)).2 1).2) (fun _ => rfl) (fun _ => rfl) rfl rfl

@[blueprint "lem:relu-shatter-net-sink"
  (statement := /-- \textbf{(Orbit of $x_{t,b}$ under the network.)} Let
    $\theta_s \in [0, \tfrac14]$ for all $s$. If $E^{b+1}(\theta_t) = S_a(u)$ with
    $u \in [0,1]$ and $a \in \{0, 1\}$, then for every depth $N \ge t + b + 3$ the first
    coordinate of $(f_{\theta_{N-1}} \circ \cdots \circ f_{\theta_0})(x_{t+1,b+1})$ is $a_a$
    (`lem:relu-shatter-orbit` applied to the two coordinates of the states). -/)]
theorem shatterNet_sink {θ : ℕ → ℝ} (hθ : ∀ s, θ s ∈ Icc (0 : ℝ) (1 / 4)) {t b : ℕ}
    (a : Fin 2) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (hcode : shatterShift^[b + 1] (θ t) = shatterS a u) {N : ℕ} (hN : t + b + 3 ≤ N) :
    ((shatterNet θ N (shatterPoint t b) : unitSquare) : E₂) 0 = shatterSink a :=
  shatter_orbit (z := fun s => ((shatterNet θ s (shatterPoint t b) : unitSquare) : E₂) 0)
    (y := fun s => ((shatterNet θ s (shatterPoint t b) : unitSquare) : E₂) 1) hθ
    (fun s => (shatterNet θ s (shatterPoint t b)).2 1) (fun _ => rfl) (fun _ => rfl) rfl rfl
    a hu hcode hN

@[blueprint "def:relu-shatter-theta-seq"
  (statement := /-- The parameters of the shattering network for a labeling
    $c \in \{0,1\}^{k_1 \times B}$: $\theta_t := \theta(c_{t,1}, \dots, c_{t,B})$ for
    $t \le k_1$ and $\theta_s := 0$ for $s > k_1$. (In Lean the layers are indexed from $0$:
    $\theta_s = \theta(c_{s,\cdot})$ for $s < k_1$ and $\theta_s = 0$ for $s \ge k_1$.) -/)]
noncomputable def shatterThetaSeq {k₁ B : ℕ} (c : Fin k₁ → Fin B → Fin 2) : ℕ → ℝ :=
  fun s => if h : s < k₁ then shatterTheta (List.ofFn (c ⟨s, h⟩)) else 0

@[blueprint "lem:relu-shatter-theta-seq-mem"
  (statement := /-- $\theta_s \in [0, \tfrac14]$ for every layer $s$. -/)]
theorem shatterThetaSeq_mem {k₁ B : ℕ} (c : Fin k₁ → Fin B → Fin 2) (s : ℕ) :
    shatterThetaSeq c s ∈ Icc (0 : ℝ) (1 / 4) := by
  unfold shatterThetaSeq
  split_ifs with h
  · exact shatterTheta_mem _
  · exact ⟨le_rfl, by norm_num⟩

@[blueprint "lem:relu-shatter-theta-seq-apply"
  (statement := /-- $\theta_t = \theta(c_{t,1}, \dots, c_{t,B})$ for $t \le k_1$. -/)]
theorem shatterThetaSeq_apply {k₁ B : ℕ} (c : Fin k₁ → Fin B → Fin 2) (t : Fin k₁) :
    shatterThetaSeq c t = shatterTheta (List.ofFn (c t)) := by
  simp only [shatterThetaSeq, dif_pos t.2, Fin.eta]

@[blueprint "lem:relu-shatter-net-labels"
  (statement := /-- \textbf{(The explicit network realizes the labeling.)} Let
    $c \in \{0,1\}^{k_1 \times B}$ and $\theta_s$ as in `def:relu-shatter-theta-seq`. For
    $t \le k_1$, $b \le B$ and every depth $N \ge t + b + 1$ (in particular for
    $N = k_1 + B + 1$), the first coordinate of
    $(f_{\theta_N} \circ \cdots \circ f_{\theta_1})(x_{t,b})$ equals $a_{c_{t,b}}$: by
    `lem:relu-shatter-shift-iterate-theta`, $E^{b}(\theta_t) = S_{c_{t,b}}(\mathrm{code}(
    c_{t,b+1}, \dots, c_{t,B}))$, and `lem:relu-shatter-net-sink` applies. (In Lean, with
    $0$-based $t, b$: $N \ge t + b + 3$.) -/)]
theorem shatterNet_shatterThetaSeq {k₁ B : ℕ} (c : Fin k₁ → Fin B → Fin 2) (t : Fin k₁)
    (b : Fin B) {N : ℕ} (hN : (t : ℕ) + b + 3 ≤ N) :
    ((shatterNet (shatterThetaSeq c) N (shatterPoint t b) : unitSquare) : E₂) 0 =
      shatterSink (c t b) := by
  have hl : (b : ℕ) < (List.ofFn (c t)).length := by
    rw [List.length_ofFn]
    exact b.2
  have hcode : shatterShift^[(b : ℕ) + 1] (shatterThetaSeq c t) =
      shatterS (c t b) (shatterCode ((List.ofFn (c t)).drop ((b : ℕ) + 1))) := by
    rw [shatterThetaSeq_apply, shatterShift_iterate_shatterTheta _ hl, List.getElem_ofFn]
  exact shatterNet_sink (shatterThetaSeq_mem c) (c t b) (shatterCode_mem _) hcode hN

@[blueprint "prop:relu-shatter-labels-of-subset"
  (statement := /-- \textbf{(`prop:relu-shatter`(ii) for every class containing the blocks
    $f_\theta$: depth $k_1 + B + 1$ realizes every labeling of $k_1 B$ points.)} Let $F$ be a
    hidden-layer class on
    $K = [0,1]^2$ with $f_\theta \in F$ for all $\theta \in [0, \tfrac14]$ (a one-parameter
    family suffices). Let $k_1, B \ge 0$ and $c \in \{0,1\}^{k_1 \times B}$, and put
    $\theta_t := \theta(c_{t,1}, \dots, c_{t,B})$ for $t \le k_1$ and $\theta_s := 0$ for
    $k_1 < s \le k_1 + B + 1$. Then
    $g := f_{\theta_{k_1+B+1}} \circ \cdots \circ f_{\theta_1} \in B(k_1 + B + 1, F)$
    satisfies: the first coordinate of $g(x_{t,b})$ equals $a_{c_{t,b}}$ for all
    $t \le k_1$, $b \le B$, where $a_0 = \tfrac34$ and $a_1 = \tfrac78$. -/)]
theorem prop_relu_shatter_labels_of_subset {F : Set (unitSquare → unitSquare)}
    (hF : ∀ θ ∈ Icc (0 : ℝ) (1 / 4), shatterBlock θ ∈ F) (k₁ B : ℕ)
    (c : Fin k₁ → Fin B → Fin 2) :
    ∃ g ∈ wordBall F (k₁ + B + 1), ∀ (t : Fin k₁) (b : Fin B),
      ((g (shatterPoint t b) : unitSquare) : E₂) 0 = shatterSink (c t b) := by
  /-- Take $g$ = the composition of the first $k_1 + B + 1$ layers with the parameters
    `def:relu-shatter-theta-seq`. All parameters lie in $[0, \tfrac14]$, so every layer is in
    $F$ and $g \in B(k_1 + B + 1, F)$ (`lem:relu-shatter-net-mem`); the labels are given by
    `lem:relu-shatter-net-labels`, since $k_1 + B + 1 \ge t + b + 1$. -/
  refine ⟨shatterNet (shatterThetaSeq c) (k₁ + B + 1), shatterNet_mem_wordBall
    (fun s => hF _ (shatterThetaSeq_mem c s)) _, fun t b => ?_⟩
  have ht := t.2
  have hb := b.2
  exact shatterNet_shatterThetaSeq c t b (by omega)

@[blueprint "prop:relu-shatter-ii"
  (statement := /-- \textbf{(`prop:relu-shatter`(ii), shattering.)} Let $k_1, B \ge 0$,
    $a_0 := \tfrac34$, $a_1 := \tfrac78$ and
    $x_{t,b} := (\tfrac18(1 + 2^{-b})\,2^{-(t-1)}, 0)$, $1 \le t \le k_1$, $1 \le b \le B$. For
    every $c \in \{0,1\}^{k_1 \times B}$ there are
    $\theta_1, \dots, \theta_{k_1+B+1} \in [0, \tfrac14]$ such that the first coordinate of
    $f_{\theta_{k_1+B+1}} \circ \cdots \circ f_{\theta_1}(x_{t,b})$ equals $a_{c_{t,b}}$ for
    all $t$ and $b$; namely $\theta_t = \tfrac14 S_{c_{t,1}} \circ \cdots \circ
    S_{c_{t,B}}(0)$ for $t \le k_1$ and $\theta_s = 0$ for $s > k_1$
    (`lem:relu-shatter-net-labels`). -/)]
theorem prop_relu_shatter_params (k₁ B : ℕ) (c : Fin k₁ → Fin B → Fin 2) :
    ∃ θ : ℕ → ℝ, (∀ s, θ s ∈ Icc (0 : ℝ) (1 / 4)) ∧ ∀ (t : Fin k₁) (b : Fin B),
      ((shatterNet θ (k₁ + B + 1) (shatterPoint t b) : unitSquare) : E₂) 0 =
        shatterSink (c t b) := by
  refine ⟨shatterThetaSeq c, shatterThetaSeq_mem c, fun t b => ?_⟩
  have ht := t.2
  have hb := b.2
  exact shatterNet_shatterThetaSeq c t b (by omega)

@[blueprint "prop:relu-shatter-labels"
  (statement := /-- \textbf{(Depth $k_1 + B + 1$ realizes every labeling of $k_1 B$ points;
    `prop:relu-shatter`(ii) in terms of the depth-$(k_1 + B + 1)$ hidden class.)} Let
    $K = [0,1]^2$ with the clipping retraction,
    $w \ge 11$, $\beta_W \ge 17$, $\beta \ge 2$, $\Lambda \ge 85$ and $F_\Lambda$ the class of
    ReLU blocks of width $w$. Let $k_1, B \ge 0$ and $c \in \{0,1\}^{k_1 \times B}$. Put
    $\theta_t := \theta(c_{t,1}, \dots, c_{t,B})$ for $t \le k_1$ and $\theta_s := 0$ for
    $k_1 < s \le k_1 + B + 1$. Then
    $g := f_{\theta_{k_1+B+1}} \circ \cdots \circ f_{\theta_1} \in B(k_1 + B + 1, F_\Lambda)$
    satisfies: the first coordinate of $g(x_{t,b})$ equals $a_{c_{t,b}}$ for all
    $t \le k_1$, $b \le B$, where $a_0 = \tfrac34$ and $a_1 = \tfrac78$. -/)]
theorem prop_relu_shatter_labels {w : ℕ} (hw : 11 ≤ w) {βW β Λ : ℝ≥0} (hβW : 17 ≤ βW)
    (hβ : 2 ≤ β) (hΛ : 85 ≤ Λ) (k₁ B : ℕ) (c : Fin k₁ → Fin B → Fin 2) :
    ∃ g ∈ wordBall (reluClass isProjectionOnto_clipSquare w βW β Λ) (k₁ + B + 1),
      ∀ (t : Fin k₁) (b : Fin B),
        ((g (shatterPoint t b) : unitSquare) : E₂) 0 = shatterSink (c t b) := by
  /-- `prop:relu-shatter-labels-of-subset` with $F = F_\Lambda$, which contains every
    $f_\theta$, $\theta \in [0, \tfrac14]$ (`prop:relu-shatter-i`). -/
  exact prop_relu_shatter_labels_of_subset
    (fun _ hθ => shatterBlock_mem_reluClass_of_le hw hθ hβW hβ hΛ) k₁ B c

@[blueprint "def:relu-shatter-sample"
  (statement := /-- The sample $S = (x_{t,b})_{t \le k_1,\, b \le B}$ of $n = k_1 B$ points,
    indexed through the bijection $\{1,\dots,k_1\} \times \{1,\dots,B\} \cong
    \{1,\dots,k_1 B\}$. -/)]
noncomputable def shatterSample (k₁ B : ℕ) : Fin (k₁ * B) → unitSquare :=
  fun i => shatterPoint (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

@[blueprint "prop:relu-shatter-iii-of-subset"
  (statement := /-- \textbf{(`prop:relu-shatter`(iii) for every class containing the blocks
    $f_\theta$: Rademacher lower bound.)} Let $F$ be a hidden-layer class on $K = [0,1]^2$
    with $f_\theta \in F$ for
    all $\theta \in [0, \tfrac14]$. Let $k_1, B \ge 1$, $k \ge k_1 + B + 1$, $R \ge 0$,
    $H_R = \{x \mapsto \langle u, x\rangle : \|u\| \le R\}$ and $S = (x_{t,b})_{t,b}$ the
    sample of $n = k_1 B$ points. Then
    $$\hat{\mathfrak R}_S\bigl(H_R \circ B(k, F)\bigr) \ge \frac{R}{16}.$$ -/)]
theorem prop_relu_shatter_rademacher_of_subset {F : Set (unitSquare → unitSquare)}
    (hF : ∀ θ ∈ Icc (0 : ℝ) (1 / 4), shatterBlock θ ∈ F) {k₁ B k : ℕ} (hk₁ : 0 < k₁)
    (hB : 0 < B) (hk : k₁ + B + 1 ≤ k) {R : ℝ} (hR : 0 ≤ R) :
    R / 16 ≤ empRademacher (shatterSample k₁ B)
      (hypothesisClass (linearReadouts (fun x : unitSquare => (x : E₂)) R) F k) := by
  have hn : 0 < k₁ * B := Nat.mul_pos hk₁ hB
  have hΦ : ∀ x : unitSquare, ‖(x : E₂)‖ ≤ √2 := fun x => norm_le_sqrt_two_of_mem_unitSquare x.2
  /-- Step 1. The output layer $h(x) = \langle R e_0, x\rangle = R\,x_0$ ($e_0$ the first
    basis vector) belongs to $H_R$. -/
  have hh : (fun x : unitSquare =>
      inner ℝ (R • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) (x : E₂)) ∈
      linearReadouts (fun x : unitSquare => (x : E₂)) R := by
    refine ⟨R • EuclideanSpace.single (0 : Fin 2) (1 : ℝ), ?_, rfl⟩
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hR]
    simp
  have hval : ∀ x : unitSquare,
      inner ℝ (R • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) (x : E₂) = R * (x : E₂) 0 := by
    intro x
    rw [real_inner_smul_left, EuclideanSpace.inner_single_left]
    simp
  /-- Step 2. Every labeling $c \in \{0,1\}^n$ of the sample is realized at the levels
    $a_0 = \tfrac34 R$, $a_1 = \tfrac78 R$ by $h \circ g$ with
    $g \in B(k_1 + B + 1, F) \subseteq B(k, F)$ (`prop:relu-shatter-labels-of-subset`). -/
  have hshatter : ∀ c : Fin (k₁ * B) → Bool, ∃ f ∈ wordBall F k, ∀ i,
      (fun x : unitSquare =>
        inner ℝ (R • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) (x : E₂))
        (f (shatterSample k₁ B i)) = if c i then R * (7 / 8) else R * (3 / 4) := by
    intro c
    obtain ⟨g, hg, hgS⟩ := prop_relu_shatter_labels_of_subset hF k₁ B
      (fun t b => if c (finProdFinEquiv (t, b)) then 1 else 0)
    refine ⟨g, wordBall_mono hk hg, fun i => ?_⟩
    have h := hgS (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
    rw [Prod.mk.eta, Equiv.apply_symm_apply] at h
    change inner ℝ (R • EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
      ((g (shatterSample k₁ B i) : unitSquare) : E₂) = _
    rw [hval]
    change R * ((g (shatterPoint (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) :
      unitSquare) : E₂) 0 = _
    rw [h]
    cases c i <;> simp [shatterSink]
  /-- Step 3. Every function of $H_R \circ B(k, F)$ is bounded by $R\sqrt2$ on $K$
    (Cauchy--Schwarz and $\|x\| \le \sqrt 2$ on $K$), so `lem:shatter-rademacher-comp` gives
    $\hat{\mathfrak R}_S \ge (\tfrac78 R - \tfrac34 R)/2 = R/16$. -/
  have key := empRademacher_compClass_ge_of_shatter hn (shatterSample k₁ B)
    (linearReadouts (fun x : unitSquare => (x : E₂)) R) (wordBall F k) hh
    (a₀ := R * (3 / 4)) (a₁ := R * (7 / 8)) (C := R * √2) (by linarith) hshatter
    (fun g hg i => abs_le_of_mem_compClass_linearReadouts hΦ hR hg _)
  have hval' : R / 16 = (R * (7 / 8) - R * (3 / 4)) / 2 := by ring
  rw [hval']
  exact key

@[blueprint "prop:relu-shatter-iii"
  (statement := /-- \textbf{(`prop:relu-shatter`(iii), lower bound on the sample: deep ReLU
    networks shatter $k_1 B$ points at depth $k_1 + B + 1$.)} Let $K = [0,1]^2$ with the
    clipping retraction $\Pi_K$, $w \ge 11$,
    $\beta_W \ge 17$, $\beta \ge 2$, $\Lambda \ge 85$ and $F_\Lambda$ the class of ReLU blocks
    $x \mapsto \Pi_K(V\,\mathrm{relu}(Wx + b) + c)$ of width $w$ with
    $\|W\|_{\rm op}, \|V\|_{\rm op} \le \beta_W$, $\|b\|, \|c\| \le \beta$ and Lipschitz
    constant at most $\Lambda$. Let $k_1, B \ge 1$ and
    $x_{t,b} = (\tfrac18(1 + 2^{-b})2^{-(t-1)}, 0)$, $t \le k_1$, $b \le B$. For every
    $c \in \{0,1\}^{k_1 \times B}$ there is $g \in B(k_1 + B + 1, F_\Lambda)$ such that the
    first coordinate (the track) of $g(x_{t,b})$ equals $a_{c_{t,b}}$ for all $t, b$, with
    $a_0 = \tfrac34$, $a_1 = \tfrac78$ (`prop:relu-shatter-labels`). Consequently, for every
    $k \ge k_1 + B + 1$, the linear output layers
    $H_R = \{x \mapsto \langle u, x\rangle : \|u\| \le R\}$, $R \ge 0$, and the sample
    $S = (x_{t,b})_{t,b}$ of $n = k_1 B$ points,
    $$\hat{\mathfrak R}_S\bigl(H_R \circ B(k, F_\Lambda)\bigr) \ge \frac{R}{16}.$$ -/)]
theorem prop_relu_shatter_rademacher {w : ℕ} (hw : 11 ≤ w) {βW β Λ : ℝ≥0} (hβW : 17 ≤ βW)
    (hβ : 2 ≤ β) (hΛ : 85 ≤ Λ) {k₁ B k : ℕ} (hk₁ : 0 < k₁) (hB : 0 < B)
    (hk : k₁ + B + 1 ≤ k) {R : ℝ} (hR : 0 ≤ R) :
    R / 16 ≤ empRademacher (shatterSample k₁ B)
      (hypothesisClass (linearReadouts (fun x : unitSquare => (x : E₂)) R)
        (reluClass isProjectionOnto_clipSquare w βW β Λ) k) := by
  /-- `prop:relu-shatter-iii-of-subset` with $F = F_\Lambda$, which contains every $f_\theta$,
    $\theta \in [0, \tfrac14]$ (`prop:relu-shatter-i`): the labelings are
    realized by `prop:relu-shatter-labels`, and `lem:shatter-rademacher-comp` with the output
    layer $x \mapsto R\,x_0$ gives $(\tfrac78 R - \tfrac34 R)/2 = R/16$. -/
  exact prop_relu_shatter_rademacher_of_subset
    (fun _ hθ => shatterBlock_mem_reluClass_of_le hw hθ hβW hβ hΛ) hk₁ hB hk hR

@[blueprint "prop:relu-shatter"
  (statement := /-- \textbf{(Load--count--sort blocks.)} Let $K = [0,1]^2$ with the
    coordinatewise clipping retraction, and write a state as $(z, y)$. For
    $\theta \in [0, \tfrac14]$ let (`def:relu-shatter-block`)
    $$f_\theta(z, y) := \Bigl(\mathrm{clip}\bigl(P(z) + s(z, y)\bigr),\
      \mathrm{clip}\bigl(4\,\mathrm{relu}(y) - 8\,\mathrm{relu}(y - \tfrac12)
      + \theta\,\psi(z)\bigr)\Bigr),$$
    where $\mathrm{clip} = \Pi_{[0,1]}$ and (`def:relu-shatter-P`, `def:relu-shatter-psi`,
    `def:relu-shatter-sort`)
    $$P(z) := 2\,\mathrm{relu}(z) - 4\,\mathrm{relu}(z - \tfrac3{16})
      + 4\,\mathrm{relu}(z - \tfrac14) - \tfrac52\,\mathrm{relu}(z - \tfrac12)
      + \tfrac32\,\mathrm{relu}(z - \tfrac34),$$
    $$\psi(z) := 32\,\mathrm{relu}(z - \tfrac3{32}) - 32\,\mathrm{relu}(z - \tfrac18)
      - 16\,\mathrm{relu}(z - \tfrac3{16}) + 16\,\mathrm{relu}(z - \tfrac14),$$
    $$s(z, y) := \mathrm{relu}\bigl(2(z - \tfrac12) + \tfrac14(y - \tfrac14)\bigr)
      - \mathrm{relu}\bigl(2(z - \tfrac12) + \tfrac14(y - \tfrac34)\bigr).$$
    \begin{enumerate}
    \item[(i)] (Membership.) Every $f_\theta$, $\theta \in [0, \tfrac14]$, is a ReLU block of
      width $11$ (with the parameters `def:relu-shatter-param`) and belongs to $F_\Lambda$ for
      every width $w \ge 11$, $\beta_W \ge 17$, $\beta \ge 2$ and $\Lambda \ge 85$.
    \item[(ii)] (Shattering.) Let $k_1, B \ge 1$, $a_0 := \tfrac34$, $a_1 := \tfrac78$ and
      $x_{t,b} := (\tfrac18(1 + 2^{-b})\,2^{-(t-1)}, 0)$, $1 \le t \le k_1$,
      $1 \le b \le B$. For every $c \in \{0,1\}^{k_1 \times B}$ there are
      $\theta_1, \dots, \theta_{k_1+B+1} \in [0, \tfrac14]$ such that the first coordinate of
      $f_{\theta_{k_1+B+1}} \circ \cdots \circ f_{\theta_1}(x_{t,b})$ equals $a_{c_{t,b}}$ for
      all $t$ and $b$.
    \item[(iii)] (Lower bound on the sample.) Let $k \ge k_1 + B + 1$, let $S$ be the sample
      of the $n = k_1 B$ points $x_{t,b}$ and
      $H = \{x \mapsto \langle u, x\rangle : \|u\| \le R\}$ with $R \ge 0$. Then, for
      $F_\Lambda$ as in (i),
      $$\hat{\mathfrak R}_S\bigl(H \circ B(k, F_\Lambda)\bigr) \ge \frac{R}{16}.$$
    \end{enumerate}
    The Lean statement is the conjunction of (i), (ii) and (iii) for $w$, $\beta_W$, $\beta$,
    $\Lambda$ in the ranges of (i); the three parts are `prop:relu-shatter-i`,
    `prop:relu-shatter-ii` and `prop:relu-shatter-iii`. In Lean, (ii) is stated for all
    $k_1, B \ge 0$ and (iii) for $k_1, B \ge 1$. -/)]
theorem prop_relu_shatter {w : ℕ} (hw : 11 ≤ w) {βW β Λ : ℝ≥0} (hβW : 17 ≤ βW)
    (hβ : 2 ≤ β) (hΛ : 85 ≤ Λ) :
    (∀ θ ∈ Icc (0 : ℝ) (1 / 4),
      reluBlock isProjectionOnto_clipSquare (shatterParam 0 θ) = shatterBlock θ ∧
        shatterBlock θ ∈ reluClass isProjectionOnto_clipSquare w βW β Λ) ∧
    (∀ (k₁ B : ℕ) (c : Fin k₁ → Fin B → Fin 2),
      ∃ θ : ℕ → ℝ, (∀ s, θ s ∈ Icc (0 : ℝ) (1 / 4)) ∧ ∀ (t : Fin k₁) (b : Fin B),
        ((shatterNet θ (k₁ + B + 1) (shatterPoint t b) : unitSquare) : E₂) 0 =
          shatterSink (c t b)) ∧
    (∀ k₁ B k : ℕ, 0 < k₁ → 0 < B → k₁ + B + 1 ≤ k → ∀ R : ℝ, 0 ≤ R →
      R / 16 ≤ empRademacher (shatterSample k₁ B)
        (hypothesisClass (linearReadouts (fun x : unitSquare => (x : E₂)) R)
          (reluClass isProjectionOnto_clipSquare w βW β Λ) k)) :=
  ⟨fun θ hθ => ⟨reluBlock_shatterParam 0 θ, shatterBlock_mem_reluClass_of_le hw hθ hβW hβ hΛ⟩,
    prop_relu_shatter_params,
    fun _ _ _ hk₁ hB hk _ hR => prop_relu_shatter_rademacher hw hβW hβ hΛ hk₁ hB hk hR⟩

end Shatter

/-! ### Consequence for the entropy integral `V_k(S)` -/

section EnvelopeIntegrable

open FoML.ToMathlib

variable {X : Type*} [PseudoMetricSpace X] {F : Set (X → X)} {Λ : ℝ≥0}

@[blueprint "lem:envelope-wordball-totally-bounded"
  (statement := /-- If every $f \in F$ is $\Lambda$-Lipschitz and
    $N^{\mathrm{ext}}(F, d_\infty, \varepsilon) < \infty$ for all $\varepsilon > 0$, then for
    $k \ge 1$ the depth-$k$ hidden class $B(k,F)$ is totally bounded in $d_S$, for every
    sample $S$: by the envelope (`lem:envelope-ne-top`),
    $N^{\mathrm{ext}}(B(k,F), d_S, \varepsilon) \le N^{\mathrm{ext}}(B(k,F), d_\infty,
    \varepsilon) < \infty$. -/)]
theorem totallyBounded_empSpace_wordBall_of_covering (hF : ∀ f ∈ F, LipschitzWith Λ f)
    (hfin : ∀ ε : ℝ≥0, 0 < ε → externalCoveringNumber (X := UnifMaps X) ε F ≠ ⊤) {n : ℕ}
    (S : Fin n → X) {k : ℕ} (hk : 1 ≤ k) : TotallyBounded (α := EmpSpace S) (wordBall F k) :=
  FoML.ToFoML.totallyBounded_of_externalCoveringNumber_ne_top (X := EmpSpace S) fun ε hε =>
    ne_top_of_le_ne_top (envelope_ne_top hF (hfin _ (div_pos hε (geomSum_pos hk))))
      (externalCoveringNumber_empSpace_le S ε _)

@[blueprint "lem:envelope-one-add-majorant"
  (statement := /-- (Pointwise majorant of the entropy integrand under the envelope.) Let
    every $f \in F$ be $\Lambda$-Lipschitz, $\overline D > 0$, $C \ge 0$, $p \ge 0$, and suppose
    $N^{\mathrm{ext}}(F, d_\infty, \varepsilon) < \infty$ and
    $\log N^{\mathrm{ext}}(F, d_\infty, \varepsilon) \le p\log(1 + C/\varepsilon)$ for all
    $\varepsilon > 0$. Then for $k \ge 1$, every sample $S$ and $0 < \varepsilon \le
    \overline D$,
    $$\sqrt{\log N(B(k,F), d_S, \varepsilon)} \le
      \sqrt{\log(k+1) + kp\bigl(\log(1 + 2C/\overline D) + \log S_k(\Lambda)\bigr)}
      + \sqrt{kp}\,\sqrt{\log(\overline D/\varepsilon)} ,$$
    with $S_k(\Lambda) = \sum_{i<k}\Lambda^i$ (the pointwise step of
    `cor:envelope-profiles-a-one-add`). -/)]
theorem sqrt_metricEntropy_wordBall_le_one_add (hF : ∀ f ∈ F, LipschitzWith Λ f) {p C Dbar : ℝ}
    (hp : 0 ≤ p) (hC : 0 ≤ C) (hDbar : 0 < Dbar)
    (hfin : ∀ ε : ℝ≥0, 0 < ε → externalCoveringNumber (X := UnifMaps X) ε F ≠ ⊤)
    (hN : ∀ ε : ℝ≥0, 0 < ε →
      Real.log (externalCoveringNumber (X := UnifMaps X) ε F : ℝ≥0∞).toReal ≤
        p * Real.log (1 + C / ε))
    {n : ℕ} (S : Fin n → X) {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : ε ∈ Ioc 0 Dbar) :
    √(metricEntropy (X := EmpSpace S) ε.toNNReal (wordBall F k)) ≤
      √(Real.log (k + 1) + k * p * (Real.log (1 + 2 * C / Dbar) + Real.log (geomSum Λ k)))
        + √(k * p) * √(Real.log (Dbar / ε)) := by
  /-- $\log N(B(k,F), d_S, \varepsilon) \le \log N^{\mathrm{ext}}(B(k,F), d_\infty,
    \varepsilon/2) \le \log(k+1) + kp\log(1 + 2CS_k/\varepsilon)$ and
    $1 + 2CS_k/\varepsilon \le (1 + 2C/\overline D)\,S_k\,\overline D/\varepsilon$ for
    $\varepsilon \le \overline D$; then $\sqrt{a + b} \le \sqrt a + \sqrt b$. -/
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := by linarith
  have hkp : (0 : ℝ) ≤ k * p := by positivity
  have hS1 : (1 : ℝ) ≤ geomSum Λ k := by exact_mod_cast one_le_geomSum (Λ := Λ) hk
  have hSpos : (0 : ℝ) < geomSum Λ k := by linarith
  have hε0 : 0 < ε := hε.1
  have hεD : ε ≤ Dbar := hε.2
  have hεr : ((ε.toNNReal : ℝ≥0) : ℝ) = ε := Real.coe_toNNReal ε hε0.le
  have hε2 : 0 < ε.toNNReal / 2 := by positivity
  have hρ : 0 < ε.toNNReal / 2 / geomSum Λ k := div_pos hε2 (geomSum_pos hk)
  have h1 := metricEntropy_wordBall_le_envelope hF S (k := k) (ε := ε.toNNReal) (hfin _ hρ)
  have h2 := log_envelope_le hF hk (hfin _ hρ)
  have h3 := hN _ hρ
  have hρval : ((ε.toNNReal / 2 / geomSum Λ k : ℝ≥0) : ℝ) = ε / 2 / geomSum Λ k := by
    rw [NNReal.coe_div, NNReal.coe_div, hεr]
    norm_num
  have h4 : Real.log (1 + C / ((ε.toNNReal / 2 / geomSum Λ k : ℝ≥0) : ℝ)) ≤
      Real.log (1 + 2 * C / Dbar) + Real.log (geomSum Λ k) + Real.log (Dbar / ε) := by
    rw [hρval]
    have e1 : 1 + C / (ε / 2 / geomSum Λ k) = 1 + 2 * C * geomSum Λ k / ε := by
      field_simp
    have e2 : (1 + 2 * C / Dbar) * geomSum Λ k * (Dbar / ε) =
        geomSum Λ k * (Dbar / ε) + 2 * C * geomSum Λ k / ε := by
      field_simp
    have h5 : 1 ≤ geomSum Λ k * (Dbar / ε) :=
      one_le_mul_of_one_le_of_one_le hS1 ((one_le_div hε0).2 hεD)
    have h6 : 1 + 2 * C * geomSum Λ k / ε ≤ (1 + 2 * C / Dbar) * geomSum Λ k * (Dbar / ε) := by
      rw [e2]; linarith
    rw [e1]
    calc Real.log (1 + 2 * C * geomSum Λ k / ε)
        ≤ Real.log ((1 + 2 * C / Dbar) * geomSum Λ k * (Dbar / ε)) :=
          Real.log_le_log (by positivity) h6
      _ = Real.log (1 + 2 * C / Dbar) + Real.log (geomSum Λ k) + Real.log (Dbar / ε) := by
          rw [Real.log_mul (by positivity) (by positivity),
            Real.log_mul (by positivity) (by positivity)]
  have h7 : metricEntropy (X := EmpSpace S) ε.toNNReal (wordBall F k) ≤
      Real.log (k + 1) + k * p * (Real.log (1 + 2 * C / Dbar) + Real.log (geomSum Λ k))
        + k * p * Real.log (Dbar / ε) := by
    have h8 : Real.log (externalCoveringNumber (X := UnifMaps X)
        (ε.toNNReal / 2 / geomSum Λ k) F : ℝ≥0∞).toReal ≤
        p * (Real.log (1 + 2 * C / Dbar) + Real.log (geomSum Λ k) + Real.log (Dbar / ε)) :=
      h3.trans (mul_le_mul_of_nonneg_left h4 hp)
    have h9 := mul_le_mul_of_nonneg_left h8 hk0
    nlinarith
  calc √(metricEntropy (X := EmpSpace S) ε.toNNReal (wordBall F k))
      ≤ √(Real.log (k + 1) + k * p * (Real.log (1 + 2 * C / Dbar) + Real.log (geomSum Λ k))
          + k * p * Real.log (Dbar / ε)) := Real.sqrt_le_sqrt h7
    _ ≤ √(Real.log (k + 1) + k * p * (Real.log (1 + 2 * C / Dbar) + Real.log (geomSum Λ k)))
          + √(k * p * Real.log (Dbar / ε)) := sqrt_add_le _ _
    _ = √(Real.log (k + 1) + k * p * (Real.log (1 + 2 * C / Dbar) + Real.log (geomSum Λ k)))
          + √(k * p) * √(Real.log (Dbar / ε)) := by rw [Real.sqrt_mul hkp]

@[blueprint "lem:envelope-one-add-integrable"
  (statement := /-- \textbf{(Integrability under the envelope.)} Under the hypotheses of
    `lem:envelope-one-add-majorant`, if $D_k(S) \le \overline D$ then the entropy integrand
    $\varepsilon \mapsto \sqrt{\log N(B(k,F), d_S, \varepsilon)}$ is interval-integrable on
    $[0, D_k(S)]$: the hypothesis of `thm:hidden-decomp-depth` is automatic for parametric
    Lipschitz layers (the majorant is a constant plus a multiple of
    $\sqrt{\log(\overline D/\varepsilon)}$, which is integrable on $[0, \overline D]$). -/)]
theorem intervalIntegrable_wordBall_of_one_add (hF : ∀ f ∈ F, LipschitzWith Λ f) {p C Dbar : ℝ}
    (hp : 0 ≤ p) (hC : 0 ≤ C) (hDbar : 0 < Dbar)
    (hfin : ∀ ε : ℝ≥0, 0 < ε → externalCoveringNumber (X := UnifMaps X) ε F ≠ ⊤)
    (hN : ∀ ε : ℝ≥0, 0 < ε →
      Real.log (externalCoveringNumber (X := UnifMaps X) ε F : ℝ≥0∞).toReal ≤
        p * Real.log (1 + C / ε))
    {n : ℕ} (S : Fin n → X) {k : ℕ} (hk : 1 ≤ k) (hD : empDiam S (wordBall F k) ≤ Dbar) :
    IntervalIntegrable
      (fun ε : ℝ => √(metricEntropy (X := EmpSpace S) ε.toNNReal (wordBall F k)))
      volume 0 (empDiam S (wordBall F k)) :=
  intervalIntegrable_sqrt_metricEntropy_of_le_of_le (empDiam_nonneg S _) hD
    (intervalIntegrable_const.add ((intervalIntegrable_sqrt_log_div hDbar).const_mul _))
    fun _ hε => sqrt_metricEntropy_wordBall_le_one_add hF hp hC hDbar hfin hN S hk hε

end EnvelopeIntegrable

section EntropyLower

@[blueprint "prop:relu-shatter-entropy"
  (statement := /-- \textbf{(Entropy-integral lower bound from shattering.)} In the situation
    of `prop:relu-shatter` ($K = [0,1]^2$, $w \ge 11$, $\beta_W \ge 17$, $\beta \ge 2$,
    $\Lambda \ge 85$, $k_1, B \ge 1$, $k \ge k_1 + B + 1$, sample $S = (x_{t,b})$ of
    $n = k_1 B$ points),
    $$\mathsf V_k(S) = \int_0^{D_k(S)} \sqrt{\log N(B(k, F_\Lambda), d_S, \varepsilon)}\,
      d\varepsilon \ \ge\ \frac{\sqrt n}{192} - \frac{\sqrt 2}{12} .$$
    Proof: with $R = 1$, `prop:relu-shatter`(iii) gives
    $\hat{\mathfrak R}_S(H_1 \circ B(k, F_\Lambda)) \ge \tfrac1{16}$; the hidden--output
    decomposition `thm:hidden-decomp-depth` with $A_H = 1$, $L = 1$ (`prop:hilbert-sg`) gives
    $\hat{\mathfrak R}_S(H_1 \circ B(k, F_\Lambda)) \le \hat{\mathfrak R}_S(H_1)
    + \tfrac{12}{\sqrt n}\mathsf V_k(S)$, and $\hat{\mathfrak R}_S(H_1) \le \sqrt2/\sqrt n$
    (`lem:linear-readouts-rademacher`, $\|x\| \le \sqrt 2$ on $K$). The total boundedness
    and integrability hypotheses of the decomposition hold by the covering bound
    `lem:relu-layer-covering` and the envelope (`lem:envelope-wordball-totally-bounded`,
    `lem:envelope-one-add-integrable`). -/)]
theorem prop_relu_shatter_entropy {w : ℕ} (hw : 11 ≤ w) {βW β Λ : ℝ≥0} (hβW : 17 ≤ βW)
    (hβ : 2 ≤ β) (hΛ : 85 ≤ Λ) {k₁ B k : ℕ} (hk₁ : 0 < k₁) (hB : 0 < B)
    (hk : k₁ + B + 1 ≤ k) :
    √((k₁ * B : ℕ) : ℝ) / 192 - √2 / 12 ≤
      entropyIntegral (Y := EmpSpace (shatterSample k₁ B))
        (empDiam (shatterSample k₁ B)
          (wordBall (reluClass isProjectionOnto_clipSquare w βW β Λ) k))
        (wordBall (reluClass isProjectionOnto_clipSquare w βW β Λ) k) := by
  have hn : 0 < k₁ * B := Nat.mul_pos hk₁ hB
  have hk1 : 1 ≤ k := by omega
  have hΦ : ∀ x : unitSquare, ‖(x : E₂)‖ ≤ √2 := fun x => norm_le_sqrt_two_of_mem_unitSquare x.2
  /-- Step 1. Lower bound: `prop:relu-shatter-iii` with $R = 1$. -/
  have hlow := prop_relu_shatter_rademacher hw hβW hβ hΛ hk₁ hB hk (R := 1) zero_le_one
  /-- Step 2. The hypotheses of the hidden--output decomposition for $F_\Lambda$: Lipschitz
    layers, finite covering numbers with $\log N \le p\log(1 + C_F/\varepsilon)$
    (`lem:relu-layer-covering-log` with $R_K = \sqrt2$), $D_k(S) \le 2\sqrt2$, total
    boundedness and integrability. -/
  have hFlip : ∀ f ∈ reluClass isProjectionOnto_clipSquare w βW β Λ, LipschitzWith Λ f :=
    fun f hf => lipschitzWith_of_mem_reluClass isProjectionOnto_clipSquare hf
  have hcov := fun (ε : ℝ≥0) (hε : 0 < ε) =>
    reluClass_covering_log isProjectionOnto_clipSquare (w := w)
      (fun x hx => norm_le_sqrt_two_of_mem_unitSquare hx) (Real.sqrt_nonneg 2) βW β Λ hε
  have hC0 : 0 ≤ reluCoverConst (√2) βW β := by rw [reluCoverConst]; positivity
  have hD : empDiam (shatterSample k₁ B)
      (wordBall (reluClass isProjectionOnto_clipSquare w βW β Λ) k) ≤ 2 * √2 :=
    empDiam_le_of_bounded _ (by positivity) (fun x y => by
      rw [Subtype.dist_eq]
      exact (dist_le_norm_add_norm _ _).trans (by linarith [hΦ x, hΦ y])) _
  have hFtb : TotallyBounded (α := EmpSpace (shatterSample k₁ B))
      (wordBall (reluClass isProjectionOnto_clipSquare w βW β Λ) k) :=
    totallyBounded_empSpace_wordBall_of_covering hFlip (fun ε hε => (hcov ε hε).1) _ hk1
  have hint := intervalIntegrable_wordBall_of_one_add hFlip (Nat.cast_nonneg _) hC0
    (by positivity : (0 : ℝ) < 2 * √2) (fun ε hε => (hcov ε hε).1) (fun ε hε => (hcov ε hε).2)
    (shatterSample k₁ B) hk1 hD
  /-- Step 3. Upper bound: `thm:hidden-decomp-depth` for $H_1$ ($A_H = 1$, $L = 1$) and
    $\hat{\mathfrak R}_S(H_1) \le \sqrt2/\sqrt n$. -/
  have hcoe : (((1 : ℝ).toNNReal * 1 : ℝ≥0) : ℝ) = 1 := by simp
  have hdec := empRademacher_le_of_entropyIntegral_le (shatterSample k₁ B)
    (linearReadouts (fun x : unitSquare => (x : E₂)) 1) hn
    (reluClass isProjectionOnto_clipSquare w βW β Λ) k (AH := 1)
    (L := (((1 : ℝ).toNNReal * 1 : ℝ≥0) : ℝ)) one_pos (by rw [hcoe]; exact one_pos)
    (fun f _ σ => bddAbove_range_normalizedRademacherSum_of_bound (f ∘ shatterSample k₁ B)
      (by positivity : (0 : ℝ) ≤ 1 * √2)
      (fun g hg x => (abs_le_of_mem_linearReadouts hg _).trans
        (mul_le_mul_of_nonneg_left (hΦ _) zero_le_one)) σ)
    hFtb (linearReadouts_sg (shatterSample k₁ B) _ (LipschitzWith.subtype_val _) one_pos _)
    hint le_rfl
  rw [hcoe] at hdec
  have hH := empRademacher_linearReadouts_le (shatterSample k₁ B)
    (fun x : unitSquare => (x : E₂)) zero_le_one (Real.sqrt_nonneg 2) hΦ
  /-- Step 4. Combine: $\tfrac1{16} \le \tfrac{\sqrt2}{\sqrt n} + \tfrac{12}{\sqrt n}
    \mathsf V_k(S)$, and multiply by $\sqrt n/12$. -/
  have hs : 0 < √((k₁ * B : ℕ) : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  set V := entropyIntegral (Y := EmpSpace (shatterSample k₁ B))
    (empDiam (shatterSample k₁ B) (wordBall (reluClass isProjectionOnto_clipSquare w βW β Λ) k))
    (wordBall (reluClass isProjectionOnto_clipSquare w βW β Λ) k) with hV
  set s := √((k₁ * B : ℕ) : ℝ) with hsdef
  have h1 : (1 : ℝ) / 16 ≤ 1 * √2 / s + 12 * 1 * 1 / s * V :=
    hlow.trans (hdec.trans (add_le_add hH le_rfl))
  have h2 : (1 : ℝ) / 16 * s ≤ (1 * √2 / s + 12 * 1 * 1 / s * V) * s :=
    mul_le_mul_of_nonneg_right h1 hs.le
  have h3 : (1 * √2 / s + 12 * 1 * 1 / s * V) * s = √2 + 12 * V := by
    field_simp
  linarith

@[blueprint "cor:relu-shatter-entropy-linear"
  (statement := /-- \textbf{(The linear order of the layerwise bound is attained by ReLU
    blocks.)} In the situation of `prop:relu-shatter`, let $k \ge 0$ and
    $k_1 = B = \lfloor (k-1)/2 \rfloor$, so that the sample $S = (x_{t,b})$ has
    $n = \lfloor (k-1)/2 \rfloor^2$ points and $k_1 + B + 1 \le k$. Then
    $$\mathsf V_k(S) \ge \frac{1}{192}\Bigl\lfloor \frac{k-1}{2} \Bigr\rfloor
      - \frac{\sqrt 2}{12},$$
    which is linear in $k$, as is the upper bound $O(k\sqrt{p\log\Lambda})$ of
    `prop:relu-regimes`(iii). (For $k \le 2$ the sample is empty and the right-hand side is
    negative.) -/)]
theorem prop_relu_shatter_entropy_linear {w : ℕ} (hw : 11 ≤ w) {βW β Λ : ℝ≥0} (hβW : 17 ≤ βW)
    (hβ : 2 ≤ β) (hΛ : 85 ≤ Λ) (k : ℕ) :
    (((k - 1) / 2 : ℕ) : ℝ) / 192 - √2 / 12 ≤
      entropyIntegral (Y := EmpSpace (shatterSample ((k - 1) / 2) ((k - 1) / 2)))
        (empDiam (shatterSample ((k - 1) / 2) ((k - 1) / 2))
          (wordBall (reluClass isProjectionOnto_clipSquare w βW β Λ) k))
        (wordBall (reluClass isProjectionOnto_clipSquare w βW β Λ) k) := by
  rcases Nat.lt_or_ge k 3 with hk | hk
  · /-- For $k \le 2$: $\lfloor (k-1)/2 \rfloor = 0$ and $\mathsf V_k(S) \ge 0$. -/
    have h0 : (((k - 1) / 2 : ℕ) : ℝ) = 0 := by
      have : (k - 1) / 2 = 0 := by omega
      rw [this, Nat.cast_zero]
    have hnn := entropyIntegral_nonneg (Y := EmpSpace (shatterSample ((k - 1) / 2) ((k - 1) / 2)))
      (empDiam_nonneg (shatterSample ((k - 1) / 2) ((k - 1) / 2))
        (wordBall (reluClass isProjectionOnto_clipSquare w βW β Λ) k))
      (wordBall (reluClass isProjectionOnto_clipSquare w βW β Λ) k)
    have hs : (0 : ℝ) ≤ √2 := Real.sqrt_nonneg 2
    rw [h0]
    linarith
  · /-- For $k \ge 3$: `prop:relu-shatter-entropy` with
      $k_1 = B = \lfloor (k-1)/2 \rfloor \ge 1$ and $\sqrt n = \lfloor (k-1)/2 \rfloor$. -/
    have h := prop_relu_shatter_entropy hw hβW hβ hΛ (k₁ := (k - 1) / 2) (B := (k - 1) / 2)
      (k := k) (by omega) (by omega) (by omega)
    rwa [Nat.cast_mul, Real.sqrt_mul_self (Nat.cast_nonneg _)] at h

end EntropyLower

end LeanDeepgen
