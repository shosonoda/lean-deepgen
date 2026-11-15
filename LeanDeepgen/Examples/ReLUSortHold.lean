import Mathlib
import Architect
import LeanDeepgen.Setting.WordBall
import LeanDeepgen.Setting.Metrics
import LeanDeepgen.Setting.Hypothesis
import LeanDeepgen.Setting.Rademacher
import LeanDeepgen.Growth.Defs
import LeanDeepgen.Growth.Exponential
import LeanDeepgen.Bounds.Shatter
import LeanDeepgen.Examples.Readout
import LeanDeepgen.Examples.ReLU

/-!
# Expand–sort–hold ReLU blocks: separation on the sample (paper App. `sec:app-relu`,
`lem:relu-sort-hold`)

Two explicit ReLU blocks of the state space `K = [0,1]` (clipping retraction,
`isProjectionOnto_clipUnit`) whose `2^k` compositions of depth `k` are separated *on a sample of
`k` points*, in contrast with the expand-and-reset maps of `LeanDeepgen.Examples.ReLU`, which are
separated in the uniform distance only.

* The maps (`sortHold₀`, `sortHold₁`; as self-maps of `[0,1]`: `sortHoldMap₀`, `sortHoldMap₁`,
  `sortHoldGen`):
  `f₀(x) = 2 relu(x) − 2 relu(x − 3/8) + relu(x − 3/4)` and
  `f₁(x) = 2 relu(x) + 2 relu(x − 1/4) − 4 relu(x − 3/8) − 2 relu(x − 5/8) + 3 relu(x − 3/4)`.
  Both double on `[0,1/4]` (expansion zone), send the gate point `1/2` to the level
  `a₀ = 3/4`, resp. `a₁ = 1` (`sortHoldSink`), and fix both levels (hold zone)
  (`sortHold₀_eq_piecewise`, `sortHold₁_eq_piecewise`, `sortHoldGen_apply_of_le`,
  `sortHoldGen_apply_half`, `sortHoldGen_apply_of_eq_sink`).
* (i) Membership: `f₀` is `2`-Lipschitz, `f₁` is `4`-Lipschitz, both are ReLU blocks of width
  `5` (thresholds `0, 1/4, 3/8, 5/8, 3/4`, output weights `(2,0,−2,0,1)` and `(2,2,−4,−2,3)`,
  `c = 0`; `reluBlock_sortHoldParam₀`, `reluBlock_sortHoldParam₁`), hence belong to
  `F_Λ = reluClass isProjectionOnto_clipUnit w βW β Λ` for `w ≥ 5`, `β_W ≥ 7`, `β ≥ 2`,
  `Λ ≥ 4` (`range_sortHoldGen_subset_reluClass`, `range_sortHoldGen_subset_reluClass_of_le`).
* (ii) The composition writes the word on the sample: for `x_j = 2^{-(j+1)}`
  (`sortHoldPoint`) and a word `u ∈ {0,1}^k`, `f_u = f_{u_{k-1}} ∘ ⋯ ∘ f_{u_0}`
  (`sortHoldWord`, an element of `B(k, {f₀,f₁})`) satisfies `f_u(x_j) = a_{u_j}`
  (`sortHoldWord_apply_point`).
* (iii) Separation and lower bound on the sample `S = (x_0, …, x_{k-1})`:
  `d_S(f_u, f_v)² = (1/16) · Ham(u,v)/k` (`empDist_sortHoldWord_sq`), and for the linear output
  layers `H_R = {x ↦ w x : |w| ≤ R}` (`linearReadouts` of the inclusion `[0,1] → ℝ`) and `k ≥ 1`,
  `R̂_S(H_R ∘ B(k, {f₀,f₁})) ≥ R/8` and `R̂_S(H_R ∘ B(k, F_Λ)) ≥ R/8`
  (`relu_sort_hold_rademacher`, `relu_sort_hold_rademacher_reluClass`), by
  `lem:shatter-rademacher` in the form for composite classes
  (`empRademacher_compClass_ge_of_shatter`, `LeanDeepgen.Bounds.Shatter`).

The statement of the paper, with its parts (i)–(iii), is assembled in `lem_relu_sort_hold`.

## Conventions

The sample has `n = k` points (each point once), so the lower bound `R/8` does not involve
Khintchine's inequality.  A word is a function `u : Fin k → Fin 2` and `sortHoldWord u` is
`wordOf sortHoldGen (List.ofFn u)` (`LeanDeepgen.Growth.Defs`): the letter `u 0` acts first.
-/

open scoped NNReal ENNReal
open Set

namespace LeanDeepgen

section SortHold

/-! ### The two maps -/

@[blueprint "def:relu-sort-hold-0"
  (statement := /-- The first expand–sort–hold map,
    $f_0(x) = 2\,\mathrm{relu}(x) - 2\,\mathrm{relu}(x - \tfrac38) + \mathrm{relu}(x - \tfrac34)$.
    -/)]
noncomputable def sortHold₀ (x : ℝ) : ℝ :=
  2 * max x 0 + (-2) * max (x - 3 / 8) 0 + max (x - 3 / 4) 0

@[blueprint "def:relu-sort-hold-1"
  (statement := /-- The second expand–sort–hold map,
    $f_1(x) = 2\,\mathrm{relu}(x) + 2\,\mathrm{relu}(x - \tfrac14) - 4\,\mathrm{relu}(x - \tfrac38)
    - 2\,\mathrm{relu}(x - \tfrac58) + 3\,\mathrm{relu}(x - \tfrac34)$. -/)]
noncomputable def sortHold₁ (x : ℝ) : ℝ :=
  2 * max x 0 + 2 * max (x - 1 / 4) 0 + (-4) * max (x - 3 / 8) 0 + (-2) * max (x - 5 / 8) 0
    + 3 * max (x - 3 / 4) 0

@[blueprint "lem:relu-sort-hold-0-piecewise"
  (statement := /-- For $x \ge 0$ (in particular on $[0,1]$): $f_0(x) = 2x$ on $[0, \tfrac38]$,
    $= \tfrac34$ on $[\tfrac38, \tfrac34]$, and $= x$ for $x \ge \tfrac34$. -/)]
theorem sortHold₀_eq_piecewise {x : ℝ} (hx : 0 ≤ x) :
    sortHold₀ x = if x ≤ 3 / 8 then 2 * x else if x ≤ 3 / 4 then 3 / 4 else x := by
  unfold sortHold₀
  split_ifs with h1 h2
  · rw [max_eq_left hx, max_eq_right (by linarith), max_eq_right (by linarith)]; ring
  · rw [max_eq_left hx, max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  · rw [max_eq_left hx, max_eq_left (by linarith), max_eq_left (by linarith)]; ring

@[blueprint "lem:relu-sort-hold-1-piecewise"
  (statement := /-- For $x \ge 0$ (in particular on $[0,1]$): $f_1(x) = 2x$ on $[0, \tfrac14]$,
    $= 4x - \tfrac12$ on $[\tfrac14, \tfrac38]$, $= 1$ on $[\tfrac38, \tfrac58]$,
    $= \tfrac94 - 2x$ on $[\tfrac58, \tfrac34]$, and $= x$ for $x \ge \tfrac34$. -/)]
theorem sortHold₁_eq_piecewise {x : ℝ} (hx : 0 ≤ x) :
    sortHold₁ x = if x ≤ 1 / 4 then 2 * x else if x ≤ 3 / 8 then 4 * x - 1 / 2
      else if x ≤ 5 / 8 then 1 else if x ≤ 3 / 4 then 9 / 4 - 2 * x else x := by
  unfold sortHold₁
  split_ifs with h1 h2 h3 h4
  · rw [max_eq_left hx, max_eq_right (by linarith), max_eq_right (by linarith),
      max_eq_right (by linarith), max_eq_right (by linarith)]; ring
  · rw [max_eq_left hx, max_eq_left (by linarith), max_eq_right (by linarith),
      max_eq_right (by linarith), max_eq_right (by linarith)]; ring
  · rw [max_eq_left hx, max_eq_left (by linarith), max_eq_left (by linarith),
      max_eq_right (by linarith), max_eq_right (by linarith)]; ring
  · rw [max_eq_left hx, max_eq_left (by linarith), max_eq_left (by linarith),
      max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  · rw [max_eq_left hx, max_eq_left (by linarith), max_eq_left (by linarith),
      max_eq_left (by linarith), max_eq_left (by linarith)]; ring

@[blueprint "lem:relu-sort-hold-0-mem"
  (statement := /-- $f_0$ maps $[0,1]$ into $[0,1]$. -/)]
theorem sortHold₀_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : sortHold₀ x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := hx
  rw [sortHold₀_eq_piecewise h0]
  split_ifs <;> constructor <;> linarith

@[blueprint "lem:relu-sort-hold-1-mem"
  (statement := /-- $f_1$ maps $[0,1]$ into $[0,1]$. -/)]
theorem sortHold₁_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : sortHold₁ x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := hx
  rw [sortHold₁_eq_piecewise h0]
  split_ifs <;> constructor <;> linarith

@[blueprint "lem:relu-sort-hold-0-lipschitz-on"
  (statement := /-- $|f_0(x) - f_0(y)| \le 2|x - y|$ for $x, y \ge 0$ (the slopes of $f_0$ are
    $2, 0, 1$). -/)]
theorem abs_sortHold₀_sub_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |sortHold₀ x - sortHold₀ y| ≤ 2 * |x - y| := by
  /-- Case analysis on the linear pieces containing $x$ and $y$; every case is a linear
    inequality. -/
  rw [sortHold₀_eq_piecewise hx, sortHold₀_eq_piecewise hy]
  rcases le_total x y with hxy | hxy
  · rw [abs_of_nonpos (sub_nonpos.2 hxy), abs_le]
    split_ifs <;> constructor <;> linarith
  · rw [abs_of_nonneg (sub_nonneg.2 hxy), abs_le]
    split_ifs <;> constructor <;> linarith

@[blueprint "lem:relu-sort-hold-1-lipschitz-on"
  (statement := /-- $|f_1(x) - f_1(y)| \le 4|x - y|$ for $x, y \ge 0$ (the slopes of $f_1$ are
    $2, 4, 0, -2, 1$). -/)]
theorem abs_sortHold₁_sub_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |sortHold₁ x - sortHold₁ y| ≤ 4 * |x - y| := by
  /-- Case analysis on the linear pieces containing $x$ and $y$; every case is a linear
    inequality. -/
  rw [sortHold₁_eq_piecewise hx, sortHold₁_eq_piecewise hy]
  rcases le_total x y with hxy | hxy
  · rw [abs_of_nonpos (sub_nonpos.2 hxy), abs_le]
    split_ifs <;> constructor <;> linarith
  · rw [abs_of_nonneg (sub_nonneg.2 hxy), abs_le]
    split_ifs <;> constructor <;> linarith

@[blueprint "def:relu-sort-hold-map-0"
  (statement := /-- $f_0$ as a self-map of the state space $[0,1]$. -/)]
noncomputable def sortHoldMap₀ : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 :=
  fun x => ⟨sortHold₀ x, sortHold₀_mem x.2⟩

@[blueprint "def:relu-sort-hold-map-1"
  (statement := /-- $f_1$ as a self-map of the state space $[0,1]$. -/)]
noncomputable def sortHoldMap₁ : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 :=
  fun x => ⟨sortHold₁ x, sortHold₁_mem x.2⟩

@[blueprint "lem:relu-sort-hold-map-0-lipschitz"
  (statement := /-- $f_0 : [0,1] \to [0,1]$ is $2$-Lipschitz. -/)]
theorem lipschitzWith_sortHoldMap₀ : LipschitzWith 2 sortHoldMap₀ := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Subtype.dist_eq, Subtype.dist_eq, Real.dist_eq, Real.dist_eq, NNReal.coe_ofNat]
  exact abs_sortHold₀_sub_le x.2.1 y.2.1

@[blueprint "lem:relu-sort-hold-map-1-lipschitz"
  (statement := /-- $f_1 : [0,1] \to [0,1]$ is $4$-Lipschitz. -/)]
theorem lipschitzWith_sortHoldMap₁ : LipschitzWith 4 sortHoldMap₁ := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Subtype.dist_eq, Subtype.dist_eq, Real.dist_eq, Real.dist_eq, NNReal.coe_ofNat]
  exact abs_sortHold₁_sub_le x.2.1 y.2.1

/-! ### (i) ReLU representation and membership in `F_Λ` -/

@[blueprint "def:relu-sort-hold-input"
  (statement := /-- Input weights of both expand–sort–hold blocks at width $5 + w'$: the vector
    $u = (1,1,1,1,1,0,\dots,0)$. -/)]
def sortHoldInput (w' : ℕ) : Fin (5 + w') → ℝ := Fin.append ![1, 1, 1, 1, 1] 0

@[blueprint "def:relu-sort-hold-thresholds"
  (statement := /-- Thresholds of both blocks:
    $t = (0, \tfrac14, \tfrac38, \tfrac58, \tfrac34, 0, \dots, 0)$. -/)]
noncomputable def sortHoldThreshold (w' : ℕ) : Fin (5 + w') → ℝ :=
  Fin.append ![0, 1 / 4, 3 / 8, 5 / 8, 3 / 4] 0

@[blueprint "def:relu-sort-hold-coefficients-0"
  (statement := /-- Output weights of $f_0$: $v = (2, 0, -2, 0, 1, 0, \dots, 0)$. -/)]
noncomputable def sortHoldCoef₀ (w' : ℕ) : Fin (5 + w') → ℝ := Fin.append ![2, 0, -2, 0, 1] 0

@[blueprint "def:relu-sort-hold-coefficients-1"
  (statement := /-- Output weights of $f_1$: $v = (2, 2, -4, -2, 3, 0, \dots, 0)$. -/)]
noncomputable def sortHoldCoef₁ (w' : ℕ) : Fin (5 + w') → ℝ := Fin.append ![2, 2, -4, -2, 3] 0

@[blueprint "def:relu-sort-hold-param-0"
  (statement := /-- The ReLU parameters of $f_0$ at width $5 + w'$ (bias $c = 0$). -/)]
noncomputable def sortHoldParam₀ (w' : ℕ) : ReLUParam ℝ (5 + w') :=
  unitParam (sortHoldInput w') (sortHoldThreshold w') (sortHoldCoef₀ w') 0

@[blueprint "def:relu-sort-hold-param-1"
  (statement := /-- The ReLU parameters of $f_1$ at width $5 + w'$ (bias $c = 0$). -/)]
noncomputable def sortHoldParam₁ (w' : ℕ) : ReLUParam ℝ (5 + w') :=
  unitParam (sortHoldInput w') (sortHoldThreshold w') (sortHoldCoef₁ w') 0

@[blueprint "lem:relu-sort-hold-sum-units-0"
  (statement := /-- The unit sum of $f_0$ at width $5 + w'$ (the units with zero output weight
    and the padding units vanish). -/)]
theorem sum_sortHoldCoef₀ (w' : ℕ) (x : ℝ) :
    ∑ i, sortHoldCoef₀ w' i * max (x * sortHoldInput w' i - sortHoldThreshold w' i) 0 =
      sortHold₀ x := by
  simp [sortHoldCoef₀, sortHoldInput, sortHoldThreshold, sortHold₀, Fin.sum_univ_add,
    Fin.sum_univ_five]

@[blueprint "lem:relu-sort-hold-sum-units-1"
  (statement := /-- The unit sum of $f_1$ at width $5 + w'$. -/)]
theorem sum_sortHoldCoef₁ (w' : ℕ) (x : ℝ) :
    ∑ i, sortHoldCoef₁ w' i * max (x * sortHoldInput w' i - sortHoldThreshold w' i) 0 =
      sortHold₁ x := by
  simp [sortHoldCoef₁, sortHoldInput, sortHoldThreshold, sortHold₁, Fin.sum_univ_add,
    Fin.sum_univ_five]

@[blueprint "lem:relu-sort-hold-block-0"
  (statement := /-- (\textbf{$f_0$ is a ReLU block of width $5 + w'$.}) With the clipping
    $\Pi_{[0,1]}$, thresholds $0, \tfrac14, \tfrac38, \tfrac58, \tfrac34$, output weights
    $(2, 0, -2, 0, 1)$ and $c = 0$: $f_{\vartheta_0} = f_0$ on $[0,1]$. -/)]
theorem reluBlock_sortHoldParam₀ (w' : ℕ) :
    reluBlock isProjectionOnto_clipUnit (sortHoldParam₀ w') = sortHoldMap₀ := by
  funext x
  apply Subtype.ext
  rw [sortHoldParam₀, reluBlock_unitParam, sum_sortHoldCoef₀, add_zero]
  exact clipUnit_of_mem (sortHold₀_mem x.2)

@[blueprint "lem:relu-sort-hold-block-1"
  (statement := /-- (\textbf{$f_1$ is a ReLU block of width $5 + w'$.}) With the clipping
    $\Pi_{[0,1]}$, thresholds $0, \tfrac14, \tfrac38, \tfrac58, \tfrac34$, output weights
    $(2, 2, -4, -2, 3)$ and $c = 0$: $f_{\vartheta_1} = f_1$ on $[0,1]$. -/)]
theorem reluBlock_sortHoldParam₁ (w' : ℕ) :
    reluBlock isProjectionOnto_clipUnit (sortHoldParam₁ w') = sortHoldMap₁ := by
  funext x
  apply Subtype.ext
  rw [sortHoldParam₁, reluBlock_unitParam, sum_sortHoldCoef₁, add_zero]
  exact clipUnit_of_mem (sortHold₁_mem x.2)

@[blueprint "lem:relu-sort-hold-norms-0"
  (statement := /-- Weight norms of the representation of $f_0$:
    $\|W\|_{\rm op} = \|u\| = \sqrt5 \le 7$, $\|b\| = \|t\| = \sqrt{74}/8 \le 2$,
    $\|V\|_{\rm op} = \|v\| = 3 \le 7$, $\|c\| = 0 \le 2$. -/)]
theorem sortHoldParam₀_norms (w' : ℕ) :
    ‖(sortHoldParam₀ w').1‖ ≤ 7 ∧ ‖(sortHoldParam₀ w').2.1‖ ≤ 2 ∧
      ‖(sortHoldParam₀ w').2.2.1‖ ≤ 7 ∧ ‖(sortHoldParam₀ w').2.2.2‖ ≤ 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change ‖ContinuousLinearMap.toSpanSingleton ℝ (WithLp.toLp 2 (sortHoldInput w') :
      EuclideanSpace ℝ (Fin (5 + w')))‖ ≤ 7
    rw [ContinuousLinearMap.norm_toSpanSingleton, EuclideanSpace.norm_eq,
      Real.sqrt_le_left (by norm_num)]
    simp [sortHoldInput, Fin.sum_univ_add, Fin.sum_univ_five]
    norm_num
  · change ‖(WithLp.toLp 2 (fun i => -sortHoldThreshold w' i) :
      EuclideanSpace ℝ (Fin (5 + w')))‖ ≤ 2
    rw [EuclideanSpace.norm_eq, Real.sqrt_le_left (by norm_num)]
    simp [sortHoldThreshold, Fin.sum_univ_add, Fin.sum_univ_five]
    norm_num
  · change ‖innerSL ℝ (WithLp.toLp 2 (sortHoldCoef₀ w') : EuclideanSpace ℝ (Fin (5 + w')))‖ ≤ 7
    rw [innerSL_apply_norm, EuclideanSpace.norm_eq, Real.sqrt_le_left (by norm_num)]
    simp [sortHoldCoef₀, Fin.sum_univ_add, Fin.sum_univ_five]
    norm_num
  · change ‖(0 : ℝ)‖ ≤ 2
    rw [norm_zero]; norm_num

@[blueprint "lem:relu-sort-hold-norms-1"
  (statement := /-- Weight norms of the representation of $f_1$:
    $\|W\|_{\rm op} = \sqrt5 \le 7$, $\|b\| = \sqrt{74}/8 \le 2$,
    $\|V\|_{\rm op} = \|v\| = \sqrt{37} \le 7$, $\|c\| = 0 \le 2$. -/)]
theorem sortHoldParam₁_norms (w' : ℕ) :
    ‖(sortHoldParam₁ w').1‖ ≤ 7 ∧ ‖(sortHoldParam₁ w').2.1‖ ≤ 2 ∧
      ‖(sortHoldParam₁ w').2.2.1‖ ≤ 7 ∧ ‖(sortHoldParam₁ w').2.2.2‖ ≤ 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change ‖ContinuousLinearMap.toSpanSingleton ℝ (WithLp.toLp 2 (sortHoldInput w') :
      EuclideanSpace ℝ (Fin (5 + w')))‖ ≤ 7
    rw [ContinuousLinearMap.norm_toSpanSingleton, EuclideanSpace.norm_eq,
      Real.sqrt_le_left (by norm_num)]
    simp [sortHoldInput, Fin.sum_univ_add, Fin.sum_univ_five]
    norm_num
  · change ‖(WithLp.toLp 2 (fun i => -sortHoldThreshold w' i) :
      EuclideanSpace ℝ (Fin (5 + w')))‖ ≤ 2
    rw [EuclideanSpace.norm_eq, Real.sqrt_le_left (by norm_num)]
    simp [sortHoldThreshold, Fin.sum_univ_add, Fin.sum_univ_five]
    norm_num
  · change ‖innerSL ℝ (WithLp.toLp 2 (sortHoldCoef₁ w') : EuclideanSpace ℝ (Fin (5 + w')))‖ ≤ 7
    rw [innerSL_apply_norm, EuclideanSpace.norm_eq, Real.sqrt_le_left (by norm_num)]
    simp [sortHoldCoef₁, Fin.sum_univ_add, Fin.sum_univ_five]
    norm_num
  · change ‖(0 : ℝ)‖ ≤ 2
    rw [norm_zero]; norm_num

@[blueprint "def:relu-sort-hold-generators"
  (statement := /-- The two generators $f = (f_0, f_1)$, as self-maps of $[0,1]$. -/)]
noncomputable def sortHoldGen : Fin 2 → Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 :=
  ![sortHoldMap₀, sortHoldMap₁]

@[blueprint "lem:relu-sort-hold-mem-class"
  (statement := /-- (\textbf{`lem:relu-sort-hold`(i), width $5 + w'$.}) For $\beta_W \ge 7$,
    $\beta \ge 2$, $\Lambda \ge 4$ and width $5 + w'$, $f_0, f_1 \in F_\Lambda$ on $K = [0,1]$
    with the clipping retraction. -/)]
theorem range_sortHoldGen_subset_reluClass (w' : ℕ) {βW β Λ : ℝ≥0} (hβW : 7 ≤ βW) (hβ : 2 ≤ β)
    (hΛ : 4 ≤ Λ) :
    Set.range sortHoldGen ⊆ reluClass isProjectionOnto_clipUnit (5 + w') βW β Λ := by
  have hβW' : (7 : ℝ) ≤ βW := by exact_mod_cast hβW
  have hβ' : (2 : ℝ) ≤ β := by exact_mod_cast hβ
  have hΛ₀ : (2 : ℝ≥0) ≤ Λ := le_trans (by norm_num) hΛ
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · obtain ⟨h1, h2, h3, h4⟩ := sortHoldParam₀_norms w'
    refine ⟨sortHoldParam₀ w', ⟨h1.trans hβW', h2.trans hβ', h3.trans hβW', h4.trans hβ', ?_⟩,
      reluBlock_sortHoldParam₀ w'⟩
    rw [reluBlock_sortHoldParam₀]
    exact lipschitzWith_sortHoldMap₀.weaken hΛ₀
  · obtain ⟨h1, h2, h3, h4⟩ := sortHoldParam₁_norms w'
    refine ⟨sortHoldParam₁ w', ⟨h1.trans hβW', h2.trans hβ', h3.trans hβW', h4.trans hβ', ?_⟩,
      reluBlock_sortHoldParam₁ w'⟩
    rw [reluBlock_sortHoldParam₁]
    exact lipschitzWith_sortHoldMap₁.weaken hΛ

@[blueprint "lem:relu-sort-hold-mem-class-of-le"
  (statement := /-- (\textbf{`lem:relu-sort-hold`(i).}) For every width $w \ge 5$,
    $\beta_W \ge 7$, $\beta \ge 2$ and $\Lambda \ge 4$, $f_0, f_1 \in F_\Lambda$ on $K = [0,1]$
    with the clipping retraction. -/)]
theorem range_sortHoldGen_subset_reluClass_of_le {w : ℕ} (hw : 5 ≤ w) {βW β Λ : ℝ≥0}
    (hβW : 7 ≤ βW) (hβ : 2 ≤ β) (hΛ : 4 ≤ Λ) :
    Set.range sortHoldGen ⊆ reluClass isProjectionOnto_clipUnit w βW β Λ := by
  obtain ⟨w', rfl⟩ : ∃ w', w = 5 + w' := ⟨w - 5, by omega⟩
  exact range_sortHoldGen_subset_reluClass w' hβW hβ hΛ

/-! ### (ii) The composition writes the word on the sample -/

@[blueprint "def:relu-sort-hold-sink"
  (statement := /-- The two levels $a_0 = \tfrac34$, $a_1 = 1$. -/)]
noncomputable def sortHoldSink : Fin 2 → ℝ := ![3 / 4, 1]

@[blueprint "lem:relu-sort-hold-double"
  (statement := /-- (Expansion zone.) $f_i(x) = 2x$ for $x \in [0, \tfrac14]$, $i = 0, 1$. -/)]
theorem sortHoldGen_apply_of_le (i : Fin 2) {x : Icc (0 : ℝ) 1} (hx : (x : ℝ) ≤ 1 / 4) :
    ((sortHoldGen i x : Icc (0 : ℝ) 1) : ℝ) = 2 * x := by
  have h0 := x.2.1
  fin_cases i
  · change sortHold₀ x = 2 * x
    rw [sortHold₀_eq_piecewise h0, if_pos (by linarith)]
  · change sortHold₁ x = 2 * x
    rw [sortHold₁_eq_piecewise h0, if_pos hx]

@[blueprint "lem:relu-sort-hold-gate"
  (statement := /-- (Gate.) $f_i(\tfrac12) = a_i$, $i = 0, 1$: $f_0(\tfrac12) = \tfrac34$ and
    $f_1(\tfrac12) = 1$. -/)]
theorem sortHoldGen_apply_half (i : Fin 2) {x : Icc (0 : ℝ) 1} (hx : (x : ℝ) = 1 / 2) :
    ((sortHoldGen i x : Icc (0 : ℝ) 1) : ℝ) = sortHoldSink i := by
  fin_cases i
  · change sortHold₀ x = 3 / 4
    rw [hx, sortHold₀_eq_piecewise (by norm_num)]
    norm_num
  · change sortHold₁ x = 1
    rw [hx, sortHold₁_eq_piecewise (by norm_num)]
    norm_num

@[blueprint "lem:relu-sort-hold-hold"
  (statement := /-- (Hold zone.) Both maps fix both levels: $f_i(a_s) = a_s$ for
    $i, s \in \{0, 1\}$. -/)]
theorem sortHoldGen_apply_of_eq_sink (i s : Fin 2) {x : Icc (0 : ℝ) 1}
    (hx : (x : ℝ) = sortHoldSink s) : sortHoldGen i x = x := by
  apply Subtype.ext
  have hx' : (x : ℝ) = 3 / 4 ∨ (x : ℝ) = 1 := by
    fin_cases s
    · exact Or.inl hx
    · exact Or.inr hx
  fin_cases i
  · change sortHold₀ x = x
    rcases hx' with h | h <;> rw [h, sortHold₀_eq_piecewise (by norm_num)] <;> norm_num
  · change sortHold₁ x = x
    rcases hx' with h | h <;> rw [h, sortHold₁_eq_piecewise (by norm_num)] <;> norm_num

@[blueprint "def:relu-sort-hold-point"
  (statement := /-- The sample points $x_j = 2^{-(j+1)} \in [0,1]$, $j \ge 0$. -/)]
noncomputable def sortHoldPoint (j : ℕ) : Icc (0 : ℝ) 1 :=
  ⟨(1 / 2) ^ (j + 1), by positivity, pow_le_one₀ (by norm_num) (by norm_num)⟩

@[blueprint "lem:relu-sort-hold-point-coe"
  (statement := /-- $x_j = (1/2)^{j+1}$ as a real number. -/)]
theorem sortHoldPoint_coe (j : ℕ) : ((sortHoldPoint j : Icc (0 : ℝ) 1) : ℝ) = (1 / 2) ^ (j + 1) :=
  rfl

@[blueprint "def:relu-sort-hold-word"
  (statement := /-- For a word $u = (u_0, \dots, u_{k-1}) \in \{0,1\}^k$, the composition
    $f_u = f_{u_{k-1}} \circ \cdots \circ f_{u_0}$ (the letter $u_0$ acts first;
    `def:word-of` for the list $(u_0, \dots, u_{k-1})$). -/)]
noncomputable def sortHoldWord {k : ℕ} (u : Fin k → Fin 2) : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 :=
  wordOf sortHoldGen (List.ofFn u)

@[blueprint "lem:relu-sort-hold-word-mem"
  (statement := /-- $f_u \in B(k, \{f_0, f_1\})$ for every word $u \in \{0,1\}^k$. -/)]
theorem sortHoldWord_mem_wordBall {k : ℕ} (u : Fin k → Fin 2) :
    sortHoldWord u ∈ wordBall (Set.range sortHoldGen) k :=
  wordOf_mem_wordBall sortHoldGen (by simp)

@[blueprint "lem:relu-sort-hold-word-succ"
  (statement := /-- $f_{(u_0, u_1, \dots, u_k)} = f_{(u_1, \dots, u_k)} \circ f_{u_0}$. -/)]
theorem sortHoldWord_succ {k : ℕ} (u : Fin (k + 1) → Fin 2) :
    sortHoldWord u = sortHoldWord (Fin.tail u) ∘ sortHoldGen (u 0) := by
  rw [sortHoldWord, List.ofFn_succ, wordOf_cons]
  rfl

@[blueprint "lem:relu-sort-hold-word-sink"
  (statement := /-- Every composition fixes both levels: $f_u(a_s) = a_s$. -/)]
theorem sortHoldWord_apply_of_eq_sink {k : ℕ} (u : Fin k → Fin 2) (s : Fin 2)
    {x : Icc (0 : ℝ) 1} (hx : (x : ℝ) = sortHoldSink s) : sortHoldWord u x = x := by
  /-- The set $\{a_s\}$ is invariant under both generators (`lem:relu-sort-hold-hold`), hence
    under every word (`lem:wordof-mem-of-invariant`). -/
  have hinv : ∀ i, sortHoldGen i '' {x} ⊆ {x} := by
    rintro i _ ⟨y, rfl, rfl⟩
    exact sortHoldGen_apply_of_eq_sink i s hx
  exact wordOf_mem_of_forall_image_subset sortHoldGen hinv (List.ofFn u) (Set.mem_singleton x)

@[blueprint "lem:relu-sort-hold-word-point"
  (statement := /-- (\textbf{`lem:relu-sort-hold`(ii): the composition writes the word on
    the sample.}) For every word $u \in \{0,1\}^k$ and every $j < k$, $f_u(x_j) = a_{u_j}$,
    where $x_j = 2^{-(j+1)}$. -/)]
theorem sortHoldWord_apply_point {k : ℕ} (u : Fin k → Fin 2) (j : Fin k) :
    ((sortHoldWord u (sortHoldPoint j) : Icc (0 : ℝ) 1) : ℝ) = sortHoldSink (u j) := by
  /-- Induction on $k$, peeling off the first letter: $f_u = f_{u'} \circ f_{u_0}$ with
    $u' = (u_1, \dots, u_{k-1})$. If $j = 0$ then $f_{u_0}(x_0) = f_{u_0}(\tfrac12) = a_{u_0}$
    (gate), which every later layer fixes (hold). If $j \ge 1$ then $x_j \le \tfrac14$, so
    $f_{u_0}(x_j) = 2x_j = x_{j-1}$ (expansion), and $f_{u'}(x_{j-1}) = a_{u'_{j-1}} = a_{u_j}$ by
    induction. -/
  induction k with
  | zero => exact j.elim0
  | succ k ih =>
    rw [sortHoldWord_succ, Function.comp_apply]
    induction j using Fin.cases with
    | zero =>
      have h0 : ((sortHoldGen (u 0) (sortHoldPoint ((0 : Fin (k + 1)) : ℕ)) : Icc (0 : ℝ) 1) : ℝ)
          = sortHoldSink (u 0) :=
        sortHoldGen_apply_half (u 0) (by rw [sortHoldPoint_coe, Fin.val_zero]; norm_num)
      rw [sortHoldWord_apply_of_eq_sink (Fin.tail u) (u 0) h0, h0]
    | succ i =>
      have h1 : sortHoldGen (u 0) (sortHoldPoint ((i.succ : Fin (k + 1)) : ℕ)) =
          sortHoldPoint (i : ℕ) := by
        apply Subtype.ext
        have hle : ((sortHoldPoint ((i.succ : Fin (k + 1)) : ℕ) : Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 4 := by
          rw [sortHoldPoint_coe, Fin.val_succ]
          calc ((1 : ℝ) / 2) ^ ((i : ℕ) + 1 + 1) = (1 / 2) ^ (i : ℕ) * (1 / 4) := by ring
            _ ≤ 1 * (1 / 4) :=
              mul_le_mul_of_nonneg_right (pow_le_one₀ (by norm_num) (by norm_num)) (by norm_num)
            _ = 1 / 4 := one_mul _
        rw [sortHoldGen_apply_of_le (u 0) hle, sortHoldPoint_coe, sortHoldPoint_coe, Fin.val_succ]
        ring
      rw [h1]
      exact ih (Fin.tail u) i

/-! ### (iii) Separation on the sample and the Rademacher lower bound -/

@[blueprint "lem:relu-sort-hold-dist"
  (statement := /-- (\textbf{`lem:relu-sort-hold`(iii): separation on the sample.}) On the
    sample $S = (x_0, \dots, x_{k-1})$, for all words $u, v \in \{0,1\}^k$,
    $$d_S(f_u, f_v)^2 = \frac1{16}\,\frac{\#\{j : u_j \ne v_j\}}{k} .$$ -/)]
theorem empDist_sortHoldWord_sq {k : ℕ} (u v : Fin k → Fin 2) :
    empDist (fun j : Fin k => sortHoldPoint j) (sortHoldWord u) (sortHoldWord v) ^ 2 =
      1 / 16 * (hammingDist u v : ℝ) / k := by
  /-- By (ii), $d(f_u(x_j), f_v(x_j)) = |a_{u_j} - a_{v_j}|$, which is $\tfrac14$ if
    $u_j \ne v_j$ and $0$ otherwise. -/
  have hterm : ∀ j : Fin k,
      dist (sortHoldWord u (sortHoldPoint j)) (sortHoldWord v (sortHoldPoint j)) ^ 2 =
        1 / 16 * (if u j ≠ v j then 1 else 0) := by
    intro j
    rw [Subtype.dist_eq, Real.dist_eq, sq_abs, sortHoldWord_apply_point,
      sortHoldWord_apply_point]
    generalize u j = a
    generalize v j = b
    fin_cases a <;> fin_cases b <;> simp [sortHoldSink] <;> norm_num
  unfold empDist
  rw [Real.sq_sqrt (by positivity), Finset.sum_congr rfl fun j _ => hterm j, ← Finset.mul_sum,
    Finset.sum_boole]
  simp only [hammingDist]
  ring

@[blueprint "lem:relu-sort-hold-rademacher-of-subset"
  (statement := /-- Let $F$ be any hidden-layer class on $[0,1]$ that contains $f_0$ and $f_1$,
    $H_R = \{x \mapsto w\,x : |w| \le R\}$ with $R \ge 0$, $k \ge 1$ and
    $S = (x_0, \dots, x_{k-1})$. Then $\hat{\mathfrak R}_S(H_R \circ B(k, F)) \ge R/8$. -/)]
theorem relu_sort_hold_rademacher_of_subset {F : Set (Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1)}
    (hF : Set.range sortHoldGen ⊆ F) {k : ℕ} (hk : 0 < k) {R : ℝ} (hR : 0 ≤ R) :
    R / 8 ≤ empRademacher (fun j : Fin k => sortHoldPoint j)
      (hypothesisClass (linearReadouts (fun x : Icc (0 : ℝ) 1 => (x : ℝ)) R) F k) := by
  /-- The functions $x \mapsto R f_u(x)$, $u \in \{0,1\}^k$, belong to $H_R \circ B(k,F)$ and
    realize every labeling of the sample with the two values $R a_0 = \tfrac34 R$ and
    $R a_1 = R$ (by (ii)); all functions of the class are bounded by $R$ on $[0,1]$. Apply
    `lem:shatter-rademacher-comp`: the lower bound is $(R - \tfrac34 R)/2 = R/8$. -/
  have hmain := empRademacher_compClass_ge_of_shatter hk (fun j : Fin k => sortHoldPoint j)
    (linearReadouts (fun x : Icc (0 : ℝ) 1 => (x : ℝ)) R) (wordBall F k)
    (h := fun x => inner ℝ R (x : ℝ)) ⟨R, by rw [Real.norm_eq_abs, abs_of_nonneg hR], rfl⟩
    (a₀ := R * (3 / 4)) (a₁ := R * 1) (C := R)
    (mul_le_mul_of_nonneg_left (by norm_num) hR) (fun c => ?_) ?_
  · calc R / 8 = (R * 1 - R * (3 / 4)) / 2 := by ring
      _ ≤ _ := hmain
  · refine ⟨sortHoldWord fun i => if c i then 1 else 0,
      wordBall_subset_wordBall_of_subset hF (sortHoldWord_mem_wordBall _), fun i => ?_⟩
    simp only [RCLike.inner_apply, conj_trivial]
    rw [sortHoldWord_apply_point]
    cases c i <;> simp [sortHoldSink, mul_comm]
  · rintro g ⟨h, ⟨w, hw, rfl⟩, f, -, rfl⟩ i
    simp only [Function.comp_apply]
    have hf := (f (sortHoldPoint (i : ℕ))).2
    calc |inner ℝ w ((f (sortHoldPoint (i : ℕ)) : Icc (0 : ℝ) 1) : ℝ)|
        ≤ ‖w‖ * ‖((f (sortHoldPoint (i : ℕ)) : Icc (0 : ℝ) 1) : ℝ)‖ := abs_real_inner_le_norm _ _
      _ ≤ R * 1 := by
          refine mul_le_mul hw ?_ (norm_nonneg _) hR
          rw [Real.norm_eq_abs, abs_of_nonneg hf.1]
          exact hf.2
      _ = R := mul_one R

@[blueprint "lem:relu-sort-hold-rademacher"
  (statement := /-- (\textbf{`lem:relu-sort-hold`(iii): Rademacher lower bound for the two-map
    class.}) For the linear output layers $H_R = \{x \mapsto w\,x : |w| \le R\}$, $R \ge 0$,
    every $k \ge 1$ and the sample $S = (x_0, \dots, x_{k-1})$,
    $$\hat{\mathfrak R}_S\bigl(H_R \circ B(k, \{f_0, f_1\})\bigr) \ge \frac R8 .$$ -/)]
theorem relu_sort_hold_rademacher {k : ℕ} (hk : 0 < k) {R : ℝ} (hR : 0 ≤ R) :
    R / 8 ≤ empRademacher (fun j : Fin k => sortHoldPoint j)
      (hypothesisClass (linearReadouts (fun x : Icc (0 : ℝ) 1 => (x : ℝ)) R)
        (Set.range sortHoldGen) k) :=
  relu_sort_hold_rademacher_of_subset subset_rfl hk hR

@[blueprint "lem:relu-sort-hold-rademacher-relu"
  (statement := /-- (\textbf{`lem:relu-sort-hold`(iii): Rademacher lower bound for
    $F_\Lambda$.})
    For $K = [0,1]$ with the clipping retraction, width $w \ge 5$, $\beta_W \ge 7$,
    $\beta \ge 2$, $\Lambda \ge 4$, the linear output layers
    $H_R = \{x \mapsto w\,x : |w| \le R\}$, $R \ge 0$, every $k \ge 1$ and the sample
    $S = (x_0, \dots, x_{k-1})$,
    $$\hat{\mathfrak R}_S\bigl(H_R \circ B(k, F_\Lambda)\bigr) \ge \frac R8 .$$ -/)]
theorem relu_sort_hold_rademacher_reluClass {w : ℕ} (hw : 5 ≤ w) {βW β Λ : ℝ≥0} (hβW : 7 ≤ βW)
    (hβ : 2 ≤ β) (hΛ : 4 ≤ Λ) {k : ℕ} (hk : 0 < k) {R : ℝ} (hR : 0 ≤ R) :
    R / 8 ≤ empRademacher (fun j : Fin k => sortHoldPoint j)
      (hypothesisClass (linearReadouts (fun x : Icc (0 : ℝ) 1 => (x : ℝ)) R)
        (reluClass isProjectionOnto_clipUnit w βW β Λ) k) :=
  relu_sort_hold_rademacher_of_subset (range_sortHoldGen_subset_reluClass_of_le hw hβW hβ hΛ) hk hR

/-! ### The statement of the paper -/

@[blueprint "lem:relu-sort-hold"
  (statement := /-- \textbf{(Expand–sort–hold ReLU blocks: separation on the sample.)} Let
    $K = [0,1]$ with the clipping retraction, $a_0 = \tfrac34$, $a_1 = 1$, and
    $$f_0(x) = 2\,\mathrm{relu}(x) - 2\,\mathrm{relu}(x - \tfrac38)
    + \mathrm{relu}(x - \tfrac34),$$
    $$f_1(x) = 2\,\mathrm{relu}(x) + 2\,\mathrm{relu}(x - \tfrac14)
    - 4\,\mathrm{relu}(x - \tfrac38) - 2\,\mathrm{relu}(x - \tfrac58)
    + 3\,\mathrm{relu}(x - \tfrac34) .$$
    On $[0,1]$: $f_0(x) = 2x$ on $[0, \tfrac38]$, $= \tfrac34$ on $[\tfrac38, \tfrac34]$,
    $= x$ on $[\tfrac34, 1]$; $f_1(x) = 2x$ on $[0, \tfrac14]$, $= 4x - \tfrac12$ on
    $[\tfrac14, \tfrac38]$, $= 1$ on $[\tfrac38, \tfrac58]$, $= \tfrac94 - 2x$ on
    $[\tfrac58, \tfrac34]$, $= x$ on $[\tfrac34, 1]$. Both map $[0,1]$ into itself.
    \begin{enumerate}
    \item[(i)] (Membership.) $f_0$ is $2$-Lipschitz, $f_1$ is $4$-Lipschitz, and both are ReLU
    blocks of width $5$, of the form $x \mapsto \Pi_K(V\,\mathrm{relu}(Wx + b) + c)$ (thresholds
    $0, \tfrac14, \tfrac38, \tfrac58, \tfrac34$; output weights $(2, 0, -2, 0, 1)$ and
    $(2, 2, -4, -2, 3)$; $c = 0$). Hence $f_0, f_1 \in F_\Lambda$ for every width $w \ge 5$,
    $\beta_W \ge 7$, $\beta \ge 2$, $\Lambda \ge 4$.
    \item[(ii)] (The composition writes the word on the sample.) For $k \ge 1$ let
    $x_j := 2^{-(j+1)}$, $j = 0, \dots, k-1$. For every word
    $u = (u_0, \dots, u_{k-1}) \in \{0,1\}^k$ and
    $f_u := f_{u_{k-1}} \circ \cdots \circ f_{u_0} \in B(k, \{f_0, f_1\})$ (so $u_0$ is applied
    first), $f_u(x_j) = a_{u_j}$ for all $j$.
    \item[(iii)] (Separation and lower bound on the sample.) On the sample
    $S = (x_0, \dots, x_{k-1})$: $d_S(f_u, f_v)^2 = \tfrac1{16}\,\#\{j : u_j \ne v_j\}/k$. For
    the linear output layers $H_R = \{x \mapsto w\,x : |w| \le R\}$, $R \ge 0$, and every
    $k \ge 1$,
    $$\hat{\mathfrak R}_S\bigl(H_R \circ B(k, \{f_0, f_1\})\bigr) \ge \frac R8 ,$$
    and the same bound holds for $H_R \circ B(k, F_\Lambda)$ for the parameter ranges in (i).
    \end{enumerate}
    The Lean statement lists, in this order: the two formulas for $f_0$ and for $f_1$ on
    $[0,1]$; (i); (ii); the two claims of (iii). -/)]
theorem lem_relu_sort_hold :
    ((∀ (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1),
        ((sortHoldGen 0 ⟨x, hx⟩ : Icc (0 : ℝ) 1) : ℝ) =
            2 * max x 0 + (-2) * max (x - 3 / 8) 0 + max (x - 3 / 4) 0 ∧
          ((sortHoldGen 0 ⟨x, hx⟩ : Icc (0 : ℝ) 1) : ℝ) =
            if x ≤ 3 / 8 then 2 * x else if x ≤ 3 / 4 then 3 / 4 else x) ∧
      (∀ (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1),
        ((sortHoldGen 1 ⟨x, hx⟩ : Icc (0 : ℝ) 1) : ℝ) =
            2 * max x 0 + 2 * max (x - 1 / 4) 0 + (-4) * max (x - 3 / 8) 0
              + (-2) * max (x - 5 / 8) 0 + 3 * max (x - 3 / 4) 0 ∧
          ((sortHoldGen 1 ⟨x, hx⟩ : Icc (0 : ℝ) 1) : ℝ) =
            if x ≤ 1 / 4 then 2 * x else if x ≤ 3 / 8 then 4 * x - 1 / 2
              else if x ≤ 5 / 8 then 1 else if x ≤ 3 / 4 then 9 / 4 - 2 * x else x)) ∧
    (LipschitzWith 2 (sortHoldGen 0) ∧ LipschitzWith 4 (sortHoldGen 1) ∧
      ∀ (w : ℕ) (βW β Λ : ℝ≥0), 5 ≤ w → 7 ≤ βW → 2 ≤ β → 4 ≤ Λ →
        Set.range sortHoldGen ⊆ reluClass isProjectionOnto_clipUnit w βW β Λ) ∧
    (∀ (k : ℕ) (u : Fin k → Fin 2), sortHoldWord u ∈ wordBall (Set.range sortHoldGen) k ∧
      ∀ j : Fin k,
        ((sortHoldWord u (sortHoldPoint j) : Icc (0 : ℝ) 1) : ℝ) = sortHoldSink (u j)) ∧
    (∀ (k : ℕ) (u v : Fin k → Fin 2),
      empDist (fun j : Fin k => sortHoldPoint j) (sortHoldWord u) (sortHoldWord v) ^ 2 =
        1 / 16 * (hammingDist u v : ℝ) / k) ∧
    (∀ (k : ℕ) (R : ℝ), 0 < k → 0 ≤ R →
      R / 8 ≤ empRademacher (fun j : Fin k => sortHoldPoint j)
          (hypothesisClass (linearReadouts (fun x : Icc (0 : ℝ) 1 => (x : ℝ)) R)
            (Set.range sortHoldGen) k) ∧
      ∀ (w : ℕ) (βW β Λ : ℝ≥0), 5 ≤ w → 7 ≤ βW → 2 ≤ β → 4 ≤ Λ →
        R / 8 ≤ empRademacher (fun j : Fin k => sortHoldPoint j)
          (hypothesisClass (linearReadouts (fun x : Icc (0 : ℝ) 1 => (x : ℝ)) R)
            (reluClass isProjectionOnto_clipUnit w βW β Λ) k)) :=
  ⟨⟨fun _ hx => ⟨rfl, sortHold₀_eq_piecewise hx.1⟩, fun _ hx => ⟨rfl, sortHold₁_eq_piecewise hx.1⟩⟩,
    ⟨lipschitzWith_sortHoldMap₀, lipschitzWith_sortHoldMap₁,
      fun _ _ _ _ hw hβW hβ hΛ => range_sortHoldGen_subset_reluClass_of_le hw hβW hβ hΛ⟩,
    fun _ u => ⟨sortHoldWord_mem_wordBall u, sortHoldWord_apply_point u⟩,
    fun _ u v => empDist_sortHoldWord_sq u v,
    fun _ _ hk hR => ⟨relu_sort_hold_rademacher hk hR,
      fun _ _ _ _ hw hβW hβ hΛ => relu_sort_hold_rademacher_reluClass hw hβW hβ hΛ hk hR⟩⟩

end SortHold

end LeanDeepgen
