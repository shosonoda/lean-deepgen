import Mathlib
import Architect
import LeanDeepgen.Setting.WordBall
import LeanDeepgen.Setting.Metrics
import LeanDeepgen.Setting.Covering
import LeanDeepgen.Growth.Defs
import LeanDeepgen.Growth.Lemmas
import LeanDeepgen.Growth.Exponential
import LeanDeepgen.Growth.Saturation
import LeanDeepgen.Growth.Envelope
import LeanDeepgen.Profiles.Profiles
import LeanDeepgen.Bounds.Variance
import LeanDeepgen.Examples.ODE

/-!
# Worked example: deep ReLU networks (paper App. `sec:app-relu`)

The state space is a bounded set `K` of a finite-dimensional real inner product space `E`
(the paper's `ℝ^m`, `m = finrank ℝ E`), used as the subtype `↥K`, with a `1`-Lipschitz
retraction `Π_K` (`IsProjectionOnto`, `LeanDeepgen.Examples.ODE`).  A hidden layer is a ReLU
block of width `w`,
`f_θ(x) = Π_K(V relu(W x + b) + c)`, `θ = (W, b, V, c)`, with `W : E →L[ℝ] ℝ^w`,
`V : ℝ^w →L[ℝ] E` (operator norms), `b ∈ ℝ^w`, `c ∈ E` (`reluBlock`), and the hidden-layer class
`F_Λ = {f_θ : ‖W‖, ‖V‖ ≤ β_W, ‖b‖, ‖c‖ ≤ β, lip(f_θ) ≤ Λ}` (`reluClass`) has
`p = 2mw + w + m` parameters.

* `lem:relu-layer-covering`: (a) the parameter-Lipschitz estimate
  `d_∞(f_θ, f_θ') ≤ β_W R_K ‖W − W'‖ + β_W ‖b − b'‖ + (β_W R_K + β) ‖V − V'‖ + ‖c − c'‖`
  (`uniformDist_reluBlock_le`) and (b) the covering bound
  `log N(F_Λ, d_∞, ε) ≤ p log(1 + C_F/ε)` with the explicit
  `C_F = 2 (2 β_W R_K + β_W + β + 1) max{β_W, β}` (`externalCoveringNumber_reluClass_le`,
  `lem_relu_layer_covering`).  The covering bound is obtained from the volumetric bound
  `M(B(x, ρ), δ) ≤ (1 + 2ρ/δ)^q` for packing numbers of balls in a `q`-dimensional normed space
  (`packingNumber_closedBall_le`, proved by comparing Haar measures of disjoint balls) applied to
  the sup-norm ball of radius `max{β_W, β}` in the parameter space, and the Lipschitz estimate
  (a); the operator norm is used directly, so the paper's factor `√max{m, w}` (operator vs
  Frobenius norm) does not appear.
* `prop:relu-regimes`: (i) `Λ < 1` (contractive): `cond:p1-ucont` with `A = K`, `L = 0` and the
  absorbing set `K`, plus the telescoping estimate `N(F^l, ε) ≤ N(F, (1 − Λ)ε)^l`, gives
  `N(B(k,F_Λ), d_∞, ε) ≤ N(K, ε/2) + m(ε) N(F_Λ, (1 − Λ)ε)^{m(ε)} < ∞` for every `k`
  (`prop_relu_regimes_i`); (ii) `Λ ≤ 1` on a compact `K` (non-expanding): `cond:p1` (2c)
  (`prop_relu_regimes_ii`); (iii) the envelope profile
  `V_k(S) ≤ D̄(√log(k+1) + √(kp log k) + k√(p log Λ₊) + √(kp)(√log(1 + 2C_F/D̄) + √π/2))`
  from `prop:envelope` in the form `envelope_profile_one_add` (a variant of
  `cor:envelope-profiles`(a) for the hypothesis `log N(F, ε) ≤ p log(1 + C/ε)`), which is
  `O(√(kp log k))` for `Λ ≤ 1` and `O(k√(p log Λ))` for `Λ > 1` (`prop_relu_regimes_iii`);
  and the lower bound for `Λ ≥ 20`: the two piecewise-linear expand-and-reset maps of the
  paper's computed illustration (`expandReset₀`, `expandReset₁`, breakpoints
  `(0,3/8), (η,0), (1/4−η,1), (1/4,3/8), (1,3/8)` and `(0,5/8), (3/4,5/8), (3/4+η,0), (1−η,1),
  (1,5/8)`, `η = 1/32`) are ReLU blocks of width `4` (hence of any width `w ≥ 4`;
  `reluBlock_unitParam`), are `20`-Lipschitz, and satisfy `cond:e2-pingpong` with the chambers
  `[0,1/4]`, `[3/4,1]`, the cores `[η,1/4−η]`, `[3/4+η,1−η]`, the anchors `3/8`, `5/8`, the
  marker `1/2` and separation `1/8`, so `N(B(k,F_Λ), d_∞, ε) ≥ 2^k` for `ε < 1/16`
  (`prop_relu_regimes_iii_lower`).

## Conventions

`R_K` is any bound `‖x‖ ≤ R_K` on `K` (the paper's `sup_{x ∈ K} ‖x‖`).  The parameter bounds
`β_W, β, Λ` are nonnegative reals (`ℝ≥0`), so `F_Λ` is never empty (`θ = 0` gives a constant
map).  Covering numbers are external in `d_∞`; the entropy integral `V_k(S)` is defined through
the internal covering number in `d_S` and compared through
`N(A, d_S, ε) ≤ N^ext(A, d_∞, ε/2)` (`LeanDeepgen.Bounds.Variance`), which is where the factor
`2` in `log(1 + 2C_F/D̄)` comes from.
-/

open scoped NNReal ENNReal UniformConvergence Real
open Metric MeasureTheory Set

open FoML.ToMathlib

namespace LeanDeepgen

/-! ### A volumetric bound for packing numbers of balls in finite dimension -/

section Volumetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

@[blueprint "lem:relu-packing-mono"
  (statement := /-- Packing numbers are monotone in the set: $A \subseteq B$ implies
    $M(A, \varepsilon) \le M(B, \varepsilon)$. -/)]
theorem packingNumber_mono_set' {X : Type*} [PseudoEMetricSpace X] {A B : Set X} (h : A ⊆ B)
    (ε : ℝ≥0) : packingNumber ε A ≤ packingNumber ε B := by
  simp only [packingNumber, iSup_le_iff]
  exact fun C hCA hC => hC.encard_le_packingNumber (hCA.trans h)

@[blueprint "lem:relu-volumetric-finset"
  (statement := /-- (Volumetric bound, finite sets.) Let $E$ be a real normed space of
    dimension $q$, $\rho \ge 0$, $\delta > 0$. If $s \subseteq \overline B(x, \rho)$ is a finite
    $\delta$-separated set (distinct points at distance $> \delta$) then
    $|s| \le (1 + 2\rho/\delta)^q$: the open balls $B(y, \delta/2)$, $y \in s$, are pairwise
    disjoint and contained in $B(x, \rho + \delta/2)$, and Haar measure scales like
    $r^q$. -/)]
theorem card_le_of_isSeparated_subset_closedBall (x : E) {ρ : ℝ} (hρ : 0 ≤ ρ) {δ : ℝ≥0}
    (hδ : 0 < δ) (s : Finset E) (hs : (s : Set E) ⊆ closedBall x ρ)
    (hsep : IsSeparated (δ : ℝ≥0∞) (s : Set E)) :
    (s.card : ℝ) ≤ (1 + 2 * ρ / δ) ^ Module.finrank ℝ E := by
  borelize E
  set μ : Measure E := Measure.addHaar
  set q := Module.finrank ℝ E
  have hδ' : (0 : ℝ) < δ := hδ
  have hr : (0 : ℝ) < δ / 2 := by positivity
  have hB0 : μ (ball 0 1) ≠ 0 := (Metric.measure_ball_pos μ 0 one_pos).ne'
  have hBtop : μ (ball 0 1) ≠ ⊤ := measure_ball_lt_top.ne
  /-- The balls $B(y, \delta/2)$, $y \in s$, are pairwise disjoint. -/
  have hdisj : (s : Set E).PairwiseDisjoint fun y => ball y ((δ : ℝ) / 2) := by
    intro y hy z hz hyz
    refine Set.disjoint_left.2 fun p hpy hpz => ?_
    have h1 : (δ : ℝ) < dist y z := by
      have h : (δ : ℝ≥0∞) < edist y z := hsep hy hz hyz
      rw [edist_dist, ← ENNReal.ofReal_coe_nnreal] at h
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg δ.coe_nonneg).1 h
    have h2 : dist y z ≤ dist y p + dist p z := dist_triangle _ _ _
    rw [mem_ball, dist_comm] at hpy
    rw [mem_ball] at hpz
    linarith
  /-- Each of them lies in $B(x, \rho + \delta/2)$. -/
  have hsub : (⋃ y ∈ s, ball y ((δ : ℝ) / 2)) ⊆ ball x (ρ + δ / 2) := by
    refine Set.iUnion₂_subset fun y hy => ball_subset_ball' ?_
    have := hs hy
    rw [mem_closedBall] at this
    linarith
  /-- Comparing measures: $|s| \cdot (\delta/2)^q \mu(B(0,1)) \le (\rho + \delta/2)^q
    \mu(B(0,1))$. -/
  have hmeas : (s.card : ℝ≥0∞) * (ENNReal.ofReal ((δ / 2 : ℝ) ^ q) * μ (ball 0 1)) ≤
      ENNReal.ofReal ((ρ + δ / 2) ^ q) * μ (ball 0 1) := by
    calc (s.card : ℝ≥0∞) * (ENNReal.ofReal ((δ / 2 : ℝ) ^ q) * μ (ball 0 1))
        = ∑ y ∈ s, μ (ball y ((δ : ℝ) / 2)) := by
          rw [Finset.sum_congr rfl fun y _ => Measure.addHaar_ball_of_pos μ y hr,
            Finset.sum_const, nsmul_eq_mul]
      _ = μ (⋃ y ∈ s, ball y ((δ : ℝ) / 2)) :=
          (measure_biUnion_finset hdisj fun y _ => measurableSet_ball).symm
      _ ≤ μ (ball x (ρ + δ / 2)) := measure_mono hsub
      _ = ENNReal.ofReal ((ρ + δ / 2) ^ q) * μ (ball 0 1) :=
          Measure.addHaar_ball_of_pos μ x (by positivity)
  rw [← mul_assoc, ENNReal.mul_le_mul_iff_left hB0 hBtop, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hmeas
  have hpow : (0 : ℝ) < (δ / 2 : ℝ) ^ q := by positivity
  rw [← le_div_iff₀ hpow] at hmeas
  refine hmeas.trans (le_of_eq ?_)
  rw [← div_pow]
  congr 1
  field_simp
  ring

@[blueprint "lem:relu-volumetric"
  (statement := /-- (Volumetric bound.) In a real normed space $E$ of dimension $q$, for
    $\rho \ge 0$ and $\delta > 0$, the packing number of the closed ball satisfies
    $M(\overline B(x, \rho), \delta) \le \lfloor (1 + 2\rho/\delta)^q \rfloor$; in particular a
    $\delta$-cover of the ball of size at most $(1 + 2\rho/\delta)^q$ exists. -/)]
theorem packingNumber_closedBall_le (x : E) {ρ : ℝ} (hρ : 0 ≤ ρ) {δ : ℝ≥0} (hδ : 0 < δ) :
    packingNumber δ (closedBall x ρ) ≤
      ((⌊(1 + 2 * ρ / δ) ^ Module.finrank ℝ E⌋₊ : ℕ) : ℕ∞) := by
  /-- Every separated subset is finite (its finite subsets have bounded cardinality) and its
    cardinality is bounded by `lem:relu-volumetric-finset`. -/
  simp only [packingNumber, iSup_le_iff]
  intro D hD hsep
  set b : ℝ := (1 + 2 * ρ / δ) ^ Module.finrank ℝ E
  have hfin : D.Finite := by
    by_contra hinf
    obtain ⟨t, htD, htc⟩ := Set.Infinite.exists_subset_card_eq hinf (⌊b⌋₊ + 1)
    have h := card_le_of_isSeparated_subset_closedBall x hρ hδ t (htD.trans hD) (hsep.mono htD)
    rw [htc] at h
    have := Nat.lt_floor_add_one b
    push_cast at h
    linarith
  rw [hfin.encard_eq_coe_toFinset_card]
  norm_cast
  refine Nat.le_floor ?_
  have h := card_le_of_isSeparated_subset_closedBall x hρ hδ hfin.toFinset
    (by rw [hfin.coe_toFinset]; exact hD) (by rw [hfin.coe_toFinset]; exact hsep)
  exact h

end Volumetric

/-! ### Covering numbers of the image of a set under a map that is Lipschitz on that set -/

section LipschitzOnImage

variable {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]

@[blueprint "lem:relu-lipschitz-on-image"
  (statement := /-- If $\varphi$ is $L$-Lipschitz on $A$ then
    $N^{\mathrm{ext}}(\varphi(A), L\varepsilon) \le N(A, \varepsilon)$ (internal covering number
    of $A$ on the right, since the centres must lie in $A$ where $\varphi$ is controlled). -/)]
theorem externalCoveringNumber_image_le_coveringNumber {L : ℝ≥0} {φ : X → Y} {A : Set X}
    (hφ : LipschitzOnWith L φ A) (ε : ℝ≥0) :
    externalCoveringNumber (L * ε) (φ '' A) ≤ Metric.coveringNumber ε A := by
  simp only [Metric.coveringNumber, le_iInf_iff]
  intro C hCA hC
  refine (IsCover.externalCoveringNumber_le_encard (C := φ '' C) ?_).trans
    (Set.encard_image_le _ _)
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨c, hc, hac⟩ := hC ha
  refine ⟨φ c, ⟨c, hc, rfl⟩, ?_⟩
  calc edist (φ a) (φ c) ≤ L * edist a c := hφ.edist_le_mul_of_le ha (hCA hc) le_rfl
    _ ≤ L * ε := mul_le_mul_right hac _

end LipschitzOnImage

/-! ### The envelope profile for parametric layers with `log N(F, ε) ≤ p log(1 + C/ε)` -/

section EnvelopeOneAdd

variable {X : Type*} [PseudoMetricSpace X] {F : Set (X → X)} {Λ : ℝ≥0}

@[blueprint "cor:envelope-profiles-a-one-add"
  (statement := /-- (\textbf{Parametric layers, `cor:envelope-profiles`(a) for the hypothesis
    $\log N(F, \varepsilon) \le p\log(1 + C/\varepsilon)$.}) Let every $f \in F$ be
    $\Lambda$-Lipschitz, let $\overline D > 0$, $C \ge 0$, $p \ge 0$, and suppose
    $N^{\mathrm{ext}}(F, d_\infty, \varepsilon) < \infty$ and
    $\log N^{\mathrm{ext}}(F, d_\infty, \varepsilon) \le p\log(1 + C/\varepsilon)$ for all
    $\varepsilon > 0$. If $D_k(S) \le \overline D$ then, for $k \ge 1$, with
    $\Lambda_+ := \max\{1,\Lambda\}$,
    $$\mathsf V_k(S) \le \overline D\Bigl(\sqrt{\log(k+1)} + \sqrt{kp\log k}
      + k\sqrt{p\log\Lambda_+} + \sqrt{kp}\bigl(\sqrt{\log(1 + 2C/\overline D)}
      + \tfrac{\sqrt\pi}{2}\bigr)\Bigr).$$
    (Same proof as `cor:envelope-profiles-a`, with $1 + 2CS_k/\varepsilon \le
    (1 + 2C/\overline D)\,S_k\,\overline D/\varepsilon$ for $\varepsilon \le \overline D$.) -/)]
theorem envelope_profile_one_add (hF : ∀ f ∈ F, LipschitzWith Λ f) {p C Dbar : ℝ}
    (hp : 0 ≤ p) (hC : 0 ≤ C) (hDbar : 0 < Dbar)
    (hfin : ∀ ε : ℝ≥0, 0 < ε → externalCoveringNumber (X := UnifMaps X) ε F ≠ ⊤)
    (hN : ∀ ε : ℝ≥0, 0 < ε →
      Real.log (externalCoveringNumber (X := UnifMaps X) ε F : ℝ≥0∞).toReal ≤
        p * Real.log (1 + C / ε))
    {n : ℕ} (S : Fin n → X) {k : ℕ} (hk : 1 ≤ k) (hD : empDiam S (wordBall F k) ≤ Dbar) :
    entropyIntegral (Y := EmpSpace S) (empDiam S (wordBall F k)) (wordBall F k) ≤
      Dbar * (√(Real.log (k + 1)) + √(k * p * Real.log k)
        + k * √(p * Real.log ((max 1 Λ : ℝ≥0) : ℝ))
        + √(k * p) * (√(Real.log (1 + 2 * C / Dbar)) + √π / 2)) := by
  /-- Pointwise, for $0 < \varepsilon \le \overline D$: $\log N(B(k,F), d_S, \varepsilon)
    \le \log N^{\mathrm{ext}}(B(k,F), d_\infty, \varepsilon/2) \le \log(k+1)
    + kp\log(1 + 2CS_k/\varepsilon)$, and $1 + 2CS_k/\varepsilon \le (1 + 2C/\overline D)
    S_k \overline D/\varepsilon$ with $\log S_k \le \log k + k\log\Lambda_+$; take square
    roots termwise and integrate, using $\int_0^{\overline D}\sqrt{\log(\overline D/\varepsilon)}
    \,d\varepsilon = \tfrac{\sqrt\pi}{2}\overline D$. -/
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := by linarith
  have hkp : (0 : ℝ) ≤ k * p := by positivity
  have hS1 : (1 : ℝ) ≤ geomSum Λ k := by exact_mod_cast one_le_geomSum (Λ := Λ) hk
  have hSpos : (0 : ℝ) < geomSum Λ k := by linarith
  have hΛ1 : (1 : ℝ) ≤ ((max 1 Λ : ℝ≥0) : ℝ) := by exact_mod_cast le_max_left 1 Λ
  have hlogS : Real.log (geomSum Λ k) ≤ Real.log k + k * Real.log ((max 1 Λ : ℝ≥0) : ℝ) := by
    have h := geomSum_le_mul_pow Λ k
    have h' : ((geomSum Λ k : ℝ≥0) : ℝ) ≤ k * ((max 1 Λ : ℝ≥0) : ℝ) ^ k := by
      exact_mod_cast h
    calc Real.log (geomSum Λ k) ≤ Real.log (k * ((max 1 Λ : ℝ≥0) : ℝ) ^ k) :=
          Real.log_le_log (by linarith) h'
      _ = Real.log k + k * Real.log ((max 1 Λ : ℝ≥0) : ℝ) := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have hC2 : 0 ≤ Real.log (1 + 2 * C / Dbar) := Real.log_nonneg (by
    have : 0 ≤ 2 * C / Dbar := by positivity
    linarith)
  set A : ℝ := √(Real.log (k + 1)) + √(k * p * Real.log k)
    + k * √(p * Real.log ((max 1 Λ : ℝ≥0) : ℝ)) + √(k * p) * √(Real.log (1 + 2 * C / Dbar))
    with hA
  have hgint : IntervalIntegrable (fun ε : ℝ => A + √(k * p) * √(Real.log (Dbar / ε)))
      volume 0 Dbar :=
    intervalIntegrable_const.add ((intervalIntegrable_sqrt_log_div hDbar).const_mul _)
  refine (entropyIntegral_le_integral_of_le (empDiam_nonneg S _) hD hgint
    fun ε hε => ?_).trans (le_of_eq ?_)
  · have hε0 : 0 < ε := hε.1
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
        Real.log (1 + 2 * C / Dbar) + Real.log k + k * Real.log ((max 1 Λ : ℝ≥0) : ℝ)
          + Real.log (Dbar / ε) := by
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
        _ ≤ _ := by linarith [hlogS]
    have h7 : metricEntropy (X := EmpSpace S) ε.toNNReal (wordBall F k) ≤
        Real.log (k + 1) + k * p * Real.log k + (k : ℝ) ^ 2 * (p * Real.log ((max 1 Λ : ℝ≥0) : ℝ))
          + k * p * Real.log (1 + 2 * C / Dbar) + k * p * Real.log (Dbar / ε) := by
      have h8 : Real.log (externalCoveringNumber (X := UnifMaps X)
          (ε.toNNReal / 2 / geomSum Λ k) F : ℝ≥0∞).toReal ≤
          p * (Real.log (1 + 2 * C / Dbar) + Real.log k
            + k * Real.log ((max 1 Λ : ℝ≥0) : ℝ) + Real.log (Dbar / ε)) :=
        h3.trans (mul_le_mul_of_nonneg_left h4 hp)
      have h9 := mul_le_mul_of_nonneg_left h8 hk0
      nlinarith
    calc √(metricEntropy (X := EmpSpace S) ε.toNNReal (wordBall F k))
        ≤ √(Real.log (k + 1) + k * p * Real.log k
            + (k : ℝ) ^ 2 * (p * Real.log ((max 1 Λ : ℝ≥0) : ℝ))
            + k * p * Real.log (1 + 2 * C / Dbar) + k * p * Real.log (Dbar / ε)) :=
          Real.sqrt_le_sqrt h7
      _ ≤ √(Real.log (k + 1) + k * p * Real.log k
            + (k : ℝ) ^ 2 * (p * Real.log ((max 1 Λ : ℝ≥0) : ℝ))
            + k * p * Real.log (1 + 2 * C / Dbar)) + √(k * p * Real.log (Dbar / ε)) :=
          sqrt_add_le _ _
      _ ≤ √(Real.log (k + 1) + k * p * Real.log k
            + (k : ℝ) ^ 2 * (p * Real.log ((max 1 Λ : ℝ≥0) : ℝ)))
            + √(k * p * Real.log (1 + 2 * C / Dbar)) + √(k * p * Real.log (Dbar / ε)) :=
          add_le_add_left (sqrt_add_le _ _) _
      _ ≤ √(Real.log (k + 1)) + √(k * p * Real.log k)
            + √((k : ℝ) ^ 2 * (p * Real.log ((max 1 Λ : ℝ≥0) : ℝ)))
            + √(k * p * Real.log (1 + 2 * C / Dbar)) + √(k * p * Real.log (Dbar / ε)) :=
          add_le_add_left (add_le_add_left (sqrt_add_add_le _ _ _) _) _
      _ = A + √(k * p) * √(Real.log (Dbar / ε)) := by
          rw [hA, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hk0, Real.sqrt_mul hkp,
            Real.sqrt_mul hkp, Real.sqrt_mul hkp]
  · rw [intervalIntegral.integral_add intervalIntegrable_const
        ((intervalIntegrable_sqrt_log_div hDbar).const_mul _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      integral_sqrt_log_div hDbar, hA]
    simp only [smul_eq_mul, sub_zero]
    ring

end EnvelopeOneAdd

/-! ### The ReLU nonlinearity -/

section ReLU

variable {w : ℕ}

@[blueprint "def:relu-vec"
  (statement := /-- The ReLU nonlinearity acting coordinatewise on $\mathbb R^w$ (the scalar
    `relu` of `LeanDeepgen.Examples.Implementation` in every coordinate):
    $\mathrm{relu}(z)_i = \max\{z_i, 0\}$. -/)]
noncomputable def reluVec (z : EuclideanSpace ℝ (Fin w)) : EuclideanSpace ℝ (Fin w) :=
  WithLp.toLp 2 fun i => max (z i) 0

@[simp, blueprint "lem:relu-apply"
  (statement := /-- $\mathrm{relu}(z)_i = \max\{z_i, 0\}$. -/)]
theorem reluVec_apply (z : EuclideanSpace ℝ (Fin w)) (i : Fin w) : reluVec z i = max (z i) 0 := rfl

@[blueprint "lem:relu-lipschitz"
  (statement := /-- $\mathrm{relu}$ is $1$-Lipschitz for the Euclidean norm, since
    $|\max\{a,0\} - \max\{b,0\}| \le |a - b|$ coordinatewise. -/)]
theorem lipschitzWith_reluVec : LipschitzWith 1 (reluVec (w := w)) := by
  refine LipschitzWith.of_dist_le_mul fun z z' => ?_
  rw [NNReal.coe_one, one_mul, EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  change dist (max (z i) 0) (max (z' i) 0) ^ 2 ≤ dist (z i) (z' i) ^ 2
  rw [Real.dist_eq, Real.dist_eq]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_max_sub_max_le_abs _ _ _) 2

@[simp, blueprint "lem:relu-zero"
  (statement := /-- $\mathrm{relu}(0) = 0$. -/)]
theorem reluVec_zero : reluVec (0 : EuclideanSpace ℝ (Fin w)) = 0 := by
  ext i
  simp [reluVec]

@[blueprint "lem:relu-norm-le"
  (statement := /-- $\|\mathrm{relu}(z)\| \le \|z\|$. -/)]
theorem norm_reluVec_le (z : EuclideanSpace ℝ (Fin w)) : ‖reluVec z‖ ≤ ‖z‖ := by
  have h := lipschitzWith_reluVec.dist_le_mul z 0
  rwa [reluVec_zero, dist_zero_right, dist_zero_right, NNReal.coe_one, one_mul] at h

end ReLU

/-! ### ReLU blocks and the hidden-layer class `F_Λ` -/

section Setting

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

@[blueprint "def:relu-param"
  (statement := /-- The parameter space of a ReLU block of width $w$ on $\mathbb R^m$ ($=E$):
    $\vartheta = (W, b, V, c) \in (\mathbb R^m \to \mathbb R^w) \times \mathbb R^w \times
    (\mathbb R^w \to \mathbb R^m) \times \mathbb R^m$, with the operator norm on the linear
    maps and the sup (product) norm on the tuple. -/)]
abbrev ReLUParam (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (w : ℕ) :
    Type _ :=
  (E →L[ℝ] EuclideanSpace ℝ (Fin w)) × EuclideanSpace ℝ (Fin w) ×
    (EuclideanSpace ℝ (Fin w) →L[ℝ] E) × E

variable {K : Set E} {proj : E → E} {w : ℕ}

@[blueprint "def:relu-block"
  (statement := /-- The ReLU block with parameters $\vartheta = (W,b,V,c)$ on the state space
    $K$: $f_\vartheta(x) = \Pi_K\bigl(V\,\mathrm{relu}(Wx + b) + c\bigr)$, a self-map of
    $K$. -/)]
noncomputable def reluBlock (hP : IsProjectionOnto K proj) (θ : ReLUParam E w) : K → K :=
  fun x => ⟨proj (θ.2.2.1 (reluVec (θ.1 x + θ.2.1)) + θ.2.2.2), hP.mem _⟩

@[blueprint "def:relu-param-set"
  (statement := /-- The admissible parameters: $\|W\|_{\rm op}, \|V\|_{\rm op} \le \beta_W$,
    $\|b\|, \|c\| \le \beta$ and $\mathrm{lip}(f_\vartheta) \le \Lambda$. -/)]
def reluParamSet (hP : IsProjectionOnto K proj) (w : ℕ) (βW β Λ : ℝ≥0) :
    Set (ReLUParam E w) :=
  {θ | ‖θ.1‖ ≤ βW ∧ ‖θ.2.1‖ ≤ β ∧ ‖θ.2.2.1‖ ≤ βW ∧ ‖θ.2.2.2‖ ≤ β ∧
    LipschitzWith Λ (reluBlock hP θ)}

@[blueprint "def:relu-class"
  (statement := /-- The hidden-layer class of ReLU blocks of width $w$,
    $F_\Lambda = \{f_\vartheta : \|W\|_{\rm op}, \|V\|_{\rm op} \le \beta_W,\ \|b\|, \|c\|
    \le \beta,\ \mathrm{lip}(f_\vartheta) \le \Lambda\}$. -/)]
noncomputable def reluClass (hP : IsProjectionOnto K proj) (w : ℕ) (βW β Λ : ℝ≥0) :
    Set (K → K) :=
  reluBlock hP '' reluParamSet hP w βW β Λ

@[blueprint "lem:relu-class-lipschitz"
  (statement := /-- Every $f \in F_\Lambda$ is $\Lambda$-Lipschitz. -/)]
theorem lipschitzWith_of_mem_reluClass (hP : IsProjectionOnto K proj) {βW β Λ : ℝ≥0}
    {f : K → K} (hf : f ∈ reluClass hP w βW β Λ) : LipschitzWith Λ f := by
  obtain ⟨θ, hθ, rfl⟩ := hf
  exact hθ.2.2.2.2

@[blueprint "lem:relu-class-nonempty"
  (statement := /-- $F_\Lambda \ne \emptyset$: the zero parameters give the constant map
    $x \mapsto \Pi_K(0)$. -/)]
theorem reluClass_nonempty (hP : IsProjectionOnto K proj) (w : ℕ) (βW β Λ : ℝ≥0) :
    (reluClass hP w βW β Λ).Nonempty := by
  refine ⟨reluBlock hP 0, 0, ⟨by simp, by simp, by simp, by simp, ?_⟩, rfl⟩
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have h0 : dist (reluBlock hP (0 : ReLUParam E w) x) (reluBlock hP (0 : ReLUParam E w) y) = 0 := by
    simp [reluBlock]
  rw [h0]
  positivity

@[blueprint "lem:relu-param-set-subset-ball"
  (statement := /-- The admissible parameters lie in the sup-norm ball of radius
    $\max\{\beta_W, \beta\}$. -/)]
theorem reluParamSet_subset_closedBall (hP : IsProjectionOnto K proj) (βW β Λ : ℝ≥0) :
    reluParamSet hP w βW β Λ ⊆ closedBall (0 : ReLUParam E w) (max βW β : ℝ≥0) := by
  rintro θ ⟨h1, h2, h3, h4, -⟩
  rw [mem_closedBall_zero_iff, Prod.norm_def, Prod.norm_def, Prod.norm_def]
  have hW : (βW : ℝ) ≤ max βW β := by exact_mod_cast le_max_left βW β
  have hb : (β : ℝ) ≤ max βW β := by exact_mod_cast le_max_right βW β
  exact max_le (h1.trans hW) (max_le (h2.trans hb) (max_le (h3.trans hW) (h4.trans hb)))

end Setting

/-! ### `lem:relu-layer-covering` -/

section LayerCovering

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {K : Set E} {proj : E → E} {w : ℕ}

omit [FiniteDimensional ℝ E] in
@[blueprint "lem:relu-layer-covering-a"
  (statement := /-- (Parameter-Lipschitz estimate.) Let $\|x\| \le R_K$ on $K$,
    $\|V\|_{\rm op} \le \beta_W$, $\|W'\|_{\rm op} \le \beta_W$ and $\|b'\| \le \beta$. Then
    $$d_\infty(f_\vartheta, f_{\vartheta'}) \le \beta_W R_K\|W - W'\|_{\rm op}
      + \beta_W\|b - b'\| + (\beta_W R_K + \beta)\|V - V'\|_{\rm op} + \|c - c'\| .$$
    (Only these three parameter bounds are used, as in the paper's proof.) -/)]
theorem uniformDist_reluBlock_le (hP : IsProjectionOnto K proj) {R : ℝ}
    (hR : ∀ x ∈ K, ‖x‖ ≤ R) {βW β : ℝ≥0} {θ θ' : ReLUParam E w}
    (hV : ‖θ.2.2.1‖ ≤ βW) (hW' : ‖θ'.1‖ ≤ βW) (hb' : ‖θ'.2.1‖ ≤ β) :
    uniformDist (reluBlock hP θ) (reluBlock hP θ') ≤
      ENNReal.ofReal (βW * R * ‖θ.1 - θ'.1‖ + βW * ‖θ.2.1 - θ'.2.1‖
        + (βW * R + β) * ‖θ.2.2.1 - θ'.2.2.1‖ + ‖θ.2.2.2 - θ'.2.2.2‖) := by
  /-- For $x \in K$ write $z = \mathrm{relu}(Wx+b)$, $z' = \mathrm{relu}(W'x+b')$; then
    $\|z - z'\| \le R_K\|W - W'\| + \|b - b'\|$, $\|z'\| \le \beta_W R_K + \beta$ and
    $\|Vz + c - V'z' - c'\| \le \|V\|\|z - z'\| + \|V - V'\|\|z'\| + \|c - c'\|$; apply the
    $1$-Lipschitz retraction. -/
  obtain ⟨W, b, V, c⟩ := θ
  obtain ⟨W', b', V', c'⟩ := θ'
  simp only at hV hW' hb' ⊢
  refine iSup_le fun x => ?_
  rw [edist_dist]
  refine ENNReal.ofReal_le_ofReal ?_
  have hx : ‖(x : E)‖ ≤ R := hR x x.2
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hx
  set z := reluVec (W x + b)
  set z' := reluVec (W' x + b')
  have hz : ‖z - z'‖ ≤ R * ‖W - W'‖ + ‖b - b'‖ := by
    have h1 := lipschitzWith_reluVec.dist_le_mul (W x + b) (W' x + b')
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm] at h1
    refine h1.trans ?_
    have e : W x + b - (W' x + b') = (W - W') x + (b - b') := by
      simp only [sub_apply]; abel
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    calc ‖(W - W') x‖ ≤ ‖W - W'‖ * ‖(x : E)‖ := (W - W').le_opNorm x
      _ ≤ ‖W - W'‖ * R := mul_le_mul_of_nonneg_left hx (norm_nonneg _)
      _ = R * ‖W - W'‖ := mul_comm _ _
  have hz' : ‖z'‖ ≤ βW * R + β := by
    refine (norm_reluVec_le _).trans ((norm_add_le _ _).trans (add_le_add ?_ hb'))
    calc ‖W' x‖ ≤ ‖W'‖ * ‖(x : E)‖ := W'.le_opNorm x
      _ ≤ βW * R := mul_le_mul hW' hx (norm_nonneg _) βW.coe_nonneg
  have hdist : dist (reluBlock hP (W, b, V, c) x) (reluBlock hP (W', b', V', c') x) ≤
      ‖V z + c - (V' z' + c')‖ :=
    calc dist (reluBlock hP (W, b, V, c) x) (reluBlock hP (W', b', V', c') x)
        = dist (proj (V z + c)) (proj (V' z' + c')) := rfl
      _ ≤ ((1 : ℝ≥0) : ℝ) * dist (V z + c) (V' z' + c') := hP.lipschitz.dist_le_mul _ _
      _ = ‖V z + c - (V' z' + c')‖ := by rw [NNReal.coe_one, one_mul, dist_eq_norm]
  refine hdist.trans ?_
  have e : V z + c - (V' z' + c') = V (z - z') + (V - V') z' + (c - c') := by
    simp only [sub_apply, map_sub]; abel
  rw [e]
  refine (norm_add₃_le).trans ?_
  have h1 : ‖V (z - z')‖ ≤ βW * (R * ‖W - W'‖ + ‖b - b'‖) :=
    (V.le_opNorm _).trans (mul_le_mul hV hz (norm_nonneg _) βW.coe_nonneg)
  have h2 : ‖(V - V') z'‖ ≤ ‖V - V'‖ * (βW * R + β) :=
    ((V - V').le_opNorm _).trans (mul_le_mul_of_nonneg_left hz' (norm_nonneg _))
  calc ‖V (z - z')‖ + ‖(V - V') z'‖ + ‖c - c'‖
      ≤ βW * (R * ‖W - W'‖ + ‖b - b'‖) + ‖V - V'‖ * (βW * R + β) + ‖c - c'‖ :=
        add_le_add (add_le_add h1 h2) le_rfl
    _ = _ := by ring

@[blueprint "def:relu-lip-const"
  (statement := /-- The parameter-Lipschitz constant of $\vartheta \mapsto f_\vartheta$ on
    $F_\Lambda$ for the sup norm on parameters:
    $L_F := 2\beta_W R_K + \beta_W + \beta + 1$ (the sum of the four coefficients of
    `lem:relu-layer-covering-a`). -/)]
noncomputable def reluLipConst (R : ℝ) (βW β : ℝ≥0) : ℝ≥0 :=
  Real.toNNReal (2 * βW * R + βW + β + 1)

@[blueprint "def:relu-cover-const"
  (statement := /-- The covering constant of one ReLU block:
    $C_F := 2 L_F \max\{\beta_W, \beta\} = 2(2\beta_W R_K + \beta_W + \beta + 1)
    \max\{\beta_W,\beta\}$. (The paper's $C_F = 8\sqrt{\max\{m,w\}}\max\{\beta_W,1\}
    \max\{\beta_W R_K + \beta, \beta_W, 1\}$ has the same shape; the factor
    $\sqrt{\max\{m,w\}}$ comes from bounding the operator norm by the Frobenius norm, which the
    volumetric argument in the operator norm avoids.) -/)]
noncomputable def reluCoverConst (R : ℝ) (βW β : ℝ≥0) : ℝ :=
  2 * (reluLipConst R βW β : ℝ) * (max βW β : ℝ≥0)

@[blueprint "lem:relu-lip-const-pos"
  (statement := /-- $L_F \ge 1$ when $R_K \ge 0$. -/)]
theorem one_le_reluLipConst {R : ℝ} (hR0 : 0 ≤ R) (βW β : ℝ≥0) : 1 ≤ reluLipConst R βW β := by
  rw [reluLipConst, ← Real.toNNReal_one]
  exact Real.toNNReal_le_toNNReal (le_add_of_nonneg_left (by positivity))

omit [FiniteDimensional ℝ E] in
@[blueprint "lem:relu-param-lipschitz-on"
  (statement := /-- $\vartheta \mapsto f_\vartheta$ is $L_F$-Lipschitz on the admissible
    parameter set, from $(\mathrm{parameters}, \|\cdot\|_{\sup})$ to
    $(\mathcal X^{\mathcal X}, d_\infty)$: each of the four differences in
    `lem:relu-layer-covering-a` is at most $\|\vartheta - \vartheta'\|_{\sup}$. -/)]
theorem lipschitzOnWith_reluBlock (hP : IsProjectionOnto K proj) {R : ℝ}
    (hR : ∀ x ∈ K, ‖x‖ ≤ R) (hR0 : 0 ≤ R) (βW β Λ : ℝ≥0) :
    LipschitzOnWith (reluLipConst R βW β) (fun θ : ReLUParam E w => toUnifMaps (reluBlock hP θ))
      (reluParamSet hP w βW β Λ) := by
  intro θ hθ θ' hθ'
  obtain ⟨-, -, hV, -, -⟩ := hθ
  obtain ⟨hW', hb', -, -, -⟩ := hθ'
  have hL : ((reluLipConst R βW β : ℝ≥0) : ℝ) = 2 * βW * R + βW + β + 1 := by
    rw [reluLipConst, Real.coe_toNNReal _ (by positivity)]
  calc edist (toUnifMaps (reluBlock hP θ)) (toUnifMaps (reluBlock hP θ'))
      = uniformDist (reluBlock hP θ) (reluBlock hP θ') := rfl
    _ ≤ ENNReal.ofReal (βW * R * ‖θ.1 - θ'.1‖ + βW * ‖θ.2.1 - θ'.2.1‖
          + (βW * R + β) * ‖θ.2.2.1 - θ'.2.2.1‖ + ‖θ.2.2.2 - θ'.2.2.2‖) :=
        uniformDist_reluBlock_le hP hR hV hW' hb'
    _ ≤ ENNReal.ofReal ((reluLipConst R βW β : ℝ) * ‖θ - θ'‖) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : ‖θ.1 - θ'.1‖ ≤ ‖θ - θ'‖ := by
          rw [← Prod.fst_sub]; exact norm_fst_le _
        have h2 : ‖θ.2.1 - θ'.2.1‖ ≤ ‖θ - θ'‖ := by
          rw [← Prod.fst_sub, ← Prod.snd_sub]; exact (norm_fst_le _).trans (norm_snd_le _)
        have h3 : ‖θ.2.2.1 - θ'.2.2.1‖ ≤ ‖θ - θ'‖ := by
          rw [← Prod.fst_sub, ← Prod.snd_sub, ← Prod.snd_sub]
          exact (norm_fst_le _).trans ((norm_snd_le _).trans (norm_snd_le _))
        have h4 : ‖θ.2.2.2 - θ'.2.2.2‖ ≤ ‖θ - θ'‖ := by
          rw [← Prod.snd_sub, ← Prod.snd_sub, ← Prod.snd_sub]
          exact (norm_snd_le _).trans ((norm_snd_le _).trans (norm_snd_le _))
        rw [hL]
        have hβW : (0 : ℝ) ≤ βW := βW.coe_nonneg
        have hβ : (0 : ℝ) ≤ β := β.coe_nonneg
        nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ βW * R),
          mul_le_mul_of_nonneg_left h2 hβW,
          mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ βW * R + β)]
    _ = (reluLipConst R βW β : ℝ≥0∞) * edist θ θ' := by
        rw [edist_dist, dist_eq_norm, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_coe_nnreal]

@[blueprint "lem:relu-finrank-param"
  (statement := /-- The parameter space has dimension $p = 2mw + w + m$,
    $m = \dim E$. -/)]
theorem finrank_reluParam (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (w : ℕ) :
    Module.finrank ℝ (ReLUParam E w) = 2 * Module.finrank ℝ E * w + w + Module.finrank ℝ E := by
  have h1 : Module.finrank ℝ (E →L[ℝ] EuclideanSpace ℝ (Fin w)) = Module.finrank ℝ E * w := by
    rw [← LinearEquiv.finrank_eq (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E)
      (F' := EuclideanSpace ℝ (Fin w))), Module.finrank_linearMap, finrank_euclideanSpace_fin]
  have h2 : Module.finrank ℝ (EuclideanSpace ℝ (Fin w) →L[ℝ] E) = w * Module.finrank ℝ E := by
    rw [← LinearEquiv.finrank_eq (LinearMap.toContinuousLinearMap (𝕜 := ℝ)
      (E := EuclideanSpace ℝ (Fin w)) (F' := E)), Module.finrank_linearMap,
      finrank_euclideanSpace_fin]
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_prod, h1, h2,
    finrank_euclideanSpace_fin]
  ring

@[blueprint "lem:relu-layer-covering-b"
  (statement := /-- (Covering bound, cardinality form.) Let $\|x\| \le R_K$ on $K$ with
    $R_K \ge 0$ and $p = 2mw + w + m$. For every $\varepsilon > 0$,
    $N^{\mathrm{ext}}(F_\Lambda, d_\infty, \varepsilon) \le (1 + C_F/\varepsilon)^p$ with
    $C_F = 2(2\beta_W R_K + \beta_W + \beta + 1)\max\{\beta_W, \beta\}$:
    $N^{\mathrm{ext}}(F_\Lambda, \varepsilon) \le N(P, \varepsilon/L_F) \le M(P, \varepsilon/L_F)
    \le M(\overline B(0, \max\{\beta_W,\beta\}), \varepsilon/L_F)
    \le (1 + 2L_F\max\{\beta_W,\beta\}/\varepsilon)^p$ by `lem:relu-lipschitz-on-image`,
    `lem:packing-covering` and `lem:relu-volumetric`. -/)]
theorem externalCoveringNumber_reluClass_le (hP : IsProjectionOnto K proj) {R : ℝ}
    (hR : ∀ x ∈ K, ‖x‖ ≤ R) (hR0 : 0 ≤ R) (βW β Λ : ℝ≥0) {ε : ℝ≥0} (hε : 0 < ε) :
    (externalCoveringNumber (X := UnifMaps K) ε (reluClass hP w βW β Λ) : ℝ≥0∞) ≤
      ENNReal.ofReal ((1 + reluCoverConst R βW β / ε) ^
        (2 * Module.finrank ℝ E * w + w + Module.finrank ℝ E)) := by
  set L := reluLipConst R βW β with hL
  have hL1 : 1 ≤ L := one_le_reluLipConst hR0 βW β
  have hL0 : L ≠ 0 := by
    intro h; rw [h] at hL1; exact absurd hL1 (by norm_num)
  set ρ : ℝ≥0 := max βW β
  set q := 2 * Module.finrank ℝ E * w + w + Module.finrank ℝ E
  have hchain : externalCoveringNumber (X := UnifMaps K) ε (reluClass hP w βW β Λ) ≤
      ((⌊(1 + 2 * (ρ : ℝ) / ((ε / L : ℝ≥0) : ℝ)) ^ q⌋₊ : ℕ) : ℕ∞) := by
    calc externalCoveringNumber (X := UnifMaps K) ε (reluClass hP w βW β Λ)
        = externalCoveringNumber (X := UnifMaps K) (L * (ε / L))
            ((fun θ : ReLUParam E w => toUnifMaps (reluBlock hP θ)) ''
              reluParamSet hP w βW β Λ) := by
          rw [mul_div_cancel₀ _ hL0]; rfl
      _ ≤ Metric.coveringNumber (ε / L) (reluParamSet hP w βW β Λ) :=
          externalCoveringNumber_image_le_coveringNumber
            (lipschitzOnWith_reluBlock hP hR hR0 βW β Λ) (ε / L)
      _ ≤ packingNumber (ε / L) (reluParamSet hP w βW β Λ) := coveringNumber_le_packingNumber _ _
      _ ≤ packingNumber (ε / L) (closedBall (0 : ReLUParam E w) ρ) :=
          packingNumber_mono_set' (reluParamSet_subset_closedBall hP βW β Λ) _
      _ ≤ _ := by
          have h := packingNumber_closedBall_le (0 : ReLUParam E w) (ρ := (ρ : ℝ)) ρ.coe_nonneg
            (δ := ε / L) (div_pos hε (lt_of_lt_of_le one_pos hL1))
          rwa [finrank_reluParam] at h
  have hval : 1 + 2 * (ρ : ℝ) / ((ε / L : ℝ≥0) : ℝ) = 1 + reluCoverConst R βW β / ε := by
    rw [reluCoverConst, NNReal.coe_div]
    have hε' : (0 : ℝ) < ε := hε
    have hL' : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL1
    field_simp
    ring
  rw [hval] at hchain
  have hC0 : 0 ≤ reluCoverConst R βW β := by
    rw [reluCoverConst]; positivity
  calc (externalCoveringNumber (X := UnifMaps K) ε (reluClass hP w βW β Λ) : ℝ≥0∞)
      ≤ ((⌊(1 + reluCoverConst R βW β / ε) ^ q⌋₊ : ℕ) : ℝ≥0∞) := by
        exact_mod_cast hchain
    _ ≤ ENNReal.ofReal ((1 + reluCoverConst R βW β / ε) ^ q) := by
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal (Nat.floor_le (by positivity))

@[blueprint "lem:relu-layer-covering-log"
  (statement := /-- (Covering bound, entropy form.) Under the hypotheses of
    `lem:relu-layer-covering-b`, for every $\varepsilon > 0$,
    $N^{\mathrm{ext}}(F_\Lambda, d_\infty, \varepsilon) < \infty$ and
    $\log N^{\mathrm{ext}}(F_\Lambda, d_\infty, \varepsilon) \le p\log(1 + C_F/\varepsilon)$. -/)]
theorem reluClass_covering_log (hP : IsProjectionOnto K proj) {R : ℝ}
    (hR : ∀ x ∈ K, ‖x‖ ≤ R) (hR0 : 0 ≤ R) (βW β Λ : ℝ≥0) {ε : ℝ≥0} (hε : 0 < ε) :
    externalCoveringNumber (X := UnifMaps K) ε (reluClass hP w βW β Λ) ≠ ⊤ ∧
      Real.log (externalCoveringNumber (X := UnifMaps K) ε (reluClass hP w βW β Λ) : ℝ≥0∞).toReal ≤
        (2 * Module.finrank ℝ E * w + w + Module.finrank ℝ E : ℕ) *
          Real.log (1 + reluCoverConst R βW β / ε) := by
  have h := externalCoveringNumber_reluClass_le hP hR hR0 βW β Λ (w := w) hε
  set N := externalCoveringNumber (X := UnifMaps K) ε (reluClass hP w βW β Λ)
  set q := 2 * Module.finrank ℝ E * w + w + Module.finrank ℝ E
  have hC0 : 0 ≤ reluCoverConst R βW β := by
    rw [reluCoverConst]; positivity
  have hb : 0 ≤ 1 + reluCoverConst R βW β / ε := by positivity
  have hN : N ≠ ⊤ := by
    intro htop
    rw [htop, ENat.toENNReal_top] at h
    exact absurd h (by simp)
  refine ⟨hN, ?_⟩
  have hle : (N : ℝ≥0∞).toReal ≤ (1 + reluCoverConst R βW β / ε) ^ q := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  have h1 : (1 : ℝ≥0∞) ≤ (N : ℝ≥0∞) := by
    have : 1 ≤ N := Order.one_le_iff_pos.2
      (externalCoveringNumber_pos_iff.2 (reluClass_nonempty hP w βW β Λ))
    exact_mod_cast this
  have hpos : (0 : ℝ) < (N : ℝ≥0∞).toReal := by
    have := ENNReal.toReal_mono (ENat.toENNReal_ne_top.2 hN) h1
    rw [ENNReal.toReal_one] at this
    linarith
  calc Real.log (N : ℝ≥0∞).toReal ≤ Real.log ((1 + reluCoverConst R βW β / ε) ^ q) :=
        Real.log_le_log hpos hle
    _ = (q : ℕ) * Real.log (1 + reluCoverConst R βW β / ε) := by rw [Real.log_pow]

@[blueprint "lem:relu-layer-covering"
  (statement := /-- \textbf{(Covering numbers of one ReLU block.)} Let $K \subseteq \mathbb R^m$
    with $\|x\| \le R_K$ on $K$ ($R_K \ge 0$), let $\Pi_K$ be a $1$-Lipschitz retraction onto
    $K$, and let $F_\Lambda$ be the class of ReLU blocks of width $w$ with $p = 2mw + w + m$
    parameters. (a) For admissible $\vartheta, \vartheta'$,
    $$d_\infty(f_\vartheta, f_{\vartheta'}) \le \beta_W R_K\|W - W'\|_{\rm op}
      + \beta_W\|b - b'\| + (\beta_W R_K + \beta)\|V - V'\|_{\rm op} + \|c - c'\| ;$$
    (b) for every $\varepsilon > 0$, $N^{\mathrm{ext}}(F_\Lambda, d_\infty, \varepsilon) < \infty$
    and $\log N^{\mathrm{ext}}(F_\Lambda, d_\infty, \varepsilon) \le p\log(1 + C_F/\varepsilon)$
    with $C_F = 2(2\beta_W R_K + \beta_W + \beta + 1)\max\{\beta_W, \beta\}$
    (`def:relu-cover-const`; the paper's constant has the same shape, see there). -/)]
theorem lem_relu_layer_covering (hP : IsProjectionOnto K proj) {R : ℝ}
    (hR : ∀ x ∈ K, ‖x‖ ≤ R) (hR0 : 0 ≤ R) (βW β Λ : ℝ≥0) :
    (∀ θ ∈ reluParamSet hP w βW β Λ, ∀ θ' ∈ reluParamSet hP w βW β Λ,
      uniformDist (reluBlock hP θ) (reluBlock hP θ') ≤
        ENNReal.ofReal (βW * R * ‖θ.1 - θ'.1‖ + βW * ‖θ.2.1 - θ'.2.1‖
          + (βW * R + β) * ‖θ.2.2.1 - θ'.2.2.1‖ + ‖θ.2.2.2 - θ'.2.2.2‖)) ∧
    (∀ ε : ℝ≥0, 0 < ε →
      externalCoveringNumber (X := UnifMaps K) ε (reluClass hP w βW β Λ) ≠ ⊤ ∧
      Real.log (externalCoveringNumber (X := UnifMaps K) ε
          (reluClass hP w βW β Λ) : ℝ≥0∞).toReal ≤
        (2 * Module.finrank ℝ E * w + w + Module.finrank ℝ E : ℕ) *
          Real.log (1 + reluCoverConst R βW β / ε)) :=
  ⟨fun _θ hθ _θ' hθ' => uniformDist_reluBlock_le hP hR hθ.2.2.1 hθ'.1 hθ'.2.1,
    fun _ε hε => reluClass_covering_log hP hR hR0 βW β Λ hε⟩

end LayerCovering

/-! ### `prop:relu-regimes`: the three growth regimes from the Lipschitz constant -/

section Regimes

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {K : Set E} {proj : E → E} {w : ℕ}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
@[blueprint "lem:relu-bounded-univ"
  (statement := /-- If $K$ is bounded then so is the state space $K$ (as a metric space in its
    own right). -/)]
theorem isBounded_univ_of_isBounded (hK : Bornology.IsBounded K) :
    Bornology.IsBounded (Set.univ : Set K) := by
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.1 hK
  exact Metric.isBounded_iff.2 ⟨C, fun x _ y _ => hC x.2 y.2⟩

@[blueprint "lem:relu-covering-univ-ne-top"
  (statement := /-- A bounded set $K$ of a finite-dimensional space has finite covering numbers:
    $N^{\mathrm{ext}}(K, \varepsilon) < \infty$ for $\varepsilon > 0$ (external covering number
    of the state space $K$ by points of $K$; $K$ is totally bounded since its closure is
    compact). -/)]
theorem externalCoveringNumber_univ_ne_top (hK : Bornology.IsBounded K) {ε : ℝ≥0} (hε : 0 < ε) :
    externalCoveringNumber ε (Set.univ : Set K) ≠ ⊤ := by
  have htb : TotallyBounded K :=
    (isCompact_of_isClosed_isBounded isClosed_closure hK.closure).totallyBounded.subset
      subset_closure
  have h2 : Metric.coveringNumber ε (Set.univ : Set K) = Metric.coveringNumber ε K := by
    rw [← isometry_subtype_coe.coveringNumber_image (A := (Set.univ : Set K)), Set.image_univ,
      Subtype.range_coe]
  refine ne_top_of_le_ne_top ?_ (externalCoveringNumber_le_coveringNumber ε _)
  rw [h2]
  exact coveringNumber_ne_top_of_totallyBounded htb hε

@[blueprint "lem:relu-words-covering-contractive"
  (statement := /-- (Telescoping estimate for contractive layers.) If every $f \in F$ is
    $\Lambda$-Lipschitz with $\Lambda < 1$ then
    $N^{\mathrm{ext}}(F^l, d_\infty, \varepsilon) \le N^{\mathrm{ext}}(F, d_\infty,
    (1 - \Lambda)\varepsilon)^l$, since $S_l(\Lambda) = \sum_{i<l}\Lambda^i \le 1/(1-\Lambda)$
    in `lem:envelope-words`. -/)]
theorem externalCoveringNumber_words_le_of_lt_one {X : Type*} [PseudoEMetricSpace X]
    {F : Set (X → X)} {Λ : ℝ≥0} (hF : ∀ f ∈ F, LipschitzWith Λ f) (hΛ : Λ < 1) (ε : ℝ≥0)
    (l : ℕ) :
    externalCoveringNumber (X := UnifMaps X) ε (words F l) ≤
      externalCoveringNumber (X := UnifMaps X) ((1 - Λ) * ε) F ^ l := by
  refine (externalCoveringNumber_words_le hF ε l).trans ?_
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · simp
  · refine pow_le_pow_left₀ zero_le (externalCoveringNumber_anti ?_) l
    have hS : 0 < geomSum Λ l := geomSum_pos hl
    rw [le_div_iff₀ hS]
    have key : (1 - Λ) * geomSum Λ l ≤ 1 := by
      rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_sub hΛ.le, coe_geomSum, NNReal.coe_one,
        mul_comm, geom_sum_mul_neg]
      have : (0 : ℝ) ≤ (Λ : ℝ) ^ l := by positivity
      linarith
    calc (1 - Λ) * ε * geomSum Λ l = (1 - Λ) * geomSum Λ l * ε := by ring
      _ ≤ 1 * ε := mul_le_mul_of_nonneg_right key zero_le
      _ = ε := one_mul ε

@[blueprint "lem:relu-sum-pow-le"
  (statement := /-- For $N \ge 1$ in $\mathbb N \cup \{\infty\}$, $\sum_{l<m} N^l \le m N^m$. -/)]
theorem sum_pow_le_mul_pow_enat {N : ℕ∞} (hN : 1 ≤ N) (m : ℕ) :
    ∑ l ∈ Finset.range m, N ^ l ≤ m * N ^ m := by
  calc ∑ l ∈ Finset.range m, N ^ l ≤ ∑ _l ∈ Finset.range m, N ^ m :=
        Finset.sum_le_sum fun l hl => pow_le_pow_right₀ hN (Finset.mem_range.1 hl).le
    _ = m * N ^ m := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

omit [FiniteDimensional ℝ E] in
@[blueprint "lem:relu-class-one-le-covering"
  (statement := /-- $N^{\mathrm{ext}}(F_\Lambda, d_\infty, \varepsilon) \ge 1$ (the class is
    nonempty). -/)]
theorem one_le_externalCoveringNumber_reluClass (hP : IsProjectionOnto K proj) (βW β Λ : ℝ≥0)
    (ε : ℝ≥0) : 1 ≤ externalCoveringNumber (X := UnifMaps K) ε (reluClass hP w βW β Λ) :=
  Order.one_le_iff_pos.2 (externalCoveringNumber_pos_iff.2 (reluClass_nonempty hP w βW β Λ))

@[blueprint "prop:relu-regimes-i"
  (statement := /-- \textbf{(`prop:relu-regimes`(i): contractive layers, $\Lambda < 1$.)} Let
    $K \ne \emptyset$ be bounded with $\|x\| \le R_K$ on $K$, and $0 < \Lambda < 1$. Then
    `cond:p1-ucont` applies with the invariant set $K$ itself ($L = 0$, absorbing set $K$),
    and with $m(\varepsilon) = \lceil\log(2D_K/\varepsilon)/\log(1/\Lambda)\rceil$
    ($D_K = \mathrm{diam}\,K$), for every $\varepsilon > 0$ and \emph{every} $k$,
    $$N^{\mathrm{ext}}(B(k,F_\Lambda), d_\infty, \varepsilon)
      \le N^{\mathrm{ext}}(K, \varepsilon/2) + m(\varepsilon)\,
      N^{\mathrm{ext}}(F_\Lambda, d_\infty, (1-\Lambda)\varepsilon)^{m(\varepsilon)} < \infty ,$$
    which does not depend on $k$; in particular
    $\sup_k N^{\mathrm{ext}}(B(k,F_\Lambda), d_\infty, \varepsilon) < \infty$.
    (The paper's $k \ge m(\varepsilon)$ is not needed, cf. `cond:p1-ucont`; the right-hand side
    is finite by `lem:relu-layer-covering` and the total boundedness of $K$.) -/)]
theorem prop_relu_regimes_i (hP : IsProjectionOnto K proj) (hK : Bornology.IsBounded K)
    (hKne : K.Nonempty) {R : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R) (hR0 : 0 ≤ R) (βW β : ℝ≥0)
    {Λ : ℝ≥0} (hΛ0 : 0 < Λ) (hΛ : Λ < 1) (ε : ℝ≥0) (hε : 0 < ε) (k : ℕ) :
    externalCoveringNumber (X := UnifMaps K) ε (wordBall (reluClass hP w βW β Λ) k) ≤
        externalCoveringNumber (ε / 2) (Set.univ : Set K) +
          memoryLength Λ 0 (Set.univ : Set K) ε *
            externalCoveringNumber (X := UnifMaps K) ((1 - Λ) * ε) (reluClass hP w βW β Λ) ^
              memoryLength Λ 0 (Set.univ : Set K) ε ∧
      externalCoveringNumber (ε / 2) (Set.univ : Set K) +
          memoryLength Λ 0 (Set.univ : Set K) ε *
            externalCoveringNumber (X := UnifMaps K) ((1 - Λ) * ε) (reluClass hP w βW β Λ) ^
              memoryLength Λ 0 (Set.univ : Set K) ε ≠ ⊤ := by
  /-- `cond:p1-ucont` with $c = \Lambda$, $A = K$, $L = 0$ and the bounded absorbing set $K$;
    the short words are bounded by `lem:relu-words-covering-contractive` and
    `lem:relu-sum-pow-le`; finiteness from `lem:relu-covering-univ-ne-top` and
    `lem:relu-layer-covering-log`. -/
  haveI : Nonempty K := hKne.to_subtype
  set F := reluClass hP w βW β Λ
  set m := memoryLength Λ 0 (Set.univ : Set K) ε
  set N := externalCoveringNumber (X := UnifMaps K) ((1 - Λ) * ε) F
  have hF : ∀ f ∈ F, LipschitzWith Λ f := fun _ hf => lipschitzWith_of_mem_reluClass hP hf
  have h1 := cond_p1_ucont hF hΛ0 hΛ Set.univ_nonempty (fun _ _ => Set.subset_univ _) (L := 0)
    (isBounded_univ_of_isBounded hK) (fun _ _ => Set.subset_univ _) ε hε k
  have h2 : ∑ l ∈ Finset.range m, externalCoveringNumber (X := UnifMaps K) ε (words F l) ≤
      m * N ^ m :=
    (Finset.sum_le_sum fun l _ => externalCoveringNumber_words_le_of_lt_one hF hΛ ε l).trans
      (sum_pow_le_mul_pow_enat (one_le_externalCoveringNumber_reluClass hP βW β Λ _) m)
  refine ⟨h1.trans (add_le_add le_rfl h2), ?_⟩
  have hε' : 0 < (1 - Λ) * ε := mul_pos (tsub_pos_of_lt hΛ) hε
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1
    (externalCoveringNumber_univ_ne_top hK (by positivity : 0 < ε / 2))
  have hN : N ≠ ⊤ := (reluClass_covering_log hP hR hR0 βW β Λ (w := w) hε').1
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.1 hN
  rw [← ha, ← hb]
  exact_mod_cast ENat.coe_ne_top (a + m * b ^ m)

@[blueprint "def:relu-saturation-bound"
  (statement := /-- The $k$-independent majorant of case (i) at the scale of the empirical
    metric: $N_\infty(\varepsilon) := N^{\mathrm{ext}}(K, \varepsilon/4) + m(\varepsilon/2)\,
    N^{\mathrm{ext}}(F_\Lambda, d_\infty, (1-\Lambda)\varepsilon/2)^{m(\varepsilon/2)}$
    (the factor $2$ from $N(A, d_S, \varepsilon) \le N^{\mathrm{ext}}(A, d_\infty,
    \varepsilon/2)$). -/)]
noncomputable def reluSatBound (hP : IsProjectionOnto K proj) (w : ℕ) (βW β Λ : ℝ≥0)
    (ε : ℝ≥0) : ℕ∞ :=
  externalCoveringNumber (ε / 4) (Set.univ : Set K) +
    memoryLength Λ 0 (Set.univ : Set K) (ε / 2) *
      externalCoveringNumber (X := UnifMaps K) ((1 - Λ) * (ε / 2)) (reluClass hP w βW β Λ) ^
        memoryLength Λ 0 (Set.univ : Set K) (ε / 2)

@[blueprint "prop:relu-regimes-i-profile"
  (statement := /-- (Case (i), saturated profile: $\mathsf V_k(S) = O(1)$.) Under the
    hypotheses of `prop:relu-regimes-i`, if $\varepsilon \mapsto \sqrt{\log N_\infty(\varepsilon)}$
    is interval-integrable on $[0, D_K]$ then $\mathsf V_k(S) \le \mathsf V_\infty :=
    \int_0^{D_K}\sqrt{\log N_\infty(\varepsilon)}\,d\varepsilon$ for all $k$ and all samples $S$
    (case (i) of `prop:profiles`). -/)]
theorem prop_relu_regimes_i_profile (hP : IsProjectionOnto K proj) (hK : Bornology.IsBounded K)
    (hKne : K.Nonempty) {R : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R) (hR0 : 0 ≤ R) (βW β : ℝ≥0)
    {Λ : ℝ≥0} (hΛ0 : 0 < Λ) (hΛ : Λ < 1) {n : ℕ} (S : Fin n → K)
    (hint : IntervalIntegrable (fun ε : ℝ =>
      √(Real.log (reluSatBound hP w βW β Λ ε.toNNReal : ℝ≥0∞).toReal))
      volume 0 (Metric.diam (Set.univ : Set K))) (k : ℕ) :
    entropyIntegral (Y := EmpSpace S) (empDiam S (wordBall (reluClass hP w βW β Λ) k))
        (wordBall (reluClass hP w βW β Λ) k) ≤
      ∫ ε in (0 : ℝ)..Metric.diam (Set.univ : Set K),
        √(Real.log (reluSatBound hP w βW β Λ ε.toNNReal : ℝ≥0∞).toReal) := by
  /-- $N(B(k,F), d_S, \varepsilon) \le N^{\mathrm{ext}}(B(k,F), d_\infty, \varepsilon/2)
    \le N_\infty(\varepsilon)$ by `prop:relu-regimes-i`, and $D_k(S) \le D_K$. -/
  have hbdd := isBounded_univ_of_isBounded hK
  refine entropyIntegral_le_integral_of_le (empDiam_nonneg S _)
    (empDiam_le_of_bounded S Metric.diam_nonneg
      (fun x y => Metric.dist_le_diam_of_mem hbdd (Set.mem_univ x) (Set.mem_univ y)) _)
    hint fun ε hε => ?_
  have hε : 0 < ε.toNNReal := Real.toNNReal_pos.2 hε.1
  have h := prop_relu_regimes_i hP hK hKne hR hR0 βW β hΛ0 hΛ (w := w) (ε.toNNReal / 2)
    (by positivity) k
  have e : ε.toNNReal / 2 / 2 = ε.toNNReal / 4 := by
    rw [div_div]; norm_num
  rw [e] at h
  refine Real.sqrt_le_sqrt (log_toReal_toENNReal_mono h.2 ?_)
  exact (coveringNumber_empSpace_le_externalCoveringNumber_unifMaps S ε.toNNReal _).trans h.1

omit [FiniteDimensional ℝ E] in
@[blueprint "prop:relu-regimes-ii"
  (statement := /-- \textbf{(`prop:relu-regimes`(ii): non-expanding layers, $\Lambda \le 1$.)}
    If $K$ is compact and $\Lambda \le 1$ then `cond:p1` (2c, non-expanding generators on a
    compact state space) applies: for every $\varepsilon > 0$ and every $k$,
    $N^{\mathrm{ext}}(B(k,F_\Lambda), d_\infty, \varepsilon) \le
    N^{\mathrm{ext}}(\overline{\langle F_\Lambda\rangle}, d_\infty, \varepsilon) < \infty$; in
    particular $\sup_k N^{\mathrm{ext}}(B(k,F_\Lambda), d_\infty, \varepsilon) < \infty$. -/)]
theorem prop_relu_regimes_ii (hP : IsProjectionOnto K proj) (hK : IsCompact K) (βW β : ℝ≥0)
    {Λ : ℝ≥0} (hΛ : Λ ≤ 1) (ε : ℝ≥0) (hε : 0 < ε) (k : ℕ) :
    externalCoveringNumber (X := UnifMaps K) ε (wordBall (reluClass hP w βW β Λ) k) ≤
        externalCoveringNumber (X := UnifMaps K) ε
          (closure (X := UnifMaps K) (semigroupClosure (reluClass hP w βW β Λ))) ∧
      externalCoveringNumber (X := UnifMaps K) ε
        (closure (X := UnifMaps K) (semigroupClosure (reluClass hP w βW β Λ))) ≠ ⊤ := by
  /-- `cond:p1-2c` on the compact state space $K$. -/
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  exact cond_p1_of_nonexpanding
    (fun _ hf => (lipschitzWith_of_mem_reluClass hP hf).weaken hΛ) ε hε k

omit [FiniteDimensional ℝ E] in
@[blueprint "prop:relu-regimes-ii-profile"
  (statement := /-- (Case (ii), saturated profile: $\mathsf V_k(S) = O(1)$.) Under the
    hypotheses of `prop:relu-regimes-ii`, with $N_\infty(\varepsilon) :=
    N(\overline{\langle F_\Lambda\rangle}, d_\infty, \varepsilon/2) < \infty$: if
    $\int_0^{D_K}\sqrt{\log N_\infty(\varepsilon)}\,d\varepsilon < \infty$ then
    $\mathsf V_k(S) \le \int_0^{D_K}\sqrt{\log N_\infty(\varepsilon)}\,d\varepsilon$ for all
    $k$ and all samples $S$ (case (i) of `prop:profiles`, as in `lem:fp-profile`). -/)]
theorem prop_relu_regimes_ii_profile (hP : IsProjectionOnto K proj) (hK : IsCompact K)
    (βW β : ℝ≥0) {Λ : ℝ≥0} (hΛ : Λ ≤ 1) {n : ℕ} (S : Fin n → K)
    (hint : IntervalIntegrable (fun ε : ℝ => √(Real.log (Metric.coveringNumber (X := UnifMaps K)
      (ε.toNNReal / 2) (closure (X := UnifMaps K) (semigroupClosure (reluClass hP w βW β Λ))) :
        ℝ≥0∞).toReal)) volume 0 (Metric.diam (Set.univ : Set K))) (k : ℕ) :
    entropyIntegral (Y := EmpSpace S) (empDiam S (wordBall (reluClass hP w βW β Λ) k))
        (wordBall (reluClass hP w βW β Λ) k) ≤
      ∫ ε in (0 : ℝ)..Metric.diam (Set.univ : Set K),
        √(Real.log (Metric.coveringNumber (X := UnifMaps K) (ε.toNNReal / 2)
          (closure (X := UnifMaps K) (semigroupClosure (reluClass hP w βW β Λ))) :
            ℝ≥0∞).toReal) := by
  /-- The non-expanding semigroup is equicontinuous, hence totally bounded in $d_\infty$
    (`thm:caa`); apply `lem:ode-profile-saturation-generic`. -/
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hG : TotallyBounded (α := UnifMaps K) (semigroupClosure (reluClass hP w βW β Λ)) :=
    totallyBounded_unifMaps_of_equicontinuous
      ((LipschitzWith.uniformEquicontinuous
        (fun g : semigroupClosure (reluClass hP w βW β Λ) => (g : K → K)) 1 fun g =>
          lipschitzWith_one_of_mem_semigroupClosure
            (fun _ hf => (lipschitzWith_of_mem_reluClass hP hf).weaken hΛ) g.2).equicontinuous)
  exact entropyIntegral_le_of_totallyBounded hG (fun _ => subset_semigroupClosure) S hint k

@[blueprint "lem:relu-envelope-profile"
  (statement := /-- (Envelope profile of the ReLU class, all $\Lambda$.) Let $K$ be bounded with
    $\|x\| \le R_K$ on $K$, $D_K \le \overline D$, $\overline D > 0$, $p = 2mw + w + m$ and
    $C_F$ as in `lem:relu-layer-covering`. Then for $k \ge 1$ and every sample $S$, with
    $\Lambda_+ = \max\{1, \Lambda\}$,
    $$\mathsf V_k(S) \le \overline D\Bigl(\sqrt{\log(k+1)} + \sqrt{kp\log k}
      + k\sqrt{p\log\Lambda_+} + \sqrt{kp}\bigl(\sqrt{\log(1 + 2C_F/\overline D)}
      + \tfrac{\sqrt\pi}{2}\bigr)\Bigr)$$
    (`cor:envelope-profiles-a-one-add` with `lem:relu-layer-covering`). -/)]
theorem reluClass_envelope_profile (hP : IsProjectionOnto K proj) (hK : Bornology.IsBounded K)
    {R : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R) (hR0 : 0 ≤ R) (βW β Λ : ℝ≥0) {Dbar : ℝ} (hDbar : 0 < Dbar)
    (hD : Metric.diam (Set.univ : Set K) ≤ Dbar) {n : ℕ} (S : Fin n → K) {k : ℕ} (hk : 1 ≤ k) :
    entropyIntegral (Y := EmpSpace S) (empDiam S (wordBall (reluClass hP w βW β Λ) k))
        (wordBall (reluClass hP w βW β Λ) k) ≤
      Dbar * (√(Real.log (k + 1))
        + √(k * (2 * Module.finrank ℝ E * w + w + Module.finrank ℝ E : ℕ) * Real.log k)
        + k * √((2 * Module.finrank ℝ E * w + w + Module.finrank ℝ E : ℕ)
            * Real.log ((max 1 Λ : ℝ≥0) : ℝ))
        + √(k * (2 * Module.finrank ℝ E * w + w + Module.finrank ℝ E : ℕ))
          * (√(Real.log (1 + 2 * reluCoverConst R βW β / Dbar)) + √π / 2)) := by
  have hbdd := isBounded_univ_of_isBounded hK
  have hD' : empDiam S (wordBall (reluClass hP w βW β Λ) k) ≤ Dbar :=
    (empDiam_le_of_bounded S Metric.diam_nonneg
      (fun x y => Metric.dist_le_diam_of_mem hbdd (Set.mem_univ x) (Set.mem_univ y)) _).trans hD
  have hC0 : 0 ≤ reluCoverConst R βW β := by rw [reluCoverConst]; positivity
  exact envelope_profile_one_add (fun _ hf => lipschitzWith_of_mem_reluClass hP hf)
    (Nat.cast_nonneg _) hC0 hDbar (fun ε hε => (reluClass_covering_log hP hR hR0 βW β Λ hε).1)
    (fun ε hε => (reluClass_covering_log hP hR hR0 βW β Λ hε).2) S hk hD'

@[blueprint "prop:relu-regimes-ii-envelope"
  (statement := /-- (Case (ii), explicit envelope: $\mathsf V_k(S) = O(\sqrt{kp\log k})$.) For
    $\Lambda \le 1$, under the hypotheses of `lem:relu-envelope-profile`,
    $$\mathsf V_k(S) \le \overline D\Bigl(\sqrt{\log(k+1)} + \sqrt{kp\log k}
      + \sqrt{kp}\bigl(\sqrt{\log(1 + 2C_F/\overline D)} + \tfrac{\sqrt\pi}{2}\bigr)\Bigr) .$$ -/)]
theorem prop_relu_regimes_ii_envelope (hP : IsProjectionOnto K proj) (hK : Bornology.IsBounded K)
    {R : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R) (hR0 : 0 ≤ R) (βW β : ℝ≥0) {Λ : ℝ≥0} (hΛ : Λ ≤ 1)
    {Dbar : ℝ} (hDbar : 0 < Dbar) (hD : Metric.diam (Set.univ : Set K) ≤ Dbar) {n : ℕ}
    (S : Fin n → K) {k : ℕ} (hk : 1 ≤ k) :
    entropyIntegral (Y := EmpSpace S) (empDiam S (wordBall (reluClass hP w βW β Λ) k))
        (wordBall (reluClass hP w βW β Λ) k) ≤
      Dbar * (√(Real.log (k + 1))
        + √(k * (2 * Module.finrank ℝ E * w + w + Module.finrank ℝ E : ℕ) * Real.log k)
        + √(k * (2 * Module.finrank ℝ E * w + w + Module.finrank ℝ E : ℕ))
          * (√(Real.log (1 + 2 * reluCoverConst R βW β / Dbar)) + √π / 2)) := by
  have h := reluClass_envelope_profile hP hK hR hR0 βW β Λ (w := w) hDbar hD S hk
  rwa [max_eq_left hΛ, NNReal.coe_one, Real.log_one, mul_zero, Real.sqrt_zero, mul_zero,
    add_zero] at h

@[blueprint "prop:relu-regimes-iii"
  (statement := /-- \textbf{(`prop:relu-regimes`(iii), upper bound: expanding layers,
    $\Lambda > 1$: $\mathsf V_k(S) = O(k\sqrt{p\log\Lambda})$.)} Under the hypotheses of
    `lem:relu-envelope-profile`, for $\Lambda > 1$,
    $$\mathsf V_k(S) \le \overline D\Bigl(\sqrt{\log(k+1)} + \sqrt{kp\log k}
      + k\sqrt{p\log\Lambda} + \sqrt{kp}\bigl(\sqrt{\log(1 + 2C_F/\overline D)}
      + \tfrac{\sqrt\pi}{2}\bigr)\Bigr) .$$ -/)]
theorem prop_relu_regimes_iii (hP : IsProjectionOnto K proj) (hK : Bornology.IsBounded K)
    {R : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R) (hR0 : 0 ≤ R) (βW β : ℝ≥0) {Λ : ℝ≥0} (hΛ : 1 < Λ)
    {Dbar : ℝ} (hDbar : 0 < Dbar) (hD : Metric.diam (Set.univ : Set K) ≤ Dbar) {n : ℕ}
    (S : Fin n → K) {k : ℕ} (hk : 1 ≤ k) :
    entropyIntegral (Y := EmpSpace S) (empDiam S (wordBall (reluClass hP w βW β Λ) k))
        (wordBall (reluClass hP w βW β Λ) k) ≤
      Dbar * (√(Real.log (k + 1))
        + √(k * (2 * Module.finrank ℝ E * w + w + Module.finrank ℝ E : ℕ) * Real.log k)
        + k * √((2 * Module.finrank ℝ E * w + w + Module.finrank ℝ E : ℕ) * Real.log (Λ : ℝ))
        + √(k * (2 * Module.finrank ℝ E * w + w + Module.finrank ℝ E : ℕ))
          * (√(Real.log (1 + 2 * reluCoverConst R βW β / Dbar)) + √π / 2)) := by
  have h := reluClass_envelope_profile hP hK hR hR0 βW β Λ (w := w) hDbar hD S hk
  rwa [max_eq_right hΛ.le] at h

@[blueprint "prop:relu-regimes"
  (statement := /-- \textbf{(Depth profiles of ReLU networks by Lipschitz constant, upper
    bounds.)} Let $K \ne \emptyset$ be bounded with $\|x\| \le R_K$ on $K$ ($R_K \ge 0$),
    $F = F_\Lambda$, $p = 2mw + w + m$ and $C_F$ as in `lem:relu-layer-covering`.
    \begin{enumerate}
    \item[(i)] (Contractive, $0 < \Lambda < 1$.) For every $\varepsilon > 0$ and $k$,
    $N^{\mathrm{ext}}(B(k,F), d_\infty, \varepsilon) \le N^{\mathrm{ext}}(K, \varepsilon/2)
    + m(\varepsilon) N^{\mathrm{ext}}(F, d_\infty, (1-\Lambda)\varepsilon)^{m(\varepsilon)}
    < \infty$ with $m(\varepsilon) = \lceil\log(2D_K/\varepsilon)/\log(1/\Lambda)\rceil$, so
    $\sup_k N^{\mathrm{ext}}(B(k,F), d_\infty, \varepsilon) < \infty$.
    \item[(ii)] (Non-expanding, $\Lambda \le 1$.) If $K$ is compact then for every
    $\varepsilon > 0$ and $k$, $N^{\mathrm{ext}}(B(k,F), d_\infty, \varepsilon) \le
    N^{\mathrm{ext}}(\overline{\langle F\rangle}, d_\infty, \varepsilon) < \infty$; and for
    $D_K \le \overline D$, $\overline D > 0$, $k \ge 1$, the envelope gives
    $\mathsf V_k(S) \le \overline D(\sqrt{\log(k+1)} + \sqrt{kp\log k}
    + \sqrt{kp}(\sqrt{\log(1 + 2C_F/\overline D)} + \sqrt\pi/2)) = O(\sqrt{kp\log k})$.
    \item[(iii)] (Expanding, $\Lambda > 1$.) For $D_K \le \overline D$, $\overline D > 0$,
    $k \ge 1$, $\mathsf V_k(S) \le \overline D(\sqrt{\log(k+1)} + \sqrt{kp\log k}
    + k\sqrt{p\log\Lambda} + \sqrt{kp}(\sqrt{\log(1 + 2C_F/\overline D)} + \sqrt\pi/2))
    = O(k\sqrt{p\log\Lambda})$.
    \end{enumerate}
    The lower bound of (iii) is `prop:relu-regimes-iii-lower`; the saturated profiles
    $\mathsf V_k(S) = O(1)$ of (i) and (ii) are `prop:relu-regimes-i-profile` and
    `prop:relu-regimes-ii-profile`. -/)]
theorem prop_relu_regimes (hP : IsProjectionOnto K proj) (hK : Bornology.IsBounded K)
    (hKne : K.Nonempty) {R : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R) (hR0 : 0 ≤ R) (βW β Λ : ℝ≥0) :
    (0 < Λ → Λ < 1 → ∀ ε : ℝ≥0, 0 < ε → ∀ k : ℕ,
      externalCoveringNumber (X := UnifMaps K) ε (wordBall (reluClass hP w βW β Λ) k) ≤
          externalCoveringNumber (ε / 2) (Set.univ : Set K) +
            memoryLength Λ 0 (Set.univ : Set K) ε *
              externalCoveringNumber (X := UnifMaps K) ((1 - Λ) * ε) (reluClass hP w βW β Λ) ^
                memoryLength Λ 0 (Set.univ : Set K) ε ∧
        externalCoveringNumber (ε / 2) (Set.univ : Set K) +
            memoryLength Λ 0 (Set.univ : Set K) ε *
              externalCoveringNumber (X := UnifMaps K) ((1 - Λ) * ε) (reluClass hP w βW β Λ) ^
                memoryLength Λ 0 (Set.univ : Set K) ε ≠ ⊤) ∧
    (Λ ≤ 1 → IsCompact K → ∀ ε : ℝ≥0, 0 < ε → ∀ k : ℕ,
      externalCoveringNumber (X := UnifMaps K) ε (wordBall (reluClass hP w βW β Λ) k) ≤
          externalCoveringNumber (X := UnifMaps K) ε
            (closure (X := UnifMaps K) (semigroupClosure (reluClass hP w βW β Λ))) ∧
        externalCoveringNumber (X := UnifMaps K) ε
          (closure (X := UnifMaps K) (semigroupClosure (reluClass hP w βW β Λ))) ≠ ⊤) ∧
    (Λ ≤ 1 → ∀ Dbar : ℝ, 0 < Dbar → Metric.diam (Set.univ : Set K) ≤ Dbar →
      ∀ (n : ℕ) (S : Fin n → K) (k : ℕ), 1 ≤ k →
      entropyIntegral (Y := EmpSpace S) (empDiam S (wordBall (reluClass hP w βW β Λ) k))
          (wordBall (reluClass hP w βW β Λ) k) ≤
        Dbar * (√(Real.log (k + 1))
          + √(k * (2 * Module.finrank ℝ E * w + w + Module.finrank ℝ E : ℕ) * Real.log k)
          + √(k * (2 * Module.finrank ℝ E * w + w + Module.finrank ℝ E : ℕ))
            * (√(Real.log (1 + 2 * reluCoverConst R βW β / Dbar)) + √π / 2))) ∧
    (1 < Λ → ∀ Dbar : ℝ, 0 < Dbar → Metric.diam (Set.univ : Set K) ≤ Dbar →
      ∀ (n : ℕ) (S : Fin n → K) (k : ℕ), 1 ≤ k →
      entropyIntegral (Y := EmpSpace S) (empDiam S (wordBall (reluClass hP w βW β Λ) k))
          (wordBall (reluClass hP w βW β Λ) k) ≤
        Dbar * (√(Real.log (k + 1))
          + √(k * (2 * Module.finrank ℝ E * w + w + Module.finrank ℝ E : ℕ) * Real.log k)
          + k * √((2 * Module.finrank ℝ E * w + w + Module.finrank ℝ E : ℕ) * Real.log (Λ : ℝ))
          + √(k * (2 * Module.finrank ℝ E * w + w + Module.finrank ℝ E : ℕ))
            * (√(Real.log (1 + 2 * reluCoverConst R βW β / Dbar)) + √π / 2))) :=
  ⟨fun hΛ0 hΛ ε hε k => prop_relu_regimes_i hP hK hKne hR hR0 βW β hΛ0 hΛ ε hε k,
    fun hΛ hKc ε hε k => prop_relu_regimes_ii hP hKc βW β hΛ ε hε k,
    fun hΛ _Dbar hDbar hD _n S _k hk => prop_relu_regimes_ii_envelope hP hK hR hR0 βW β hΛ hDbar hD S hk,
    fun hΛ _Dbar hDbar hD _n S _k hk => prop_relu_regimes_iii hP hK hR hR0 βW β hΛ hDbar hD S hk⟩

end Regimes

/-! ### `prop:relu-regimes`(iii), lower bound: the expand-and-reset maps -/

section ExpandReset

/-! #### Affine and piecewise-linear maps of `[0,1]` -/

@[blueprint "def:relu-clip-unit"
  (statement := /-- The clipping $\Pi_{[0,1]}(x) = \max\{0, \min\{1, x\}\}$, a $1$-Lipschitz
    retraction of $\mathbb R$ onto $[0,1]$. -/)]
noncomputable def clipUnit (x : ℝ) : ℝ := max 0 (min 1 x)

@[blueprint "lem:relu-clip-unit-of-mem"
  (statement := /-- $\Pi_{[0,1]}(x) = x$ for $x \in [0,1]$. -/)]
theorem clipUnit_of_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : clipUnit x = x := by
  rw [clipUnit, min_eq_right hx.2, max_eq_right hx.1]

@[blueprint "lem:relu-clip-unit-projection"
  (statement := /-- $\Pi_{[0,1]}$ is a $1$-Lipschitz retraction onto $[0,1]$
    (`def:ode-projection`). -/)]
theorem isProjectionOnto_clipUnit : IsProjectionOnto (Icc (0 : ℝ) 1) clipUnit where
  mem x := ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  eq_of_mem _ hx := clipUnit_of_mem hx
  lipschitz := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq, clipUnit, clipUnit, max_comm 0,
      max_comm 0]
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
    simp

@[blueprint "lem:relu-affine-lipschitz"
  (statement := /-- $x \mapsto ax + b$ is $L$-Lipschitz on $\mathbb R$ when $|a| \le L$. -/)]
theorem lipschitzWith_affine {a b : ℝ} {L : ℝ≥0} (h : |a| ≤ L) :
    LipschitzWith L (fun x : ℝ => a * x + b) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, Real.dist_eq, show a * x + b - (a * y + b) = a * (x - y) by ring, abs_mul]
  exact mul_le_mul_of_nonneg_right h (abs_nonneg _)

@[blueprint "def:relu-expand-reset-0"
  (statement := /-- The first expand-and-reset map of the computed illustration
    (`sec:relu-computed`), $\eta = 1/32$: the piecewise-linear map with breakpoints
    $(0, 3/8), (\eta, 0), (1/4 - \eta, 1), (1/4, 3/8), (1, 3/8)$, i.e.
    $g_0(x) = 3/8 - 12x$ on $[0, \eta]$, $= \tfrac{16}{3}(x - \eta)$ on $[\eta, 1/4 - \eta]$,
    $= 1 - 20(x - 1/4 + \eta)$ on $[1/4 - \eta, 1/4]$ and $= 3/8$ on $[1/4, 1]$. -/)]
noncomputable def expandReset₀ (x : ℝ) : ℝ :=
  if x ≤ 1 / 32 then 3 / 8 - 12 * x
  else if x ≤ 7 / 32 then 16 / 3 * (x - 1 / 32)
  else if x ≤ 1 / 4 then 1 - 20 * (x - 7 / 32)
  else 3 / 8

@[blueprint "def:relu-expand-reset-1"
  (statement := /-- The second expand-and-reset map, with breakpoints
    $(0, 5/8), (3/4, 5/8), (3/4 + \eta, 0), (1 - \eta, 1), (1, 5/8)$, i.e.
    $g_1(x) = 5/8$ on $[0, 3/4]$, $= 5/8 - 20(x - 3/4)$ on $[3/4, 3/4 + \eta]$,
    $= \tfrac{16}{3}(x - 3/4 - \eta)$ on $[3/4 + \eta, 1 - \eta]$ and $= 1 - 12(x - 1 + \eta)$
    on $[1 - \eta, 1]$. -/)]
noncomputable def expandReset₁ (x : ℝ) : ℝ :=
  if x ≤ 3 / 4 then 5 / 8
  else if x ≤ 25 / 32 then 5 / 8 - 20 * (x - 3 / 4)
  else if x ≤ 31 / 32 then 16 / 3 * (x - 25 / 32)
  else 1 - 12 * (x - 31 / 32)

@[blueprint "lem:relu-expand-reset-0-mem"
  (statement := /-- $g_0$ maps $[0,1]$ into $[0,1]$. -/)]
theorem expandReset₀_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : expandReset₀ x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := hx
  unfold expandReset₀
  split_ifs <;> constructor <;> linarith

@[blueprint "lem:relu-expand-reset-1-mem"
  (statement := /-- $g_1$ maps $[0,1]$ into $[0,1]$. -/)]
theorem expandReset₁_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : expandReset₁ x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := hx
  unfold expandReset₁
  split_ifs <;> constructor <;> linarith

@[blueprint "lem:relu-expand-reset-0-maxmin"
  (statement := /-- On $[0,1]$, $g_0(x) = \max\{-12x + 3/8, \min\{\tfrac{16}{3}x - \tfrac16,
    \max\{3/8, -20x + 43/8\}\}\}$ (a max–min of affine maps of slopes $\le 20$). -/)]
theorem expandReset₀_eq_maxmin {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    expandReset₀ x = max ((-12) * x + 3 / 8)
      (min (16 / 3 * x + (-1 / 6)) (max (3 / 8) ((-20) * x + 43 / 8))) := by
  obtain ⟨h0, h1⟩ := hx
  unfold expandReset₀
  split_ifs with ha hb hc
  · rw [max_eq_right (show (3 / 8 : ℝ) ≤ (-20) * x + 43 / 8 by linarith),
      min_eq_left (show (16 / 3 * x + (-1 / 6) : ℝ) ≤ (-20) * x + 43 / 8 by linarith),
      max_eq_left (show (16 / 3 * x + (-1 / 6) : ℝ) ≤ (-12) * x + 3 / 8 by linarith)]
    ring
  · rw [max_eq_right (show (3 / 8 : ℝ) ≤ (-20) * x + 43 / 8 by linarith),
      min_eq_left (show (16 / 3 * x + (-1 / 6) : ℝ) ≤ (-20) * x + 43 / 8 by linarith),
      max_eq_right (show ((-12) * x + 3 / 8 : ℝ) ≤ 16 / 3 * x + (-1 / 6) by linarith)]
    ring
  · rw [max_eq_right (show (3 / 8 : ℝ) ≤ (-20) * x + 43 / 8 by linarith),
      min_eq_right (show ((-20) * x + 43 / 8 : ℝ) ≤ 16 / 3 * x + (-1 / 6) by linarith),
      max_eq_right (show ((-12) * x + 3 / 8 : ℝ) ≤ (-20) * x + 43 / 8 by linarith)]
    ring
  · rw [max_eq_left (show ((-20) * x + 43 / 8 : ℝ) ≤ 3 / 8 by linarith),
      min_eq_right (show (3 / 8 : ℝ) ≤ 16 / 3 * x + (-1 / 6) by linarith),
      max_eq_right (show ((-12) * x + 3 / 8 : ℝ) ≤ 3 / 8 by linarith)]

@[blueprint "lem:relu-expand-reset-1-maxmin"
  (statement := /-- On $[0,1]$, $g_1(x) = \max\{\min\{5/8, -20x + 125/8\},
    \min\{\tfrac{16}{3}x - \tfrac{25}{6}, -12x + 101/8\}\}$. -/)]
theorem expandReset₁_eq_maxmin {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    expandReset₁ x = max (min (5 / 8) ((-20) * x + 125 / 8))
      (min (16 / 3 * x + (-25 / 6)) ((-12) * x + 101 / 8)) := by
  obtain ⟨h0, h1⟩ := hx
  unfold expandReset₁
  split_ifs with ha hb hc
  · rw [min_eq_left (show (5 / 8 : ℝ) ≤ (-20) * x + 125 / 8 by linarith),
      min_eq_left (show (16 / 3 * x + (-25 / 6) : ℝ) ≤ (-12) * x + 101 / 8 by linarith),
      max_eq_left (show (16 / 3 * x + (-25 / 6) : ℝ) ≤ 5 / 8 by linarith)]
  · rw [min_eq_right (show ((-20) * x + 125 / 8 : ℝ) ≤ 5 / 8 by linarith),
      min_eq_left (show (16 / 3 * x + (-25 / 6) : ℝ) ≤ (-12) * x + 101 / 8 by linarith),
      max_eq_left (show (16 / 3 * x + (-25 / 6) : ℝ) ≤ (-20) * x + 125 / 8 by linarith)]
    ring
  · rw [min_eq_right (show ((-20) * x + 125 / 8 : ℝ) ≤ 5 / 8 by linarith),
      min_eq_left (show (16 / 3 * x + (-25 / 6) : ℝ) ≤ (-12) * x + 101 / 8 by linarith),
      max_eq_right (show ((-20) * x + 125 / 8 : ℝ) ≤ 16 / 3 * x + (-25 / 6) by linarith)]
    ring
  · rw [min_eq_right (show ((-20) * x + 125 / 8 : ℝ) ≤ 5 / 8 by linarith),
      min_eq_right (show ((-12) * x + 101 / 8 : ℝ) ≤ 16 / 3 * x + (-25 / 6) by linarith),
      max_eq_right (show ((-20) * x + 125 / 8 : ℝ) ≤ (-12) * x + 101 / 8 by linarith)]
    ring

@[blueprint "lem:relu-expand-reset-0-lipschitz-on"
  (statement := /-- $g_0$ is $20$-Lipschitz on $[0,1]$ (max–min of $20$-Lipschitz affine
    maps). -/)]
theorem lipschitzOnWith_expandReset₀ : LipschitzOnWith 20 expandReset₀ (Icc (0 : ℝ) 1) := by
  have h1 : LipschitzWith 20 (fun x : ℝ => (-12) * x + 3 / 8) := lipschitzWith_affine (by norm_num)
  have h2 : LipschitzWith 20 (fun x : ℝ => 16 / 3 * x + (-1 / 6)) :=
    lipschitzWith_affine (by norm_num)
  have h3 : LipschitzWith 20 (fun _ : ℝ => (3 / 8 : ℝ)) := (LipschitzWith.const _).weaken zero_le
  have h4 : LipschitzWith 20 (fun x : ℝ => (-20) * x + 43 / 8) := lipschitzWith_affine (by norm_num)
  have h : LipschitzWith 20 (fun x : ℝ => max ((-12) * x + 3 / 8)
      (min (16 / 3 * x + (-1 / 6)) (max (3 / 8) ((-20) * x + 43 / 8)))) := by
    simpa only [max_self] using h1.max (h2.min (h3.max h4))
  intro x hx y hy
  rw [expandReset₀_eq_maxmin hx, expandReset₀_eq_maxmin hy]
  exact h.edist_le_mul x y

@[blueprint "lem:relu-expand-reset-1-lipschitz-on"
  (statement := /-- $g_1$ is $20$-Lipschitz on $[0,1]$. -/)]
theorem lipschitzOnWith_expandReset₁ : LipschitzOnWith 20 expandReset₁ (Icc (0 : ℝ) 1) := by
  have h1 : LipschitzWith 20 (fun _ : ℝ => (5 / 8 : ℝ)) := (LipschitzWith.const _).weaken zero_le
  have h2 : LipschitzWith 20 (fun x : ℝ => (-20) * x + 125 / 8) :=
    lipschitzWith_affine (by norm_num)
  have h3 : LipschitzWith 20 (fun x : ℝ => 16 / 3 * x + (-25 / 6)) :=
    lipschitzWith_affine (by norm_num)
  have h4 : LipschitzWith 20 (fun x : ℝ => (-12) * x + 101 / 8) :=
    lipschitzWith_affine (by norm_num)
  have h : LipschitzWith 20 (fun x : ℝ => max (min (5 / 8) ((-20) * x + 125 / 8))
      (min (16 / 3 * x + (-25 / 6)) ((-12) * x + 101 / 8))) := by
    simpa only [max_self] using (h1.min h2).max (h3.min h4)
  intro x hx y hy
  rw [expandReset₁_eq_maxmin hx, expandReset₁_eq_maxmin hy]
  exact h.edist_le_mul x y

@[blueprint "def:relu-expand-reset-map-0"
  (statement := /-- $g_0$ as a self-map of the state space $[0,1]$. -/)]
noncomputable def expandResetMap₀ : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 :=
  fun x => ⟨expandReset₀ x, expandReset₀_mem x.2⟩

@[blueprint "def:relu-expand-reset-map-1"
  (statement := /-- $g_1$ as a self-map of the state space $[0,1]$. -/)]
noncomputable def expandResetMap₁ : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 :=
  fun x => ⟨expandReset₁ x, expandReset₁_mem x.2⟩

@[blueprint "lem:relu-expand-reset-map-0-lipschitz"
  (statement := /-- $g_0 : [0,1] \to [0,1]$ is $20$-Lipschitz. -/)]
theorem lipschitzWith_expandResetMap₀ : LipschitzWith 20 expandResetMap₀ :=
  (lipschitzOnWith_iff_restrict.1 lipschitzOnWith_expandReset₀).subtype_mk
    fun x => expandReset₀_mem x.2

@[blueprint "lem:relu-expand-reset-map-1-lipschitz"
  (statement := /-- $g_1 : [0,1] \to [0,1]$ is $20$-Lipschitz. -/)]
theorem lipschitzWith_expandResetMap₁ : LipschitzWith 20 expandResetMap₁ :=
  (lipschitzOnWith_iff_restrict.1 lipschitzOnWith_expandReset₁).subtype_mk
    fun x => expandReset₁_mem x.2

/-! #### ReLU representation of piecewise-linear maps -/

@[blueprint "def:relu-unit-param"
  (statement := /-- The parameters of a one-dimensional ReLU block with $w$ units of input
    weights $u_i$, thresholds $t_i$, output weights $v_i$ and bias $c$:
    $W = (u_i)_i$, $b = (-t_i)_i$, $V = (v_i)_i$ (as a row), so that
    $V\,\mathrm{relu}(Wx + b) + c = \sum_i v_i\,\mathrm{relu}(u_i x - t_i) + c$. -/)]
noncomputable def unitParam {w : ℕ} (u t v : Fin w → ℝ) (c : ℝ) : ReLUParam ℝ w :=
  (ContinuousLinearMap.toSpanSingleton ℝ (WithLp.toLp 2 u), WithLp.toLp 2 (fun i => -t i),
    innerSL ℝ (WithLp.toLp 2 v), c)

@[blueprint "lem:relu-block-unit-param"
  (statement := /-- $f_\vartheta(x) = \Pi_K\bigl(\sum_i v_i\max\{u_ix - t_i, 0\} + c\bigr)$ for the
    parameters `def:relu-unit-param`. -/)]
theorem reluBlock_unitParam {K : Set ℝ} {proj : ℝ → ℝ} (hP : IsProjectionOnto K proj) {w : ℕ}
    (u t v : Fin w → ℝ) (c : ℝ) (x : K) :
    (reluBlock hP (unitParam u t v c) x : ℝ) = proj (∑ i, v i * max (x * u i - t i) 0 + c) := by
  change proj _ = proj _
  congr 1
  simp [unitParam, PiLp.inner_apply, reluVec, mul_comm, sub_eq_add_neg]

@[blueprint "def:relu-unit-weights"
  (statement := /-- Input weights of the expand-and-reset blocks at width $4 + w'$:
    $u = (1,1,1,1,0,\dots,0)$. -/)]
def erInput (w' : ℕ) : Fin (4 + w') → ℝ := Fin.append ![1, 1, 1, 1] 0

@[blueprint "def:relu-thresholds-0"
  (statement := /-- Thresholds of $g_0$: $t = (0, \eta, 1/4 - \eta, 1/4, 0, \dots, 0)$. -/)]
noncomputable def erThreshold₀ (w' : ℕ) : Fin (4 + w') → ℝ := Fin.append ![0, 1 / 32, 7 / 32, 1 / 4] 0

@[blueprint "def:relu-coefficients-0"
  (statement := /-- Output weights of $g_0$ (the slope increments at the breakpoints):
    $v = (-12, 52/3, -76/3, 20, 0, \dots, 0)$. -/)]
noncomputable def erCoef₀ (w' : ℕ) : Fin (4 + w') → ℝ := Fin.append ![-12, 52 / 3, -76 / 3, 20] 0

@[blueprint "def:relu-thresholds-1"
  (statement := /-- Thresholds of $g_1$: $t = (3/4, 3/4 + \eta, 1 - \eta, 0, 0, \dots, 0)$. -/)]
noncomputable def erThreshold₁ (w' : ℕ) : Fin (4 + w') → ℝ :=
  Fin.append ![3 / 4, 25 / 32, 31 / 32, 0] 0

@[blueprint "def:relu-coefficients-1"
  (statement := /-- Output weights of $g_1$: $v = (-20, 76/3, -52/3, 0, 0, \dots, 0)$. -/)]
noncomputable def erCoef₁ (w' : ℕ) : Fin (4 + w') → ℝ := Fin.append ![-20, 76 / 3, -52 / 3, 0] 0

@[blueprint "def:relu-expand-reset-param-0"
  (statement := /-- The ReLU parameters of $g_0$ (bias $c = 3/8$). -/)]
noncomputable def expandResetParam₀ (w' : ℕ) : ReLUParam ℝ (4 + w') :=
  unitParam (erInput w') (erThreshold₀ w') (erCoef₀ w') (3 / 8)

@[blueprint "def:relu-expand-reset-param-1"
  (statement := /-- The ReLU parameters of $g_1$ (bias $c = 5/8$). -/)]
noncomputable def expandResetParam₁ (w' : ℕ) : ReLUParam ℝ (4 + w') :=
  unitParam (erInput w') (erThreshold₁ w') (erCoef₁ w') (5 / 8)

@[blueprint "lem:relu-expand-reset-0-relu"
  (statement := /-- On $[0,1]$, $g_0(x) = -12\,\mathrm{relu}(x) + \tfrac{52}{3}\mathrm{relu}(x - \eta)
    - \tfrac{76}{3}\mathrm{relu}(x - 1/4 + \eta) + 20\,\mathrm{relu}(x - 1/4) + 3/8$. -/)]
theorem expandReset₀_eq_relu {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (-12) * max x 0 + 52 / 3 * max (x - 1 / 32) 0 + (-76 / 3) * max (x - 7 / 32) 0
      + 20 * max (x - 1 / 4) 0 + 3 / 8 = expandReset₀ x := by
  obtain ⟨h0, h1⟩ := hx
  unfold expandReset₀
  split_ifs with ha hb hc
  · rw [max_eq_left h0, max_eq_right (by linarith), max_eq_right (by linarith),
      max_eq_right (by linarith)]; ring
  · rw [max_eq_left h0, max_eq_left (by linarith), max_eq_right (by linarith),
      max_eq_right (by linarith)]; ring
  · rw [max_eq_left h0, max_eq_left (by linarith), max_eq_left (by linarith),
      max_eq_right (by linarith)]; ring
  · rw [max_eq_left h0, max_eq_left (by linarith), max_eq_left (by linarith),
      max_eq_left (by linarith)]; ring

@[blueprint "lem:relu-expand-reset-1-relu"
  (statement := /-- On $[0,1]$, $g_1(x) = -20\,\mathrm{relu}(x - 3/4) + \tfrac{76}{3}
    \mathrm{relu}(x - 3/4 - \eta) - \tfrac{52}{3}\mathrm{relu}(x - 1 + \eta) + 5/8$. -/)]
theorem expandReset₁_eq_relu {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (-20) * max (x - 3 / 4) 0 + 76 / 3 * max (x - 25 / 32) 0 + (-52 / 3) * max (x - 31 / 32) 0
      + 5 / 8 = expandReset₁ x := by
  obtain ⟨h0, h1⟩ := hx
  unfold expandReset₁
  split_ifs with ha hb hc
  · rw [max_eq_right (by linarith), max_eq_right (by linarith), max_eq_right (by linarith)]; ring
  · rw [max_eq_left (by linarith), max_eq_right (by linarith), max_eq_right (by linarith)]; ring
  · rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  · rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith)]; ring

@[blueprint "lem:relu-sum-units-0"
  (statement := /-- The unit sum of $g_0$ at width $4 + w'$ (the padding units vanish). -/)]
theorem sum_erCoef₀ (w' : ℕ) (x : ℝ) :
    ∑ i, erCoef₀ w' i * max (x * erInput w' i - erThreshold₀ w' i) 0 =
      (-12) * max x 0 + 52 / 3 * max (x - 1 / 32) 0 + (-76 / 3) * max (x - 7 / 32) 0
        + 20 * max (x - 1 / 4) 0 := by
  simp [erCoef₀, erInput, erThreshold₀, Fin.sum_univ_add, Fin.sum_univ_four]

@[blueprint "lem:relu-sum-units-1"
  (statement := /-- The unit sum of $g_1$ at width $4 + w'$. -/)]
theorem sum_erCoef₁ (w' : ℕ) (x : ℝ) :
    ∑ i, erCoef₁ w' i * max (x * erInput w' i - erThreshold₁ w' i) 0 =
      (-20) * max (x - 3 / 4) 0 + 76 / 3 * max (x - 25 / 32) 0
        + (-52 / 3) * max (x - 31 / 32) 0 := by
  simp [erCoef₁, erInput, erThreshold₁, Fin.sum_univ_add, Fin.sum_univ_four]

@[blueprint "lem:relu-block-expand-reset-0"
  (statement := /-- (\textbf{$g_0$ is a ReLU block of width $4 + w'$.}) With the clipping
    $\Pi_{[0,1]}$, $f_{\vartheta_0} = g_0$ on $[0,1]$. -/)]
theorem reluBlock_expandResetParam₀ (w' : ℕ) :
    reluBlock isProjectionOnto_clipUnit (expandResetParam₀ w') = expandResetMap₀ := by
  funext x
  apply Subtype.ext
  rw [expandResetParam₀, reluBlock_unitParam, sum_erCoef₀, expandReset₀_eq_relu x.2]
  exact clipUnit_of_mem (expandReset₀_mem x.2)

@[blueprint "lem:relu-block-expand-reset-1"
  (statement := /-- (\textbf{$g_1$ is a ReLU block of width $4 + w'$.}) $f_{\vartheta_1} = g_1$
    on $[0,1]$. -/)]
theorem reluBlock_expandResetParam₁ (w' : ℕ) :
    reluBlock isProjectionOnto_clipUnit (expandResetParam₁ w') = expandResetMap₁ := by
  funext x
  apply Subtype.ext
  rw [expandResetParam₁, reluBlock_unitParam, sum_erCoef₁, expandReset₁_eq_relu x.2]
  exact clipUnit_of_mem (expandReset₁_mem x.2)

@[blueprint "lem:relu-expand-reset-norms-0"
  (statement := /-- Weight norms of the representation of $g_0$: $\|W\|_{\rm op} = \|u\| = 2$,
    $\|b\| = \|t\| \le 2$, $\|V\|_{\rm op} = \|v\| \le 41$, $\|c\| = 3/8 \le 2$. -/)]
theorem expandResetParam₀_norms (w' : ℕ) :
    ‖(expandResetParam₀ w').1‖ ≤ 41 ∧ ‖(expandResetParam₀ w').2.1‖ ≤ 2 ∧
      ‖(expandResetParam₀ w').2.2.1‖ ≤ 41 ∧ ‖(expandResetParam₀ w').2.2.2‖ ≤ 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change ‖ContinuousLinearMap.toSpanSingleton ℝ (WithLp.toLp 2 (erInput w') :
      EuclideanSpace ℝ (Fin (4 + w')))‖ ≤ 41
    rw [ContinuousLinearMap.norm_toSpanSingleton, EuclideanSpace.norm_eq,
      Real.sqrt_le_left (by norm_num)]
    simp [erInput, Fin.sum_univ_add, Fin.sum_univ_four]
    norm_num
  · change ‖(WithLp.toLp 2 (fun i => -erThreshold₀ w' i) : EuclideanSpace ℝ (Fin (4 + w')))‖ ≤ 2
    rw [EuclideanSpace.norm_eq, Real.sqrt_le_left (by norm_num)]
    simp [erThreshold₀, Fin.sum_univ_add, Fin.sum_univ_four]
    norm_num
  · change ‖innerSL ℝ (WithLp.toLp 2 (erCoef₀ w') : EuclideanSpace ℝ (Fin (4 + w')))‖ ≤ 41
    rw [innerSL_apply_norm, EuclideanSpace.norm_eq, Real.sqrt_le_left (by norm_num)]
    simp [erCoef₀, Fin.sum_univ_add, Fin.sum_univ_four]
    norm_num
  · change ‖(3 / 8 : ℝ)‖ ≤ 2
    rw [Real.norm_eq_abs]; norm_num

@[blueprint "lem:relu-expand-reset-norms-1"
  (statement := /-- Weight norms of the representation of $g_1$: $\|W\|_{\rm op} = 2$,
    $\|b\| \le 2$, $\|V\|_{\rm op} \le 41$, $\|c\| = 5/8 \le 2$. -/)]
theorem expandResetParam₁_norms (w' : ℕ) :
    ‖(expandResetParam₁ w').1‖ ≤ 41 ∧ ‖(expandResetParam₁ w').2.1‖ ≤ 2 ∧
      ‖(expandResetParam₁ w').2.2.1‖ ≤ 41 ∧ ‖(expandResetParam₁ w').2.2.2‖ ≤ 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change ‖ContinuousLinearMap.toSpanSingleton ℝ (WithLp.toLp 2 (erInput w') :
      EuclideanSpace ℝ (Fin (4 + w')))‖ ≤ 41
    rw [ContinuousLinearMap.norm_toSpanSingleton, EuclideanSpace.norm_eq,
      Real.sqrt_le_left (by norm_num)]
    simp [erInput, Fin.sum_univ_add, Fin.sum_univ_four]
    norm_num
  · change ‖(WithLp.toLp 2 (fun i => -erThreshold₁ w' i) : EuclideanSpace ℝ (Fin (4 + w')))‖ ≤ 2
    rw [EuclideanSpace.norm_eq, Real.sqrt_le_left (by norm_num)]
    simp [erThreshold₁, Fin.sum_univ_add, Fin.sum_univ_four]
    norm_num
  · change ‖innerSL ℝ (WithLp.toLp 2 (erCoef₁ w') : EuclideanSpace ℝ (Fin (4 + w')))‖ ≤ 41
    rw [innerSL_apply_norm, EuclideanSpace.norm_eq, Real.sqrt_le_left (by norm_num)]
    simp [erCoef₁, Fin.sum_univ_add, Fin.sum_univ_four]
    norm_num
  · change ‖(5 / 8 : ℝ)‖ ≤ 2
    rw [Real.norm_eq_abs]; norm_num

/-! #### The ping–pong data of `cond:e2-pingpong` -/

@[blueprint "def:relu-er-generators"
  (statement := /-- The two generators $f = (g_0, g_1)$. -/)]
noncomputable def erGen : Fin 2 → Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 := ![expandResetMap₀, expandResetMap₁]

@[blueprint "def:relu-er-chambers"
  (statement := /-- The chambers $U_0 = [0, 1/4]$, $U_1 = [3/4, 1]$. -/)]
def erChamber : Fin 2 → Set (Icc (0 : ℝ) 1) :=
  ![{x | (x : ℝ) ≤ 1 / 4}, {x | 3 / 4 ≤ (x : ℝ)}]

@[blueprint "def:relu-er-cores"
  (statement := /-- The coding cores $V_0 = [\eta, 1/4 - \eta]$,
    $V_1 = [3/4 + \eta, 1 - \eta]$. -/)]
def erCore : Fin 2 → Set (Icc (0 : ℝ) 1) :=
  ![{x | 1 / 32 ≤ (x : ℝ) ∧ (x : ℝ) ≤ 7 / 32}, {x | 25 / 32 ≤ (x : ℝ) ∧ (x : ℝ) ≤ 31 / 32}]

@[blueprint "def:relu-er-anchors"
  (statement := /-- The anchors $a_0 = 3/8$, $a_1 = 5/8$. -/)]
noncomputable def erAnchor : Fin 2 → Icc (0 : ℝ) 1 := ![⟨3 / 8, by norm_num⟩, ⟨5 / 8, by norm_num⟩]

@[blueprint "def:relu-er-marker"
  (statement := /-- The marker $q = 1/2$. -/)]
noncomputable def erMarker : Icc (0 : ℝ) 1 := ⟨1 / 2, by norm_num⟩

@[blueprint "lem:relu-er-core-subset"
  (statement := /-- $V_i \subseteq U_i$. -/)]
theorem erCore_subset_erChamber (i : Fin 2) : erCore i ⊆ erChamber i := by
  fin_cases i <;> intro x hx <;> simp [erCore, erChamber] at hx ⊢ <;> linarith [hx.1, hx.2]

@[blueprint "lem:relu-er-disjoint"
  (statement := /-- (Disjoint chambers.) $U_0 \cap U_1 = \emptyset$. -/)]
theorem erChamber_disjoint (i j : Fin 2) (hij : i ≠ j) : Disjoint (erChamber i) (erChamber j) := by
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact Set.disjoint_left.2 fun x hx hx' => by simp [erChamber] at hx hx'; linarith
  · exact Set.disjoint_left.2 fun x hx hx' => by simp [erChamber] at hx hx'; linarith
  · exact absurd rfl hij

@[blueprint "lem:relu-er-reset"
  (statement := /-- (Reset.) $g_i(x) = a_i$ for $x \notin U_i$: $g_0 = 3/8$ outside $[0,1/4]$
    and $g_1 = 5/8$ outside $[3/4, 1]$. -/)]
theorem erGen_reset (i : Fin 2) (x : Icc (0 : ℝ) 1) (hx : x ∉ erChamber i) :
    erGen i x = erAnchor i := by
  obtain ⟨hx0, hx1⟩ := x.2
  fin_cases i <;> simp [erChamber] at hx <;> apply Subtype.ext
  · change expandReset₀ x = 3 / 8
    unfold expandReset₀
    split_ifs <;> linarith
  · change expandReset₁ x = 5 / 8
    unfold expandReset₁
    split_ifs <;> linarith

@[blueprint "lem:relu-er-anchor-not-mem"
  (statement := /-- The anchors lie outside both chambers. -/)]
theorem erAnchor_not_mem_erChamber (i j : Fin 2) : erAnchor j ∉ erChamber i := by
  fin_cases i <;> fin_cases j <;> simp [erAnchor, erChamber] <;> norm_num

@[blueprint "lem:relu-er-anchor-invariant"
  (statement := /-- $g_i(A) \subseteq A$ for $A = \{a_0, a_1\}$ (each anchor is reset to
    $a_i$). -/)]
theorem erGen_anchor (i : Fin 2) : erGen i '' Set.range erAnchor ⊆ Set.range erAnchor := by
  rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
  exact ⟨i, (erGen_reset i (erAnchor j) (erAnchor_not_mem_erChamber i j)).symm⟩

@[blueprint "lem:relu-er-core"
  (statement := /-- (Coding cores.) $g_i(V_i) = [0,1] \supseteq \{q\} \cup V_0 \cup V_1$: for
    $y \in [0,1]$, $x = \eta + \tfrac{3}{16}y \in V_0$ has $g_0(x) = y$, and
    $x = 3/4 + \eta + \tfrac{3}{16}y \in V_1$ has $g_1(x) = y$. -/)]
theorem erGen_core (i : Fin 2) : ({erMarker} ∪ ⋃ j, erCore j) ⊆ erGen i '' erCore i := by
  intro y _
  obtain ⟨hy0, hy1⟩ := y.2
  fin_cases i
  · refine ⟨⟨1 / 32 + 3 / 16 * y, by constructor <;> linarith⟩, ?_, ?_⟩
    · simp only [erCore]
      constructor <;> simp <;> linarith
    · apply Subtype.ext
      change expandReset₀ (1 / 32 + 3 / 16 * y) = y
      unfold expandReset₀
      split_ifs <;> linarith
  · refine ⟨⟨25 / 32 + 3 / 16 * y, by constructor <;> linarith⟩, ?_, ?_⟩
    · simp only [erCore]
      constructor <;> simp <;> linarith
    · apply Subtype.ext
      change expandReset₁ (25 / 32 + 3 / 16 * y) = y
      unfold expandReset₁
      split_ifs <;> linarith

@[blueprint "lem:relu-er-marker"
  (statement := /-- (Marker separation.) $d(q, a_i) = 1/8$ for $i = 0, 1$. -/)]
theorem erMarker_separated (i : Fin 2) : ((1 / 8 : ℝ≥0) : ℝ≥0∞) ≤ edist erMarker (erAnchor i) := by
  rw [Subtype.edist_eq, edist_dist, Real.dist_eq, ← ENNReal.ofReal_coe_nnreal]
  refine ENNReal.ofReal_le_ofReal ?_
  fin_cases i <;> simp [erMarker, erAnchor] <;> norm_num [abs_of_nonneg, abs_of_nonpos]

@[blueprint "lem:relu-er-pingpong"
  (statement := /-- (\textbf{The expand-and-reset maps satisfy `cond:e2-pingpong`.}) With the
    chambers, cores, anchors and marker above and separation $\alpha = 1/8$:
    $N^{\mathrm{ext}}(B(k, \{g_0, g_1\}), d_\infty, \varepsilon) \ge 2^k$ for all $k$ and
    $2\varepsilon < 1/8$, and the words of each length are pairwise distinct. -/)]
theorem expandReset_pingpong :
    (∀ k, ∀ ε : ℝ≥0, 2 * ε < 1 / 8 →
      (2 : ℕ∞) ^ k ≤ externalCoveringNumber (X := UnifMaps (Icc (0 : ℝ) 1)) ε
        (wordBall (Set.range erGen) k)) ∧
    (∀ k, Set.InjOn (wordOf erGen) {u : List (Fin 2) | u.length = k}) :=
  cond_e2_pingpong le_rfl erGen erChamber erCore erCore_subset_erChamber erAnchor erMarker
    (α := 1 / 8) (by norm_num) erChamber_disjoint erGen_core erGen_reset erGen_anchor
    erMarker_separated

@[blueprint "lem:relu-er-mem-class"
  (statement := /-- For $\beta_W \ge 41$, $\beta \ge 2$, $\Lambda \ge 20$ and width $4 + w'$,
    $g_0, g_1 \in F_\Lambda$ on $K = [0,1]$ with the clipping retraction. -/)]
theorem range_erGen_subset_reluClass (w' : ℕ) {βW β Λ : ℝ≥0} (hβW : 41 ≤ βW) (hβ : 2 ≤ β)
    (hΛ : 20 ≤ Λ) :
    Set.range erGen ⊆ reluClass isProjectionOnto_clipUnit (4 + w') βW β Λ := by
  have hβW' : (41 : ℝ) ≤ βW := by exact_mod_cast hβW
  have hβ' : (2 : ℝ) ≤ β := by exact_mod_cast hβ
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · obtain ⟨h1, h2, h3, h4⟩ := expandResetParam₀_norms w'
    refine ⟨expandResetParam₀ w', ⟨h1.trans hβW', h2.trans hβ', h3.trans hβW', h4.trans hβ', ?_⟩,
      reluBlock_expandResetParam₀ w'⟩
    rw [reluBlock_expandResetParam₀]
    exact lipschitzWith_expandResetMap₀.weaken hΛ
  · obtain ⟨h1, h2, h3, h4⟩ := expandResetParam₁_norms w'
    refine ⟨expandResetParam₁ w', ⟨h1.trans hβW', h2.trans hβ', h3.trans hβW', h4.trans hβ', ?_⟩,
      reluBlock_expandResetParam₁ w'⟩
    rw [reluBlock_expandResetParam₁]
    exact lipschitzWith_expandResetMap₁.weaken hΛ

@[blueprint "prop:relu-regimes-iii-lower"
  (statement := /-- \textbf{(`prop:relu-regimes`(iii), lower bound.)} For $m = 1$,
    $K = [0,1]$ with the clipping retraction, width $w \ge 4$, $\Lambda \ge 20$, and
    $\beta_W \ge 41$, $\beta \ge 2$ (at least the weight norms of the representations of the
    two expand-and-reset maps), the class $F_\Lambda$ contains $g_0, g_1$, which satisfy
    `cond:e2-pingpong` with two generators and separation $1/8$; hence
    $$N^{\mathrm{ext}}(B(k, F_\Lambda), d_\infty, \varepsilon) \ge 2^k
      \quad\text{for all } k \text{ and all } \varepsilon < 1/16 .$$
    (The paper states $w \ge 5$; the two maps have three interior breakpoints each, so width
    $4$ suffices.) -/)]
theorem prop_relu_regimes_iii_lower {w : ℕ} (hw : 4 ≤ w) {βW β Λ : ℝ≥0} (hβW : 41 ≤ βW)
    (hβ : 2 ≤ β) (hΛ : 20 ≤ Λ) (k : ℕ) {ε : ℝ≥0} (hε : ε < 1 / 16) :
    (2 : ℕ∞) ^ k ≤ externalCoveringNumber (X := UnifMaps (Icc (0 : ℝ) 1)) ε
      (wordBall (reluClass isProjectionOnto_clipUnit w βW β Λ) k) := by
  /-- Write $w = 4 + w'$; `lem:relu-er-pingpong` gives the bound for $\{g_0, g_1\}$, and
    $B(k, \{g_0,g_1\}) \subseteq B(k, F_\Lambda)$ by `lem:relu-er-mem-class`. -/
  obtain ⟨w', rfl⟩ : ∃ w', w = 4 + w' := ⟨w - 4, by omega⟩
  have h2ε : 2 * ε < 1 / 8 := by
    calc 2 * ε < 2 * (1 / 16) := by gcongr
      _ = 1 / 8 := by norm_num
  exact (expandReset_pingpong.1 k ε h2ε).trans (externalCoveringNumber_mono_set
    (wordBall_subset_wordBall_of_subset (range_erGen_subset_reluClass w' hβW hβ hΛ)))

end ExpandReset

end LeanDeepgen
