import Mathlib
import Architect
import LeanDeepgen.Setting.Covering
import LeanDeepgen.Profiles.Defs
import LeanDeepgen.Profiles.LogSplit
import FoML.ToMathlib.Misc

/-!
# Variance profiles from growth and diameter

Abstract form of the paper's Proposition `prop:profiles` (i)–(iv).  For a set `A` in a
pseudo-emetric space and a diameter `D ≥ 0`, the entropy integral is
`entropyIntegral D A = ∫_0^D √(log N(A, ε)) dε` (defined in `LeanDeepgen.Profiles.Defs`), where
`log N(A, ε) = metricEntropy ε A`.
In the paper, `V_k(S) = ∫_0^{D_k(S)} √(log N(B(k,F), d_S, ε)) dε` is
`entropyIntegral (empDiam S (wordBall F k)) (wordBall F k)` on the empirical space of the sample
`S`; the results below only use the abstract data (a family of sets `A k` and diameters `D k`).

The four profiles (saturation; polynomial growth with bounded diameter; exponential growth with
bounded diameter; polynomial growth with linearly growing diameter) are obtained from a single
comparison lemma `entropyIntegral_le_integral` (domination of the integrand by an integrable
majorant) and the log-splitting lemma of `LeanDeepgen.Profiles.LogSplit`.

Conventions: `metricEntropy ε A = log (N(A, ε)).toReal` is `0` when `N(A, ε) = ∞` (junk value)
or `A = ∅`; it is always nonnegative.  All hypotheses on covering numbers are stated through
`((coveringNumber ε A : ℝ≥0∞)).toReal`, exactly as in `metricEntropy`.
-/

open scoped NNReal ENNReal Real
open MeasureTheory Set intervalIntegral Metric

open FoML.ToMathlib

namespace LeanDeepgen

variable {Y : Type*} [PseudoEMetricSpace Y]

/-! ### Metric entropy: sign, monotonicity, measurability -/

@[blueprint "lem:metric-entropy-nonneg"
  (statement := /-- $\log N(A,\varepsilon) \ge 0$ for every $A$ and $\varepsilon$. -/)]
theorem metricEntropy_nonneg (ε : ℝ≥0) (A : Set Y) : 0 ≤ metricEntropy ε A :=
  log_toReal_toENNReal_nonneg _

@[blueprint "lem:metric-entropy-anti"
  (statement := /-- The metric entropy is antitone in the scale: if $\varepsilon \le \delta$ and
    $N(A,\varepsilon) < \infty$ then $\log N(A,\delta) \le \log N(A,\varepsilon)$. -/)]
theorem metricEntropy_anti {ε δ : ℝ≥0} {A : Set Y} (hε : coveringNumber ε A ≠ ⊤)
    (h : ε ≤ δ) :
    metricEntropy δ A ≤ metricEntropy ε A :=
  log_toReal_toENNReal_mono hε (coveringNumber_anti h)

@[blueprint "lem:sqrt-metric-entropy-measurable"
  (statement := /-- $\varepsilon \mapsto \sqrt{\log N(A, \varepsilon^+)}$ is a measurable
    function on $\mathbb R$ (it is the composition of the antitone map
    $\varepsilon \mapsto N(A,\varepsilon^+)$
    with measurable maps). -/)]
theorem measurable_sqrt_metricEntropy (A : Set Y) :
    Measurable fun ε : ℝ => √(metricEntropy ε.toNNReal A) := by
  /-- $\varepsilon \mapsto N(A, \varepsilon^+) \in [0,\infty]$ is antitone, hence measurable;
    compose with $x \mapsto x.\mathrm{toReal}$, $\log$ and $\sqrt{\cdot}$. -/
  have h1 : Antitone fun ε : ℝ => (coveringNumber ε.toNNReal A : ℝ≥0∞) := fun ε δ h =>
    ENat.toENNReal_le.2 (coveringNumber_anti (Real.toNNReal_le_toNNReal h))
  exact Real.continuous_sqrt.measurable.comp
    (Real.measurable_log.comp (ENNReal.measurable_toReal.comp h1.measurable))

/-! ### The entropy integral -/

@[blueprint "lem:entropy-integral-nonneg"
  (statement := /-- $\mathsf V(D, A) \ge 0$ for $D \ge 0$. -/)]
theorem entropyIntegral_nonneg {D : ℝ} (hD : 0 ≤ D) (A : Set Y) : 0 ≤ entropyIntegral D A :=
  integral_nonneg hD fun _ _ => Real.sqrt_nonneg _

@[blueprint "lem:sqrt-metric-entropy-integrable-of-le"
  (statement := /-- If $\sqrt{\log N(A,\varepsilon)} \le g(\varepsilon)$ on $(0, D]$ for an
    interval-integrable $g$ on $[0,D]$, then $\varepsilon \mapsto \sqrt{\log N(A,\varepsilon)}$ is
    interval-integrable on $[0,D]$. -/)]
theorem intervalIntegrable_sqrt_metricEntropy_of_le {A : Set Y} {D : ℝ} (hD : 0 ≤ D)
    {g : ℝ → ℝ} (hg : IntervalIntegrable g volume 0 D)
    (hle : ∀ ε ∈ Ioc 0 D, √(metricEntropy ε.toNNReal A) ≤ g ε) :
    IntervalIntegrable (fun ε : ℝ => √(metricEntropy ε.toNNReal A)) volume 0 D := by
  /-- The integrand is measurable and nonnegative, and dominated by $|g|$ on $(0,D]$. -/
  refine hg.mono_fun (measurable_sqrt_metricEntropy A).aestronglyMeasurable ?_
  rw [uIoc_of_le hD]
  refine ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => ?_
  dsimp only
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (hle x hx).trans (le_abs_self _)

@[blueprint "lem:sqrt-metric-entropy-integrable-of-pos"
  (statement := /-- For $0 < a \le D$ with $N(A, a) < \infty$, $\varepsilon \mapsto
    \sqrt{\log N(A,\varepsilon)}$ is interval-integrable on $[a, D]$ (it is antitone and bounded
    there). -/)]
theorem intervalIntegrable_sqrt_metricEntropy_of_pos {A : Set Y} {a D : ℝ} (_ha : 0 < a)
    (haD : a ≤ D) (hA : coveringNumber a.toNNReal A ≠ ⊤) :
    IntervalIntegrable (fun ε : ℝ => √(metricEntropy ε.toNNReal A)) volume a D := by
  /-- Antitone functions on a compact interval are interval-integrable. -/
  refine AntitoneOn.intervalIntegrable ?_
  rw [uIcc_of_le haD]
  intro x hx y hy hxy
  have hx' : coveringNumber x.toNNReal A ≠ ⊤ :=
    ne_top_of_le_ne_top hA (coveringNumber_anti (Real.toNNReal_le_toNNReal hx.1))
  exact Real.sqrt_le_sqrt (metricEntropy_anti hx' (Real.toNNReal_le_toNNReal hxy))

@[blueprint "lem:entropy-integral-mono-D"
  (statement := /-- $\mathsf V(D, A) \le \mathsf V(D', A)$ for $0 \le D \le D'$, provided the
    integrand is interval-integrable on $[0, D']$ (the integrand is nonnegative). -/)]
theorem entropyIntegral_mono {A : Set Y} {D D' : ℝ} (hD : 0 ≤ D) (hDD' : D ≤ D')
    (hint : IntervalIntegrable (fun ε : ℝ => √(metricEntropy ε.toNNReal A)) volume 0 D') :
    entropyIntegral D A ≤ entropyIntegral D' A :=
  integral_mono_interval le_rfl hD hDD' (Filter.Eventually.of_forall fun _ => Real.sqrt_nonneg _)
    hint

@[blueprint "lem:entropy-integral-le-integral"
  (statement := /-- If $\sqrt{\log N(A,\varepsilon)} \le g(\varepsilon)$ on $(0, D]$ for an
    interval-integrable $g$ on $[0, D]$, then $\mathsf V(D, A) \le \int_0^D g$. -/)]
theorem entropyIntegral_le_integral {A : Set Y} {D : ℝ} (hD : 0 ≤ D) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume 0 D)
    (hle : ∀ ε ∈ Ioc 0 D, √(metricEntropy ε.toNNReal A) ≤ g ε) :
    entropyIntegral D A ≤ ∫ ε in (0 : ℝ)..D, g ε := by
  /-- Monotonicity of the integral; the integrand is integrable by domination. -/
  exact integral_mono_on_of_le_Ioo hD (intervalIntegrable_sqrt_metricEntropy_of_le hD hg hle) hg
    fun x hx => hle x (Ioo_subset_Ioc_self hx)

@[blueprint "lem:entropy-integral-le-of-le"
  (statement := /-- Combined comparison: if $0 \le D \le \overline D$ and
    $\sqrt{\log N(A,\varepsilon)} \le g(\varepsilon)$ on $(0, \overline D]$ for an
    interval-integrable $g$ on $[0, \overline D]$, then
    $\mathsf V(D, A) \le \int_0^{\overline D} g$. -/)]
theorem entropyIntegral_le_integral_of_le {A : Set Y} {D D' : ℝ} (hD : 0 ≤ D) (hDD' : D ≤ D')
    {g : ℝ → ℝ} (hg : IntervalIntegrable g volume 0 D')
    (hle : ∀ ε ∈ Ioc 0 D', √(metricEntropy ε.toNNReal A) ≤ g ε) :
    entropyIntegral D A ≤ ∫ ε in (0 : ℝ)..D', g ε := by
  /-- $\mathsf V(D,A) \le \mathsf V(\overline D, A) \le \int_0^{\overline D} g$. -/
  exact (entropyIntegral_mono hD hDD'
    (intervalIntegrable_sqrt_metricEntropy_of_le (hD.trans hDD') hg hle)).trans
    (entropyIntegral_le_integral (hD.trans hDD') hg hle)

/-! ### Profile (i): saturation -/

@[blueprint "prop:profiles-i"
  (statement := /-- (Saturation.) Let $A_k$ be sets with diameters $0 \le D_k \le \overline D$ and
    $N(A_k, \varepsilon) \le N_\infty(\varepsilon)$ for all $k$ and $\varepsilon$, with
    $N_\infty(\varepsilon) < \infty$ for $\varepsilon > 0$ and
    $\mathsf V_\infty := \int_0^{\overline D} \sqrt{\log N_\infty(\varepsilon)}\,d\varepsilon
    < \infty$ (the integrand is interval-integrable).  Then
    $\mathsf V(D_k, A_k) \le \mathsf V_\infty$ for all $k$. -/)]
theorem profile_saturation {A : ℕ → Set Y} {D : ℕ → ℝ} {Dbar : ℝ}
    (hD0 : ∀ k, 0 ≤ D k) (hD : ∀ k, D k ≤ Dbar) {Ninf : ℝ≥0 → ℕ∞}
    (hN : ∀ k ε, coveringNumber ε (A k) ≤ Ninf ε)
    (hNtop : ∀ ε : ℝ≥0, 0 < ε → Ninf ε ≠ ⊤)
    (hint : IntervalIntegrable
      (fun ε : ℝ => √(Real.log (Ninf ε.toNNReal : ℝ≥0∞).toReal)) volume 0 Dbar)
    (k : ℕ) :
    entropyIntegral (D k) (A k) ≤
      ∫ ε in (0 : ℝ)..Dbar, √(Real.log (Ninf ε.toNNReal : ℝ≥0∞).toReal) := by
  /-- Both the integrand and the upper limit are dominated. -/
  refine entropyIntegral_le_integral_of_le (hD0 k) (hD k) hint fun ε hε => ?_
  exact Real.sqrt_le_sqrt
    (log_toReal_toENNReal_mono (hNtop _ (Real.toNNReal_pos.2 hε.1)) (hN k _))

/-! ### Profiles (ii) and (iv): polynomial growth -/

@[blueprint "lem:sqrt-metric-entropy-le-of-poly"
  (statement := /-- If $N(A, \varepsilon) \le C_0 (1 + k/\varepsilon)^{D}$ for $\varepsilon > 0$,
    with $C_0 \ge 1$, $D \ge 0$, then for $0 < \varepsilon \le \overline D$,
    $\sqrt{\log N(A,\varepsilon)} \le \sqrt{\log C_0} + \sqrt{D}\sqrt{\log(1 + k/\overline D)}
    + \sqrt{D}\sqrt{\log(\overline D/\varepsilon)}$. -/)]
theorem sqrt_metricEntropy_le_of_poly {A : Set Y} {Dbar C₀ Dd : ℝ} {k : ℕ} (hDbar : 0 < Dbar)
    (hC₀ : 1 ≤ C₀) (hDd : 0 ≤ Dd)
    (hN : ∀ ε : ℝ, 0 < ε →
      (coveringNumber ε.toNNReal A : ℝ≥0∞).toReal ≤ C₀ * (1 + k / ε) ^ Dd)
    {ε : ℝ} (hε : ε ∈ Ioc 0 Dbar) :
    √(metricEntropy ε.toNNReal A) ≤
      √(Real.log C₀) + √Dd * √(Real.log (1 + k / Dbar))
        + √Dd * √(Real.log (Dbar / ε)) := by
  /-- $\log N \le \log C_0 + D \log(1 + k/\varepsilon)
    \le \log C_0 + D\log(1 + k/\overline D) + D \log(\overline D/\varepsilon)$ by the
    log-splitting inequality, then $\sqrt{a+b+c} \le \sqrt a + \sqrt b + \sqrt c$. -/
  have hε0 : 0 < ε := hε.1
  have hb : 1 ≤ C₀ * (1 + k / ε) ^ Dd := by
    have h1 : 1 ≤ (1 + k / ε) ^ Dd :=
      Real.one_le_rpow (le_add_of_nonneg_right (by positivity)) hDd
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ C₀ * (1 + k / ε) ^ Dd := mul_le_mul hC₀ h1 zero_le_one (by linarith)
  have h2 : metricEntropy ε.toNNReal A ≤ Real.log (C₀ * (1 + k / ε) ^ Dd) := by
    unfold metricEntropy
    rcases eq_or_lt_of_le
        (ENNReal.toReal_nonneg : 0 ≤ (coveringNumber ε.toNNReal A : ℝ≥0∞).toReal)
      with h0 | h0
    · rw [← h0, Real.log_zero]; exact Real.log_nonneg hb
    · exact Real.log_le_log h0 (hN ε hε0)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow (by positivity)] at h2
  have h3 := log_one_add_div_le hDbar (Nat.cast_nonneg k) hε0 hε.2
  have h4 : Dd * Real.log (1 + k / ε) ≤ Dd * (Real.log (1 + k / Dbar) + Real.log (Dbar / ε)) :=
    mul_le_mul_of_nonneg_left h3 hDd
  have h5 : metricEntropy ε.toNNReal A ≤
      Real.log C₀ + Dd * Real.log (1 + k / Dbar) + Dd * Real.log (Dbar / ε) := by linarith
  calc √(metricEntropy ε.toNNReal A)
      ≤ √(Real.log C₀ + Dd * Real.log (1 + k / Dbar) + Dd * Real.log (Dbar / ε)) :=
        Real.sqrt_le_sqrt h5
    _ ≤ √(Real.log C₀) + √(Dd * Real.log (1 + k / Dbar)) + √(Dd * Real.log (Dbar / ε)) :=
        sqrt_add_add_le _ _ _
    _ = _ := by rw [Real.sqrt_mul hDd, Real.sqrt_mul hDd]

@[blueprint "lem:entropy-integral-le-of-poly"
  (statement := /-- (Polynomial growth, bounded diameter; single-set form.) If
    $0 \le D \le \overline D$, $\overline D > 0$, $C_0 \ge 1$, $D \ge 0$ (the exponent) and
    $N(A, \varepsilon) \le C_0 (1 + k/\varepsilon)^{D}$ for all $\varepsilon > 0$, then
    $\mathsf V(D, A) \le \overline D\sqrt{D}\bigl(\sqrt{\log(1 + k/\overline D)}
    + \tfrac{\sqrt\pi}{2}\bigr) + \overline D\sqrt{\log C_0}$. -/)]
theorem entropyIntegral_le_of_poly {A : Set Y} {D Dbar C₀ Dd : ℝ} {k : ℕ} (hD0 : 0 ≤ D)
    (hD : D ≤ Dbar) (hDbar : 0 < Dbar) (hC₀ : 1 ≤ C₀) (hDd : 0 ≤ Dd)
    (hN : ∀ ε : ℝ, 0 < ε →
      (coveringNumber ε.toNNReal A : ℝ≥0∞).toReal ≤ C₀ * (1 + k / ε) ^ Dd) :
    entropyIntegral D A ≤
      Dbar * √Dd * (√(Real.log (1 + k / Dbar)) + √π / 2) + Dbar * √(Real.log C₀) := by
  /-- Integrate the pointwise bound over $(0, \overline D]$ and use
    $\int_0^{\overline D} \sqrt{\log(\overline D/\varepsilon)}\,d\varepsilon
    = \tfrac{\sqrt\pi}{2}\overline D$. -/
  have hgint : IntervalIntegrable
      (fun ε : ℝ => √(Real.log C₀) + √Dd * √(Real.log (1 + k / Dbar))
        + √Dd * √(Real.log (Dbar / ε))) volume 0 Dbar :=
    (intervalIntegrable_const.add intervalIntegrable_const).add
      ((intervalIntegrable_sqrt_log_div hDbar).const_mul _)
  refine (entropyIntegral_le_integral_of_le hD0 hD hgint
    fun ε hε => sqrt_metricEntropy_le_of_poly hDbar hC₀ hDd hN hε).trans (le_of_eq ?_)
  rw [intervalIntegral.integral_add (intervalIntegrable_const.add intervalIntegrable_const)
      ((intervalIntegrable_sqrt_log_div hDbar).const_mul _),
    intervalIntegral.integral_add intervalIntegrable_const intervalIntegrable_const,
    intervalIntegral.integral_const, intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, integral_sqrt_log_div hDbar]
  simp only [smul_eq_mul, sub_zero]
  ring

@[blueprint "prop:profiles-ii"
  (statement := /-- (Polynomial growth, bounded diameter.) If $0 \le D_k \le \overline D$,
    $\overline D > 0$, and $N(A_k, \varepsilon) \le C_0 (1 + k/\varepsilon)^{D}$ for all
    $k \ge 1$ and $\varepsilon > 0$ (with $C_0 \ge 1$, $D \ge 0$), then for $k \ge 1$
    \[
      \mathsf V(D_k, A_k) \le \overline D\sqrt{D}\Bigl(\sqrt{\log(1 + k/\overline D)}
      + \tfrac{\sqrt\pi}{2}\Bigr) + \overline D\sqrt{\log C_0} = O\bigl(\sqrt{D \log k}\bigr).
    \] -/)]
theorem profile_poly_bounded {A : ℕ → Set Y} {D : ℕ → ℝ} {Dbar C₀ Dd : ℝ}
    (hD0 : ∀ k, 0 ≤ D k) (hD : ∀ k, D k ≤ Dbar) (hDbar : 0 < Dbar) (hC₀ : 1 ≤ C₀)
    (hDd : 0 ≤ Dd)
    (hN : ∀ k, 1 ≤ k → ∀ ε : ℝ, 0 < ε →
      (coveringNumber ε.toNNReal (A k) : ℝ≥0∞).toReal ≤ C₀ * (1 + k / ε) ^ Dd)
    {k : ℕ} (hk : 1 ≤ k) :
    entropyIntegral (D k) (A k) ≤
      Dbar * √Dd * (√(Real.log (1 + k / Dbar)) + √π / 2) + Dbar * √(Real.log C₀) :=
  entropyIntegral_le_of_poly (hD0 k) (hD k) hDbar hC₀ hDd (hN k hk)

@[blueprint "prop:profiles-iv"
  (statement := /-- (Polynomial growth, linearly growing diameter.) If $0 \le D_k \le D_1 k$
    with $D_1 > 0$, and $N(A_k, \varepsilon) \le C_0 (1 + k/\varepsilon)^{D}$ for all $k \ge 1$
    and $\varepsilon > 0$ (with $C_0 \ge 1$, $D \ge 0$), then for $k \ge 1$
    \[
      \mathsf V(D_k, A_k) \le D_1 k\Bigl(\sqrt{D}\bigl(\sqrt{\log(1 + 1/D_1)}
      + \tfrac{\sqrt\pi}{2}\bigr) + \sqrt{\log C_0}\Bigr) = O(k\sqrt D).
    \] -/)]
theorem profile_poly_linear {A : ℕ → Set Y} {D : ℕ → ℝ} {D₁ C₀ Dd : ℝ}
    (hD0 : ∀ k, 0 ≤ D k) (hD : ∀ k, D k ≤ D₁ * k) (hD₁ : 0 < D₁) (hC₀ : 1 ≤ C₀)
    (hDd : 0 ≤ Dd)
    (hN : ∀ k, 1 ≤ k → ∀ ε : ℝ, 0 < ε →
      (coveringNumber ε.toNNReal (A k) : ℝ≥0∞).toReal ≤ C₀ * (1 + k / ε) ^ Dd)
    {k : ℕ} (hk : 1 ≤ k) :
    entropyIntegral (D k) (A k) ≤
      D₁ * k * (√Dd * (√(Real.log (1 + 1 / D₁)) + √π / 2) + √(Real.log C₀)) := by
  /-- Apply the bounded-diameter estimate with $\overline D = D_1 k$ and simplify
    $k/(D_1 k) = 1/D_1$. -/
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hDk : 0 < D₁ * k := by positivity
  have hdiv : (k : ℝ) / (D₁ * k) = 1 / D₁ := by field_simp
  calc entropyIntegral (D k) (A k)
      ≤ D₁ * k * √Dd * (√(Real.log (1 + k / (D₁ * k))) + √π / 2)
          + D₁ * k * √(Real.log C₀) :=
        entropyIntegral_le_of_poly (hD0 k) (hD k) hDk hC₀ hDd (hN k hk)
    _ = _ := by rw [hdiv]; ring

/-! ### Profile (iii): exponential growth -/

@[blueprint "prop:profiles-iii"
  (statement := /-- (Exponential growth, bounded diameter.) If $0 \le D_k \le \overline D$ and
    $\log N(A_k, \varepsilon) \le \alpha k + \psi(\varepsilon)$ for all $k$ and $\varepsilon > 0$,
    with $\Psi := \int_0^{\overline D} \sqrt{\psi(\varepsilon)}\,d\varepsilon < \infty$
    (i.e. $\sqrt\psi$ is interval-integrable on $[0,\overline D]$), then
    $\mathsf V(D_k, A_k) \le \overline D\sqrt{\alpha k} + \Psi = O(\sqrt k)$. -/)]
theorem profile_exp_bounded {A : ℕ → Set Y} {D : ℕ → ℝ} {Dbar α : ℝ} {ψ : ℝ → ℝ}
    (hD0 : ∀ k, 0 ≤ D k) (hD : ∀ k, D k ≤ Dbar)
    (hΨ : IntervalIntegrable (fun ε => √(ψ ε)) volume 0 Dbar)
    (hN : ∀ k, ∀ ε : ℝ, 0 < ε → metricEntropy ε.toNNReal (A k) ≤ α * k + ψ ε)
    (k : ℕ) :
    entropyIntegral (D k) (A k) ≤ Dbar * √(α * k) + ∫ ε in (0 : ℝ)..Dbar, √(ψ ε) := by
  /-- $\sqrt{\log N_k(\varepsilon)} \le \sqrt{\alpha k} + \sqrt{\psi(\varepsilon)}$; integrate. -/
  have hgint : IntervalIntegrable (fun ε : ℝ => √(α * k) + √(ψ ε)) volume 0 Dbar :=
    intervalIntegrable_const.add hΨ
  refine (entropyIntegral_le_integral_of_le (hD0 k) (hD k) hgint fun ε hε =>
    (Real.sqrt_le_sqrt (hN k ε hε.1)).trans (sqrt_add_le _ _)).trans (le_of_eq ?_)
  rw [intervalIntegral.integral_add intervalIntegrable_const hΨ, intervalIntegral.integral_const]
  simp only [smul_eq_mul, sub_zero]

@[blueprint "prop:profiles-finite"
  (statement := /-- (Finite classes.) If $|A_k| \le r^{k+1}$ and $0 \le D_k \le \overline D$, then
    $N(A_k, \varepsilon) \le r^{k+1}$ at every scale and
    $\mathsf V(D_k, A_k) \le \overline D\sqrt{(k+1)\log r}$. -/)]
theorem profile_finite {A : ℕ → Set Y} {D : ℕ → ℝ} {Dbar : ℝ} {r : ℕ}
    (hD0 : ∀ k, 0 ≤ D k) (hD : ∀ k, D k ≤ Dbar)
    (hA : ∀ k, (A k).encard ≤ (r : ℕ∞) ^ (k + 1)) (k : ℕ) :
    entropyIntegral (D k) (A k) ≤ Dbar * √((k + 1) * Real.log r) := by
  /-- $N(A_k,\varepsilon) \le |A_k| \le r^{k+1}$, so $\log N(A_k, \varepsilon) \le (k+1)\log r$;
    integrate the constant bound. -/
  have hle : ∀ ε ∈ Ioc 0 Dbar,
      √(metricEntropy ε.toNNReal (A k)) ≤ √((k + 1) * Real.log r) := by
    intro ε _
    refine Real.sqrt_le_sqrt ?_
    have h1 : coveringNumber ε.toNNReal (A k) ≤ ((r ^ (k + 1) : ℕ) : ℕ∞) := by
      rw [Nat.cast_pow]; exact (coveringNumber_le_encard_self _).trans (hA k)
    have h2 := log_toReal_toENNReal_mono (ENat.coe_ne_top _) h1
    rw [ENat.toENNReal_coe, ENNReal.toReal_natCast, Nat.cast_pow, Real.log_pow] at h2
    exact h2.trans (le_of_eq (by push_cast; ring))
  refine (entropyIntegral_le_integral_of_le (hD0 k) (hD k) intervalIntegrable_const hle).trans
    (le_of_eq ?_)
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul, sub_zero]

end LeanDeepgen
