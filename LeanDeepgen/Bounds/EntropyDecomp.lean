import Mathlib
import Architect
import FoML
import LeanDeepgen.Setting.Metrics
import LeanDeepgen.Setting.Covering
import LeanDeepgen.Setting.Hypothesis
import LeanDeepgen.Setting.Rademacher
import LeanDeepgen.Setting.Assumptions
import FoML.ToMathlib.Misc
import FoML.ToMathlib.SqrtLogIntegral

/-!
# Deterministic entropy decomposition

Assumptions `ass:ent-readout`, `ass:ent-transition` and Theorem `thm:rad.decomp.ent.ent`
(Appendix D): a bound on `R̂_S(H ∘ F)` in terms of the sup-norm covering numbers of the
output-layer class `H` and the `d_∞` covering numbers of the hidden class `F`, without any
sub-Gaussian increment condition.

All results are fully proved. The main theorem `rad_decomp_ent_ent` (`thm:rad.decomp.ent.ent`)
is the paper's statement up to two deviations explained in its docstring: an integrability
hypothesis on the entropy integrand (with Lean's convention that a non-integrable function has
integral `0` the paper's form is false as transcribed), and the scales `x/4`, `x/(4 L_H)` on
`[0, B_H/2]` in place of `ε/2`, `ε/(2 L_H)` on `[0, 2 B_H]` (the price of converting the external
closed-ball covering numbers of the assumptions into the internal open-ball covers of FoML's
Dudley bound). Contents:

* `lem:comp-cover`, `lem:ent-composition-covering`, `lem:ent-composition-entropy`: the composition
  covering lemma `N(H ∘ F, ‖·‖_∞, ε) ≤ N(H, ε/2) · N(F, ε/(2 L_H))` and its entropy form;
* `lem:totallyBounded-empiricalFunctionSpace`, `lem:foml-covering-le-external-unifFun`: the bridge
  from uniform external covering numbers to FoML's `EmpiricalFunctionSpace` (metric `‖·‖_S`);
* `thm:rad.decomp.ent.ent-foml`: for `0 < ε < B_H/2`,
  `R̂_S(H ∘ F) ≤ 4ε + (12/√n) ∫_ε^{B_H/2} (𝓔_H(x/4) + 𝓔_F(x/(4 L_H))) dx`
  (fully proved from FoML's `dudley_entropy_integral'`);
* `thm:rad.decomp.ent.ent`: the `ε → 0` form under an integrability hypothesis.

Covering numbers are Mathlib's `Metric.externalCoveringNumber` (closed balls, `ℕ∞`-valued) in
the pseudo-emetric spaces `UnifFun X = X →ᵤ ℝ` (sup distance on real-valued functions) and
`UnifMaps X = X →ᵤ X` (uniform distance `d_∞` on self-maps, from `LeanDeepgen.Setting.Metrics`).
The space `UnifFun X`, the assumptions `EntReadout`, `EntTransition` and the root entropies
`entH`, `entF` are defined in `LeanDeepgen.Setting.Assumptions`.

The empirical-metric version (assumptions only on the sample: `H` Lipschitz on the reachable
points `{f(x_i)}`, `F` covered in `d_S`, `H` covered in `‖·‖_{f ∘ S}` uniformly in `f ∈ F`;
PLAN.md W8) is `LeanDeepgen.Bounds.EntropyDecompSample` (`thm:rad.decomp.ent.ent-sample`), which
also recovers this theorem up to a factor `2` in the scale of `F`
(`cor:rad.decomp.ent.ent-of-sample`).
-/

open scoped NNReal ENNReal UniformConvergence

open FoML.ToMathlib

namespace LeanDeepgen

variable {X : Type*} [PseudoMetricSpace X]

section CompositionCover

open Metric

variable {H : Set (X → ℝ)} {F : Set (X → X)} {LH : ℝ≥0}

@[blueprint "lem:comp-cover"
  (statement := /-- \textbf{Composition of covers.} Let every $h \in H$ be $L_H$-Lipschitz, let
    $C_H$ be an $r_1$-cover of $H$ for $\|\cdot\|_\infty$ and $C_F$ an $r_2$-cover of $F$ for
    $d_\infty$ (centres anywhere). Then $\{h_a \circ f_b : h_a \in C_H, f_b \in C_F\}$ is an
    $(r_1 + L_H r_2)$-cover of $H \circ F$ for $\|\cdot\|_\infty$:
    $|h(f(x)) - h_a(f_b(x))| \le |h(f(x)) - h(f_b(x))| + |h(f_b(x)) - h_a(f_b(x))|
    \le L_H d_\infty(f, f_b) + \|h - h_a\|_\infty$. -/)]
theorem isCover_compClass (hlip : ∀ h ∈ H, LipschitzWith LH h) {r₁ r₂ : ℝ≥0}
    {CH : Set (X → ℝ)} {CF : Set (X → X)} (hCH : IsCover (X := UnifFun X) r₁ H CH)
    (hCF : IsCover (X := UnifMaps X) r₂ F CF) :
    IsCover (X := UnifFun X) (r₁ + LH * r₂) (compClass H F)
      (Set.image2 (fun (h : X → ℝ) (f : X → X) => h ∘ f) CH CF) := by
  rintro _ ⟨h, hh, f, hf, rfl⟩
  obtain ⟨ha, hha, hdh⟩ := hCH hh
  obtain ⟨fb, hfb, hdf⟩ := hCF hf
  refine ⟨ha ∘ fb, Set.mem_image2_of_mem hha hfb, ?_⟩
  change edist (toUnifFun (h ∘ f)) (toUnifFun (ha ∘ fb)) ≤ _
  have hdh' : ∀ x, edist (h x) (ha x) ≤ r₁ := fun x =>
    (le_iSup (fun x => edist (h x) (ha x)) x).trans hdh
  have hdf' : ∀ x, edist (f x) (fb x) ≤ r₂ := fun x =>
    (le_iSup (fun x => edist (f x) (fb x)) x).trans hdf
  rw [edist_toUnifFun]
  refine iSup_le fun x => ?_
  calc edist (h (f x)) (ha (fb x))
      ≤ edist (h (f x)) (h (fb x)) + edist (h (fb x)) (ha (fb x)) := edist_triangle _ _ _
    _ ≤ LH * edist (f x) (fb x) + edist (h (fb x)) (ha (fb x)) := by
        gcongr
        exact (hlip h hh).edist_le_mul _ _
    _ ≤ LH * r₂ + r₁ := by
        gcongr
        · exact hdf' x
        · exact hdh' (fb x)
    _ = ((r₁ + LH * r₂ : ℝ≥0) : ℝ≥0∞) := by
        push_cast
        ring

@[blueprint "lem:ent-composition-covering-mul"
  (statement := /-- For $L_H$-Lipschitz $H$ and radii $r_1, r_2 \ge 0$,
    $N^{\mathrm{ext}}(H \circ F, \|\cdot\|_\infty, r_1 + L_H r_2)
    \le N^{\mathrm{ext}}(H, \|\cdot\|_\infty, r_1) \cdot
    N^{\mathrm{ext}}(F, d_\infty, r_2)$. -/)]
theorem externalCoveringNumber_compClass_le (hlip : ∀ h ∈ H, LipschitzWith LH h)
    (r₁ r₂ : ℝ≥0) :
    externalCoveringNumber (X := UnifFun X) (r₁ + LH * r₂) (compClass H F) ≤
      externalCoveringNumber (X := UnifFun X) r₁ H *
        externalCoveringNumber (X := UnifMaps X) r₂ F := by
  obtain ⟨CH, hCH, hCHe⟩ := exists_isCover_encard_eq_externalCoveringNumber (X := UnifFun X) r₁ H
  obtain ⟨CF, hCF, hCFe⟩ := exists_isCover_encard_eq_externalCoveringNumber (X := UnifMaps X) r₂ F
  rw [← hCHe, ← hCFe]
  refine (isCover_compClass hlip hCH hCF).externalCoveringNumber_le_encard.trans ?_
  rw [← Set.image_prod]
  exact (Set.encard_image_le _ _).trans Set.encard_prod.le

@[blueprint "lem:ent-composition-covering"
  (statement := /-- \textbf{Composition covering lemma.} If every $h \in H$ is $L_H$-Lipschitz then
    for every $\varepsilon \ge 0$,
    $$N^{\mathrm{ext}}(H \circ F, \|\cdot\|_\infty, \varepsilon) \le
    N^{\mathrm{ext}}(H, \|\cdot\|_\infty, \varepsilon/2)\cdot
    N^{\mathrm{ext}}(F, d_\infty, \varepsilon/(2L_H)).$$
    (For $L_H = 0$ the second radius is $0$ by the convention $x/0 = 0$, and the inequality still
    holds.) -/)]
theorem externalCoveringNumber_compClass_le_mul (hlip : ∀ h ∈ H, LipschitzWith LH h) (ε : ℝ≥0) :
    externalCoveringNumber (X := UnifFun X) ε (compClass H F) ≤
      externalCoveringNumber (X := UnifFun X) (ε / 2) H *
        externalCoveringNumber (X := UnifMaps X) (ε / (2 * LH)) F := by
  refine (externalCoveringNumber_anti ?_).trans
    (externalCoveringNumber_compClass_le hlip (ε / 2) (ε / (2 * LH)))
  rcases eq_or_ne LH 0 with hLH | hLH
  · subst hLH
    simp only [zero_mul, add_zero]
    exact half_le_self zero_le
  · rw [show LH * (ε / (2 * LH)) = ε / 2 by
      rw [mul_div_assoc', mul_comm, mul_div_mul_right _ _ hLH]]
    rw [add_halves]

omit [PseudoMetricSpace X] in
@[blueprint "lem:entH-nonneg"
  (statement := /-- $\mathcal E_H(u) \ge 0$. -/)]
theorem entH_nonneg (H : Set (X → ℝ)) (u : ℝ) : 0 ≤ entH H u := Real.sqrt_nonneg _

@[blueprint "lem:entF-nonneg"
  (statement := /-- $\mathcal E_F(v) \ge 0$. -/)]
theorem entF_nonneg (F : Set (X → X)) (v : ℝ) : 0 ≤ entF F v := Real.sqrt_nonneg _

@[blueprint "lem:log-enat-le-of-le-mul"
  (statement := /-- If $c \le a\, b$ in $\mathbb N \cup \{\infty\}$ with $a, b < \infty$, then
    $\log c \le \log a + \log b$ (with $\log 0 = 0$; all three logarithms are
    $\ge 0$). -/)]
theorem log_toReal_le_of_le_mul {a b c : ℕ∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hc : c ≤ a * b) :
    Real.log (c : ℝ≥0∞).toReal ≤ Real.log (a : ℝ≥0∞).toReal + Real.log (b : ℝ≥0∞).toReal := by
  obtain ⟨a', rfl⟩ := ENat.ne_top_iff_exists.mp ha
  obtain ⟨b', rfl⟩ := ENat.ne_top_iff_exists.mp hb
  have hc' : c ≠ ⊤ := ne_top_of_le_ne_top (by exact_mod_cast ENat.coe_ne_top _) hc
  obtain ⟨c', rfl⟩ := ENat.ne_top_iff_exists.mp hc'
  have hcab : c' ≤ a' * b' := by exact_mod_cast hc
  simp only [ENat.toENNReal_coe, ENNReal.toReal_natCast]
  rcases Nat.eq_zero_or_pos c' with rfl | hcpos
  · simp only [Nat.cast_zero, Real.log_zero]
    exact add_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  · have ha' : (a' : ℝ) ≠ 0 := by
      rcases Nat.eq_zero_or_pos a' with rfl | h
      · simp at hcab; omega
      · exact_mod_cast h.ne'
    have hb' : (b' : ℝ) ≠ 0 := by
      rcases Nat.eq_zero_or_pos b' with rfl | h
      · simp at hcab; omega
      · exact_mod_cast h.ne'
    rw [← Real.log_mul ha' hb']
    exact Real.log_le_log (by exact_mod_cast hcpos) (by exact_mod_cast hcab)

@[blueprint "lem:ent-composition-entropy"
  (statement := /-- \textbf{Entropy of the composition class.} Let every $h \in H$ be
    $L_H$-Lipschitz with $L_H > 0$, and let $\varepsilon \in \mathbb R$ be such that
    $N^{\mathrm{ext}}(H, \|\cdot\|_\infty, \varepsilon/2)$ and
    $N^{\mathrm{ext}}(F, d_\infty, \varepsilon/(2L_H))$ are finite. Then
    $$\sqrt{\log N^{\mathrm{ext}}(H \circ F, \|\cdot\|_\infty, \varepsilon)}
    \le \mathcal E_H(\varepsilon/2) + \mathcal E_F(\varepsilon/(2L_H)).$$ -/)]
theorem sqrt_log_compClass_le (hlip : ∀ h ∈ H, LipschitzWith LH h) (hLH : 0 < LH) {ε : ℝ}
    (hHfin : externalCoveringNumber (X := UnifFun X) (Real.toNNReal (ε / 2)) H ≠ ⊤)
    (hFfin : externalCoveringNumber (X := UnifMaps X) (Real.toNNReal (ε / (2 * LH))) F ≠ ⊤) :
    Real.sqrt (Real.log
        (externalCoveringNumber (X := UnifFun X) (Real.toNNReal ε) (compClass H F) : ℝ≥0∞).toReal)
      ≤ entH H (ε / 2) + entF F (ε / (2 * LH)) := by
  have h1 : Real.toNNReal ε / 2 = Real.toNNReal (ε / 2) := by
    rw [Real.toNNReal_div' (by norm_num), Real.toNNReal_ofNat]
  have h2 : Real.toNNReal ε / (2 * LH) = Real.toNNReal (ε / (2 * LH)) := by
    rw [Real.toNNReal_div' (by positivity), Real.toNNReal_mul (by norm_num), Real.toNNReal_ofNat,
      Real.toNNReal_coe]
  have hc := externalCoveringNumber_compClass_le_mul (F := F) hlip (Real.toNNReal ε)
  rw [h1, h2] at hc
  refine (Real.sqrt_le_sqrt (log_toReal_le_of_le_mul hHfin hFfin hc)).trans ?_
  exact sqrt_add_le _ _

end CompositionCover

section FoMLBridge

variable (S : Fin n → X)

omit [PseudoMetricSpace X] in
@[blueprint "lem:empiricalDist-le-edist-unifFun"
  (statement := /-- FoML's empirical distance is dominated by the uniform distance:
    $\|u - v\|_S \le \|u - v\|_\infty$ whenever the latter is finite ($n \ge 1$). -/)]
theorem empiricalDist_le_toReal_edist (hn : 0 < n) (u v : X → ℝ)
    (h : edist (toUnifFun u) (toUnifFun v) ≠ ⊤) :
    empiricalDist S u v ≤ (edist (toUnifFun u) (toUnifFun v)).toReal := by
  refine empiricalDist_le_of_abs_sub_le hn S u v ENNReal.toReal_nonneg fun k => ?_
  rw [← Real.dist_eq, dist_edist]
  exact ENNReal.toReal_mono h (le_iSup (fun x => edist (u x) (v x)) (S k))

omit [PseudoMetricSpace X] in
@[blueprint "lem:totallyBounded-empiricalFunctionSpace"
  (statement := /-- If $G \subseteq \mathbb R^{\mathcal X}$ is nonempty with finite uniform
    covering numbers $N^{\mathrm{ext}}(G, \|\cdot\|_\infty, r) < \infty$ for all $r > 0$, then
    $G$ is totally bounded for the empirical pseudometric $\|\cdot\|_S$ (FoML's
    `EmpiricalFunctionSpace`), $n \ge 1$. -/)]
theorem totallyBounded_empiricalFunctionSpace (hn : 0 < n) (G : Set (X → ℝ)) [Nonempty G]
    (hG : ∀ r : ℝ≥0, 0 < r → Metric.externalCoveringNumber (X := UnifFun X) r G ≠ ⊤) :
    TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace (fun g : G => (g : X → ℝ)) S)) := by
  /-- A finite internal closed $(\varepsilon/2)$-cover for $\|\cdot\|_\infty$ (which exists since
    $N(G, 2r) \le N^{\mathrm{ext}}(G, r) < \infty$) is a finite open $\varepsilon$-cover for
    $\|\cdot\|_S$. -/
  classical
  rw [Metric.totallyBounded_iff]
  intro ε hε
  set r : ℝ≥0 := Real.toNNReal (ε / 4) with hr
  have hrpos : 0 < r := Real.toNNReal_pos.mpr (by positivity)
  have hcov : Metric.coveringNumber (X := UnifFun X) (2 * r) G ≠ ⊤ :=
    ne_top_of_le_ne_top (hG r hrpos)
      (Metric.coveringNumber_two_mul_le_externalCoveringNumber (X := UnifFun X) r G)
  obtain ⟨C, hCG, hCfin, hCcov, -⟩ :=
    Metric.exists_set_encard_eq_coveringNumber (X := UnifFun X) hcov
  let φ : UnifFun X → EmpiricalFunctionSpace (fun g : G => (g : X → ℝ)) S := fun c =>
    if hc : c ∈ G then ⟨⟨c, hc⟩⟩ else Classical.arbitrary _
  refine ⟨φ '' C, hCfin.image φ, fun q _ => ?_⟩
  obtain ⟨c, hcC, hqc⟩ := hCcov q.index.2
  simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop]
  refine ⟨φ c, Set.mem_image_of_mem φ hcC, ?_⟩
  have hcG : c ∈ G := hCG hcC
  simp only [φ]
  rw [dif_pos hcG]
  change empiricalDist S (q.index : X → ℝ) c < ε
  have hqc' : edist (toUnifFun (q.index : X → ℝ)) (toUnifFun c) ≤ ((2 * r : ℝ≥0) : ℝ≥0∞) := hqc
  have h2r : ((2 * r : ℝ≥0) : ℝ) = ε / 2 := by
    rw [hr]; push_cast; rw [Real.coe_toNNReal _ (by positivity)]; ring
  calc empiricalDist S (q.index : X → ℝ) c
      ≤ (edist (toUnifFun (q.index : X → ℝ)) (toUnifFun c)).toReal :=
        empiricalDist_le_toReal_edist S hn _ _ (ne_top_of_le_ne_top ENNReal.coe_ne_top hqc')
    _ ≤ ((2 * r : ℝ≥0) : ℝ) := by
        rw [← ENNReal.coe_toReal]
        exact ENNReal.toReal_mono ENNReal.coe_ne_top hqc'
    _ = ε / 2 := h2r
    _ < ε := by linarith

omit [PseudoMetricSpace X] in
@[blueprint "lem:foml-covering-le-external-unifFun"
  (statement := /-- \textbf{FoML covering numbers versus uniform external covering numbers.} Let
    $G \subseteq \mathbb R^{\mathcal X}$ be nonempty and totally bounded for $\|\cdot\|_S$, and
    let $0 \le 2r < x$. Then FoML's open-ball covering number of $G$ for $\|\cdot\|_S$ satisfies
    $N^{\mathrm{open}}_S(G, x) \le N(G, \|\cdot\|_\infty, 2r) \le
    N^{\mathrm{ext}}(G, \|\cdot\|_\infty, r)$ (internal closed $2r$-balls for the sup norm
    with centres in $G$ are contained in open $x$-balls for $\|\cdot\|_S$). -/)]
theorem coveringNumber_empiricalFunctionSpace_le (hn : 0 < n) (G : Set (X → ℝ)) [Nonempty G]
    (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace (fun g : G => (g : X → ℝ)) S)))
    {x : ℝ} {r : ℝ≥0} (hr : 2 * (r : ℝ) < x) :
    (coveringNumber h' x : ℕ∞) ≤ Metric.externalCoveringNumber (X := UnifFun X) r G := by
  classical
  by_cases htop : Metric.externalCoveringNumber (X := UnifFun X) r G = ⊤
  · rw [htop]; exact le_top
  have hcov : Metric.coveringNumber (X := UnifFun X) (2 * r) G ≠ ⊤ :=
    ne_top_of_le_ne_top htop
      (Metric.coveringNumber_two_mul_le_externalCoveringNumber (X := UnifFun X) r G)
  obtain ⟨C, hCG, hCfin, hCcov, hCe⟩ :=
    Metric.exists_set_encard_eq_coveringNumber (X := UnifFun X) hcov
  have hx : 0 < x := lt_of_le_of_lt (by positivity) hr
  let φ : UnifFun X → EmpiricalFunctionSpace (fun g : G => (g : X → ℝ)) S := fun c =>
    if hc : c ∈ G then ⟨⟨c, hc⟩⟩ else Classical.arbitrary _
  have hcover : (Set.univ : Set (EmpiricalFunctionSpace (fun g : G => (g : X → ℝ)) S)) ⊆
      ⋃ y ∈ hCfin.toFinset.image φ, Metric.ball y x := by
    intro q _
    obtain ⟨c, hcC, hqc⟩ := hCcov q.index.2
    simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop, Finset.mem_image]
    refine ⟨φ c, ⟨c, hCfin.mem_toFinset.mpr hcC, rfl⟩, ?_⟩
    have hcG : c ∈ G := hCG hcC
    simp only [φ]
    rw [dif_pos hcG]
    change empiricalDist S (q.index : X → ℝ) c < x
    have hqc' : edist (toUnifFun (q.index : X → ℝ)) (toUnifFun c) ≤ ((2 * r : ℝ≥0) : ℝ≥0∞) := hqc
    calc empiricalDist S (q.index : X → ℝ) c
        ≤ (edist (toUnifFun (q.index : X → ℝ)) (toUnifFun c)).toReal :=
          empiricalDist_le_toReal_edist S hn _ _ (ne_top_of_le_ne_top ENNReal.coe_ne_top hqc')
      _ ≤ ((2 * r : ℝ≥0) : ℝ) := by
          rw [← ENNReal.coe_toReal]
          exact ENNReal.toReal_mono ENNReal.coe_ne_top hqc'
      _ < x := by push_cast; exact hr
  have h1 := coveringNumber_le_card_of_cover h' hx _ hcover
  calc (coveringNumber h' x : ℕ∞) ≤ ((hCfin.toFinset.image φ).card : ℕ∞) := by exact_mod_cast h1
    _ ≤ (hCfin.toFinset.card : ℕ∞) := by exact_mod_cast Finset.card_image_le
    _ = C.encard := hCfin.encard_eq_coe_toFinset_card.symm
    _ = Metric.coveringNumber (X := UnifFun X) (2 * r) G := hCe
    _ ≤ _ := Metric.coveringNumber_two_mul_le_externalCoveringNumber (X := UnifFun X) r G

end FoMLBridge

section Antitone

omit [PseudoMetricSpace X] in
@[blueprint "lem:entH-antitone"
  (statement := /-- If $H \ne \emptyset$ has finite uniform covering numbers at every positive
    scale, then $u \mapsto \mathcal E_H(u)$ is antitone on $(0, \infty)$. -/)]
theorem antitoneOn_entH (H : Set (X → ℝ)) (hne : H.Nonempty)
    (hfin : ∀ r : ℝ≥0, 0 < r → Metric.externalCoveringNumber (X := UnifFun X) r H ≠ ⊤) :
    AntitoneOn (entH H) (Set.Ioi 0) := by
  intro a ha b hb hab
  have hb' : 0 < Real.toNNReal b := Real.toNNReal_pos.mpr hb
  have ha' : 0 < Real.toNNReal a := Real.toNNReal_pos.mpr ha
  obtain ⟨ma, hma⟩ := ENat.ne_top_iff_exists.mp (hfin _ ha')
  obtain ⟨mb, hmb⟩ := ENat.ne_top_iff_exists.mp (hfin _ hb')
  have hle : Metric.externalCoveringNumber (X := UnifFun X) (Real.toNNReal b) H ≤
      Metric.externalCoveringNumber (X := UnifFun X) (Real.toNNReal a) H :=
    Metric.externalCoveringNumber_anti (Real.toNNReal_le_toNNReal hab)
  have hpos : 0 < Metric.externalCoveringNumber (X := UnifFun X) (Real.toNNReal b) H :=
    Metric.externalCoveringNumber_pos_iff.mpr hne
  unfold entH
  rw [← hma, ← hmb] at *
  simp only [ENat.toENNReal_coe, ENNReal.toReal_natCast]
  refine Real.sqrt_le_sqrt (Real.log_le_log ?_ ?_)
  · exact_mod_cast hpos
  · exact_mod_cast hle

@[blueprint "lem:entF-antitone"
  (statement := /-- If $F \ne \emptyset$ has finite $d_\infty$ covering numbers at every positive
    scale, then $v \mapsto \mathcal E_F(v)$ is antitone on $(0, \infty)$. -/)]
theorem antitoneOn_entF (F : Set (X → X)) (hne : F.Nonempty)
    (hfin : ∀ r : ℝ≥0, 0 < r → Metric.externalCoveringNumber (X := UnifMaps X) r F ≠ ⊤) :
    AntitoneOn (entF F) (Set.Ioi 0) := by
  intro a ha b hb hab
  have hb' : 0 < Real.toNNReal b := Real.toNNReal_pos.mpr hb
  have ha' : 0 < Real.toNNReal a := Real.toNNReal_pos.mpr ha
  obtain ⟨ma, hma⟩ := ENat.ne_top_iff_exists.mp (hfin _ ha')
  obtain ⟨mb, hmb⟩ := ENat.ne_top_iff_exists.mp (hfin _ hb')
  have hle : Metric.externalCoveringNumber (X := UnifMaps X) (Real.toNNReal b) F ≤
      Metric.externalCoveringNumber (X := UnifMaps X) (Real.toNNReal a) F :=
    Metric.externalCoveringNumber_anti (Real.toNNReal_le_toNNReal hab)
  have hpos : 0 < Metric.externalCoveringNumber (X := UnifMaps X) (Real.toNNReal b) F :=
    Metric.externalCoveringNumber_pos_iff.mpr hne
  unfold entF
  rw [← hma, ← hmb] at *
  simp only [ENat.toENNReal_coe, ENNReal.toReal_natCast]
  refine Real.sqrt_le_sqrt (Real.log_le_log ?_ ?_)
  · exact_mod_cast hpos
  · exact_mod_cast hle

end Antitone

omit [PseudoMetricSpace X] in
@[blueprint "lem:emp-rademacher-empty"
  (statement := /-- $\hat{\mathfrak R}_S(\emptyset) = 0$ (the supremum over the empty class is $0$
    by convention). -/)]
theorem empRademacher_empty (S : Fin n → X) : empRademacher S (∅ : Set (X → ℝ)) = 0 := by
  unfold empRademacher empiricalRademacherComplexity_without_abs
  haveI : IsEmpty ((∅ : Set (X → ℝ))) := Set.isEmpty_coe_sort.mpr rfl
  simp only [iSup_of_empty', Real.sSup_empty, Finset.sum_const_zero, mul_zero]

@[blueprint "lem:entropy-integrand-ae"
  (statement := /-- \textbf{Almost-everywhere comparison of the entropy integrands.} Let $H \ne
    \emptyset$, $F \ne \emptyset$ satisfy Assumptions \texttt{ass:ent-readout},
    \texttt{ass:ent-transition} with $L_H > 0$, $n \ge 1$, and let
    $N_S(x)$ be FoML's open-ball covering number of $H \circ F$ for $\|\cdot\|_S$. Then for
    every $\varepsilon > 0$ and Lebesgue-a.e. $x > \varepsilon$,
    $$\sqrt{\log N_S(x)} \le \mathcal E_H(x/4) + \mathcal E_F\bigl(x/(4L_H)\bigr).$$
    Proof: for every $y < x$, $N_S(x) \le N^{\mathrm{ext}}(H \circ F, \|\cdot\|_\infty, y/2)
    \le N^{\mathrm{ext}}(H, y/4) N^{\mathrm{ext}}(F, y/(4L_H))$; the right-hand side
    $\psi(y) = \mathcal E_H(y/4) + \mathcal E_F(y/(4L_H))$ is antitone in $y$, hence continuous
    outside a countable set, and letting $y \uparrow x$ at a continuity point gives the
    claim. -/)]
theorem sqrt_log_coveringNumber_ae_le {n : ℕ} (hn : 0 < n) (S : Fin n → X) (H : Set (X → ℝ))
    (F : Set (X → X)) {BH : ℝ} {LH : ℝ≥0} (hLH : 0 < LH) (hH : EntReadout H BH LH)
    (hF : EntTransition F) [Nonempty (compClass H F)] (hHne : H.Nonempty) (hFne : F.Nonempty)
    (hGfin : ∀ r : ℝ≥0, 0 < r →
      Metric.externalCoveringNumber (X := UnifFun X) r (compClass H F) ≠ ⊤)
    (h' : TotallyBounded (Set.univ :
      Set (EmpiricalFunctionSpace (fun g : compClass H F => (g : X → ℝ)) S)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂MeasureTheory.volume, ε < x →
      Real.sqrt (Real.log (coveringNumber h' x : ℕ)) ≤ entH H (x / 4) + entF F (x / (4 * LH)) := by
  set ψ : ℝ → ℝ := fun x => entH H (x / 4) + entF F (x / (4 * LH)) with hψ
  have hψanti : AntitoneOn ψ (Set.Ioi 0) := by
    intro a ha b hb hab
    have ha' : 0 < a := ha
    have hb' : 0 < b := hb
    exact add_le_add
      (antitoneOn_entH H hHne hH.cov (Set.mem_Ioi.mpr (by positivity))
        (Set.mem_Ioi.mpr (by positivity)) (by gcongr))
      (antitoneOn_entF F hFne hF (Set.mem_Ioi.mpr (by positivity))
        (Set.mem_Ioi.mpr (by positivity)) (by gcongr))
  set ψ' : ℝ → ℝ := fun x => ψ (max x ε) with hψ'
  have hψ'anti : Antitone ψ' := by
    intro a b hab
    exact hψanti (Set.mem_Ioi.mpr (lt_max_of_lt_right hε)) (Set.mem_Ioi.mpr (lt_max_of_lt_right hε))
      (max_le_max hab le_rfl)
  have hae := hψ'anti.countable_not_continuousAt.ae_notMem MeasureTheory.volume
  filter_upwards [hae] with x hx hxε
  simp only [not_not] at hx
  have hxpos : 0 < x := hε.trans hxε
  -- for every `y < x`: `√log N_S(x) ≤ ψ y`
  have hbound : ∀ y, 0 < y → y < x → Real.sqrt (Real.log (coveringNumber h' x : ℕ)) ≤ ψ y := by
    intro y hy hyx
    have hr : 2 * ((Real.toNNReal (y / 2) : ℝ≥0) : ℝ) < x := by
      rw [Real.coe_toNNReal _ (by positivity)]
      linarith
    have h1 := coveringNumber_empiricalFunctionSpace_le S hn (compClass H F) h' hr
    have h2 := sqrt_log_compClass_le (F := F) hH.lip hLH (ε := y / 2)
      (hH.cov _ (Real.toNNReal_pos.mpr (by positivity)))
      (hF _ (Real.toNNReal_pos.mpr (by positivity)))
    have hy4 : y / 2 / 2 = y / 4 := by ring
    have hy4' : y / 2 / (2 * (LH : ℝ)) = y / (4 * LH) := by
      rw [div_div]
      congr 1
      ring
    rw [hy4, hy4'] at h2
    refine le_trans ?_ h2
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp
      (hGfin (Real.toNNReal (y / 2)) (Real.toNNReal_pos.mpr (by positivity)))
    rw [← hm] at h1 ⊢
    simp only [ENat.toENNReal_coe, ENNReal.toReal_natCast]
    have hle : coveringNumber h' x ≤ m := by exact_mod_cast h1
    have hpos : 0 < coveringNumber h' x := coveringNumber_nonzero Set.univ_nonempty h' hxpos
    exact Real.sqrt_le_sqrt (Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hle))
  -- let `y ↑ x` using continuity of `ψ'` at `x`
  have hlim : Filter.Tendsto ψ' (nhdsWithin x (Set.Iio x)) (nhds (ψ' x)) :=
    hx.tendsto.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ y in nhdsWithin x (Set.Iio x),
      Real.sqrt (Real.log (coveringNumber h' x : ℕ)) ≤ ψ' y := by
    filter_upwards [Ioo_mem_nhdsLT hxε] with y hy
    have : ψ' y = ψ y := by simp only [ψ', max_eq_left hy.1.le]
    rw [this]
    exact hbound y (hε.trans hy.1) hy.2
  have hx' : ψ' x = ψ x := by simp only [ψ', max_eq_left hxε.le]
  have := ge_of_tendsto hlim hev
  rwa [hx'] at this

@[blueprint "thm:rad.decomp.ent.ent-foml"
  (statement := /-- \textbf{Deterministic entropy decomposition (FoML form).} Under Assumptions
    \texttt{ass:ent-readout} and \texttt{ass:ent-transition} with $L_H > 0$, for every sample
    $S$ of size $n \ge 1$ and every $0 < \varepsilon < B_H/2$,
    $$\hat{\mathfrak R}_S(H \circ F) \le 4\varepsilon + \frac{12}{\sqrt n}
    \int_\varepsilon^{B_H/2} \Bigl\{\mathcal E_H(x/4) + \mathcal E_F\bigl(x/(4L_H)\bigr)\Bigr\}
    \, dx,$$
    where $\mathcal E_H(u) = \sqrt{\log N^{\mathrm{ext}}(H, \|\cdot\|_\infty, u)}$ and
    $\mathcal E_F(v) = \sqrt{\log N^{\mathrm{ext}}(F, d_\infty, v)}$ (external covering numbers
    by closed balls). Proof: FoML's Dudley integral for the class $H \circ F$ with the empirical
    pseudometric $\|\cdot\|_S$ (\texttt{dudley\_entropy\_integral'}), whose internal open-ball
    covering number at scale $x$ is at most $N^{\mathrm{ext}}(H \circ F, \|\cdot\|_\infty, y/2)$
    for every $y < x$ (\texttt{lem:foml-covering-le-external-unifFun}, losing a factor $2$ in
    the radius when passing from external to internal covers), followed by the composition
    covering lemma \texttt{lem:ent-composition-entropy} at scale $y/2$ and the limit
    $y \uparrow x$ almost everywhere (\texttt{lem:entropy-integrand-ae}). Compared with the
    paper's statement (quoted in \texttt{thm:rad.decomp.ent.ent}), the scales $x/2$, $x/(2L_H)$ are
    replaced by $x/4$, $x/(4L_H)$ (the paper implicitly uses covers with centres in the class,
    while the assumptions here are stated with external covering numbers), the integration range
    is $[\varepsilon, B_H/2]$ instead of $[0, 2B_H]$, and there is the additive term
    $4\varepsilon$ from FoML's Dudley bound. -/)]
theorem rad_decomp_ent_ent_foml {n : ℕ} (hn : 0 < n) (S : Fin n → X) (H : Set (X → ℝ))
    (F : Set (X → X)) {BH : ℝ} {LH : ℝ≥0} (hLH : 0 < LH) (hH : EntReadout H BH LH)
    (hF : EntTransition F) {ε : ℝ} (hε : 0 < ε) (hεB : ε < BH / 2) :
    empRademacher S (compClass H F) ≤
      4 * ε + 12 / Real.sqrt n *
        ∫ x in ε..(BH / 2), (entH H (x / 4) + entF F (x / (4 * LH))) := by
  classical
  have hψ0 : ∀ x, 0 ≤ entH H (x / 4) + entF F (x / (4 * LH)) := fun x =>
    add_nonneg (entH_nonneg _ _) (entF_nonneg _ _)
  have hint0 : 0 ≤ ∫ x in ε..(BH / 2), (entH H (x / 4) + entF F (x / (4 * LH))) :=
    intervalIntegral.integral_nonneg hεB.le fun x _ => hψ0 x
  rcases (compClass H F).eq_empty_or_nonempty with hemp | hne
  · -- the empty class has zero Rademacher complexity
    rw [hemp, empRademacher_empty]
    have : 0 ≤ 12 / Real.sqrt n *
        ∫ x in ε..(BH / 2), (entH H (x / 4) + entF F (x / (4 * LH))) :=
      mul_nonneg (by positivity) hint0
    linarith
  haveI : Nonempty (compClass H F) := hne.to_subtype
  have hHne : H.Nonempty := by
    obtain ⟨u, h, hh, f, hf, rfl⟩ := hne
    exact ⟨h, hh⟩
  have hFne : F.Nonempty := by
    obtain ⟨u, h, hh, f, hf, rfl⟩ := hne
    exact ⟨f, hf⟩
  -- finite uniform covering numbers of the composition class
  have hGfin : ∀ r : ℝ≥0, 0 < r →
      Metric.externalCoveringNumber (X := UnifFun X) r (compClass H F) ≠ ⊤ := by
    intro r hr
    refine ne_top_of_le_ne_top ?_ (externalCoveringNumber_compClass_le_mul hH.lip r)
    exact WithTop.mul_ne_top (hH.cov _ (by positivity)) (hF _ (by positivity))
  have h' := totallyBounded_empiricalFunctionSpace S hn (compClass H F) hGfin
  -- the composition class is bounded by `BH` on the sample
  have hBH0 : 0 ≤ BH := by
    obtain ⟨u, h, hh, f, hf, rfl⟩ := hne
    exact (abs_nonneg _).trans (hH.bdd h hh (f (S ⟨0, hn⟩)))
  have cs : ∀ u : compClass H F, empiricalNorm S (u : X → ℝ) ≤ BH := by
    intro u
    obtain ⟨h, hh, f, hf, hu⟩ := u.2
    refine empiricalNorm_le_of_abs_le hn S _ hBH0 fun k => ?_
    rw [hu]
    exact hH.bdd h hh _
  have hdud := dudley_entropy_integral' hε h' hn cs hεB
  -- a.e. comparison of the integrands on `[ε, BH/2]`
  have hae := sqrt_log_coveringNumber_ae_le hn S H F hLH hH hF hHne hFne hGfin h' hε
  have hle : (fun x => Real.sqrt (Real.log (coveringNumber h' x : ℕ))) ≤ᵐ[
      MeasureTheory.volume.restrict (Set.Icc ε (BH / 2))]
      fun x => entH H (x / 4) + entF F (x / (4 * LH)) := by
    have h1 : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.Icc ε (BH / 2))), x ∈ Set.Icc ε (BH / 2) :=
      MeasureTheory.ae_restrict_mem measurableSet_Icc
    have h2 := MeasureTheory.ae_restrict_of_ae (s := Set.Icc ε (BH / 2)) hae
    have h3 := MeasureTheory.ae_restrict_of_ae (s := Set.Icc ε (BH / 2))
      ((Set.countable_singleton ε).ae_notMem MeasureTheory.volume)
    filter_upwards [h1, h2, h3] with x hx hx2 hx3
    exact hx2 (lt_of_le_of_ne hx.1 fun h => hx3 (Set.mem_singleton_iff.mpr h.symm))
  -- both integrands are antitone, hence interval integrable
  have hantF : AntitoneOn (fun x => Real.sqrt (Real.log (coveringNumber h' x : ℕ)))
      (Set.uIcc ε (BH / 2)) := by
    rw [Set.uIcc_of_le hεB.le]
    intro a ha b hb hab
    have hapos : 0 < a := hε.trans_le ha.1
    have hbpos : 0 < b := hε.trans_le hb.1
    have := coveringNumber_antitone h' (Set.mem_Ioi.mpr hapos) (Set.mem_Ioi.mpr hbpos) hab
    exact Real.sqrt_le_sqrt (Real.log_le_log
      (by exact_mod_cast coveringNumber_nonzero Set.univ_nonempty h' hbpos)
      (by exact_mod_cast this))
  have hantψ : AntitoneOn (fun x => entH H (x / 4) + entF F (x / (4 * LH)))
      (Set.uIcc ε (BH / 2)) := by
    rw [Set.uIcc_of_le hεB.le]
    intro a ha b hb hab
    have hapos : 0 < a := hε.trans_le ha.1
    have hbpos : 0 < b := hε.trans_le hb.1
    refine add_le_add ?_ ?_
    · exact antitoneOn_entH H hHne hH.cov (Set.mem_Ioi.mpr (by positivity))
        (Set.mem_Ioi.mpr (by positivity)) (by gcongr)
    · exact antitoneOn_entF F hFne hF (Set.mem_Ioi.mpr (by positivity))
        (Set.mem_Ioi.mpr (by positivity)) (by gcongr)
  have hmono := intervalIntegral.integral_mono_ae_restrict (μ := MeasureTheory.volume) hεB.le
    hantF.intervalIntegrable hantψ.intervalIntegrable hle
  calc empRademacher S (compClass H F) ≤ _ := hdud
    _ ≤ _ := by gcongr

@[blueprint "thm:rad.decomp.ent.ent"
  (statement := /-- \textbf{Deterministic entropy decomposition.} The paper states: under
    Assumptions \texttt{ass:ent-readout} and \texttt{ass:ent-transition}, for every sample
    $S = (x_1,\dots,x_n)$ with $n \ge 1$,
    $$\hat{\mathfrak R}_S(H \circ F) \le \frac{12}{\sqrt n} \int_0^{2B_H}
    \Bigl\{\sqrt{\log N(H, \|\cdot\|_\infty, \varepsilon/2)}
    + \sqrt{\log N(F, d_\infty, \varepsilon/(2L_H))}\Bigr\} \, d\varepsilon.$$

    The formalized statement is: under Assumptions \texttt{ass:ent-readout} and
    \texttt{ass:ent-transition} with $L_H > 0$ and $B_H > 0$, if the entropy integrand
    $x \mapsto \mathcal E_H(x/4) + \mathcal E_F(x/(4L_H))$ is integrable on $[0, B_H/2]$, then
    for every sample $S$ of size $n \ge 1$,
    $$\hat{\mathfrak R}_S(H \circ F) \le \frac{12}{\sqrt n}
    \int_0^{B_H/2} \Bigl\{\mathcal E_H(x/4) + \mathcal E_F\bigl(x/(4L_H)\bigr)\Bigr\}\, dx,$$
    where $\mathcal E_H(u) = \sqrt{\log N^{\mathrm{ext}}(H, \|\cdot\|_\infty, u)}$ and
    $\mathcal E_F(v) = \sqrt{\log N^{\mathrm{ext}}(F, d_\infty, v)}$ are the root entropies for
    the external covering numbers by closed balls of the assumptions.

    \emph{Deviations from the paper.} (i) We assume in addition that the entropy integrand is
    integrable on $[0, B_H/2]$; the paper's bound is trivially true with right-hand side
    $+\infty$ otherwise (e.g. Lipschitz classes on a two-dimensional domain), whereas Lean's
    Bochner integral of a non-integrable function is $0$, so the statement without this
    hypothesis is false as transcribed. (ii) FoML's Dudley integral
    (\texttt{dudley\_entropy\_integral'}) uses internal open-ball covers, and converting the
    external closed-ball covering numbers of the assumptions costs a factor $2$ in the radius
    (\texttt{lem:foml-covering-le-external-unifFun}), so the scales are $x/4$ and $x/(4L_H)$ on
    $[0, B_H/2]$ instead of $\varepsilon/2$, $\varepsilon/(2L_H)$ on $[0, 2B_H]$. Up to these
    constant rescalings the statement is the paper's.

    Proof: let $\varepsilon \to 0$ in \texttt{thm:rad.decomp.ent.ent-foml}, using the
    integrability hypothesis to compare the integrals over $[\varepsilon, B_H/2]$ and
    $[0, B_H/2]$. -/)]
theorem rad_decomp_ent_ent {n : ℕ} (hn : 0 < n) (S : Fin n → X) (H : Set (X → ℝ))
    (F : Set (X → X)) {BH : ℝ} {LH : ℝ≥0} (hLH : 0 < LH) (hH : EntReadout H BH LH)
    (hF : EntTransition F) (hBH : 0 < BH)
    (hint : IntervalIntegrable (fun x => entH H (x / 4) + entF F (x / (4 * LH)))
      MeasureTheory.volume 0 (BH / 2)) :
    empRademacher S (compClass H F) ≤
      12 / Real.sqrt n *
        ∫ x in (0 : ℝ)..(BH / 2), (entH H (x / 4) + entF F (x / (4 * LH))) := by
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hε0 : 0 < min (δ / 4) (BH / 4) := lt_min (by positivity) (by positivity)
  have hεB : min (δ / 4) (BH / 4) < BH / 2 := (min_le_right _ _).trans_lt (by linarith)
  have h1 := rad_decomp_ent_ent_foml hn S H F hLH hH hF hε0 hεB
  have h2 : ∫ x in (min (δ / 4) (BH / 4))..(BH / 2), (entH H (x / 4) + entF F (x / (4 * LH))) ≤
      ∫ x in (0 : ℝ)..(BH / 2), (entH H (x / 4) + entF F (x / (4 * LH))) :=
    intervalIntegral.integral_mono_interval hε0.le hεB.le le_rfl
      (Filter.Eventually.of_forall fun x => add_nonneg (entH_nonneg _ _) (entF_nonneg _ _)) hint
  have h3 : 4 * min (δ / 4) (BH / 4) ≤ δ := by
    have := min_le_left (δ / 4) (BH / 4)
    linarith
  calc empRademacher S (compClass H F)
      ≤ 4 * min (δ / 4) (BH / 4) + 12 / Real.sqrt n *
          ∫ x in (min (δ / 4) (BH / 4))..(BH / 2), (entH H (x / 4) + entF F (x / (4 * LH))) := h1
    _ ≤ δ + 12 / Real.sqrt n *
          ∫ x in (0 : ℝ)..(BH / 2), (entH H (x / 4) + entF F (x / (4 * LH))) := by gcongr
    _ = _ := add_comm _ _

end LeanDeepgen
