import Mathlib
import Architect
import LeanDeepgen.Setting.WordBall
import LeanDeepgen.Setting.Metrics
import LeanDeepgen.Setting.Covering
import LeanDeepgen.Growth.Defs
import LeanDeepgen.Growth.Lemmas

/-!
# Polynomial growth: condition P2 (paper Sec. 4 / App. F)

A group `G` (the paper's `(H, d_H)`; renamed to avoid the output class `H`) carrying a
pseudo-emetric acts on the state space `X` through a monoid homomorphism
`α : G →* Function.End X` (so `α (g * h) = α g ∘ α h` and `α 1 = id`). The hidden-layer class
`F` lies in the image `α '' Sg` of a bounded set `Sg ⊆ G`, and the orbit map
`orbitMap α : g ↦ α g` (defined in `LeanDeepgen.Growth.Defs`) is `Lα`-Lipschitz from `(G, d_G)`
to `(𝒳^𝒳, d_∞)`.

* `lem:p2-wordball-subset-ball`: `B(k,F) ⊆ α(B_G(1, k R_S))` (subadditivity of the length).
* `lem:p2-transfer`: `N^ext(α(B), d_∞, Lα δ) ≤ N^ext(B, d_G, δ)` (Lipschitz embedding).
* `cond:p2-nilp` (P2): if the balls of `G` have polynomial entropy
  `N^ext(B_G(1,R), δ) ≤ C_G (1 + R/δ)^D`, then
  `N^ext(B(k,F), d_∞, ε) ≤ C_G max(1, R_S Lα)^D (1 + k/ε)^D`.
* `lem:p2-diameter`: `diam_∞ B(k,F) ≤ 2 Lα R_S k`; `cond:p2-nilp-compact`: on a bounded state
  space `diam_∞ B(k,F) ≤ diam 𝒳`.

The polynomial ball-entropy bound of `G` (Guivarc'h–Bass for nilpotent groups) is an assumption
here, as in the paper.
-/

open scoped NNReal ENNReal
open Metric

open FoML.ToMathlib

namespace LeanDeepgen

section WordBallSubset

variable {X : Type*} {G : Type*} [Group G] [PseudoEMetricSpace G]

@[blueprint "lem:p2-wordball-subset-ball"
  (statement := /-- Let $\alpha : H \to \mathcal X^{\mathcal X}$ be a homomorphism, assume the
    length $g \mapsto d_H(e,g)$ is subadditive, $d_H(e, gh) \le d_H(e,g) + d_H(e,h)$, and let
    $S \subseteq H$ satisfy $d_H(e,s) \le R_S$ for all $s \in S$ and $F \subseteq \alpha(S)$.
    Then for every $k$,
    $$B(k,F) \subseteq \alpha\bigl(\overline B_H(e, kR_S)\bigr).$$ -/)]
theorem wordBall_subset_image_closedBall (α : G →* Function.End X) {F : Set (X → X)}
    (hsub : ∀ g h : G, edist 1 (g * h) ≤ edist 1 g + edist 1 h)
    {Sg : Set G} {RS : ℝ≥0} (hS : ∀ s ∈ Sg, edist 1 s ≤ RS) (hF : F ⊆ orbitMap α '' Sg)
    (k : ℕ) : wordBall F k ⊆ orbitMap α '' closedEBall (1 : G) ((k * RS : ℝ≥0) : ℝ≥0∞) := by
  /-- Induction on $k$. For $k = 0$, $\mathrm{id} = \alpha(e)$ and $e \in \overline B_H(e,0)$.
    For $k+1$: an element of $B(k,F)$ lies in $\alpha(\overline B_H(e,kR_S))
    \subseteq \alpha(\overline B_H(e,(k+1)R_S))$; an element $\alpha(s) \circ \alpha(h)$ with
    $s \in S$, $d_H(e,h) \le kR_S$ equals $\alpha(sh)$ and
    $d_H(e, sh) \le d_H(e,s) + d_H(e,h) \le R_S + kR_S$. -/
  induction k with
  | zero =>
    intro f hf
    rw [wordBall_zero, Set.mem_singleton_iff] at hf
    subst hf
    exact ⟨1, mem_closedEBall_self, orbitMap_one α⟩
  | succ k ih =>
    rintro f (hf | ⟨g, hg, f, hf, rfl⟩)
    · obtain ⟨h, hh, rfl⟩ := ih hf
      refine ⟨h, ?_, rfl⟩
      refine closedEBall_subset_closedEBall ?_ hh
      gcongr
      exact_mod_cast Nat.le_succ k
    · obtain ⟨s, hs, rfl⟩ := hF hg
      obtain ⟨h, hh, rfl⟩ := ih hf
      refine ⟨s * h, ?_, orbitMap_mul α s h⟩
      rw [mem_closedEBall'] at hh ⊢
      calc edist 1 (s * h) ≤ edist 1 s + edist 1 h := hsub s h
        _ ≤ RS + ((k * RS : ℝ≥0) : ℝ≥0∞) := add_le_add (hS s hs) hh
        _ = (((k + 1 : ℕ) * RS : ℝ≥0) : ℝ≥0∞) := by push_cast; ring

end WordBallSubset

section Transfer

variable {X : Type*} [PseudoEMetricSpace X] {G : Type*} [Group G] [PseudoEMetricSpace G]

@[blueprint "lem:p2-transfer"
  (statement := /-- If the orbit map is $L_\alpha$-Lipschitz,
    $d_\infty(\alpha(g), \alpha(h)) \le L_\alpha d_H(g,h)$, then for every $B \subseteq H$ and
    $\delta \ge 0$,
    $$N^{\mathrm{ext}}\bigl(\alpha(B), d_\infty, L_\alpha\delta\bigr)
      \le N^{\mathrm{ext}}(B, d_H, \delta).$$ -/)]
theorem externalCoveringNumber_image_orbitMap_le (α : G →* Function.End X) {Lα : ℝ≥0}
    (hα : LipschitzWith Lα (fun g => toUnifMaps (orbitMap α g))) (δ : ℝ≥0) (B : Set G) :
    externalCoveringNumber (X := UnifMaps X) (Lα * δ) (orbitMap α '' B) ≤
      externalCoveringNumber δ B := by
  /-- This is the Lipschitz embedding lemma `lem:lipschitz-embedding`. -/
  exact externalCoveringNumber_image_le hα δ B

@[blueprint "lem:p2-transfer-wordball"
  (statement := /-- Under the hypotheses of `lem:p2-wordball-subset-ball` and `lem:p2-transfer`,
    for every $k$ and $\delta \ge 0$,
    $$N^{\mathrm{ext}}(B(k,F), d_\infty, L_\alpha\delta)
      \le N^{\mathrm{ext}}\bigl(\overline B_H(e, kR_S), d_H, \delta\bigr).$$ -/)]
theorem externalCoveringNumber_wordBall_le_closedBall (α : G →* Function.End X)
    {F : Set (X → X)} (hsub : ∀ g h : G, edist 1 (g * h) ≤ edist 1 g + edist 1 h)
    {Sg : Set G} {RS : ℝ≥0} (hS : ∀ s ∈ Sg, edist 1 s ≤ RS) (hF : F ⊆ orbitMap α '' Sg)
    {Lα : ℝ≥0} (hα : LipschitzWith Lα (fun g => toUnifMaps (orbitMap α g))) (k : ℕ) (δ : ℝ≥0) :
    externalCoveringNumber (X := UnifMaps X) (Lα * δ) (wordBall F k) ≤
      externalCoveringNumber δ (closedEBall (1 : G) ((k * RS : ℝ≥0) : ℝ≥0∞)) := by
  /-- Monotonicity of the external covering number in the set, then `lem:p2-transfer`. -/
  exact (externalCoveringNumber_mono_set (X := UnifMaps X)
      (wordBall_subset_image_closedBall α hsub hS hF k)).trans
    (externalCoveringNumber_image_orbitMap_le α hα δ _)

end Transfer

section P2

variable {X : Type*} [PseudoEMetricSpace X] {G : Type*} [Group G] [PseudoEMetricSpace G]

@[blueprint "lem:p2-poly-factor"
  (statement := /-- For $\varepsilon, L_\alpha > 0$, $R_S \ge 0$, $k \ge 0$ and $D \ge 0$,
    $$\Bigl(1 + \frac{kR_S}{\varepsilon/L_\alpha}\Bigr)^D
      \le \max(1, R_S L_\alpha)^D \Bigl(1 + \frac{k}{\varepsilon}\Bigr)^D .$$ -/)]
theorem one_add_div_rpow_le {ε Lα RS : ℝ} (hε : 0 < ε) (hL : 0 < Lα) (hRS : 0 ≤ RS) (k : ℝ)
    (hk : 0 ≤ k) {D : ℝ} (hD : 0 ≤ D) :
    (1 + k * RS / (ε / Lα)) ^ D ≤ max 1 (RS * Lα) ^ D * (1 + k / ε) ^ D := by
  /-- With $M = \max(1, R_S L_\alpha)$ we have $1 \le M$ and $R_S L_\alpha \le M$, so
    $1 + (R_S L_\alpha)(k/\varepsilon) \le M + M (k/\varepsilon) = M(1 + k/\varepsilon)$;
    raise to the power $D \ge 0$ and use $(ab)^D = a^D b^D$. -/
  have hM1 : (1 : ℝ) ≤ max 1 (RS * Lα) := le_max_left _ _
  have hM2 : RS * Lα ≤ max 1 (RS * Lα) := le_max_right _ _
  have hke : 0 ≤ k / ε := div_nonneg hk hε.le
  have hbase : 1 + k * RS / (ε / Lα) ≤ max 1 (RS * Lα) * (1 + k / ε) := by
    have h1 : k * RS / (ε / Lα) = RS * Lα * (k / ε) := by
      field_simp
    rw [h1, mul_add, mul_one]
    exact add_le_add hM1 (mul_le_mul_of_nonneg_right hM2 hke)
  have h0 : 0 ≤ 1 + k * RS / (ε / Lα) := by positivity
  calc (1 + k * RS / (ε / Lα)) ^ D ≤ (max 1 (RS * Lα) * (1 + k / ε)) ^ D :=
        Real.rpow_le_rpow h0 hbase hD
    _ = max 1 (RS * Lα) ^ D * (1 + k / ε) ^ D :=
        Real.mul_rpow (zero_le_one.trans hM1) (by positivity)

@[blueprint "cond:p2-nilp"
  (statement := /-- \textbf{(P2: nilpotent control grows polynomially.)}
    Let $(H, d_H)$ be a group with a pseudo-emetric, identity $e$, and assume the length
    $g \mapsto d_H(e,g)$ is subadditive: $d_H(e,gh) \le d_H(e,g) + d_H(e,h)$. Assume its balls
    have polynomial entropy of degree $D \ge 0$: there is $1 \le C_H < \infty$ such that for all
    $R \ge 0$ and $\delta > 0$,
    $$N^{\mathrm{ext}}\bigl(\overline B_H(e,R), d_H, \delta\bigr)
      \le C_H \Bigl(1 + \frac R\delta\Bigr)^D .$$
    Suppose $H$ acts on $\mathcal X$ through a homomorphism
    $\alpha : H \to \mathcal X^{\mathcal X}$, that there is a bounded set $S \subseteq H$
    ($d_H(e,s) \le R_S$ for $s \in S$) with $F \subseteq \alpha(S)$, and that the orbit map is
    Lipschitz in the uniform metric: $d_\infty(\alpha(g), \alpha(h)) \le L_\alpha d_H(g,h)$ with
    $0 < L_\alpha < \infty$. Then with
    $$C := C_H \max(1, R_S L_\alpha)^D$$
    one has, for every $\varepsilon > 0$ and every $k \ge 0$,
    $$N^{\mathrm{ext}}(B(k,F), d_\infty, \varepsilon) \le C \Bigl(1 + \frac k\varepsilon\Bigr)^D .$$
    (In Lean the ball-entropy hypothesis and the conclusion are stated in $[0,\infty]$ as
    $N \le \operatorname{ofReal}(\cdots)$, which in particular asserts finiteness; the bound
    holds for $k = 0$ as well.) -/)]
theorem cond_p2_nilp (α : G →* Function.End X) {F : Set (X → X)}
    (hsub : ∀ g h : G, edist 1 (g * h) ≤ edist 1 g + edist 1 h)
    {D : ℝ} (hD : 0 ≤ D) {CH : ℝ} (hCH : 1 ≤ CH)
    (hball : ∀ R δ : ℝ≥0, 0 < δ →
      (externalCoveringNumber δ (closedEBall (1 : G) R) : ℝ≥0∞) ≤
        ENNReal.ofReal (CH * (1 + R / δ) ^ D))
    {Sg : Set G} {RS : ℝ≥0} (hS : ∀ s ∈ Sg, edist 1 s ≤ RS) (hF : F ⊆ orbitMap α '' Sg)
    {Lα : ℝ≥0} (hLα : 0 < Lα) (hα : LipschitzWith Lα (fun g => toUnifMaps (orbitMap α g))) :
    ∀ ε : ℝ≥0, 0 < ε → ∀ k : ℕ,
      (externalCoveringNumber (X := UnifMaps X) ε (wordBall F k) : ℝ≥0∞) ≤
        ENNReal.ofReal (CH * max 1 (RS * Lα) ^ D * (1 + k / ε) ^ D) := by
  /-- Put $\delta := \varepsilon / L_\alpha$, so $L_\alpha \delta = \varepsilon$. By
    `lem:p2-transfer-wordball`,
    $N^{\mathrm{ext}}(B(k,F), d_\infty, \varepsilon)
    \le N^{\mathrm{ext}}(\overline B_H(e, kR_S), d_H, \delta)
    \le C_H (1 + kR_S/\delta)^D$, and `lem:p2-poly-factor` bounds the last factor by
    $\max(1, R_S L_\alpha)^D (1 + k/\varepsilon)^D$. -/
  intro ε hε k
  set δ : ℝ≥0 := ε / Lα with hδ
  have hδpos : 0 < δ := div_pos hε hLα
  have hLδ : Lα * δ = ε := mul_div_cancel₀ ε hLα.ne'
  have h1 : externalCoveringNumber (X := UnifMaps X) ε (wordBall F k) ≤
      externalCoveringNumber δ (closedEBall (1 : G) ((k * RS : ℝ≥0) : ℝ≥0∞)) := by
    rw [← hLδ]
    exact externalCoveringNumber_wordBall_le_closedBall α hsub hS hF hα k δ
  have h2 := hball (k * RS) δ hδpos
  have hCH0 : 0 ≤ CH := zero_le_one.trans hCH
  have h3 : CH * (1 + ((k * RS : ℝ≥0) : ℝ) / (δ : ℝ)) ^ D ≤
      CH * max 1 (RS * Lα) ^ D * (1 + k / ε) ^ D := by
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hCH0
    have := one_add_div_rpow_le (ε := ε) (Lα := Lα) (RS := RS) (by exact_mod_cast hε)
      (by exact_mod_cast hLα) RS.coe_nonneg (k : ℝ) (Nat.cast_nonneg k) hD
    rw [hδ]
    push_cast
    exact this
  calc (externalCoveringNumber (X := UnifMaps X) ε (wordBall F k) : ℝ≥0∞)
      ≤ (externalCoveringNumber δ (closedEBall (1 : G) ((k * RS : ℝ≥0) : ℝ≥0∞)) :
          ℝ≥0∞) := by exact_mod_cast h1
    _ ≤ ENNReal.ofReal (CH * (1 + ((k * RS : ℝ≥0) : ℝ) / (δ : ℝ)) ^ D) := h2
    _ ≤ ENNReal.ofReal (CH * max 1 (RS * Lα) ^ D * (1 + k / ε) ^ D) :=
        ENNReal.ofReal_le_ofReal h3

@[blueprint "cond:p2-nilp-real"
  (statement := /-- (Real-valued form of P2.) Under the hypotheses of `cond:p2-nilp`, for every
    $\varepsilon > 0$ and $k \ge 0$,
    $N^{\mathrm{ext}}(B(k,F), d_\infty, \varepsilon) \le C_H \max(1, R_S L_\alpha)^D
    (1 + k/\varepsilon)^D$ as real numbers (the covering number being finite). -/)]
theorem cond_p2_nilp_toReal (α : G →* Function.End X) {F : Set (X → X)}
    (hsub : ∀ g h : G, edist 1 (g * h) ≤ edist 1 g + edist 1 h)
    {D : ℝ} (hD : 0 ≤ D) {CH : ℝ} (hCH : 1 ≤ CH)
    (hball : ∀ R δ : ℝ≥0, 0 < δ →
      (externalCoveringNumber δ (closedEBall (1 : G) R) : ℝ≥0∞) ≤
        ENNReal.ofReal (CH * (1 + R / δ) ^ D))
    {Sg : Set G} {RS : ℝ≥0} (hS : ∀ s ∈ Sg, edist 1 s ≤ RS) (hF : F ⊆ orbitMap α '' Sg)
    {Lα : ℝ≥0} (hLα : 0 < Lα) (hα : LipschitzWith Lα (fun g => toUnifMaps (orbitMap α g))) :
    ∃ C : ℝ, ∀ ε : ℝ≥0, 0 < ε → ∀ k : ℕ,
      (externalCoveringNumber (X := UnifMaps X) ε (wordBall F k) : ℝ≥0∞) ≠ ⊤ ∧
      (externalCoveringNumber (X := UnifMaps X) ε (wordBall F k) : ℝ≥0∞).toReal ≤
        C * (1 + k / ε) ^ D := by
  /-- Take $C = C_H \max(1, R_S L_\alpha)^D$ and apply `cond:p2-nilp`; a quantity bounded by
    $\operatorname{ofReal}(b)$ is finite and has real part $\le b$. -/
  refine ⟨CH * max 1 (RS * Lα) ^ D, fun ε hε k => ?_⟩
  have h := cond_p2_nilp α hsub hD hCH hball hS hF hLα hα ε hε k
  have hb : 0 ≤ CH * max 1 (RS * Lα) ^ D * (1 + k / ε) ^ D := by
    have : (0 : ℝ) ≤ CH := zero_le_one.trans hCH
    positivity
  exact ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top h, ENNReal.toReal_le_of_le_ofReal hb h⟩

end P2

section Diameter

variable {X : Type*} [PseudoEMetricSpace X] {G : Type*} [Group G] [PseudoEMetricSpace G]

@[blueprint "lem:p2-diameter"
  (statement := /-- (Diameter envelope.) Under the hypotheses of `lem:p2-wordball-subset-ball`
    and with the orbit map $L_\alpha$-Lipschitz, for all $f, g \in B(k,F)$,
    $$d_\infty(f, g) \le 2 L_\alpha R_S k ,$$
    i.e. $\mathrm{diam}_\infty B(k,F) \le 2L_\alpha R_S k$ (and a fortiori
    $D_k(S) \le 2 L_\alpha R_S k$ for every sample $S$). -/)]
theorem uniformDist_le_of_mem_wordBall (α : G →* Function.End X) {F : Set (X → X)}
    (hsub : ∀ g h : G, edist 1 (g * h) ≤ edist 1 g + edist 1 h)
    {Sg : Set G} {RS : ℝ≥0} (hS : ∀ s ∈ Sg, edist 1 s ≤ RS) (hF : F ⊆ orbitMap α '' Sg)
    {Lα : ℝ≥0} (hα : LipschitzWith Lα (fun g => toUnifMaps (orbitMap α g))) (k : ℕ)
    {f g : X → X} (hf : f ∈ wordBall F k) (hg : g ∈ wordBall F k) :
    uniformDist f g ≤ 2 * Lα * RS * k := by
  /-- Write $f = \alpha(a)$, $g = \alpha(b)$ with $d_H(e,a), d_H(e,b) \le kR_S$
    (`lem:p2-wordball-subset-ball`). Then $d_\infty(\alpha(a), \alpha(b)) \le L_\alpha d_H(a,b)
    \le L_\alpha (d_H(a,e) + d_H(e,b)) \le 2 L_\alpha R_S k$. -/
  obtain ⟨a, ha, rfl⟩ := wordBall_subset_image_closedBall α hsub hS hF k hf
  obtain ⟨b, hb, rfl⟩ := wordBall_subset_image_closedBall α hsub hS hF k hg
  rw [mem_closedEBall'] at ha hb
  calc uniformDist (orbitMap α a) (orbitMap α b)
      = edist (toUnifMaps (orbitMap α a)) (toUnifMaps (orbitMap α b)) := rfl
    _ ≤ Lα * edist a b := hα.edist_le_mul a b
    _ ≤ Lα * (edist 1 a + edist 1 b) := by
        gcongr
        rw [edist_comm 1 a]
        exact edist_triangle a 1 b
    _ ≤ Lα * (((k * RS : ℝ≥0) : ℝ≥0∞) + ((k * RS : ℝ≥0) : ℝ≥0∞)) := by gcongr
    _ = 2 * Lα * RS * k := by push_cast; ring

@[blueprint "cond:p2-nilp-compact"
  (statement := /-- On a bounded state space, $d(x,y) \le D_{\mathcal X}$ for all
    $x, y \in \mathcal X$, every pair of self-maps satisfies
    $d_\infty(f,g) \le D_{\mathcal X}$; in particular
    $\mathrm{diam}_\infty B(k,F) \le \mathrm{diam}(\mathcal X)$ for every $k$. -/)]
theorem uniformDist_le_of_bounded {Dx : ℝ≥0∞} (hX : ∀ x y : X, edist x y ≤ Dx) (f g : X → X) :
    uniformDist f g ≤ Dx := by
  /-- $\sup_x d(f(x), g(x)) \le D_{\mathcal X}$ termwise. -/
  exact iSup_le fun x => hX _ _

end Diameter

end LeanDeepgen
