import Mathlib
import Architect
import LeanDeepgen.Setting.Metrics
import LeanDeepgen.Setting.Covering
import LeanDeepgen.Growth.Defs
import FoML.ToMathlib.CoveringNumber

/-!
# Basic lemmas on covering numbers of hidden-layer classes (paper App. F.2)

* `lem:lipschitz-embedding`: a `K`-Lipschitz map sends `ε`-covers (resp. packings) to
  `Kε`-covers (resp. packings), so `N(φ(A), Kε) ≤ N(A, ε)` (external / internal covering numbers
  and packing numbers); being Mathlib-generic, these live in
  `FoML.ToMathlib.CoveringNumber` (`externalCoveringNumber_image_le`,
  `coveringNumber_image_le`, `packingNumber_image_le`).
* `lem:submultiplicativity`: for `F` uniformly `λ`-Lipschitz,
  `N^ext(F ∘ G, ε + λ δ) ≤ N^ext(F, ε) · N^ext(G, δ)` in `(𝒳^𝒳, d_∞)`.
* `lem:probes-packing`: evaluation on finitely many probes (`evalProbes`, defined in
  `LeanDeepgen.Growth.Defs`) is `1`-Lipschitz from `(𝒳^𝒳, d_∞)` to the sup-metric on `𝒳^m`; a
  `δ`-separated set of evaluations of size `M` forces `N^ext(A, ε) ≥ M` for `2ε < δ`.
-/

open scoped NNReal ENNReal
open Metric

open FoML.ToMathlib

namespace LeanDeepgen

section Submultiplicativity

variable {X : Type*} [PseudoEMetricSpace X]

@[blueprint "lem:submultiplicativity"
  (statement := /-- (Sub-multiplicativity.) Let $F, G \subseteq \mathcal X^{\mathcal X}$ and
    suppose every $f \in F$ is $\lambda$-Lipschitz. Then for all $\varepsilon, \delta \ge 0$,
    $$N^{\mathrm{ext}}(F \circ G, d_\infty, \varepsilon + \lambda\delta)
      \le N^{\mathrm{ext}}(F, d_\infty, \varepsilon)\, N^{\mathrm{ext}}(G, d_\infty, \delta).$$
    (This is the paper's
    $N(FG, \varepsilon + \delta) \le N(F, \varepsilon/\rho) N(G, \delta/\lambda)$
    with $\rho = 1$, since right composition is $1$-Lipschitz for $d_\infty$; we write
    $\lambda\delta$ in place of $\delta/\lambda$ to avoid dividing by $\lambda = 0$.) -/)]
theorem externalCoveringNumber_comp_le (F G : Set (X → X)) {lam : ℝ≥0}
    (hF : ∀ f ∈ F, LipschitzWith lam f) (ε δ : ℝ≥0) :
    externalCoveringNumber (X := UnifMaps X) (ε + lam * δ) (Set.image2 (fun f g => f ∘ g) F G) ≤
      externalCoveringNumber (X := UnifMaps X) ε F *
        externalCoveringNumber (X := UnifMaps X) δ G := by
  /-- Take an $\varepsilon$-cover $C_F$ of $F$ and a $\delta$-cover $C_G$ of $G$ of minimal
    cardinality. For $f \in F$, $g \in G$ pick $f' \in C_F$, $g' \in C_G$ with
    $d_\infty(f,f') \le \varepsilon$, $d_\infty(g,g') \le \delta$; then
    $d_\infty(f \circ g, f' \circ g') \le d_\infty(f \circ g, f \circ g')
    + d_\infty(f \circ g', f' \circ g') \le \lambda\delta + \varepsilon$,
    so $C_F \circ C_G$ (of cardinality $\le |C_F|\,|C_G|$) is a cover of $F \circ G$. -/
  obtain ⟨CF, hCF, hCFe⟩ :=
    exists_isCover_encard_eq_externalCoveringNumber (X := UnifMaps X) ε F
  obtain ⟨CG, hCG, hCGe⟩ :=
    exists_isCover_encard_eq_externalCoveringNumber (X := UnifMaps X) δ G
  have hcover : IsCover (X := UnifMaps X) (ε + lam * δ)
      (Set.image2 (fun f g => f ∘ g) F G) (Set.image2 (fun f g => f ∘ g) CF CG) := by
    rintro _ ⟨f, hf, g, hg, rfl⟩
    obtain ⟨f', hf', hff'⟩ := hCF hf
    obtain ⟨g', hg', hgg'⟩ := hCG hg
    refine ⟨f' ∘ g', ⟨f', hf', g', hg', rfl⟩, ?_⟩
    have h1 : edist (toUnifMaps (f ∘ g)) (toUnifMaps (f ∘ g')) ≤ lam * δ := by
      rw [edist_toUnifMaps]
      calc uniformDist (f ∘ g) (f ∘ g') ≤ lam * uniformDist g g' :=
            uniformDist_comp_left_le (hF f hf)
        _ ≤ lam * δ := by gcongr; exact hgg'
    have h2 : edist (toUnifMaps (f ∘ g')) (toUnifMaps (f' ∘ g')) ≤ ε := by
      rw [edist_toUnifMaps]
      exact uniformDist_comp_right_le.trans hff'
    calc edist (toUnifMaps (f ∘ g)) (toUnifMaps (f' ∘ g'))
        ≤ edist (toUnifMaps (f ∘ g)) (toUnifMaps (f ∘ g')) +
            edist (toUnifMaps (f ∘ g')) (toUnifMaps (f' ∘ g')) := edist_triangle _ _ _
      _ ≤ lam * δ + ε := add_le_add h1 h2
      _ = ((ε + lam * δ : ℝ≥0) : ℝ≥0∞) := by push_cast; ring
  rw [← hCFe, ← hCGe]
  refine hcover.externalCoveringNumber_le_encard.trans ?_
  calc (Set.image2 (fun f g => f ∘ g) CF CG : Set (UnifMaps X)).encard
      = ((fun p : UnifMaps X × UnifMaps X => toUnifMaps (p.1 ∘ p.2)) '' (CF ×ˢ CG)).encard := by
        rw [Set.image_prod]; rfl
    _ ≤ (CF ×ˢ CG).encard := Set.encard_image_le _ _
    _ = CF.encard * CG.encard := Set.encard_prod

end Submultiplicativity

section Probes

variable {X : Type*} [PseudoEMetricSpace X]

@[blueprint "lem:eval-probes-lipschitz"
  (statement := /-- The evaluation map $\mathrm{ev}_P$ is $1$-Lipschitz from $d_\infty$ to the
    sup-metric on $\mathcal X^J$. -/)]
theorem lipschitzWith_evalProbes {ι : Type*} [Fintype ι] (P : ι → X) :
    LipschitzWith 1 (evalProbes P) := by
  /-- $\max_j d(f(p_j), g(p_j)) \le \sup_x d(f(x), g(x))$. -/
  refine LipschitzWith.of_edist_le fun f g => ?_
  exact edist_pi_le_iff.2 fun j => edist_eval_le_unifMaps f g (P j)

@[blueprint "lem:probes-packing"
  (statement := /-- (Probes and packing.) Let $A \subseteq (\mathcal X^{\mathcal X}, d_\infty)$,
    let $P$ be a finite family of probes and let $T \subseteq \mathrm{ev}_P(A)$ be
    $\delta$-separated: $d_{\max}(y,z) \ge \delta$ for all distinct $y, z \in T$.
    Then for every $\varepsilon$ with $2\varepsilon < \delta$,
    $|T| \le N^{\mathrm{ext}}(A, d_\infty, \varepsilon)$. -/)]
theorem encard_le_externalCoveringNumber_of_probes {ι : Type*} [Fintype ι] (P : ι → X)
    {A : Set (UnifMaps X)} {T : Set (ι → X)} (hT : T ⊆ evalProbes P '' A) {δ : ℝ≥0}
    (hsep : ∀ y ∈ T, ∀ z ∈ T, y ≠ z → (δ : ℝ≥0∞) ≤ edist y z) {ε : ℝ≥0} (hε : 2 * ε < δ) :
    T.encard ≤ externalCoveringNumber ε A := by
  /-- $T$ is $2\varepsilon$-separated (strictly), so $|T| \le M(\mathrm{ev}_P(A), 2\varepsilon)
    \le M(A, 2\varepsilon) \le N^{\mathrm{ext}}(A, \varepsilon)$ by the Lipschitz embedding lemma
    (with $K = 1$) and the packing–covering comparison. -/
  have hTsep : IsSeparated ((2 * ε : ℝ≥0) : ℝ≥0∞) T := fun y hy z hz hne =>
    (ENNReal.coe_lt_coe.mpr hε).trans_le (hsep y hy z hz hne)
  calc T.encard ≤ packingNumber (2 * ε) (evalProbes P '' A) :=
        hTsep.encard_le_packingNumber hT
    _ = packingNumber (1 * (2 * ε)) (evalProbes P '' A) := by rw [one_mul]
    _ ≤ packingNumber (2 * ε) A := packingNumber_image_le (lipschitzWith_evalProbes P) _ _
    _ ≤ externalCoveringNumber ε A := packingNumber_two_mul_le_externalCoveringNumber ε A

@[blueprint "lem:probes-packing-internal"
  (statement := /-- Under the hypotheses of the previous lemma, also
    $|T| \le N(A, d_\infty, \varepsilon)$ (internal covering number). -/)]
theorem encard_le_coveringNumber_of_probes {ι : Type*} [Fintype ι] (P : ι → X)
    {A : Set (UnifMaps X)} {T : Set (ι → X)} (hT : T ⊆ evalProbes P '' A) {δ : ℝ≥0}
    (hsep : ∀ y ∈ T, ∀ z ∈ T, y ≠ z → (δ : ℝ≥0∞) ≤ edist y z) {ε : ℝ≥0} (hε : 2 * ε < δ) :
    T.encard ≤ coveringNumber ε A :=
  (encard_le_externalCoveringNumber_of_probes P hT hsep hε).trans
    (externalCoveringNumber_le_coveringNumber ε A)

@[blueprint "lem:probes-packing-family"
  (statement := /-- (Indexed form of `lem:probes-packing`.) Let $(g_i)_{i \in I}$ be a family
    of maps in $A \subseteq (\mathcal X^{\mathcal X}, d_\infty)$ and $P$ a finite family of probes
    such that $d_{\max}(\mathrm{ev}_P(g_i), \mathrm{ev}_P(g_j)) \ge \delta > 0$ for all $i \ne j$.
    Then $|I| \le N^{\mathrm{ext}}(A, d_\infty, \varepsilon)$ whenever $2\varepsilon < \delta$. -/)]
theorem card_le_externalCoveringNumber_of_probes {ι κ : Type*} [Fintype κ] (P : κ → X)
    {A : Set (UnifMaps X)} (g : ι → UnifMaps X) (hg : ∀ i, g i ∈ A) {δ : ℝ≥0} (hδ : 0 < δ)
    (hsep : ∀ i j, i ≠ j → (δ : ℝ≥0∞) ≤ edist (evalProbes P (g i)) (evalProbes P (g j)))
    {ε : ℝ≥0} (hε : 2 * ε < δ) :
    ENat.card ι ≤ externalCoveringNumber ε A := by
  /-- The map $i \mapsto \mathrm{ev}_P(g_i)$ is injective (distinct indices have evaluations at
    distance $\ge \delta > 0$), and its range is a $\delta$-separated subset of
    $\mathrm{ev}_P(A)$; apply `lem:probes-packing`. -/
  have hinj : Function.Injective (fun i => evalProbes P (g i)) := by
    intro i j hij
    by_contra hne
    have h := hsep i j hne
    simp only [hij, edist_self, nonpos_iff_eq_zero, ENNReal.coe_eq_zero] at h
    exact hδ.ne' h
  have hT : Set.range (fun i => evalProbes P (g i)) ⊆ evalProbes P '' A := by
    rintro _ ⟨i, rfl⟩
    exact ⟨g i, hg i, rfl⟩
  refine hinj.encard_range.trans
    (encard_le_externalCoveringNumber_of_probes P hT (δ := δ) ?_ hε)
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
  exact hsep i j (fun h => hne (by rw [h]))

end Probes

end LeanDeepgen
