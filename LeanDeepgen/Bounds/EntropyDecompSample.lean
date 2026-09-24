import Mathlib
import Architect
import FoML
import LeanDeepgen.Setting.Metrics
import LeanDeepgen.Setting.Covering
import LeanDeepgen.Setting.Hypothesis
import LeanDeepgen.Setting.Rademacher
import LeanDeepgen.Setting.Assumptions
import FoML.ToFoML.CoveringNumberBridge
import LeanDeepgen.Bounds.EntropyDecomp

/-!
# Deterministic entropy decomposition on the sample

The empirical-metric version of `LeanDeepgen.Bounds.EntropyDecomp` (Theorem
`thm:rad.decomp.ent.ent`, Appendix D; PLAN.md §5 row W8): the bound on `R̂_S(H ∘ F)` only needs
the output-layer class `H` to be Lipschitz *on the points reached by the sample*
`{f(x_i) : f ∈ F, i ≤ n}`, and only needs covering numbers in the empirical metrics `‖·‖_S`
(on real functions) and `d_S` (on self-maps).

The composition covering lemma in the empirical metric reads, pointwise on the sample,
`‖h ∘ f − h_a ∘ f_b‖_S ≤ ‖h ∘ f − h ∘ f_b‖_S + ‖h ∘ f_b − h_a ∘ f_b‖_S
≤ L_H d_S(f, f_b) + ‖h − h_a‖_{f_b ∘ S}`. Two features of this estimate dictate the shape of the
assumptions:

* the second term is the empirical norm of `h − h_a` on the *pushed-forward sample*
  `f_b ∘ S = (f_b(x_1), …, f_b(x_n))`, not on `S`; so `H` must be covered in the metric
  `‖·‖_{f ∘ S}` uniformly over `f ∈ F` (`def:pushed-covering-number`; the paper's proof avoids
  this by covering `H` in the sup norm, which dominates every empirical norm);
* the first term uses the sample-Lipschitz property of `h` at the points `f(x_i)`, `f_b(x_i)`,
  so the centres `f_b` of the cover of `F` must themselves lie in `F` (otherwise `f_b(x_i)` is
  not a reachable point and `‖·‖_{f_b ∘ S}` is not an admissible metric). Hence the cover of `F`
  is *internal* (Mathlib's `coveringNumber`), and passing to the external covering numbers of the
  assumptions costs a factor `2` in the radius of `F` (`N(F, 2r) ≤ N^ext(F, r)`), i.e. the scale
  `x/(8 L_H)` in the final bound instead of the sup-norm theorem's `x/(4 L_H)`.

Contents (the definitions — the pseudometric space `EmpFun S = (ℝ^X, ‖·‖_S)` (FoML's
`empiricalPMet S`, `def:emp-fun`), the reachable set `reachSet`, the uniform pushed-forward
covering number `pushedCoveringNumber`, the assumptions `EntReadoutSample`,
`EntTransitionSample` and the root entropies `entHS`, `entFS` — live in
`LeanDeepgen.Setting.Assumptions`):

* `lem:comp-cover-sample`, `lem:ent-composition-covering-sample-int`,
  `lem:ent-composition-covering-sample`, `lem:ent-composition-entropy-sample`: the composition
  covering lemma in the empirical metrics;
* `lem:totallyBounded-empiricalFunctionSpace-sample`, `lem:foml-covering-le-external-empFun`:
  the (now isometric) bridge to FoML's `EmpiricalFunctionSpace`;
* `thm:rad.decomp.ent.ent-sample-foml`, `thm:rad.decomp.ent.ent-sample`: the theorem;
* `lem:pushed-covering-le-unif`, `lem:emp-covering-le-unif`, `cor:rad.decomp.ent.ent-of-sample`:
  the sup-norm assumptions imply the sample assumptions, and the sup-norm theorem (with the scale
  `x/(8 L_H)`) follows from the sample theorem.

All results are fully proved.
-/

open scoped NNReal ENNReal
open Metric

open FoML.ToMathlib

namespace LeanDeepgen

section EmpFun

variable {X : Type*} {n : ℕ}

@[blueprint "lem:emp-norm-comp-right"
  (statement := /-- $\|u \circ f - v \circ f\|_S = \|u - v\|_{f \circ S}$: the empirical norm of
    a composition is the empirical norm on the pushed-forward sample
    $f \circ S = (f(x_1), \dots, f(x_n))$. -/)]
theorem empNorm_comp (S : Fin n → X) (f : X → X) (u v : X → ℝ) :
    empNorm S (u ∘ f) (v ∘ f) = empNorm (f ∘ S) u v := rfl

@[blueprint "lem:isCover-empFun"
  (statement := /-- A set $C$ is an $\varepsilon$-cover of $A$ for $\|\cdot\|_S$ iff every
    $u \in A$ has some $c \in C$ with $\|u - c\|_S \le \varepsilon$. -/)]
theorem isCover_empFun_iff (S : Fin n → X) (ε : ℝ≥0) (A C : Set (X → ℝ)) :
    IsCover (X := EmpFun S) ε A C ↔ ∀ u ∈ A, ∃ c ∈ C, empNorm S u c ≤ ε := by
  constructor
  · intro h u hu
    obtain ⟨c, hc, hd⟩ := h hu
    refine ⟨c, hc, ?_⟩
    have hd' : edist (toEmpFun S u) (toEmpFun S c) ≤ ε := hd
    rwa [edist_dist, ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top, ENNReal.coe_toReal,
      dist_empFun] at hd'
  · intro h u hu
    obtain ⟨c, hc, hd⟩ := h u hu
    refine ⟨c, hc, ?_⟩
    change edist (toEmpFun S u) (toEmpFun S c) ≤ ε
    rw [edist_dist, dist_empFun, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hd

end EmpFun

variable {X : Type*} [PseudoMetricSpace X] {n : ℕ}

@[blueprint "lem:isCover-empSpace"
  (statement := /-- A set $C$ is an $\varepsilon$-cover of $A$ for $d_S$ iff every $f \in A$ has
    some $c \in C$ with $d_S(f, c) \le \varepsilon$. -/)]
theorem isCover_empSpace_iff (S : Fin n → X) (ε : ℝ≥0) (A C : Set (X → X)) :
    IsCover (X := EmpSpace S) ε A C ↔ ∀ f ∈ A, ∃ c ∈ C, empDist S f c ≤ ε := by
  constructor
  · intro h f hf
    obtain ⟨c, hc, hd⟩ := h hf
    refine ⟨c, hc, ?_⟩
    have hd' : @edist (EmpSpace S) _ f c ≤ ε := hd
    rwa [edist_dist, ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top, ENNReal.coe_toReal,
      dist_empSpace] at hd'
  · intro h f hf
    obtain ⟨c, hc, hd⟩ := h f hf
    refine ⟨c, hc, ?_⟩
    change @edist (EmpSpace S) _ f c ≤ ε
    rw [edist_dist, dist_empSpace, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hd

omit [PseudoMetricSpace X] in
@[blueprint "lem:pushed-covering-number-le"
  (statement := /-- $N^{\mathrm{ext}}(H, \|\cdot\|_{f \circ S}, u) \le N_{S,F}(H, u)$ for
    $f \in F$. -/)]
theorem externalCoveringNumber_le_pushedCoveringNumber (S : Fin n → X) {F : Set (X → X)}
    (H : Set (X → ℝ)) {f : X → X} (hf : f ∈ F) (ε : ℝ≥0) :
    externalCoveringNumber (X := EmpFun (f ∘ S)) ε H ≤ pushedCoveringNumber S F H ε := by
  unfold pushedCoveringNumber
  exact le_iSup₂_of_le f hf le_rfl

omit [PseudoMetricSpace X] in
@[blueprint "lem:pushed-covering-number-anti"
  (statement := /-- $u \mapsto N_{S,F}(H, u)$ is antitone. -/)]
theorem pushedCoveringNumber_anti (S : Fin n → X) (F : Set (X → X)) (H : Set (X → ℝ))
    {ε δ : ℝ≥0} (h : ε ≤ δ) :
    pushedCoveringNumber S F H δ ≤ pushedCoveringNumber S F H ε :=
  iSup₂_mono fun _ _ => externalCoveringNumber_anti h

omit [PseudoMetricSpace X] in
@[blueprint "lem:pushed-covering-number-pos"
  (statement := /-- $N_{S,F}(H, u) > 0$ when $H, F \ne \emptyset$. -/)]
theorem pushedCoveringNumber_pos (S : Fin n → X) {F : Set (X → X)} {H : Set (X → ℝ)}
    (hH : H.Nonempty) (hF : F.Nonempty) (ε : ℝ≥0) : 0 < pushedCoveringNumber S F H ε := by
  obtain ⟨f, hf⟩ := hF
  exact ((externalCoveringNumber_pos_iff (X := EmpFun (f ∘ S)) (ε := ε)).mpr hH).trans_le
    (externalCoveringNumber_le_pushedCoveringNumber S H hf ε)

section CompositionCover

variable {S : Fin n → X} {H : Set (X → ℝ)} {F : Set (X → X)} {LH : ℝ≥0}

@[blueprint "lem:emp-norm-comp-le-emp-dist"
  (statement := /-- If $|h(f(x_i)) - h(g(x_i))| \le c\, d(f(x_i), g(x_i))$ for every $i$
    ($c \ge 0$), then $\|h \circ f - h \circ g\|_S \le c\, d_S(f, g)$. -/)]
theorem empNorm_comp_le_mul_empDist {c : ℝ} (hc : 0 ≤ c) (h : X → ℝ) (f g : X → X)
    (hfg : ∀ i, |h (f (S i)) - h (g (S i))| ≤ c * dist (f (S i)) (g (S i))) :
    empNorm S (h ∘ f) (h ∘ g) ≤ c * empDist S f g := by
  unfold empNorm empDist
  simp only [Function.comp_apply]
  have hsum : ∑ i, |h (f (S i)) - h (g (S i))| ^ 2 ≤
      c ^ 2 * ∑ i, dist (f (S i)) (g (S i)) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hfg i) 2
  calc Real.sqrt ((1 / (n : ℝ)) * ∑ i, |h (f (S i)) - h (g (S i))| ^ 2)
      ≤ Real.sqrt ((1 / (n : ℝ)) * (c ^ 2 * ∑ i, dist (f (S i)) (g (S i)) ^ 2)) := by
        apply Real.sqrt_le_sqrt
        gcongr
    _ = c * Real.sqrt ((1 / (n : ℝ)) * ∑ i, dist (f (S i)) (g (S i)) ^ 2) := by
        rw [mul_left_comm, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

@[blueprint "lem:comp-cover-sample"
  (statement := /-- \textbf{Composition of covers on the sample.} Let every $h \in H$ be
    $L_H$-Lipschitz on $\mathcal R_S(F)$, let $C_F \subseteq F$ be an $r_2$-cover of $F$ for $d_S$
    with centres in $F$, and for every $f_b \in C_F$ let $C_H(f_b)$ be an $r_1$-cover of $H$ for
    $\|\cdot\|_{f_b \circ S}$ (centres anywhere). Then
    $\{h_a \circ f_b : f_b \in C_F,\ h_a \in C_H(f_b)\}$ is an $(r_1 + L_H r_2)$-cover of
    $H \circ F$ for $\|\cdot\|_S$:
    $\|h \circ f - h_a \circ f_b\|_S \le \|h \circ f - h \circ f_b\|_S
    + \|h \circ f_b - h_a \circ f_b\|_S \le L_H d_S(f, f_b) + \|h - h_a\|_{f_b \circ S}$,
    where the first estimate uses the Lipschitz property of $h$ at the reachable points
    $f(x_i), f_b(x_i)$ (this is where $f_b \in F$ is needed). -/)]
theorem isCover_compClass_sample
    (hlip : ∀ h ∈ H, ∀ x ∈ reachSet S F, ∀ y ∈ reachSet S F, |h x - h y| ≤ LH * dist x y)
    {r₁ r₂ : ℝ≥0} {CF : Set (X → X)} (hCFF : CF ⊆ F) (hCF : IsCover (X := EmpSpace S) r₂ F CF)
    {CH : (X → X) → Set (X → ℝ)}
    (hCH : ∀ b ∈ CF, IsCover (X := EmpFun (b ∘ S)) r₁ H (CH b)) :
    IsCover (X := EmpFun S) (r₁ + LH * r₂) (compClass H F)
      (⋃ b ∈ CF, (fun h : X → ℝ => h ∘ b) '' CH b) := by
  rw [isCover_empFun_iff]
  rintro _ ⟨h, hh, f, hf, rfl⟩
  obtain ⟨b, hb, hdb⟩ := (isCover_empSpace_iff S r₂ F CF).mp hCF f hf
  obtain ⟨a, ha, hda⟩ := (isCover_empFun_iff (b ∘ S) r₁ H (CH b)).mp (hCH b hb) h hh
  refine ⟨a ∘ b, Set.mem_iUnion₂.mpr ⟨b, hb, Set.mem_image_of_mem _ ha⟩, ?_⟩
  have htri : empNorm S (h ∘ f) (a ∘ b) ≤
      empNorm S (h ∘ f) (h ∘ b) + empNorm S (h ∘ b) (a ∘ b) := by
    have := dist_triangle (toEmpFun S (h ∘ f)) (toEmpFun S (h ∘ b)) (toEmpFun S (a ∘ b))
    simpa only [dist_empFun] using this
  have h1 : empNorm S (h ∘ f) (h ∘ b) ≤ LH * empDist S f b :=
    empNorm_comp_le_mul_empDist LH.coe_nonneg h f b fun i =>
      hlip h hh _ (mem_reachSet hf i) _ (mem_reachSet (hCFF hb) i)
  have h2 : empNorm S (h ∘ b) (a ∘ b) ≤ r₁ := by rw [empNorm_comp]; exact hda
  calc empNorm S (h ∘ f) (a ∘ b) ≤ empNorm S (h ∘ f) (h ∘ b) + empNorm S (h ∘ b) (a ∘ b) := htri
    _ ≤ LH * r₂ + r₁ :=
        add_le_add (h1.trans (mul_le_mul_of_nonneg_left hdb LH.coe_nonneg)) h2
    _ = ((r₁ + LH * r₂ : ℝ≥0) : ℝ) := by push_cast; ring

omit [PseudoMetricSpace X] in
@[blueprint "lem:comp-class-empty-iff"
  (statement := /-- $H \circ F = \emptyset$ iff $H = \emptyset$ or $F = \emptyset$. -/)]
theorem compClass_nonempty_iff : (compClass H F).Nonempty ↔ H.Nonempty ∧ F.Nonempty := by
  constructor
  · rintro ⟨u, h, hh, f, hf, rfl⟩
    exact ⟨⟨h, hh⟩, ⟨f, hf⟩⟩
  · rintro ⟨⟨h, hh⟩, ⟨f, hf⟩⟩
    exact ⟨h ∘ f, h, hh, f, hf, rfl⟩

@[blueprint "lem:ent-composition-covering-sample-int"
  (statement := /-- For $H$ $L_H$-Lipschitz on $\mathcal R_S(F)$ and radii $r_1, r_2 \ge 0$,
    $N^{\mathrm{ext}}(H \circ F, \|\cdot\|_S, r_1 + L_H r_2) \le N_{S,F}(H, r_1) \cdot
    N(F, d_S, r_2)$, where $N(F, d_S, \cdot)$ is the internal covering number (centres in $F$).
    Proof: choose a minimal internal cover $C_F$ of $F$ and, for each $f_b \in C_F$, a minimal
    external cover of $H$ for $\|\cdot\|_{f_b \circ S}$; apply \texttt{lem:comp-cover-sample} and
    count. -/)]
theorem externalCoveringNumber_compClass_le_sample
    (hlip : ∀ h ∈ H, ∀ x ∈ reachSet S F, ∀ y ∈ reachSet S F, |h x - h y| ≤ LH * dist x y)
    (r₁ r₂ : ℝ≥0) :
    externalCoveringNumber (X := EmpFun S) (r₁ + LH * r₂) (compClass H F) ≤
      pushedCoveringNumber S F H r₁ * coveringNumber (X := EmpSpace S) r₂ F := by
  classical
  rcases (compClass H F).eq_empty_or_nonempty with hemp | hne
  · rw [hemp]
    exact (externalCoveringNumber_empty (X := EmpFun S) _).trans_le bot_le
  obtain ⟨hHne, hFne⟩ := compClass_nonempty_iff.mp hne
  have hNpos : 0 < pushedCoveringNumber S F H r₁ := pushedCoveringNumber_pos S hHne hFne r₁
  have hCpos : 0 < coveringNumber (X := EmpSpace S) r₂ F := coveringNumber_pos_iff.mpr hFne
  by_cases hN : pushedCoveringNumber S F H r₁ = ⊤
  · rw [hN, ENat.top_mul hCpos.ne']
    exact le_top
  by_cases hC : coveringNumber (X := EmpSpace S) r₂ F = ⊤
  · rw [hC, ENat.mul_top hNpos.ne']
    exact le_top
  obtain ⟨CF, hCFF, hCFfin, hCFcov, hCFe⟩ :=
    exists_set_encard_eq_coveringNumber (X := EmpSpace S) hC
  choose CH hCH hCHe using fun b : X → X =>
    exists_isCover_encard_eq_externalCoveringNumber (X := EmpFun (b ∘ S)) r₁ H
  have hcov := isCover_compClass_sample hlip hCFF hCFcov (fun b _ => hCH b)
  have hU : (⋃ b ∈ CF, (fun h : X → ℝ => h ∘ b) '' CH b) =
      ⋃ b ∈ hCFfin.toFinset, (fun h : X → ℝ => h ∘ b) '' CH b := by
    simp only [Set.Finite.mem_toFinset]
  calc externalCoveringNumber (X := EmpFun S) (r₁ + LH * r₂) (compClass H F)
      ≤ (⋃ b ∈ CF, (fun h : X → ℝ => h ∘ b) '' CH b).encard :=
        hcov.externalCoveringNumber_le_encard
    _ ≤ ∑ b ∈ hCFfin.toFinset, ((fun h : X → ℝ => h ∘ b) '' CH b).encard := by
        rw [hU]
        exact Finset.set_encard_biUnion_le _ _
    _ ≤ ∑ _b ∈ hCFfin.toFinset, pushedCoveringNumber S F H r₁ := by
        refine Finset.sum_le_sum fun b hb => (Set.encard_image_le _ _).trans ?_
        exact (hCHe b).trans_le (externalCoveringNumber_le_pushedCoveringNumber S H
          (hCFF (hCFfin.mem_toFinset.mp hb)) r₁)
    _ = (hCFfin.toFinset.card : ℕ∞) * pushedCoveringNumber S F H r₁ := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = coveringNumber (X := EmpSpace S) r₂ F * pushedCoveringNumber S F H r₁ := by
        rw [← hCFe, hCFfin.encard_eq_coe_toFinset_card]
    _ = _ := mul_comm _ _

@[blueprint "lem:ent-composition-covering-sample"
  (statement := /-- \textbf{Composition covering lemma on the sample.} If every $h \in H$ is
    $L_H$-Lipschitz on $\mathcal R_S(F)$ then for every $\varepsilon \ge 0$,
    $$N^{\mathrm{ext}}(H \circ F, \|\cdot\|_S, \varepsilon) \le
    N_{S,F}(H, \varepsilon/2)\cdot N^{\mathrm{ext}}(F, d_S, \varepsilon/(4L_H)).$$
    (For $L_H = 0$ the second radius is $0$ by the convention $x/0 = 0$.) Compared with the
    sup-norm lemma \texttt{lem:ent-composition-covering}, the radius of $F$ is
    $\varepsilon/(4L_H)$ instead of $\varepsilon/(2L_H)$: the cover of $F$ must have its centres
    in $F$, and $N(F, d_S, 2r) \le N^{\mathrm{ext}}(F, d_S, r)$. -/)]
theorem externalCoveringNumber_compClass_le_mul_sample
    (hlip : ∀ h ∈ H, ∀ x ∈ reachSet S F, ∀ y ∈ reachSet S F, |h x - h y| ≤ LH * dist x y)
    (ε : ℝ≥0) :
    externalCoveringNumber (X := EmpFun S) ε (compClass H F) ≤
      pushedCoveringNumber S F H (ε / 2) *
        externalCoveringNumber (X := EmpSpace S) (ε / (4 * LH)) F := by
  have hrad : ε / 2 + LH * (ε / (2 * LH)) ≤ ε := by
    rcases eq_or_ne LH 0 with hLH | hLH
    · subst hLH
      simp only [zero_mul, add_zero]
      exact half_le_self zero_le
    · rw [show LH * (ε / (2 * LH)) = ε / 2 by
        rw [mul_div_assoc', mul_comm, mul_div_mul_right _ _ hLH]]
      rw [add_halves]
  have h2 : (2 : ℝ≥0) * (ε / (4 * LH)) = ε / (2 * LH) := by
    rcases eq_or_ne LH 0 with hLH | hLH
    · subst hLH; simp
    · rw [mul_div_assoc', div_eq_div_iff (by positivity) (by positivity)]
      ring
  calc externalCoveringNumber (X := EmpFun S) ε (compClass H F)
      ≤ externalCoveringNumber (X := EmpFun S) (ε / 2 + LH * (ε / (2 * LH))) (compClass H F) :=
        externalCoveringNumber_anti hrad
    _ ≤ pushedCoveringNumber S F H (ε / 2) * coveringNumber (X := EmpSpace S) (ε / (2 * LH)) F :=
        externalCoveringNumber_compClass_le_sample hlip _ _
    _ ≤ _ := by
        gcongr
        rw [← h2]
        exact coveringNumber_two_mul_le_externalCoveringNumber _ _

omit [PseudoMetricSpace X] in
@[blueprint "lem:entHS-nonneg"
  (statement := /-- $\mathcal E_{H,S}(u) \ge 0$. -/)]
theorem entHS_nonneg (S : Fin n → X) (F : Set (X → X)) (H : Set (X → ℝ)) (u : ℝ) :
    0 ≤ entHS S F H u := Real.sqrt_nonneg _

@[blueprint "lem:entFS-nonneg"
  (statement := /-- $\mathcal E_{F,S}(v) \ge 0$. -/)]
theorem entFS_nonneg (S : Fin n → X) (F : Set (X → X)) (v : ℝ) : 0 ≤ entFS S F v :=
  Real.sqrt_nonneg _

@[blueprint "lem:ent-composition-entropy-sample"
  (statement := /-- \textbf{Entropy of the composition class on the sample.} Let every $h \in H$
    be $L_H$-Lipschitz on $\mathcal R_S(F)$ with $L_H > 0$, and let $\varepsilon \in \mathbb R$ be
    such that $N_{S,F}(H, \varepsilon/2)$ and $N^{\mathrm{ext}}(F, d_S, \varepsilon/(4L_H))$ are
    finite. Then
    $$\sqrt{\log N^{\mathrm{ext}}(H \circ F, \|\cdot\|_S, \varepsilon)}
    \le \mathcal E_{H,S}(\varepsilon/2) + \mathcal E_{F,S}(\varepsilon/(4L_H)).$$ -/)]
theorem sqrt_log_compClass_le_sample
    (hlip : ∀ h ∈ H, ∀ x ∈ reachSet S F, ∀ y ∈ reachSet S F, |h x - h y| ≤ LH * dist x y)
    (hLH : 0 < LH) {ε : ℝ}
    (hHfin : pushedCoveringNumber S F H (Real.toNNReal (ε / 2)) ≠ ⊤)
    (hFfin : externalCoveringNumber (X := EmpSpace S) (Real.toNNReal (ε / (4 * LH))) F ≠ ⊤) :
    Real.sqrt (Real.log
        (externalCoveringNumber (X := EmpFun S) (Real.toNNReal ε) (compClass H F) : ℝ≥0∞).toReal)
      ≤ entHS S F H (ε / 2) + entFS S F (ε / (4 * LH)) := by
  have h1 : Real.toNNReal ε / 2 = Real.toNNReal (ε / 2) := by
    rw [Real.toNNReal_div' (by norm_num), Real.toNNReal_ofNat]
  have h2 : Real.toNNReal ε / (4 * LH) = Real.toNNReal (ε / (4 * LH)) := by
    rw [Real.toNNReal_div' (by positivity), Real.toNNReal_mul (by norm_num), Real.toNNReal_ofNat,
      Real.toNNReal_coe]
  have hc := externalCoveringNumber_compClass_le_mul_sample hlip (Real.toNNReal ε)
  rw [h1, h2] at hc
  refine (Real.sqrt_le_sqrt (log_toReal_le_of_le_mul hHfin hFfin hc)).trans ?_
  exact sqrt_add_le _ _

end CompositionCover

section Antitone

variable {S : Fin n → X}

omit [PseudoMetricSpace X] in
@[blueprint "lem:entHS-antitone"
  (statement := /-- If $H, F \ne \emptyset$ and $N_{S,F}(H, u) < \infty$ for every $u > 0$, then
    $u \mapsto \mathcal E_{H,S}(u)$ is antitone on $(0, \infty)$. -/)]
theorem antitoneOn_entHS (F : Set (X → X)) (H : Set (X → ℝ)) (hHne : H.Nonempty)
    (hFne : F.Nonempty) (hfin : ∀ r : ℝ≥0, 0 < r → pushedCoveringNumber S F H r ≠ ⊤) :
    AntitoneOn (entHS S F H) (Set.Ioi 0) := by
  intro a ha b hb hab
  have hb' : 0 < Real.toNNReal b := Real.toNNReal_pos.mpr hb
  have ha' : 0 < Real.toNNReal a := Real.toNNReal_pos.mpr ha
  obtain ⟨ma, hma⟩ := ENat.ne_top_iff_exists.mp (hfin _ ha')
  obtain ⟨mb, hmb⟩ := ENat.ne_top_iff_exists.mp (hfin _ hb')
  have hle := pushedCoveringNumber_anti S F H (Real.toNNReal_le_toNNReal hab)
  have hpos := pushedCoveringNumber_pos S hHne hFne (Real.toNNReal b)
  unfold entHS
  rw [← hma, ← hmb] at *
  simp only [ENat.toENNReal_coe, ENNReal.toReal_natCast]
  refine Real.sqrt_le_sqrt (Real.log_le_log ?_ ?_)
  · exact_mod_cast hpos
  · exact_mod_cast hle

@[blueprint "lem:entFS-antitone"
  (statement := /-- If $F \ne \emptyset$ has finite $d_S$ covering numbers at every positive
    scale, then $v \mapsto \mathcal E_{F,S}(v)$ is antitone on $(0, \infty)$. -/)]
theorem antitoneOn_entFS (F : Set (X → X)) (hne : F.Nonempty) (hfin : EntTransitionSample S F) :
    AntitoneOn (entFS S F) (Set.Ioi 0) := by
  intro a ha b hb hab
  have hb' : 0 < Real.toNNReal b := Real.toNNReal_pos.mpr hb
  have ha' : 0 < Real.toNNReal a := Real.toNNReal_pos.mpr ha
  obtain ⟨ma, hma⟩ := ENat.ne_top_iff_exists.mp (hfin _ ha')
  obtain ⟨mb, hmb⟩ := ENat.ne_top_iff_exists.mp (hfin _ hb')
  have hle : externalCoveringNumber (X := EmpSpace S) (Real.toNNReal b) F ≤
      externalCoveringNumber (X := EmpSpace S) (Real.toNNReal a) F :=
    externalCoveringNumber_anti (Real.toNNReal_le_toNNReal hab)
  have hpos : 0 < externalCoveringNumber (X := EmpSpace S) (Real.toNNReal b) F :=
    externalCoveringNumber_pos_iff.mpr hne
  unfold entFS
  rw [← hma, ← hmb] at *
  simp only [ENat.toENNReal_coe, ENNReal.toReal_natCast]
  refine Real.sqrt_le_sqrt (Real.log_le_log ?_ ?_)
  · exact_mod_cast hpos
  · exact_mod_cast hle

end Antitone

section FoMLBridge

variable (S : Fin n → X)

omit [PseudoMetricSpace X] in
@[blueprint "lem:isometry-empiricalFunctionSpace"
  (statement := /-- FoML's `EmpiricalFunctionSpace` of a class $G$ (metric $\|\cdot\|_S$) embeds
    isometrically into $(\mathbb R^{\mathcal X}, \|\cdot\|_S)$ by evaluating the index. -/)]
theorem isometry_empiricalFunctionSpace (G : Set (X → ℝ)) :
    Isometry (fun q : EmpiricalFunctionSpace (fun g : G => (g : X → ℝ)) S =>
      toEmpFun S (q.index : X → ℝ)) :=
  Isometry.of_dist_eq fun _ _ => rfl

omit [PseudoMetricSpace X] in
@[blueprint "lem:totallyBounded-empiricalFunctionSpace-sample"
  (statement := /-- If $G \subseteq \mathbb R^{\mathcal X}$ has finite empirical covering numbers
    $N^{\mathrm{ext}}(G, \|\cdot\|_S, r) < \infty$ for all $r > 0$, then $G$ is totally bounded
    for $\|\cdot\|_S$ (FoML's `EmpiricalFunctionSpace`). -/)]
theorem totallyBounded_empiricalFunctionSpace_sample (G : Set (X → ℝ))
    (hG : ∀ r : ℝ≥0, 0 < r → externalCoveringNumber (X := EmpFun S) r G ≠ ⊤) :
    TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace (fun g : G => (g : X → ℝ)) S)) := by
  have hTB : @TotallyBounded (EmpFun S) _ G :=
    FoML.ToFoML.totallyBounded_of_externalCoveringNumber_ne_top (X := EmpFun S) hG
  have := totallyBounded_preimage (isometry_empiricalFunctionSpace S G).isUniformInducing hTB
  exact this.subset fun q _ => q.index.2

omit [PseudoMetricSpace X] in
@[blueprint "lem:foml-covering-le-external-empFun"
  (statement := /-- \textbf{FoML covering numbers versus empirical external covering numbers.} Let
    $G \subseteq \mathbb R^{\mathcal X}$ be nonempty and totally bounded for $\|\cdot\|_S$, and let
    $0 \le 2r < x$. Then FoML's open-ball covering number of $G$ for $\|\cdot\|_S$ satisfies
    $N^{\mathrm{open}}_S(G, x) \le N(G, \|\cdot\|_S, 2r) \le N^{\mathrm{ext}}(G, \|\cdot\|_S, r)$
    (the two metrics coincide; the factor $2$ is the price of the internal cover). -/)]
theorem coveringNumber_empiricalFunctionSpace_le_sample (G : Set (X → ℝ)) [Nonempty G]
    (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace (fun g : G => (g : X → ℝ)) S)))
    {x : ℝ} {r : ℝ≥0} (hr : 2 * (r : ℝ) < x) :
    (coveringNumber h' x : ℕ∞) ≤ externalCoveringNumber (X := EmpFun S) r G := by
  classical
  by_cases htop : externalCoveringNumber (X := EmpFun S) r G = ⊤
  · rw [htop]; exact le_top
  have hcov : Metric.coveringNumber (X := EmpFun S) (2 * r) G ≠ ⊤ :=
    ne_top_of_le_ne_top htop (coveringNumber_two_mul_le_externalCoveringNumber (X := EmpFun S) r G)
  obtain ⟨C, hCG, hCfin, hCcov, hCe⟩ := exists_set_encard_eq_coveringNumber (X := EmpFun S) hcov
  have hx : 0 < x := lt_of_le_of_lt (by positivity) hr
  let φ : EmpFun S → EmpiricalFunctionSpace (fun g : G => (g : X → ℝ)) S := fun c =>
    if hc : c ∈ G then ⟨⟨c, hc⟩⟩ else Classical.arbitrary _
  have hcover : (Set.univ : Set (EmpiricalFunctionSpace (fun g : G => (g : X → ℝ)) S)) ⊆
      ⋃ y ∈ hCfin.toFinset.image φ, Metric.ball y x := by
    intro q _
    obtain ⟨c, hcC, hqc⟩ := (isCover_empFun_iff S (2 * r) G C).mp hCcov _ q.index.2
    simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop, Finset.mem_image]
    refine ⟨φ c, ⟨c, hCfin.mem_toFinset.mpr hcC, rfl⟩, ?_⟩
    have hcG : c ∈ G := hCG hcC
    have hφc : φ c = ⟨⟨c, hcG⟩⟩ := dif_pos hcG
    rw [hφc]
    change empiricalDist S (q.index : X → ℝ) c < x
    rw [← dist_empFun_eq_empiricalDist, dist_empFun]
    calc empNorm S (q.index : X → ℝ) c ≤ ((2 * r : ℝ≥0) : ℝ) := hqc
      _ < x := by push_cast; exact hr
  have h1 := coveringNumber_le_card_of_cover h' hx _ hcover
  calc (coveringNumber h' x : ℕ∞) ≤ ((hCfin.toFinset.image φ).card : ℕ∞) := by exact_mod_cast h1
    _ ≤ (hCfin.toFinset.card : ℕ∞) := by exact_mod_cast Finset.card_image_le
    _ = C.encard := hCfin.encard_eq_coe_toFinset_card.symm
    _ = Metric.coveringNumber (X := EmpFun S) (2 * r) G := hCe
    _ ≤ _ := coveringNumber_two_mul_le_externalCoveringNumber (X := EmpFun S) r G

end FoMLBridge

section MainTheorem

@[blueprint "lem:entropy-integrand-ae-sample"
  (statement := /-- \textbf{Almost-everywhere comparison of the entropy integrands on the
    sample.} Let $H, F \ne \emptyset$ satisfy \texttt{ass:ent-readout-sample} and
    \texttt{ass:ent-transition-sample} with $L_H > 0$, and let $N_S(x)$ be FoML's open-ball
    covering number of $H \circ F$ for $\|\cdot\|_S$. Then for every $\varepsilon > 0$ and
    Lebesgue-a.e. $x > \varepsilon$,
    $$\sqrt{\log N_S(x)} \le \mathcal E_{H,S}(x/4) + \mathcal E_{F,S}\bigl(x/(8L_H)\bigr).$$
    Proof: for every $y < x$, $N_S(x) \le N^{\mathrm{ext}}(H \circ F, \|\cdot\|_S, y/2)
    \le N_{S,F}(H, y/4)\, N^{\mathrm{ext}}(F, d_S, y/(8L_H))$; the right-hand side is antitone
    in $y$, hence continuous outside a countable set, and we let $y \uparrow x$ at a continuity
    point. -/)]
theorem sqrt_log_coveringNumber_ae_le_sample (S : Fin n → X) (H : Set (X → ℝ))
    (F : Set (X → X)) {BH : ℝ} {LH : ℝ≥0} (hLH : 0 < LH) (hH : EntReadoutSample S F H BH LH)
    (hF : EntTransitionSample S F) [Nonempty (compClass H F)] (hHne : H.Nonempty)
    (hFne : F.Nonempty)
    (hGfin : ∀ r : ℝ≥0, 0 < r → externalCoveringNumber (X := EmpFun S) r (compClass H F) ≠ ⊤)
    (h' : TotallyBounded (Set.univ :
      Set (EmpiricalFunctionSpace (fun g : compClass H F => (g : X → ℝ)) S)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂MeasureTheory.volume, ε < x →
      Real.sqrt (Real.log (coveringNumber h' x : ℕ)) ≤
        entHS S F H (x / 4) + entFS S F (x / (8 * LH)) := by
  set ψ : ℝ → ℝ := fun x => entHS S F H (x / 4) + entFS S F (x / (8 * LH)) with hψ
  have hψanti : AntitoneOn ψ (Set.Ioi 0) := by
    intro a ha b hb hab
    have ha' : 0 < a := ha
    have hb' : 0 < b := hb
    exact add_le_add
      (antitoneOn_entHS F H hHne hFne hH.cov (Set.mem_Ioi.mpr (by positivity))
        (Set.mem_Ioi.mpr (by positivity)) (by gcongr))
      (antitoneOn_entFS F hFne hF (Set.mem_Ioi.mpr (by positivity))
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
  have hbound : ∀ y, 0 < y → y < x → Real.sqrt (Real.log (coveringNumber h' x : ℕ)) ≤ ψ y := by
    intro y hy hyx
    have hr : 2 * ((Real.toNNReal (y / 2) : ℝ≥0) : ℝ) < x := by
      rw [Real.coe_toNNReal _ (by positivity)]
      linarith
    have h1 := coveringNumber_empiricalFunctionSpace_le_sample S (compClass H F) h' hr
    have h2 := sqrt_log_compClass_le_sample (F := F) hH.lip hLH (ε := y / 2)
      (hH.cov _ (Real.toNNReal_pos.mpr (by positivity)))
      (hF _ (Real.toNNReal_pos.mpr (by positivity)))
    have hy4 : y / 2 / 2 = y / 4 := by ring
    have hy8 : y / 2 / (4 * (LH : ℝ)) = y / (8 * LH) := by
      rw [div_div]
      congr 1
      ring
    rw [hy4, hy8] at h2
    refine le_trans ?_ h2
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp
      (hGfin (Real.toNNReal (y / 2)) (Real.toNNReal_pos.mpr (by positivity)))
    rw [← hm] at h1 ⊢
    simp only [ENat.toENNReal_coe, ENNReal.toReal_natCast]
    have hle : coveringNumber h' x ≤ m := by exact_mod_cast h1
    have hpos : 0 < coveringNumber h' x := coveringNumber_nonzero Set.univ_nonempty h' hxpos
    exact Real.sqrt_le_sqrt (Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hle))
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

@[blueprint "thm:rad.decomp.ent.ent-sample-foml"
  (statement := /-- \textbf{Deterministic entropy decomposition on the sample (FoML form).} Under
    Assumptions \texttt{ass:ent-readout-sample} and \texttt{ass:ent-transition-sample} with
    $L_H > 0$, for every sample $S$ of size $n \ge 1$ and every $0 < \varepsilon < B_H/2$,
    $$\hat{\mathfrak R}_S(H \circ F) \le 4\varepsilon + \frac{12}{\sqrt n}
    \int_\varepsilon^{B_H/2} \Bigl\{\mathcal E_{H,S}(x/4)
    + \mathcal E_{F,S}\bigl(x/(8L_H)\bigr)\Bigr\}\, dx,$$
    where $\mathcal E_{H,S}(u) = \sqrt{\log N_{S,F}(H, u)}$ and
    $\mathcal E_{F,S}(v) = \sqrt{\log N^{\mathrm{ext}}(F, d_S, v)}$. Proof: FoML's Dudley
    integral for $H \circ F$ with the pseudometric $\|\cdot\|_S$
    (\texttt{dudley\_entropy\_integral'}); its internal open-ball covering number at scale $x$ is
    at most $N^{\mathrm{ext}}(H \circ F, \|\cdot\|_S, y/2)$ for every $y < x$
    (\texttt{lem:foml-covering-le-external-empFun}), then the composition covering lemma on the
    sample \texttt{lem:ent-composition-entropy-sample} at scale $y/2$ and the limit
    $y \uparrow x$ almost everywhere (\texttt{lem:entropy-integrand-ae-sample}). -/)]
theorem rad_decomp_ent_ent_sample_foml (hn : 0 < n) (S : Fin n → X) (H : Set (X → ℝ))
    (F : Set (X → X)) {BH : ℝ} {LH : ℝ≥0} (hLH : 0 < LH) (hH : EntReadoutSample S F H BH LH)
    (hF : EntTransitionSample S F) {ε : ℝ} (hε : 0 < ε) (hεB : ε < BH / 2) :
    empRademacher S (compClass H F) ≤
      4 * ε + 12 / Real.sqrt n *
        ∫ x in ε..(BH / 2), (entHS S F H (x / 4) + entFS S F (x / (8 * LH))) := by
  classical
  have hψ0 : ∀ x, 0 ≤ entHS S F H (x / 4) + entFS S F (x / (8 * LH)) := fun x =>
    add_nonneg (entHS_nonneg _ _ _ _) (entFS_nonneg _ _ _)
  have hint0 : 0 ≤ ∫ x in ε..(BH / 2), (entHS S F H (x / 4) + entFS S F (x / (8 * LH))) :=
    intervalIntegral.integral_nonneg hεB.le fun x _ => hψ0 x
  rcases (compClass H F).eq_empty_or_nonempty with hemp | hne
  · rw [hemp, empRademacher_empty]
    have : 0 ≤ 12 / Real.sqrt n *
        ∫ x in ε..(BH / 2), (entHS S F H (x / 4) + entFS S F (x / (8 * LH))) :=
      mul_nonneg (by positivity) hint0
    linarith
  haveI : Nonempty (compClass H F) := hne.to_subtype
  obtain ⟨hHne, hFne⟩ := compClass_nonempty_iff.mp hne
  -- finite empirical covering numbers of the composition class
  have hGfin : ∀ r : ℝ≥0, 0 < r →
      externalCoveringNumber (X := EmpFun S) r (compClass H F) ≠ ⊤ := by
    intro r hr
    refine ne_top_of_le_ne_top ?_ (externalCoveringNumber_compClass_le_mul_sample hH.lip r)
    exact WithTop.mul_ne_top (hH.cov _ (by positivity)) (hF _ (by positivity))
  have h' := totallyBounded_empiricalFunctionSpace_sample S (compClass H F) hGfin
  -- the composition class is bounded by `BH` on the sample
  have hBH0 : 0 ≤ BH := by
    obtain ⟨u, h, hh, f, hf, rfl⟩ := hne
    exact (abs_nonneg _).trans (hH.bdd h hh _ (mem_reachSet hf ⟨0, hn⟩))
  have cs : ∀ u : compClass H F, empiricalNorm S (u : X → ℝ) ≤ BH := by
    intro u
    obtain ⟨h, hh, f, hf, hu⟩ := u.2
    refine empiricalNorm_le_of_abs_le hn S _ hBH0 fun k => ?_
    rw [hu]
    exact hH.bdd h hh _ (mem_reachSet hf k)
  have hdud := dudley_entropy_integral' hε h' hn cs hεB
  -- a.e. comparison of the integrands on `[ε, BH/2]`
  have hae := sqrt_log_coveringNumber_ae_le_sample S H F hLH hH hF hHne hFne hGfin h' hε
  have hle : (fun x => Real.sqrt (Real.log (coveringNumber h' x : ℕ))) ≤ᵐ[
      MeasureTheory.volume.restrict (Set.Icc ε (BH / 2))]
      fun x => entHS S F H (x / 4) + entFS S F (x / (8 * LH)) := by
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
  have hantψ : AntitoneOn (fun x => entHS S F H (x / 4) + entFS S F (x / (8 * LH)))
      (Set.uIcc ε (BH / 2)) := by
    rw [Set.uIcc_of_le hεB.le]
    intro a ha b hb hab
    have hapos : 0 < a := hε.trans_le ha.1
    have hbpos : 0 < b := hε.trans_le hb.1
    refine add_le_add ?_ ?_
    · exact antitoneOn_entHS F H hHne hFne hH.cov (Set.mem_Ioi.mpr (by positivity))
        (Set.mem_Ioi.mpr (by positivity)) (by gcongr)
    · exact antitoneOn_entFS F hFne hF (Set.mem_Ioi.mpr (by positivity))
        (Set.mem_Ioi.mpr (by positivity)) (by gcongr)
  have hmono := intervalIntegral.integral_mono_ae_restrict (μ := MeasureTheory.volume) hεB.le
    hantF.intervalIntegrable hantψ.intervalIntegrable hle
  calc empRademacher S (compClass H F) ≤ _ := hdud
    _ ≤ _ := by gcongr

@[blueprint "thm:rad.decomp.ent.ent-sample"
  (statement := /-- \textbf{Deterministic entropy decomposition on the sample.} Let $S$ be a
    sample of size $n \ge 1$, and suppose \texttt{ass:ent-readout-sample} and
    \texttt{ass:ent-transition-sample} hold with $L_H > 0$, $B_H > 0$. If the entropy integrand
    $x \mapsto \mathcal E_{H,S}(x/4) + \mathcal E_{F,S}(x/(8L_H))$ is integrable on $[0, B_H/2]$,
    then
    $$\hat{\mathfrak R}_S(H \circ F) \le \frac{12}{\sqrt n}
    \int_0^{B_H/2} \Bigl\{\mathcal E_{H,S}(x/4)
    + \mathcal E_{F,S}\bigl(x/(8L_H)\bigr)\Bigr\}\, dx,$$
    where $\mathcal E_{H,S}(u) = \sqrt{\log N_{S,F}(H, u)}$ with
    $N_{S,F}(H, u) = \sup_{f \in F} N^{\mathrm{ext}}(H, \|\cdot\|_{f \circ S}, u)$, and
    $\mathcal E_{F,S}(v) = \sqrt{\log N^{\mathrm{ext}}(F, d_S, v)}$.

    \emph{Comparison with the paper} (\texttt{thm:rad.decomp.ent.ent}, Appendix D). The paper
    assumes $H$ uniformly $L_H$-Lipschitz and bounded on $\mathcal X$ and covered in the sup norm,
    and $F$ covered in $d_\infty$; its proof passes from $\|\cdot\|_S$ to $\|\cdot\|_\infty$ at
    the very first step. Here (W8 of the plan) every hypothesis is on the sample only: $H$ is
    bounded and $L_H$-Lipschitz on the reachable points $\mathcal R_S(F) = \{f(x_i)\}$, $F$ is
    covered in $d_S$, and $H$ is covered in the empirical metrics $\|\cdot\|_{f \circ S}$ of the
    pushed-forward samples, uniformly in $f \in F$ (this is the honest sample analogue of the sup
    norm cover: in the composition estimate the output layer is evaluated at $f_b(x_i)$, not at
    $x_i$, so a cover of $H$ for $\|\cdot\|_S$ alone would not suffice). The sup-norm assumptions
    imply the sample assumptions for every $S$ (\texttt{cor:rad.decomp.ent.ent-of-sample}).
    The scales are $x/4$, $x/(8L_H)$ on $[0, B_H/2]$ in place of the paper's $\varepsilon/2$,
    $\varepsilon/(2L_H)$ on $[0, 2B_H]$: one factor $2$ comes from FoML's internal open-ball
    covers (as in \texttt{thm:rad.decomp.ent.ent}) and, for $F$ only, a second factor $2$ from
    the fact that the cover of $F$ must have its centres in $F$ (so that the pushed-forward
    samples $f_b \circ S$ are admissible), see \texttt{lem:ent-composition-covering-sample}.
    As in the sup-norm theorem, integrability of the integrand is an additional hypothesis.

    Proof: let $\varepsilon \to 0$ in \texttt{thm:rad.decomp.ent.ent-sample-foml}. -/)]
theorem rad_decomp_ent_ent_sample (hn : 0 < n) (S : Fin n → X) (H : Set (X → ℝ))
    (F : Set (X → X)) {BH : ℝ} {LH : ℝ≥0} (hLH : 0 < LH) (hH : EntReadoutSample S F H BH LH)
    (hF : EntTransitionSample S F) (hBH : 0 < BH)
    (hint : IntervalIntegrable (fun x => entHS S F H (x / 4) + entFS S F (x / (8 * LH)))
      MeasureTheory.volume 0 (BH / 2)) :
    empRademacher S (compClass H F) ≤
      12 / Real.sqrt n *
        ∫ x in (0 : ℝ)..(BH / 2), (entHS S F H (x / 4) + entFS S F (x / (8 * LH))) := by
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hε0 : 0 < min (δ / 4) (BH / 4) := lt_min (by positivity) (by positivity)
  have hεB : min (δ / 4) (BH / 4) < BH / 2 := (min_le_right _ _).trans_lt (by linarith)
  have h1 := rad_decomp_ent_ent_sample_foml hn S H F hLH hH hF hε0 hεB
  have h2 : ∫ x in (min (δ / 4) (BH / 4))..(BH / 2),
        (entHS S F H (x / 4) + entFS S F (x / (8 * LH))) ≤
      ∫ x in (0 : ℝ)..(BH / 2), (entHS S F H (x / 4) + entFS S F (x / (8 * LH))) :=
    intervalIntegral.integral_mono_interval hε0.le hεB.le le_rfl
      (Filter.Eventually.of_forall fun x => add_nonneg (entHS_nonneg _ _ _ _) (entFS_nonneg _ _ _))
      hint
  have h3 : 4 * min (δ / 4) (BH / 4) ≤ δ := by
    have := min_le_left (δ / 4) (BH / 4)
    linarith
  calc empRademacher S (compClass H F)
      ≤ 4 * min (δ / 4) (BH / 4) + 12 / Real.sqrt n *
          ∫ x in (min (δ / 4) (BH / 4))..(BH / 2),
            (entHS S F H (x / 4) + entFS S F (x / (8 * LH))) := h1
    _ ≤ δ + 12 / Real.sqrt n *
          ∫ x in (0 : ℝ)..(BH / 2), (entHS S F H (x / 4) + entFS S F (x / (8 * LH))) := by gcongr
    _ = _ := add_comm _ _

end MainTheorem

section OfSupNorm

variable (S : Fin n → X)

omit [PseudoMetricSpace X] in
@[blueprint "lem:emp-covering-le-unif-fun"
  (statement := /-- For every sample $S$ ($n \ge 1$) and $r \ge 0$,
    $N^{\mathrm{ext}}(G, \|\cdot\|_S, r) \le N^{\mathrm{ext}}(G, \|\cdot\|_\infty, r)$:
    a sup-norm cover is an empirical cover, since $\|u - v\|_S \le \|u - v\|_\infty$. -/)]
theorem externalCoveringNumber_empFun_le_unifFun (hn : 0 < n) (G : Set (X → ℝ)) (r : ℝ≥0) :
    externalCoveringNumber (X := EmpFun S) r G ≤
      externalCoveringNumber (X := UnifFun X) r G := by
  obtain ⟨C, hC, hCe⟩ := exists_isCover_encard_eq_externalCoveringNumber (X := UnifFun X) r G
  rw [← hCe]
  refine IsCover.externalCoveringNumber_le_encard (X := EmpFun S) ?_
  rw [isCover_empFun_iff]
  intro u hu
  obtain ⟨c, hc, hd⟩ := hC hu
  refine ⟨c, hc, ?_⟩
  have hd' : edist (toUnifFun u) (toUnifFun c) ≤ r := hd
  have := empiricalDist_le_toReal_edist S hn u c (ne_top_of_le_ne_top ENNReal.coe_ne_top hd')
  rw [← dist_empFun_eq_empiricalDist, dist_empFun] at this
  refine this.trans ?_
  rw [← ENNReal.coe_toReal]
  exact ENNReal.toReal_mono ENNReal.coe_ne_top hd'

@[blueprint "lem:emp-covering-le-unif-maps"
  (statement := /-- For every sample $S$ and $r \ge 0$,
    $N^{\mathrm{ext}}(F, d_S, r) \le N^{\mathrm{ext}}(F, d_\infty, r)$, since
    $d_S \le d_\infty$ (\texttt{lem:dS-le-dinf}). -/)]
theorem externalCoveringNumber_empSpace_le_unifMaps (F : Set (X → X)) (r : ℝ≥0) :
    externalCoveringNumber (X := EmpSpace S) r F ≤
      externalCoveringNumber (X := UnifMaps X) r F := by
  obtain ⟨C, hC, hCe⟩ := exists_isCover_encard_eq_externalCoveringNumber (X := UnifMaps X) r F
  rw [← hCe]
  refine IsCover.externalCoveringNumber_le_encard (X := EmpSpace S) ?_
  rw [isCover_empSpace_iff]
  intro f hf
  obtain ⟨c, hc, hd⟩ := hC hf
  refine ⟨c, hc, ?_⟩
  have hd' : edist (toUnifMaps f) (toUnifMaps c) ≤ r := hd
  rw [edist_toUnifMaps] at hd'
  have h2 : ENNReal.ofReal (empDist S f c) ≤ r := empDist_le_uniformDist.trans hd'
  rwa [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_le_ofReal_iff r.coe_nonneg] at h2

omit [PseudoMetricSpace X] in
@[blueprint "lem:pushed-covering-le-unif"
  (statement := /-- $N_{S,F}(H, r) \le N^{\mathrm{ext}}(H, \|\cdot\|_\infty, r)$ for every
    sample $S$ ($n \ge 1$): the sup-norm covering number dominates the covering numbers on all
    pushed-forward samples. -/)]
theorem pushedCoveringNumber_le_unifFun (hn : 0 < n) (F : Set (X → X)) (H : Set (X → ℝ))
    (r : ℝ≥0) :
    pushedCoveringNumber S F H r ≤ externalCoveringNumber (X := UnifFun X) r H := by
  unfold pushedCoveringNumber
  exact iSup₂_le fun f _ => externalCoveringNumber_empFun_le_unifFun (f ∘ S) hn H r

@[blueprint "lem:ent-readout-sample-of-readout"
  (statement := /-- Assumption \texttt{ass:ent-readout} implies
    \texttt{ass:ent-readout-sample} for every sample $S$ ($n \ge 1$) and every hidden class
    $F$. -/)]
theorem EntReadout.toSample {H : Set (X → ℝ)} {BH : ℝ} {LH : ℝ≥0} (hn : 0 < n)
    (F : Set (X → X)) (hH : EntReadout H BH LH) : EntReadoutSample S F H BH LH where
  cov ε hε := ne_top_of_le_ne_top (hH.cov ε hε) (pushedCoveringNumber_le_unifFun S hn F H ε)
  bdd h hh x _ := hH.bdd h hh x
  lip h hh x _ y _ := by
    have := (hH.lip h hh).dist_le_mul x y
    rwa [Real.dist_eq] at this

@[blueprint "lem:ent-transition-sample-of-transition"
  (statement := /-- Assumption \texttt{ass:ent-transition} implies
    \texttt{ass:ent-transition-sample} for every sample $S$. -/)]
theorem EntTransition.toSample {F : Set (X → X)} (hF : EntTransition F) :
    EntTransitionSample S F :=
  fun ε hε => ne_top_of_le_ne_top (hF ε hε) (externalCoveringNumber_empSpace_le_unifMaps S F ε)

omit [PseudoMetricSpace X] in
@[blueprint "lem:sqrt-log-enat-mono"
  (statement := /-- If $a \le b < \infty$ in $\mathbb N \cup \{\infty\}$ then
    $\sqrt{\log a} \le \sqrt{\log b}$ (with $\log 0 = 0$). -/)]
theorem sqrt_log_toReal_le_of_le {a b : ℕ∞} (hb : b ≠ ⊤) (hab : a ≤ b) :
    Real.sqrt (Real.log (a : ℝ≥0∞).toReal) ≤ Real.sqrt (Real.log (b : ℝ≥0∞).toReal) := by
  obtain ⟨b', rfl⟩ := ENat.ne_top_iff_exists.mp hb
  obtain ⟨a', rfl⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top hb hab)
  have hab' : a' ≤ b' := by exact_mod_cast hab
  simp only [ENat.toENNReal_coe, ENNReal.toReal_natCast]
  rcases Nat.eq_zero_or_pos a' with rfl | hpos
  · simp only [Nat.cast_zero, Real.log_zero, Real.sqrt_zero]
    exact Real.sqrt_nonneg _
  · exact Real.sqrt_le_sqrt (Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hab'))

@[blueprint "cor:rad.decomp.ent.ent-of-sample"
  (statement := /-- \textbf{The sup-norm theorem from the sample theorem.} Under the sup-norm
    Assumptions \texttt{ass:ent-readout} and \texttt{ass:ent-transition} with $L_H > 0$,
    $B_H > 0$, if $x \mapsto \mathcal E_H(x/4) + \mathcal E_F(x/(8L_H))$ is integrable on
    $[0, B_H/2]$, then for every sample $S$ of size $n \ge 1$,
    $$\hat{\mathfrak R}_S(H \circ F) \le \frac{12}{\sqrt n}
    \int_0^{B_H/2} \Bigl\{\mathcal E_H(x/4) + \mathcal E_F\bigl(x/(8L_H)\bigr)\Bigr\}\, dx.$$
    This is \texttt{thm:rad.decomp.ent.ent} with the scale $x/(8L_H)$ in place of $x/(4L_H)$ for
    $F$ (the price of the internal cover of $F$ in the sample version), obtained from
    \texttt{thm:rad.decomp.ent.ent-sample-foml}: the sup-norm assumptions imply the sample
    assumptions, and $\mathcal E_{H,S} \le \mathcal E_H$, $\mathcal E_{F,S} \le \mathcal E_F$
    pointwise at positive scales. -/)]
theorem rad_decomp_ent_ent_of_sample (hn : 0 < n) (H : Set (X → ℝ)) (F : Set (X → X))
    {BH : ℝ} {LH : ℝ≥0} (hLH : 0 < LH) (hH : EntReadout H BH LH) (hF : EntTransition F)
    (hBH : 0 < BH)
    (hint : IntervalIntegrable (fun x => entH H (x / 4) + entF F (x / (8 * LH)))
      MeasureTheory.volume 0 (BH / 2)) :
    empRademacher S (compClass H F) ≤
      12 / Real.sqrt n *
        ∫ x in (0 : ℝ)..(BH / 2), (entH H (x / 4) + entF F (x / (8 * LH))) := by
  have hψ0 : ∀ x, 0 ≤ entH H (x / 4) + entF F (x / (8 * LH)) := fun x =>
    add_nonneg (entH_nonneg _ _) (entF_nonneg _ _)
  rcases (compClass H F).eq_empty_or_nonempty with hemp | hne
  · rw [hemp, empRademacher_empty]
    exact mul_nonneg (by positivity)
      (intervalIntegral.integral_nonneg (by positivity) fun x _ => hψ0 x)
  obtain ⟨hHne, hFne⟩ := compClass_nonempty_iff.mp hne
  have hHS : EntReadoutSample S F H BH LH := hH.toSample S hn F
  have hFS : EntTransitionSample S F := hF.toSample S
  -- pointwise comparison of the integrands at positive scales
  have hpt : ∀ x, 0 < x → entHS S F H (x / 4) + entFS S F (x / (8 * LH)) ≤
      entH H (x / 4) + entF F (x / (8 * LH)) := by
    intro x hx
    refine add_le_add ?_ ?_
    · exact sqrt_log_toReal_le_of_le (hH.cov _ (Real.toNNReal_pos.mpr (by positivity)))
        (pushedCoveringNumber_le_unifFun S hn F H _)
    · exact sqrt_log_toReal_le_of_le (hF _ (Real.toNNReal_pos.mpr (by positivity)))
        (externalCoveringNumber_empSpace_le_unifMaps S F _)
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set ε := min (δ / 4) (BH / 4) with hεdef
  have hε0 : 0 < ε := lt_min (by positivity) (by positivity)
  have hεB : ε < BH / 2 := (min_le_right _ _).trans_lt (by linarith)
  have h1 := rad_decomp_ent_ent_sample_foml hn S H F hLH hHS hFS hε0 hεB
  have hantψ : AntitoneOn (fun x => entHS S F H (x / 4) + entFS S F (x / (8 * LH)))
      (Set.uIcc ε (BH / 2)) := by
    rw [Set.uIcc_of_le hεB.le]
    intro a ha b hb hab
    have hapos : 0 < a := hε0.trans_le ha.1
    have hbpos : 0 < b := hε0.trans_le hb.1
    refine add_le_add ?_ ?_
    · exact antitoneOn_entHS F H hHne hFne hHS.cov (Set.mem_Ioi.mpr (by positivity))
        (Set.mem_Ioi.mpr (by positivity)) (by gcongr)
    · exact antitoneOn_entFS F hFne hFS (Set.mem_Ioi.mpr (by positivity))
        (Set.mem_Ioi.mpr (by positivity)) (by gcongr)
  have hsub : Set.uIcc ε (BH / 2) ⊆ Set.uIcc 0 (BH / 2) := by
    rw [Set.uIcc_of_le hεB.le, Set.uIcc_of_le (by positivity)]
    exact Set.Icc_subset_Icc hε0.le le_rfl
  have h2 : ∫ x in ε..(BH / 2), (entHS S F H (x / 4) + entFS S F (x / (8 * LH))) ≤
      ∫ x in ε..(BH / 2), (entH H (x / 4) + entF F (x / (8 * LH))) :=
    intervalIntegral.integral_mono_on hεB.le hantψ.intervalIntegrable (hint.mono_set hsub)
      fun x hx => hpt x (hε0.trans_le hx.1)
  have h3 : ∫ x in ε..(BH / 2), (entH H (x / 4) + entF F (x / (8 * LH))) ≤
      ∫ x in (0 : ℝ)..(BH / 2), (entH H (x / 4) + entF F (x / (8 * LH))) :=
    intervalIntegral.integral_mono_interval hε0.le hεB.le le_rfl
      (Filter.Eventually.of_forall hψ0) hint
  have h4 : 4 * ε ≤ δ := by
    have := min_le_left (δ / 4) (BH / 4)
    linarith
  calc empRademacher S (compClass H F)
      ≤ 4 * ε + 12 / Real.sqrt n *
          ∫ x in ε..(BH / 2), (entHS S F H (x / 4) + entFS S F (x / (8 * LH))) := h1
    _ ≤ δ + 12 / Real.sqrt n *
          ∫ x in (0 : ℝ)..(BH / 2), (entH H (x / 4) + entF F (x / (8 * LH))) :=
        add_le_add h4 (mul_le_mul_of_nonneg_left (h2.trans h3) (by positivity))
    _ = _ := add_comm _ _

end OfSupNorm

end LeanDeepgen
