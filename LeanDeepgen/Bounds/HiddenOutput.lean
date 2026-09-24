import Mathlib
import Architect
import FoML
import LeanDeepgen.Setting.WordBall
import LeanDeepgen.Setting.Metrics
import LeanDeepgen.Setting.Covering
import LeanDeepgen.Setting.Hypothesis
import LeanDeepgen.Setting.Rademacher
import LeanDeepgen.Setting.Assumptions
import FoML.ToFoML.VectorHoeffding
import FoML.ToFoML.DudleySubGaussian

/-!
# Hidden–output decomposition

Assumption `ass:sg-increment-main` (sub-Gaussian output-layer increments), Theorem
`thm:hidden-decomp` (= `thm:mixed-sg`, Appendix C) and the two sufficient conditions
`prop:hilbert-sg`, `prop:finite-lipschitz-sg`.

Status of the proofs:

* `thm:hidden-decomp` (anchored at an arbitrary `f₀ ∈ F`, generalizing the paper's `id ∈ F`),
  its identity-anchored form `thm:hidden-decomp-id` and its depth form
  `thm:hidden-decomp-depth` are fully proved from the
  sub-Gaussian Dudley bound `FoML.ToFoML.dudley_subgaussian_finite_space`, under an
  additional integrability hypothesis on the entropy integrand (Lean's Bochner interval integral
  of a non-integrable function is `0`, whereas the paper's right-hand side is `+∞` in that case);
* `prop:hilbert-sg-of-tail`, `prop:hilbert-sg-real` and `prop:finite-lipschitz-sg` are fully
  proved (real Hoeffding inequality, union bound);
* `prop:hilbert-sg` is proved from the vector Hoeffding inequality
  `FoML.ToFoML.rademacher_hilbert_tail` (`FoML/ToFoML/VectorHoeffding.lean`).

The Rademacher sign patterns are FoML's `Signs n = Fin n → {-1, 1}` (uniform distribution =
counting average), so `ℙ_σ(|Z_f - Z_g| > t)` is `#{σ : t < |Z_f σ - Z_g σ|} / 2^n`.

The Dudley entropy integral `∫_0^{diam_S F} √(log N(F, d_S, ε)) dε` is written explicitly here
with Mathlib's internal covering number of `F` in the pseudometric space `EmpSpace S`; it is
`entropyIntegral (empDiam S F) F` of `LeanDeepgen.Profiles.Defs`, and `LeanDeepgen.Bounds.Variance`
restates the depth form as `R̂_S(ℋ_k) ≤ R̂_S(H) + varTerm AH L n S F k`.

The definitions used in the statements (the hidden-indexed process `outputProcess`, the
assumption `SubGaussianIncrements` and the Hilbert readout class `hilbertReadoutClass`) live in
`LeanDeepgen.Setting.Assumptions`.
-/

open scoped NNReal ENNReal

namespace LeanDeepgen

variable {X : Type*}

section Metric

variable [PseudoMetricSpace X]

variable {n : ℕ} (S : Fin n → X) (H : Set (X → ℝ))

omit [PseudoMetricSpace X] in
@[blueprint "lem:sup-comp-class-eq-sup-output-process"
  (statement := /-- Let $F \ne \emptyset$ and fix a sign pattern $\sigma$. If for every
    $f \in F$ the Rademacher averages $\{\frac1n\sum_i \sigma_i h(f(x_i)) : h \in H\}$ are
    bounded above, and $f \mapsto Z_f(\sigma)$ is bounded above on $F$, then
    $\sup_{u \in H \circ F} \frac1n \sum_i \sigma_i u(x_i) = \sup_{f \in F} Z_f(\sigma)$. -/)]
theorem iSup_compClass_eq_iSup_outputProcess (F : Set (X → X)) (hFne : F.Nonempty)
    (σ : Signs n)
    (hbdd : ∀ f ∈ F, BddAbove (Set.range fun h : H =>
        normalizedRademacherSum n (fun h : H => (h : X → ℝ)) (f ∘ S) σ h))
    (hZbdd : BddAbove (Set.range fun f : F => outputProcess S H f σ)) :
    (⨆ u : compClass H F,
      normalizedRademacherSum n (fun u : compClass H F => (u : X → ℝ)) S σ u) =
      ⨆ f : F, outputProcess S H f σ := by
  classical
  haveI : Nonempty F := hFne.to_subtype
  obtain ⟨M, hM⟩ := hZbdd
  have hAbdd : BddAbove (Set.range fun u : compClass H F =>
      normalizedRademacherSum n (fun u : compClass H F => (u : X → ℝ)) S σ u) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨u, rfl⟩
    obtain ⟨h, hh, f, hf, hu⟩ := u.2
    have h1 : normalizedRademacherSum n (fun u : compClass H F => (u : X → ℝ)) S σ u =
        normalizedRademacherSum n (fun h : H => (h : X → ℝ)) (f ∘ S) σ ⟨h, hh⟩ := by
      simp only [normalizedRademacherSum, hu, Function.comp_apply]
    dsimp only
    rw [h1]
    have h2 : normalizedRademacherSum n (fun h : H => (h : X → ℝ)) (f ∘ S) σ ⟨h, hh⟩ ≤
        outputProcess S H f σ := le_ciSup (hbdd f hf) ⟨h, hh⟩
    exact h2.trans (hM ⟨⟨f, hf⟩, rfl⟩)
  by_cases hH : H = ∅
  · subst hH
    haveI : IsEmpty (compClass (∅ : Set (X → ℝ)) F) :=
      ⟨fun u => by obtain ⟨h, hh, -⟩ := u.2; exact hh⟩
    haveI : IsEmpty ((∅ : Set (X → ℝ))) := Set.isEmpty_coe_sort.mpr rfl
    rw [Real.iSup_of_isEmpty]
    simp only [outputProcess]
    simp [Real.iSup_of_isEmpty]
  · haveI : Nonempty H := (Set.nonempty_iff_ne_empty.mpr hH).to_subtype
    obtain ⟨h₀⟩ := (inferInstance : Nonempty H)
    obtain ⟨f₀, hf₀⟩ := hFne
    haveI : Nonempty (compClass H F) := ⟨⟨(h₀ : X → ℝ) ∘ f₀, h₀, h₀.2, f₀, hf₀, rfl⟩⟩
    apply le_antisymm
    · refine ciSup_le fun u => ?_
      obtain ⟨h, hh, f, hf, hu⟩ := u.2
      have h1 : normalizedRademacherSum n (fun u : compClass H F => (u : X → ℝ)) S σ u =
          normalizedRademacherSum n (fun h : H => (h : X → ℝ)) (f ∘ S) σ ⟨h, hh⟩ := by
        simp only [normalizedRademacherSum, hu, Function.comp_apply]
      rw [h1]
      calc _ ≤ outputProcess S H f σ := le_ciSup (hbdd f hf) ⟨h, hh⟩
        _ ≤ ⨆ f : F, outputProcess S H f σ := le_ciSup ⟨M, hM⟩ ⟨f, hf⟩
    · refine ciSup_le fun f => ?_
      simp only [outputProcess]
      refine ciSup_le fun h => ?_
      have hmem : ((h : X → ℝ) ∘ (f : X → X)) ∈ compClass H F := ⟨h, h.2, f, f.2, rfl⟩
      refine le_ciSup_of_le hAbdd ⟨_, hmem⟩ (le_of_eq ?_)
      simp only [normalizedRademacherSum, Function.comp_apply]

omit [PseudoMetricSpace X] in
@[blueprint "lem:emp-rademacher-comp-singleton"
  (statement := /-- For a single hidden map $f_0$ with bounded Rademacher averages,
    $\hat{\mathfrak R}_S(H \circ \{f_0\}) = \mathbb E_\sigma Z_{f_0}(\sigma)$. -/)]
theorem empRademacher_compClass_singleton (f₀ : X → X)
    (hbdd : ∀ σ : Signs n, BddAbove (Set.range fun h : H =>
        normalizedRademacherSum n (fun h : H => (h : X → ℝ)) (f₀ ∘ S) σ h)) :
    empRademacher S (compClass H {f₀}) =
      FoML.ToFoML.uniformExpect (fun σ => outputProcess S H f₀ σ) := by
  unfold empRademacher empiricalRademacherComplexity_without_abs FoML.ToFoML.uniformExpect
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  have h := iSup_compClass_eq_iSup_outputProcess S H {f₀} (Set.singleton_nonempty f₀) σ
    (fun f hf => by rw [Set.mem_singleton_iff] at hf; subst hf; exact hbdd σ)
    (Set.finite_range _).bddAbove
  exact h.trans ciSup_unique

@[blueprint "thm:hidden-decomp"
  (statement := /-- \textbf{Hidden--output decomposition under a sub-Gaussian increment
    condition.} Let $n \ge 1$, let $F \subseteq \mathcal X^{\mathcal X}$ be totally bounded in
    $d_S$, let $f_0 \in F$ be an arbitrary anchor, and suppose Assumption
    \texttt{ass:sg-increment-main} holds on $\mathfrak F \supseteq F$ with constants
    $A_H, L > 0$. (We also assume that the suprema defining $Z_f(\sigma)$, $f \in F$, are
    finite, i.e. the Rademacher averages over $H$ are bounded above; this is implicit in the
    paper.) Then
    $$\hat{\mathfrak R}_S(H \circ F) \le \hat{\mathfrak R}_S(H \circ \{f_0\})
    + \frac{12 A_H L}{\sqrt n} \int_0^{\mathrm{diam}_S(F)} \sqrt{\log N(F, d_S, \varepsilon)}
    \, d\varepsilon,$$
    where $\hat{\mathfrak R}_S(H \circ \{f_0\}) = \mathbb E_\sigma Z_{f_0}(\sigma)$
    (\texttt{lem:emp-rademacher-comp-singleton}). This generalizes the paper, which assumes
    $\mathrm{id} \in F$ and anchors at $f_0 = \mathrm{id}$, giving $\hat{\mathfrak R}_S(H)$ on
    the right-hand side (\texttt{thm:hidden-decomp-id}); the anchor is arbitrary because the
    Dudley bound \texttt{thm:dudley-subgaussian-finite-space} is anchored at any point.
    We assume in addition that the entropy integrand
    $\varepsilon \mapsto \sqrt{\log N(F,d_S,\varepsilon)}$ is integrable on
    $[0,\mathrm{diam}_S(F)]$; the paper's bound is trivially true with right-hand side $+\infty$
    otherwise, whereas Lean's Bochner integral of a non-integrable function is $0$. -/)]
theorem hidden_decomp (hn : 0 < n) (F 𝔉 : Set (X → X)) {AH L : ℝ} (hAH : 0 < AH) (hL : 0 < L)
    (hbdd : ∀ f ∈ F, ∀ σ : Signs n,
      BddAbove (Set.range fun h : H =>
        normalizedRademacherSum n (fun h : H => (h : X → ℝ)) (f ∘ S) σ h))
    (f₀ : X → X) (hf₀ : f₀ ∈ F) (hF : TotallyBounded (α := EmpSpace S) F) (hF𝔉 : F ⊆ 𝔉)
    (hsg : SubGaussianIncrements S H 𝔉 AH L)
    (hint : IntervalIntegrable
      (fun ε : ℝ => Real.sqrt (metricEntropy (X := EmpSpace S) (Real.toNNReal ε) F))
      MeasureTheory.volume 0 (empDiam S F)) :
    empRademacher S (compClass H F) ≤
      empRademacher S (compClass H {f₀}) + 12 * AH * L / Real.sqrt n *
        ∫ ε in (0 : ℝ)..(empDiam S F),
          Real.sqrt (metricEntropy (X := EmpSpace S) (Real.toNNReal ε) F) := by
  classical
  haveI : Nonempty (Signs n) := ⟨fun _ => ⟨1, by simp⟩⟩
  haveI hFne : Nonempty F := ⟨⟨f₀, hf₀⟩⟩
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  set σ' : ℝ := AH * L / Real.sqrt n with hσ'
  have hσ'pos : 0 < σ' := by positivity
  set Z : (X → X) → Signs n → ℝ := fun f σ => outputProcess S H f σ with hZ
  set Y : (X → X) → Signs n → ℝ := fun f σ => Z f σ - Z f₀ σ with hY
  have hY₀ : ∀ ω, Y f₀ ω = 0 := fun ω => sub_self _
  -- Step 1: `Y` has `σ'`-sub-Gaussian increments on `F` in `(𝒳^𝒳, d_S)`.
  have hYsg : FoML.ToFoML.SubGaussianIncrementsOn (Ω := Signs n) (T := EmpSpace S) F Y σ' := by
    refine ⟨?_, ?_⟩
    · intro f hf g hg hd ω
      simp only [hY, hZ]
      rw [hsg.1 f (hF𝔉 hf) g (hF𝔉 hg) hd ω]
    · intro f hf g hg u hu
      have h := hsg.2 f (hF𝔉 hf) g (hF𝔉 hg) u hu
      have hfilt : (Finset.univ.filter fun ω : Signs n => u < |Y f ω - Y g ω|) =
          Finset.univ.filter fun σ : Signs n =>
            u < |outputProcess S H f σ - outputProcess S H g σ| := by
        refine Finset.filter_congr fun ω _ => ?_
        simp only [hY, hZ, sub_sub_sub_cancel_right]
      have hexp : -(u ^ 2 / (2 * σ' ^ 2 * dist (f : EmpSpace S) g ^ 2)) =
          -(n : ℝ) * u ^ 2 / (2 * AH ^ 2 * L ^ 2 * empDist S f g ^ 2) := by
        rw [dist_empSpace, hσ', div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n),
          show 2 * (AH ^ 2 * L ^ 2 / n) * empDist S f g ^ 2 =
            (2 * AH ^ 2 * L ^ 2 * empDist S f g ^ 2) / n by ring, div_div_eq_mul_div]
        ring
      unfold FoML.ToFoML.tailFrac
      rw [hfilt, hexp]
      exact h
  -- Step 2: boundedness of the suprema (from the sure Lipschitz bound on the finite space).
  have hbddF : BddAbove (Set.image2 (empDist S) F F) := by
    obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp hF.isBounded
    refine ⟨C, ?_⟩
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact hC hx hy
  set D := empDiam S F with hD
  have hdistD : ∀ f ∈ F, empDist S f f₀ ≤ D := fun f hf =>
    le_csSup hbddF (Set.mem_image2_of_mem hf hf₀)
  have hD0 : 0 ≤ D := by
    have := le_csSup hbddF (Set.mem_image2_of_mem hf₀ hf₀)
    rwa [empDist_self] at this
  set Lm := Real.sqrt (2 * Real.log (2 * Fintype.card (Signs n))) with hLm
  have hYbound : ∀ f ∈ F, ∀ ω, |Y f ω| ≤ σ' * (D + 1) * Lm := by
    intro f hf ω
    have := FoML.ToFoML.abs_sub_le_of_dist_le hYsg hσ'pos hf hf₀ (by linarith : (0 : ℝ) < D + 1)
      (by rw [dist_empSpace]; linarith [hdistD f hf]) ω
    rwa [hY₀, sub_zero] at this
  have hZbdd : ∀ σ, BddAbove (Set.range fun f : F => Z f σ) := by
    intro σ
    refine ⟨Z f₀ σ + σ' * (D + 1) * Lm, ?_⟩
    rintro _ ⟨f, rfl⟩
    have h3 := hYbound f f.2 σ
    have h4 : Y f σ = Z f σ - Z f₀ σ := rfl
    rw [h4] at h3
    linarith [le_abs_self (Z f σ - Z f₀ σ)]
  -- Step 3: `sup_{u ∈ H ∘ F} = sup_{f ∈ F} Z_f` for each sign pattern.
  have hsup : ∀ σ : Signs n, (⨆ u : compClass H F,
      normalizedRademacherSum n (fun u : compClass H F => (u : X → ℝ)) S σ u) =
      ⨆ f : F, Z f σ := fun σ =>
    iSup_compClass_eq_iSup_outputProcess S H F ⟨f₀, hf₀⟩ σ (fun f hf => hbdd f hf σ) (hZbdd σ)
  -- Step 4: anchoring: `sup_f Z_f = Z_{f₀} + sup_f Y_f`.
  have hsplit : ∀ σ : Signs n, (⨆ f : F, Z f σ) = Z f₀ σ + ⨆ f : F, Y f σ := by
    intro σ
    have hb : BddAbove (Set.range fun f : F => Y f σ) := by
      refine ⟨σ' * (D + 1) * Lm, ?_⟩
      rintro _ ⟨f, rfl⟩
      exact (le_abs_self _).trans (hYbound f f.2 σ)
    rw [add_comm, ciSup_add hb]
    change (⨆ f : F, Z f σ) = ⨆ f : F, (Z f σ - Z f₀ σ + Z f₀ σ)
    simp only [sub_add_cancel]
  have hLHS : empRademacher S (compClass H F) =
      FoML.ToFoML.uniformExpect (fun σ => Z f₀ σ + ⨆ f : F, Y f σ) := by
    unfold empRademacher empiricalRademacherComplexity_without_abs FoML.ToFoML.uniformExpect
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    dsimp only
    rw [← hsplit σ, ← hsup σ]
    rfl
  have hH : empRademacher S (compClass H {f₀}) = FoML.ToFoML.uniformExpect (fun σ => Z f₀ σ) :=
    empRademacher_compClass_singleton S H f₀ (hbdd f₀ hf₀)
  have hdec : FoML.ToFoML.uniformExpect (fun σ => Z f₀ σ + ⨆ f : F, Y f σ) =
      empRademacher S (compClass H {f₀}) + FoML.ToFoML.uniformExpect (fun σ => ⨆ f : F, Y f σ) := by
    rw [hH]
    unfold FoML.ToFoML.uniformExpect
    rw [Finset.sum_add_distrib, mul_add]
  -- Step 5: Dudley's entropy integral for the anchored process.
  have hdiam : D = Metric.diam (α := EmpSpace S) F := by
    apply le_antisymm
    · apply csSup_le (Set.Nonempty.image2 ⟨f₀, hf₀⟩ ⟨f₀, hf₀⟩)
      rintro _ ⟨x, hx, y, hy, rfl⟩
      exact Metric.dist_le_diam_of_mem hF.isBounded hx hy
    · exact Metric.diam_le_of_forall_dist_le hD0
        (fun x hx y hy => le_csSup hbddF (Set.mem_image2_of_mem hx hy))
  -- The integrability hypothesis, transported to `[0, diam F]` (`sqrtLogCovering F` is
  -- definitionally `ε ↦ √(metricEntropy ε F)`).
  have hint' : IntervalIntegrable (FoML.ToFoML.sqrtLogCovering (T := EmpSpace S) F)
      MeasureTheory.volume 0 (Metric.diam (α := EmpSpace S) F) := by
    rw [← hdiam]
    exact hint
  have hdud := FoML.ToFoML.dudley_subgaussian_finite_space (Ω := Signs n) (T := EmpSpace S) hF hf₀ Y
    hY₀ hσ'pos hYsg hint'
  rw [← hdiam] at hdud
  have hcoef : 12 * AH * L / Real.sqrt n = 12 * σ' := by rw [hσ']; ring
  have heq : (∫ ε in (0 : ℝ)..D, Real.sqrt (metricEntropy (X := EmpSpace S) (Real.toNNReal ε) F))
      = ∫ ε in (0 : ℝ)..D, FoML.ToFoML.sqrtLogCovering (T := EmpSpace S) F ε := rfl
  rw [hLHS, hdec, hcoef, heq]
  exact add_le_add_right hdud (empRademacher S (compClass H {f₀}))

@[blueprint "thm:hidden-decomp-id"
  (statement := /-- \textbf{Hidden--output decomposition, anchored at the identity (the paper's
    form).} Under the hypotheses of \texttt{thm:hidden-decomp} with $\mathrm{id} \in F$,
    $$\hat{\mathfrak R}_S(H \circ F) \le \hat{\mathfrak R}_S(H)
    + \frac{12 A_H L}{\sqrt n} \int_0^{\mathrm{diam}_S(F)} \sqrt{\log N(F, d_S, \varepsilon)}
    \, d\varepsilon.$$
    Proof: \texttt{thm:hidden-decomp} with $f_0 = \mathrm{id}$ and
    $H \circ \{\mathrm{id}\} = H$. -/)]
theorem hidden_decomp_id (hn : 0 < n) (F 𝔉 : Set (X → X)) {AH L : ℝ} (hAH : 0 < AH)
    (hL : 0 < L)
    (hbdd : ∀ f ∈ F, ∀ σ : Signs n,
      BddAbove (Set.range fun h : H =>
        normalizedRademacherSum n (fun h : H => (h : X → ℝ)) (f ∘ S) σ h))
    (hid : id ∈ F) (hF : TotallyBounded (α := EmpSpace S) F) (hF𝔉 : F ⊆ 𝔉)
    (hsg : SubGaussianIncrements S H 𝔉 AH L)
    (hint : IntervalIntegrable
      (fun ε : ℝ => Real.sqrt (metricEntropy (X := EmpSpace S) (Real.toNNReal ε) F))
      MeasureTheory.volume 0 (empDiam S F)) :
    empRademacher S (compClass H F) ≤
      empRademacher S H + 12 * AH * L / Real.sqrt n *
        ∫ ε in (0 : ℝ)..(empDiam S F),
          Real.sqrt (metricEntropy (X := EmpSpace S) (Real.toNNReal ε) F) := by
  have h := hidden_decomp S H hn F 𝔉 hAH hL hbdd id hid hF hF𝔉 hsg hint
  rwa [compClass_singleton_id] at h

@[blueprint "thm:hidden-decomp-depth"
  (statement := /-- If Assumption \texttt{ass:sg-increment-main} holds on the semigroup
    $\langle F_0 \rangle$ with constants $(A_H, L)$, then for every depth $k \ge 0$ with
    $B(k,F_0)$ totally bounded in $d_S$,
    $$\hat{\mathfrak R}_S(\mathcal H_k) \le \hat{\mathfrak R}_S(H)
    + \frac{12 A_H L}{\sqrt n} \int_0^{\mathrm{diam}_S(B(k,F_0))}
    \sqrt{\log N(B(k,F_0), d_S, \varepsilon)} \, d\varepsilon,$$
    with the same constants $A_H, L$ (assuming, as in \texttt{thm:hidden-decomp}, that the
    entropy integrand of $B(k,F_0)$ is integrable on $[0, \mathrm{diam}_S(B(k,F_0))]$). -/)]
theorem hidden_decomp_depth (hn : 0 < n) (F₀ : Set (X → X)) (k : ℕ) {AH L : ℝ} (hAH : 0 < AH)
    (hL : 0 < L)
    (hbdd : ∀ f ∈ wordBall F₀ k, ∀ σ : Signs n,
      BddAbove (Set.range fun h : H =>
        normalizedRademacherSum n (fun h : H => (h : X → ℝ)) (f ∘ S) σ h))
    (hF : TotallyBounded (α := EmpSpace S) (wordBall F₀ k))
    (hsg : SubGaussianIncrements S H (semigroupClosure F₀) AH L)
    (hint : IntervalIntegrable
      (fun ε : ℝ => Real.sqrt (metricEntropy (X := EmpSpace S) (Real.toNNReal ε) (wordBall F₀ k)))
      MeasureTheory.volume 0 (empDiam S (wordBall F₀ k))) :
    empRademacher S (hypothesisClass H F₀ k) ≤
      empRademacher S H + 12 * AH * L / Real.sqrt n *
        ∫ ε in (0 : ℝ)..(empDiam S (wordBall F₀ k)),
          Real.sqrt (metricEntropy (X := EmpSpace S) (Real.toNNReal ε) (wordBall F₀ k)) := by
  /-- $\mathrm{id} \in B(k,F_0) \subseteq \langle F_0 \rangle$ and
    $\mathcal H_k = H \circ B(k,F_0)$. -/
  exact hidden_decomp_id S H hn (wordBall F₀ k) (semigroupClosure F₀) hAH hL hbdd id_mem_wordBall
    hF subset_semigroupClosure hsg hint

omit [PseudoMetricSpace X] in
@[blueprint "lem:output-process-congr"
  (statement := /-- If $h(f(x_i)) = h(g(x_i))$ for all $h \in H$ and $i \le n$, then
    $Z_f(\sigma) = Z_g(\sigma)$ for every $\sigma$. -/)]
theorem outputProcess_congr {f g : X → X} (h : ∀ h ∈ H, ∀ i, h (f (S i)) = h (g (S i)))
    (σ : Signs n) : outputProcess S H f σ = outputProcess S H g σ := by
  unfold outputProcess normalizedRademacherSum
  congr 1
  ext h'
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Function.comp_apply]
  rw [h h' h'.2 i]

@[blueprint "lem:empdist-eq-zero"
  (statement := /-- If $d_S(f,g) = 0$ then $d(f(x_i), g(x_i)) = 0$ for every $i \le n$. -/)]
theorem dist_eq_zero_of_empDist_eq_zero {f g : X → X} (h : empDist S f g = 0) (i : Fin n) :
    dist (f (S i)) (g (S i)) = 0 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast i.pos
  unfold empDist at h
  rw [Real.sqrt_eq_zero'] at h
  have hsum : ∑ j, dist (f (S j)) (g (S j)) ^ 2 = 0 := by
    have h1 : (1 / (n : ℝ)) * ∑ j, dist (f (S j)) (g (S j)) ^ 2 ≥ 0 := by positivity
    have h2 : (1 / (n : ℝ)) * ∑ j, dist (f (S j)) (g (S j)) ^ 2 = 0 := le_antisymm h h1
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exfalso
      rw [one_div, inv_eq_zero] at h3
      exact hn.ne' h3
    · exact h3
  have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (dist (f (S j)) (g (S j)))).mp
    hsum i (Finset.mem_univ _)
  exact pow_eq_zero_iff two_ne_zero |>.mp this

@[blueprint "lem:n-mul-empdist-sq"
  (statement := /-- $n\, d_S(f,g)^2 = \sum_{i=1}^n d(f(x_i), g(x_i))^2$. -/)]
theorem n_mul_empDist_sq (f g : X → X) :
    (n : ℝ) * empDist S f g ^ 2 = ∑ i, dist (f (S i)) (g (S i)) ^ 2 := by
  unfold empDist
  rw [Real.sq_sqrt (by positivity)]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp

@[blueprint "lem:lipschitz-apply-eq-of-empdist-zero"
  (statement := /-- If $\varphi$ is Lipschitz into a metric space and $d_S(f,g) = 0$, then
    $\varphi(f(x_i)) = \varphi(g(x_i))$ for every $i \le n$. -/)]
theorem lipschitz_apply_eq_of_empDist_eq_zero {E : Type*} [MetricSpace E] {φ : X → E} {L : ℝ≥0}
    (hφ : LipschitzWith L φ) {f g : X → X} (h : empDist S f g = 0) (i : Fin n) :
    φ (f (S i)) = φ (g (S i)) := by
  refine dist_le_zero.mp ?_
  calc dist (φ (f (S i))) (φ (g (S i))) ≤ L * dist (f (S i)) (g (S i)) := hφ.dist_le_mul _ _
    _ = 0 := by rw [dist_eq_zero_of_empDist_eq_zero S h i, mul_zero]

@[blueprint "lem:sum-sq-dist-lipschitz-le"
  (statement := /-- If $\varphi$ is $L$-Lipschitz then
    $\sum_{i=1}^n d(\varphi(f(x_i)), \varphi(g(x_i)))^2 \le L^2\, n\, d_S(f,g)^2$. -/)]
theorem sum_sq_dist_le_of_lipschitz {E : Type*} [MetricSpace E] {φ : X → E} {L : ℝ≥0}
    (hφ : LipschitzWith L φ) (f g : X → X) :
    ∑ i, dist (φ (f (S i))) (φ (g (S i))) ^ 2 ≤ L ^ 2 * (n * empDist S f g ^ 2) := by
  rw [n_mul_empDist_sq, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← mul_pow]
  exact pow_le_pow_left₀ dist_nonneg (hφ.dist_le_mul _ _) 2

omit [PseudoMetricSpace X] in
@[blueprint "lem:signs-prob-le-one"
  (statement := /-- A counting fraction on $\{\pm1\}^n$ is at most $1$:
    $\#\{\sigma : p(\sigma)\}/2^n \le 1$. -/)]
theorem card_filter_signs_div_le_one (p : Signs n → Prop) [DecidablePred p] :
    ((Finset.univ.filter p).card : ℝ) / Fintype.card (Signs n) ≤ 1 := by
  rw [div_le_one (by rw [FoML.ToFoML.card_signs]; positivity)]
  exact_mod_cast Finset.card_filter_le _ _

omit [PseudoMetricSpace X] in
@[blueprint "lem:inner-rademacher-sum"
  (statement := /-- $\frac1n \sum_k \sigma_k \langle w, u_k\rangle
    = \bigl\langle w, \frac1n \sum_k \sigma_k u_k \bigr\rangle$. -/)]
theorem inner_rademacher_sum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (w : E)
    (u : Fin n → E) (σ : Signs n) :
    (n : ℝ)⁻¹ * ∑ k, (σ k : ℝ) * inner ℝ w (u k) =
      inner ℝ w ((n : ℝ)⁻¹ • ∑ k, (σ k : ℝ) • u k) := by
  rw [real_inner_smul_right, inner_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [real_inner_smul_right]

@[blueprint "prop:hilbert-sg-of-tail"
  (statement := /-- \textbf{Hilbert output layers satisfy the increment condition, given the
    vector Hoeffding inequality.} Let $\mathcal H$ be a real inner product space and
    $\Phi : \mathcal X \to \mathcal H$ be $L$-Lipschitz. Assume the Rademacher tail bound
    \texttt{lem:rademacher-hilbert-tail} holds in $\mathcal H$ for samples of size $n$:
    $\mathbb P_\sigma(\|\sum_i \sigma_i v_i\| > t) \le 2\exp(-t^2/(2\sum_i\|v_i\|^2))$.
    Then Assumption \texttt{ass:sg-increment-main} holds for $H = H_\Phi$ with $A_H = 1$ and the
    same $L$, for every hidden-layer class $\mathfrak F$.
    Proof: $|Z_f - Z_g| \le \sup_{\|w\| \le 1} |\langle w, \frac1n\sum_i \sigma_i v_i\rangle|
    = \|\frac1n \sum_i \sigma_i v_i\|$ with $v_i = \Phi(f(x_i)) - \Phi(g(x_i))$, and
    $\sum_i \|v_i\|^2 \le L^2 n d_S(f,g)^2$. -/)]
theorem hilbert_sg_of_tail {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (Φ : X → E)
    {L : ℝ≥0} (hΦ : LipschitzWith L Φ) (𝔉 : Set (X → X))
    (htail : ∀ (v : Fin n → E) (t : ℝ), 0 < t →
      ((Finset.univ.filter fun σ : Signs n => t < ‖∑ i, (σ i : ℝ) • v i‖).card : ℝ) /
        Fintype.card (Signs n) ≤ 2 * Real.exp (-t ^ 2 / (2 * ∑ i, ‖v i‖ ^ 2))) :
    SubGaussianIncrements S (hilbertReadoutClass Φ) 𝔉 1 L := by
  refine ⟨?_, ?_⟩
  · intro f _ g _ hd σ
    refine outputProcess_congr S _ (fun h hh i => ?_) σ
    obtain ⟨w, -, rfl⟩ := hh
    simp only
    rw [lipschitz_apply_eq_of_empDist_eq_zero S hΦ hd i]
  · intro f _ g _ t ht
    -- the increment is controlled by the norm of a Rademacher sum in `E`
    set v : Fin n → E := fun i => Φ (f (S i)) - Φ (g (S i)) with hv
    haveI : Nonempty (hilbertReadoutClass Φ) :=
      ⟨⟨fun x => inner ℝ (0 : E) (Φ x), 0, by simp, rfl⟩⟩
    have hrepr : ∀ h : hilbertReadoutClass Φ, ∃ w : E, ‖w‖ ≤ 1 ∧ ∀ (u : X → X) (σ : Signs n),
          normalizedRademacherSum n (fun h : hilbertReadoutClass Φ => (h : X → ℝ)) (u ∘ S) σ h =
            inner ℝ w ((n : ℝ)⁻¹ • ∑ k, (σ k : ℝ) • Φ (u (S k))) := by
      intro h
      obtain ⟨w, hw, hh⟩ := h.2
      refine ⟨w, hw, fun u σ => ?_⟩
      unfold normalizedRademacherSum
      rw [← inner_rademacher_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Function.comp_apply]
      rw [hh]
    have hbdd : ∀ (u : X → X) (σ : Signs n), BddAbove (Set.range fun h : hilbertReadoutClass Φ =>
        normalizedRademacherSum n (fun h : hilbertReadoutClass Φ => (h : X → ℝ)) (u ∘ S) σ h) := by
      intro u σ
      refine ⟨‖(n : ℝ)⁻¹ • ∑ k, (σ k : ℝ) • Φ (u (S k))‖, ?_⟩
      rintro _ ⟨h, rfl⟩
      obtain ⟨w, hw, hh⟩ := hrepr h
      dsimp only
      rw [hh u σ]
      calc inner ℝ w ((n : ℝ)⁻¹ • ∑ k, (σ k : ℝ) • Φ (u (S k)))
          ≤ ‖w‖ * ‖(n : ℝ)⁻¹ • ∑ k, (σ k : ℝ) • Φ (u (S k))‖ := real_inner_le_norm _ _
        _ ≤ 1 * ‖(n : ℝ)⁻¹ • ∑ k, (σ k : ℝ) • Φ (u (S k))‖ := by gcongr
        _ = _ := one_mul _
    have hZ : ∀ σ : Signs n, |outputProcess S (hilbertReadoutClass Φ) f σ -
        outputProcess S (hilbertReadoutClass Φ) g σ| ≤ (n : ℝ)⁻¹ * ‖∑ i, (σ i : ℝ) • v i‖ := by
      intro σ
      unfold outputProcess
      refine abs_ciSup_sub_ciSup_le (hbdd f σ) (hbdd g σ) fun h => ?_
      obtain ⟨w, hw, hh⟩ := hrepr h
      have hf := hh f σ
      have hg := hh g σ
      rw [hf, hg, ← inner_sub_right, ← smul_sub, ← Finset.sum_sub_distrib]
      simp_rw [← smul_sub]
      calc |inner ℝ w ((n : ℝ)⁻¹ • ∑ k, (σ k : ℝ) • (Φ (f (S k)) - Φ (g (S k))))|
          ≤ ‖w‖ * ‖(n : ℝ)⁻¹ • ∑ k, (σ k : ℝ) • (Φ (f (S k)) - Φ (g (S k)))‖ :=
            abs_real_inner_le_norm _ _
        _ ≤ 1 * ‖(n : ℝ)⁻¹ • ∑ k, (σ k : ℝ) • (Φ (f (S k)) - Φ (g (S k)))‖ := by gcongr
        _ = (n : ℝ)⁻¹ * ‖∑ i, (σ i : ℝ) • v i‖ := by
            rw [one_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hcard : (0 : ℝ) < Fintype.card (Signs n) := by rw [FoML.ToFoML.card_signs]; positivity
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · -- `n = 0`: the increment vanishes and the event is empty
      have hempty : (Finset.univ.filter fun σ : Signs 0 =>
          t < |outputProcess S (hilbertReadoutClass Φ) f σ -
            outputProcess S (hilbertReadoutClass Φ) g σ|) = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr fun σ _ => ?_
        have := hZ σ
        simp only [CharP.cast_eq_zero, inv_zero, zero_mul] at this
        rw [not_lt]
        linarith
      rw [hempty]
      simp only [Finset.card_empty, Nat.cast_zero, zero_div]
      positivity
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hsub : (Finset.univ.filter fun σ : Signs n =>
          t < |outputProcess S (hilbertReadoutClass Φ) f σ -
            outputProcess S (hilbertReadoutClass Φ) g σ|) ⊆
          Finset.univ.filter fun σ : Signs n => n * t < ‖∑ i, (σ i : ℝ) • v i‖ := by
        intro σ hσ
        rw [Finset.mem_filter] at hσ ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        have := hσ.2.trans_le (hZ σ)
        rwa [lt_inv_mul_iff₀ hn'] at this
      have hV0 : 0 ≤ ∑ i, ‖v i‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      have hVle : ∑ i, ‖v i‖ ^ 2 ≤ L ^ 2 * (n * empDist S f g ^ 2) := by
        have := sum_sq_dist_le_of_lipschitz S hΦ f g
        simpa only [dist_eq_norm] using this
      have hcardle : ((Finset.univ.filter fun σ : Signs n =>
          t < |outputProcess S (hilbertReadoutClass Φ) f σ -
            outputProcess S (hilbertReadoutClass Φ) g σ|).card : ℝ) ≤
          (Finset.univ.filter fun σ : Signs n => n * t < ‖∑ i, (σ i : ℝ) • v i‖).card := by
        exact_mod_cast Finset.card_le_card hsub
      rcases hV0.lt_or_eq with hVpos | hVzero
      · have h1 := htail v (n * t) (by positivity)
        have hD : 0 < (L : ℝ) ^ 2 * (n * empDist S f g ^ 2) := hVpos.trans_le hVle
        have hD' : 0 < (L : ℝ) ^ 2 * empDist S f g ^ 2 := by
          rw [mul_left_comm] at hD
          exact pos_of_mul_pos_right hD hn'.le
        have hfrac : (n : ℝ) * t ^ 2 / (2 * 1 ^ 2 * L ^ 2 * empDist S f g ^ 2) ≤
            (n * t) ^ 2 / (2 * ∑ i, ‖v i‖ ^ 2) := by
          rw [show (n : ℝ) * t ^ 2 / (2 * 1 ^ 2 * L ^ 2 * empDist S f g ^ 2) =
              (n * t) ^ 2 / (2 * (L ^ 2 * (n * empDist S f g ^ 2))) by
            field_simp]
          exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
        calc _ ≤ ((Finset.univ.filter fun σ : Signs n =>
              n * t < ‖∑ i, (σ i : ℝ) • v i‖).card : ℝ) / Fintype.card (Signs n) := by
              gcongr
          _ ≤ 2 * Real.exp (-(n * t) ^ 2 / (2 * ∑ i, ‖v i‖ ^ 2)) := h1
          _ ≤ _ := by
              refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
              rw [neg_mul, neg_div, neg_div, neg_le_neg_iff]
              exact hfrac
      · -- all `vᵢ = 0`: the event is empty
        have hzero : ∀ i, v i = 0 := by
          intro i
          have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg ‖v i‖).mp hVzero.symm i
            (Finset.mem_univ _)
          exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
        have hempty : (Finset.univ.filter fun σ : Signs n =>
            n * t < ‖∑ i, (σ i : ℝ) • v i‖) = ∅ := by
          refine Finset.filter_eq_empty_iff.mpr fun σ _ => ?_
          simp [hzero, (by positivity : (0 : ℝ) ≤ n * t)]
        rw [hempty] at hcardle
        simp only [Finset.card_empty, Nat.cast_zero] at hcardle
        calc _ ≤ (0 : ℝ) / Fintype.card (Signs n) := by gcongr
          _ = 0 := zero_div _
          _ ≤ _ := by positivity

@[blueprint "prop:hilbert-sg"
  (statement := /-- \textbf{Hilbert output layers satisfy the increment condition.} Let
    $\mathcal H$ be a real Hilbert space and $\Phi : \mathcal X \to \mathcal H$ be $L$-Lipschitz.
    Then Assumption \texttt{ass:sg-increment-main} holds for $H = H_\Phi$ with $A_H = 1$ (and the
    same $L$), for every hidden-layer class $\mathfrak F$. -/)]
theorem hilbert_sg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (Φ : X → E)
    {L : ℝ≥0} (hΦ : LipschitzWith L Φ) (𝔉 : Set (X → X)) :
    SubGaussianIncrements S (hilbertReadoutClass Φ) 𝔉 1 L := by
  /-- Combine \texttt{prop:hilbert-sg-of-tail} with the vector Hoeffding inequality
    \texttt{lem:rademacher-hilbert-tail} (the only unproved ingredient). -/
  exact hilbert_sg_of_tail S Φ hΦ 𝔉 fun v _ ht => FoML.ToFoML.rademacher_hilbert_tail v ht

@[blueprint "prop:hilbert-sg-real"
  (statement := /-- \textbf{One-dimensional Hilbert output layers.} Let $\Phi : \mathcal X \to
    \mathbb R$ be $L$-Lipschitz and $H_\Phi = \{x \mapsto w\,\Phi(x) : |w| \le 1\}$. Then
    Assumption \texttt{ass:sg-increment-main} holds for $H_\Phi$ with $A_H = 1$ and the same $L$
    (this is \texttt{prop:hilbert-sg} for $\mathcal H = \mathbb R$, fully proved from the real
    Hoeffding inequality). -/)]
theorem hilbert_sg_real (Φ : X → ℝ) {L : ℝ≥0} (hΦ : LipschitzWith L Φ) (𝔉 : Set (X → X)) :
    SubGaussianIncrements S (hilbertReadoutClass Φ) 𝔉 1 L :=
  hilbert_sg_of_tail S Φ hΦ 𝔉 fun v _ ht => FoML.ToFoML.rademacher_hilbert_tail_real v ht

@[blueprint "prop:finite-lipschitz-sg"
  (statement := /-- \textbf{Finite Lipschitz scalar output layers.} Let $H = \{h_1, \dots, h_m\}$
    be a finite class of real-valued functions on $\mathcal X$, each $L$-Lipschitz. Then
    Assumption \texttt{ass:sg-increment-main} holds with
    $A_H = (1 + \log m / \log 2)^{1/2}$, for every hidden-layer class $\mathfrak F$. -/)]
theorem finite_lipschitz_sg (hH : H.Finite) {m : ℕ} (hm : H.ncard = m) {L : ℝ≥0}
    (hlip : ∀ h ∈ H, LipschitzWith L h) (𝔉 : Set (X → X)) :
    SubGaussianIncrements S H 𝔉 (Real.sqrt (1 + Real.log m / Real.log 2)) L := by
  /-- $|Z_f - Z_g| \le \max_j |S_j|$ with
    $S_j = \frac1n\sum_i \sigma_i (h_j(f(x_i)) - h_j(g(x_i)))$; real Hoeffding for each $S_j$
    (\texttt{lem:rademacher-real-tail}), a union bound over the $m$ functions, and
    \texttt{lem:union-bound-absorb} to absorb $m$ into $A_H$. -/
  classical
  refine ⟨?_, ?_⟩
  · intro f _ g _ hd σ
    exact outputProcess_congr S H
      (fun h hh i => lipschitz_apply_eq_of_empDist_eq_zero S (hlip h hh) hd i) σ
  · intro f _ g _ t ht
    have hcard : (0 : ℝ) < Fintype.card (Signs n) := by rw [FoML.ToFoML.card_signs]; positivity
    have hle1 := card_filter_signs_div_le_one
      (fun σ : Signs n => t < |outputProcess S H f σ - outputProcess S H g σ|)
    rcases H.eq_empty_or_nonempty with rfl | hne
    · -- empty class: both processes vanish
      have hZ : ∀ (u : X → X) (σ : Signs n), outputProcess S ∅ u σ = 0 := fun u σ => by
        unfold outputProcess
        haveI : IsEmpty ((∅ : Set (X → ℝ))) := Set.isEmpty_coe_sort.mpr rfl
        rw [iSup_of_empty']
        exact Real.sSup_empty
      have hempty : (Finset.univ.filter fun σ : Signs n =>
          t < |outputProcess S ∅ f σ - outputProcess S ∅ g σ|) = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr fun σ _ => ?_
        rw [hZ, hZ, sub_zero, abs_zero, not_lt]
        exact ht.le
      rw [hempty]
      simp only [Finset.card_empty, Nat.cast_zero, zero_div]
      positivity
    · haveI : Nonempty H := hne.to_subtype
      haveI : Finite H := hH.to_subtype
      have hm1 : 1 ≤ m := by
        rw [← hm]
        exact (Set.ncard_pos hH).mpr hne
      have hmcard : (hH.toFinset.card : ℝ) = m := by
        rw [← hm, Set.ncard_eq_toFinset_card H hH]
      -- the per-function increments
      have hdiff : ∀ (h : H) (σ : Signs n),
          normalizedRademacherSum n (fun h : H => (h : X → ℝ)) (f ∘ S) σ h -
            normalizedRademacherSum n (fun h : H => (h : X → ℝ)) (g ∘ S) σ h =
          (n : ℝ)⁻¹ * ∑ k, (σ k : ℝ) * ((h : X → ℝ) (f (S k)) - (h : X → ℝ) (g (S k))) := by
        intro h σ
        unfold normalizedRademacherSum
        rw [← mul_sub, ← Finset.sum_sub_distrib]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [Function.comp_apply]
        ring
      have hbdd : ∀ (u : X → X) (σ : Signs n), BddAbove (Set.range fun h : H =>
          normalizedRademacherSum n (fun h : H => (h : X → ℝ)) (u ∘ S) σ h) :=
        fun u σ => (Set.finite_range _).bddAbove
      -- union bound: the event is contained in the union of the `m` events for each `h`
      have hsub : (Finset.univ.filter fun σ : Signs n =>
          t < |outputProcess S H f σ - outputProcess S H g σ|) ⊆
          hH.toFinset.biUnion fun h => Finset.univ.filter fun σ : Signs n =>
            n * t < |∑ k, (σ k : ℝ) * (h (f (S k)) - h (g (S k)))| := by
        intro σ hσ
        rw [Finset.mem_filter] at hσ
        rw [Finset.mem_biUnion]
        by_contra hcon
        have hall : ∀ h : H,
            |∑ k, (σ k : ℝ) * ((h : X → ℝ) (f (S k)) - (h : X → ℝ) (g (S k)))| ≤ n * t := by
          intro h
          by_contra hlt
          rw [not_le] at hlt
          exact hcon ⟨h, hH.mem_toFinset.mpr h.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩⟩
        have hZ : |outputProcess S H f σ - outputProcess S H g σ| ≤ t := by
          unfold outputProcess
          refine abs_ciSup_sub_ciSup_le (hbdd f σ) (hbdd g σ) fun h => ?_
          rw [hdiff, abs_mul, abs_of_nonneg (inv_nonneg.mpr n.cast_nonneg)]
          rcases Nat.eq_zero_or_pos n with rfl | hn
          · simp only [CharP.cast_eq_zero, inv_zero, zero_mul]
            exact ht.le
          · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
            rw [inv_mul_le_iff₀ hn']
            exact hall h
        exact absurd hσ.2 (not_lt.mpr hZ)
      -- Hoeffding for each `h`
      have hper : ∀ h ∈ H, ((Finset.univ.filter fun σ : Signs n =>
          n * t < |∑ k, (σ k : ℝ) * (h (f (S k)) - h (g (S k)))|).card : ℝ) ≤
          Fintype.card (Signs n) *
            (2 * Real.exp (-((n : ℝ) * t ^ 2 / (2 * L ^ 2 * empDist S f g ^ 2)))) := by
        intro h hh
        have hV0 : 0 ≤ ∑ k, (h (f (S k)) - h (g (S k))) ^ 2 :=
          Finset.sum_nonneg fun k _ => sq_nonneg _
        have hVle : ∑ k, (h (f (S k)) - h (g (S k))) ^ 2 ≤ L ^ 2 * (n * empDist S f g ^ 2) := by
          have := sum_sq_dist_le_of_lipschitz S (hlip h hh) f g
          simpa only [Real.dist_eq, sq_abs] using this
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · -- `n = 0`: the sums are empty
          simp
        have hn' : (0 : ℝ) < n := by exact_mod_cast hn
        rcases hV0.lt_or_eq with hVpos | hVzero
        · have h1 := FoML.ToFoML.rademacher_real_tail (fun k => h (f (S k)) - h (g (S k)))
            (by positivity : 0 < n * t)
          rw [div_le_iff₀ hcard] at h1
          refine h1.trans ?_
          rw [mul_comm]
          gcongr
          have hD : 0 < (L : ℝ) ^ 2 * (n * empDist S f g ^ 2) := hVpos.trans_le hVle
          have hD' : 0 < (L : ℝ) ^ 2 * empDist S f g ^ 2 := by
            rw [mul_left_comm] at hD
            exact pos_of_mul_pos_right hD hn'.le
          rw [neg_div, neg_le_neg_iff,
            show (n : ℝ) * t ^ 2 / (2 * L ^ 2 * empDist S f g ^ 2) =
              (n * t) ^ 2 / (2 * (L ^ 2 * (n * empDist S f g ^ 2))) by
                field_simp]
          exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
        · have hzero : ∀ k, h (f (S k)) - h (g (S k)) = 0 := by
            intro k
            have := (Finset.sum_eq_zero_iff_of_nonneg fun k _ =>
              sq_nonneg (h (f (S k)) - h (g (S k)))).mp hVzero.symm k (Finset.mem_univ _)
            exact pow_eq_zero_iff two_ne_zero |>.mp this
          have hempty : (Finset.univ.filter fun σ : Signs n =>
              n * t < |∑ k, (σ k : ℝ) * (h (f (S k)) - h (g (S k)))|) = ∅ := by
            refine Finset.filter_eq_empty_iff.mpr fun σ _ => ?_
            simp [hzero, (by positivity : (0 : ℝ) ≤ n * t)]
          rw [hempty]
          simp only [Finset.card_empty, Nat.cast_zero]
          positivity
      -- assemble the union bound
      have hP : ((Finset.univ.filter fun σ : Signs n =>
          t < |outputProcess S H f σ - outputProcess S H g σ|).card : ℝ) /
            Fintype.card (Signs n) ≤
          2 * m * Real.exp (-((n : ℝ) * t ^ 2 / (2 * L ^ 2 * empDist S f g ^ 2))) := by
        rw [div_le_iff₀ hcard]
        calc ((Finset.univ.filter fun σ : Signs n =>
              t < |outputProcess S H f σ - outputProcess S H g σ|).card : ℝ)
            ≤ ((hH.toFinset.biUnion fun h => Finset.univ.filter fun σ : Signs n =>
                n * t < |∑ k, (σ k : ℝ) * (h (f (S k)) - h (g (S k)))|).card : ℝ) := by
              exact_mod_cast Finset.card_le_card hsub
          _ ≤ ∑ h ∈ hH.toFinset, ((Finset.univ.filter fun σ : Signs n =>
                n * t < |∑ k, (σ k : ℝ) * (h (f (S k)) - h (g (S k)))|).card : ℝ) := by
              exact_mod_cast Finset.card_biUnion_le
          _ ≤ ∑ _h ∈ hH.toFinset, (Fintype.card (Signs n) : ℝ) *
                (2 * Real.exp (-((n : ℝ) * t ^ 2 / (2 * L ^ 2 * empDist S f g ^ 2)))) :=
              Finset.sum_le_sum fun h hh => hper h (hH.mem_toFinset.mp hh)
          _ = _ := by
              rw [Finset.sum_const, nsmul_eq_mul, hmcard]
              ring
      have hA0 : 0 ≤ 1 + Real.log m / Real.log 2 := by
        have h1 : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm1)
        have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        positivity
      have := FoML.ToFoML.union_bound_absorb m hm1 hle1 hP
      have hden : 2 * (1 + Real.log m / Real.log 2) * (L : ℝ) ^ 2 * empDist S f g ^ 2 =
          2 * L ^ 2 * empDist S f g ^ 2 * (1 + Real.log m / Real.log 2) := by ring
      rw [Real.sq_sqrt hA0, hden, neg_mul, ← div_div, neg_div]
      exact this

end Metric

end LeanDeepgen
