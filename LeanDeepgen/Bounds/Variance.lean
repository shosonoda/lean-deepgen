import Mathlib
import Architect
import FoML
import LeanDeepgen.Setting.WordBall
import LeanDeepgen.Setting.Metrics
import LeanDeepgen.Setting.Covering
import LeanDeepgen.Setting.Hypothesis
import LeanDeepgen.Setting.Rademacher
import LeanDeepgen.Setting.Assumptions
import LeanDeepgen.Growth.Lemmas
import LeanDeepgen.Growth.ArzelaAscoli
import LeanDeepgen.Growth.Saturation
import LeanDeepgen.Growth.Polynomial
import LeanDeepgen.Profiles.Profiles
import LeanDeepgen.Bounds.HiddenOutput

/-!
# The variance term and the table of profiles (paper Sec. 4.2, `tab:profiles`)

This module plugs the growth mechanisms (P1, P2, finite generator sets) and the diameter
envelopes into the abstract variance profiles of `LeanDeepgen.Profiles.Profiles`, and then into
the hidden–output decomposition `thm:hidden-decomp-depth`.

* `lem:covering-empSpace-le-unifMaps`: the identity `(𝒳^𝒳, d_∞) → (𝒳^𝒳, d_S)` is
  `1`-Lipschitz, so every covering/packing number in `d_S` is dominated by the one in `d_∞`
  ("since `d_S ≤ d_∞`, all hypotheses may be verified in the uniform metric").  The internal
  covering number in `d_S` at scale `ε` is dominated by the external one in `d_∞` at scale
  `ε/2` (`lem:covering-empSpace-le-external-unifMaps`), which is the bridge used by all profiles.
* `lem:empDiam-le-of-uniformDist-le`: diameter envelopes transfer from `d_∞` to `d_S`.
* `lem:hidden-decomp-var`: with `var(k,n) = 12 A_H L V_k(S) / √n` (`varTerm`, `def:var`, defined
  together with `toEmpSpace` in `LeanDeepgen.Setting.Assumptions`), the restatement of
  `thm:hidden-decomp-depth` as `R̂_S(ℋ_k) ≤ R̂_S(H) + var(k,n)` (which requires the entropy
  integrand of `B(k,F)` to be interval-integrable on `[0, D_k(S)]`).
* `lem:p1-integrand-integrable`, `lem:p2-integrand-integrable`,
  `lem:finite-integrand-integrable`: under each profile this integrability follows from the
  domination by the majorant, so the corollaries `cor:var-profiles-*` need no extra hypothesis.
* The table of profiles: `cor:profile-p1` (saturation, `O(1)`), `cor:profile-p2-compact`
  (`O(√(D log k))`), `cor:profile-p2-noncompact` (`O(k √D)`), `cor:profile-finite`
  (`O(√(k log r))`), and their consequences `cor:var-profiles-*` for the estimation term.

Conventions.  Mathlib's internal covering number `N(A, ε)` is not monotone in the set and is
only comparable to the external one up to a factor `2` in the scale
(`N(A, 2ε) ≤ N^ext(A, ε)`); accordingly the saturation majorant is
`N_∞(ε) := N^ext(cl⟨F⟩, d_∞, ε/2)` and the polynomial constant `C_0` of P2 acquires a factor
`2^D`.  The integrability of the saturation majorant (the paper's `V_∞ < ∞`) is an explicit
hypothesis `hint`: the majorant is finite and antitone on `(0, D̄]`, but may fail to be
integrable at `0`.
-/

open scoped NNReal ENNReal Real
open Metric MeasureTheory Set

open FoML.ToMathlib

namespace LeanDeepgen

variable {X : Type*} [PseudoMetricSpace X] {n : ℕ} (S : Fin n → X)

/-! ### Comparison of covering numbers in `d_S` and `d_∞` -/

section Comparison

@[blueprint "lem:to-emp-space-lipschitz"
  (statement := /-- Since $d_S \le d_\infty$, the identity map
    $(\mathcal X^{\mathcal X}, d_\infty) \to (\mathcal X^{\mathcal X}, d_S)$ is $1$-Lipschitz. -/)]
theorem lipschitzWith_toEmpSpace : LipschitzWith 1 (toEmpSpace S) := by
  /-- This is `lem:dS-le-dinf`. -/
  refine LipschitzWith.of_edist_le fun f g => ?_
  rw [edist_dist]
  exact empDist_le_uniformDist

@[blueprint "lem:covering-empSpace-le-unifMaps"
  (statement := /-- For every $A \subseteq \mathcal X^{\mathcal X}$ and $\varepsilon \ge 0$,
    $N^{\mathrm{ext}}(A, d_S, \varepsilon) \le N^{\mathrm{ext}}(A, d_\infty, \varepsilon)$:
    covering numbers in the empirical metric are dominated by those in the uniform metric,
    so all hypotheses may be verified in $d_\infty$. -/)]
theorem externalCoveringNumber_empSpace_le (ε : ℝ≥0) (A : Set (X → X)) :
    externalCoveringNumber (X := EmpSpace S) ε A ≤
      externalCoveringNumber (X := UnifMaps X) ε A := by
  /-- `lem:lipschitz-embedding` with $K = 1$ and $\varphi = \mathrm{id}$. -/
  have himg : toEmpSpace S '' A = A := Set.image_id' A
  have h := externalCoveringNumber_image_le (lipschitzWith_toEmpSpace S) ε A
  rwa [one_mul, himg] at h

@[blueprint "lem:covering-empSpace-le-unifMaps-internal"
  (statement := /-- $N(A, d_S, \varepsilon) \le N(A, d_\infty, \varepsilon)$ (internal covering
    numbers). -/)]
theorem coveringNumber_empSpace_le (ε : ℝ≥0) (A : Set (X → X)) :
    coveringNumber (X := EmpSpace S) ε A ≤ coveringNumber (X := UnifMaps X) ε A := by
  /-- `lem:lipschitz-embedding-internal` with $K = 1$ and $\varphi = \mathrm{id}$. -/
  have himg : toEmpSpace S '' A = A := Set.image_id' A
  have h := coveringNumber_image_le (lipschitzWith_toEmpSpace S) ε A
  rwa [one_mul, himg] at h

@[blueprint "lem:packing-empSpace-le-unifMaps"
  (statement := /-- $M(A, d_S, \varepsilon) \le M(A, d_\infty, \varepsilon)$ (packing
    numbers). -/)]
theorem packingNumber_empSpace_le (ε : ℝ≥0) (A : Set (X → X)) :
    packingNumber (X := EmpSpace S) ε A ≤ packingNumber (X := UnifMaps X) ε A := by
  /-- `lem:lipschitz-embedding-packing` with $K = 1$ and $\varphi = \mathrm{id}$. -/
  have himg : toEmpSpace S '' A = A := Set.image_id' A
  have h := packingNumber_image_le (lipschitzWith_toEmpSpace S) ε A
  rwa [one_mul, himg] at h

@[blueprint "lem:covering-empSpace-le-external-unifMaps"
  (statement := /-- The bridge used by all profiles: for every $A \subseteq \mathcal X^{\mathcal X}$
    and $\varepsilon \ge 0$,
    $N(A, d_S, \varepsilon) \le N^{\mathrm{ext}}(A, d_\infty, \varepsilon/2)$
    (internal covering number on the left, external on the right; the factor $2$ is the price
    of comparing internal with external covers). -/)]
theorem coveringNumber_empSpace_le_externalCoveringNumber_unifMaps (ε : ℝ≥0)
    (A : Set (X → X)) :
    coveringNumber (X := EmpSpace S) ε A ≤
      externalCoveringNumber (X := UnifMaps X) (ε / 2) A := by
  /-- $N(A, d_S, \varepsilon) = N(A, d_S, 2\cdot\varepsilon/2)
    \le N^{\mathrm{ext}}(A, d_S, \varepsilon/2)
    \le N^{\mathrm{ext}}(A, d_\infty, \varepsilon/2)$. -/
  calc coveringNumber (X := EmpSpace S) ε A
      = coveringNumber (X := EmpSpace S) (2 * (ε / 2)) A := by ring_nf
    _ ≤ externalCoveringNumber (X := EmpSpace S) (ε / 2) A :=
        coveringNumber_two_mul_le_externalCoveringNumber _ _
    _ ≤ externalCoveringNumber (X := UnifMaps X) (ε / 2) A :=
        externalCoveringNumber_empSpace_le S _ _

@[blueprint "lem:covering-empSpace-toReal-le"
  (statement := /-- If $N^{\mathrm{ext}}(A, d_\infty, \varepsilon/2) \le b$ with $b \ge 0$, then
    $N(A, d_S, \varepsilon) \le b$ as real numbers (the covering number being finite). -/)]
theorem toReal_coveringNumber_empSpace_le {ε : ℝ≥0} {A : Set (X → X)} {b : ℝ} (hb : 0 ≤ b)
    (h : (externalCoveringNumber (X := UnifMaps X) (ε / 2) A : ℝ≥0∞) ≤ ENNReal.ofReal b) :
    (coveringNumber (X := EmpSpace S) ε A : ℝ≥0∞).toReal ≤ b :=
  ENNReal.toReal_le_of_le_ofReal hb
    ((ENat.toENNReal_le.2 (coveringNumber_empSpace_le_externalCoveringNumber_unifMaps S ε A)).trans
      h)

end Comparison

/-! ### Diameter envelopes -/

section Diameter

@[blueprint "lem:empDiam-nonneg"
  (statement := /-- $\mathrm{diam}_S(A) \ge 0$. -/)]
theorem empDiam_nonneg (A : Set (X → X)) : 0 ≤ empDiam S A :=
  Real.sSup_nonneg fun _ hx => by
    obtain ⟨f, -, g, -, rfl⟩ := hx
    exact empDist_nonneg

@[blueprint "lem:empDiam-le-of-uniformDist-le"
  (statement := /-- (Diameter envelopes transfer from $d_\infty$ to $d_S$.) If
    $d_\infty(f,g) \le D$ for all $f, g \in A$, with $D \ge 0$, then
    $\mathrm{diam}_S(A) \le D$ for every sample $S$. -/)]
theorem empDiam_le_of_uniformDist_le {A : Set (X → X)} {D : ℝ} (hD : 0 ≤ D)
    (h : ∀ f ∈ A, ∀ g ∈ A, uniformDist f g ≤ ENNReal.ofReal D) : empDiam S A ≤ D := by
  /-- $d_S(f,g) \le d_\infty(f,g) \le D$ for all $f, g \in A$; take the supremum
    (which is $0 \le D$ if $A = \emptyset$). -/
  refine Real.sSup_le ?_ hD
  rintro _ ⟨f, hf, g, hg, rfl⟩
  exact (ENNReal.ofReal_le_ofReal_iff hD).1 (empDist_le_uniformDist.trans (h f hf g hg))

@[blueprint "lem:empDiam-le-toReal-of-uniformDist-le"
  (statement := /-- If $d_\infty(f,g) \le \overline D < \infty$ for all $f, g \in A$ then
    $\mathrm{diam}_S(A) \le \overline D$. -/)]
theorem empDiam_le_toReal_of_uniformDist_le {A : Set (X → X)} {Dbar : ℝ≥0∞} (hD : Dbar ≠ ⊤)
    (h : ∀ f ∈ A, ∀ g ∈ A, uniformDist f g ≤ Dbar) : empDiam S A ≤ Dbar.toReal :=
  empDiam_le_of_uniformDist_le S ENNReal.toReal_nonneg fun f hf g hg => by
    rw [ENNReal.ofReal_toReal hD]; exact h f hf g hg

@[blueprint "lem:empDiam-le-of-bounded"
  (statement := /-- On a bounded state space, $d(x,y) \le D_{\mathcal X}$ for all $x, y$
    ($D_{\mathcal X} \ge 0$), every class satisfies $\mathrm{diam}_S(A) \le D_{\mathcal X}$;
    in particular $D_k(S) \le \mathrm{diam}(\mathcal X)$ for all $k$. -/)]
theorem empDiam_le_of_bounded {Dx : ℝ} (hDx : 0 ≤ Dx) (hX : ∀ x y : X, dist x y ≤ Dx)
    (A : Set (X → X)) : empDiam S A ≤ Dx :=
  empDiam_le_of_uniformDist_le S hDx fun f _ g _ =>
    uniformDist_le_of_bounded
      (fun x y => by rw [edist_dist]; exact ENNReal.ofReal_le_ofReal (hX x y)) f g

@[blueprint "lem:empDiam-le-of-compact"
  (statement := /-- On a compact state space, $D_k(S) \le \mathrm{diam}(\mathcal X)$ for every
    class $A$ and every sample $S$. -/)]
theorem empDiam_le_diam_univ [CompactSpace X] (A : Set (X → X)) :
    empDiam S A ≤ Metric.diam (Set.univ : Set X) :=
  empDiam_le_of_bounded S Metric.diam_nonneg
    (fun x y => Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ y)) A

@[blueprint "lem:empDiam-wordBall-le-of-p2"
  (statement := /-- (Diameter envelope under P2, non-compact case.) Under the hypotheses of
    `lem:p2-diameter`, $D_k(S) = \mathrm{diam}_S B(k,F) \le 2 L_\alpha R_S k$ for every sample
    $S$. -/)]
theorem empDiam_wordBall_le_of_p2 {Γ : Type*} [Group Γ] [PseudoEMetricSpace Γ]
    (α : Γ →* Function.End X) {F : Set (X → X)}
    (hsub : ∀ g h : Γ, edist 1 (g * h) ≤ edist 1 g + edist 1 h)
    {Sg : Set Γ} {RS : ℝ≥0} (hS : ∀ s ∈ Sg, edist 1 s ≤ RS) (hF : F ⊆ orbitMap α '' Sg)
    {Lα : ℝ≥0} (hα : LipschitzWith Lα (fun g => toUnifMaps (orbitMap α g))) (k : ℕ) :
    empDiam S (wordBall F k) ≤ 2 * Lα * RS * k := by
  /-- `lem:p2-diameter` gives $d_\infty(f,g) \le 2L_\alpha R_S k$ on $B(k,F)$; transfer to
    $d_S$. -/
  refine empDiam_le_of_uniformDist_le S (by positivity) fun f hf g hg => ?_
  refine (uniformDist_le_of_mem_wordBall α hsub hS hF hα k hf hg).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal,
    ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_natCast]

end Diameter

/-! ### The variance term -/

section VarianceTerm

variable (H : Set (X → ℝ))

@[blueprint "lem:hidden-decomp-var"
  (statement := /-- (Restatement of `thm:hidden-decomp-depth`.) Under the hypotheses of
    `thm:hidden-decomp-depth` (including the integrability of the entropy integrand of $B(k,F_0)$
    on $[0, D_k(S)]$), $\hat{\mathfrak R}_S(\mathcal H_k) \le \hat{\mathfrak R}_S(H)
    + \mathrm{var}(k,n)$. -/)]
theorem hidden_decomp_var (hn : 0 < n) (F₀ : Set (X → X)) (k : ℕ) {AH L : ℝ} (hAH : 0 < AH)
    (hL : 0 < L)
    (hbdd : ∀ f ∈ wordBall F₀ k, ∀ σ : Signs n,
      BddAbove (Set.range fun h : H =>
        normalizedRademacherSum n (fun h : H => (h : X → ℝ)) (f ∘ S) σ h))
    (hF : TotallyBounded (α := EmpSpace S) (wordBall F₀ k))
    (hsg : SubGaussianIncrements S H (semigroupClosure F₀) AH L)
    (hint : IntervalIntegrable
      (fun ε : ℝ => √(metricEntropy (X := EmpSpace S) ε.toNNReal (wordBall F₀ k)))
      volume 0 (empDiam S (wordBall F₀ k))) :
    empRademacher S (hypothesisClass H F₀ k) ≤ empRademacher S H + varTerm AH L n S F₀ k :=
  /- The Dudley integral of `thm:hidden-decomp-depth` is by definition
    $\mathsf V(D_k(S), B(k,F_0))$ in the pseudometric space $(\mathcal X^{\mathcal X}, d_S)$. -/
  hidden_decomp_depth S H hn F₀ k hAH hL hbdd hF hsg hint

@[blueprint "cor:var-profiles"
  (statement := /-- (Plugging a profile into the decomposition.) Under the hypotheses of
    `thm:hidden-decomp-depth` (including the integrability of the entropy integrand), if
    $\mathsf V_k(S) \le B$ then
    $\hat{\mathfrak R}_S(\mathcal H_k) \le \hat{\mathfrak R}_S(H) + \frac{12A_HL}{\sqrt n}\,B$.
    The statements about $\mathrm{var}(k,n)$ in `prop:profiles` follow by multiplying the profile
    bounds with $12A_HL/\sqrt n$. -/)]
theorem empRademacher_le_of_entropyIntegral_le (hn : 0 < n) (F₀ : Set (X → X)) (k : ℕ)
    {AH L : ℝ} (hAH : 0 < AH) (hL : 0 < L)
    (hbdd : ∀ f ∈ wordBall F₀ k, ∀ σ : Signs n,
      BddAbove (Set.range fun h : H =>
        normalizedRademacherSum n (fun h : H => (h : X → ℝ)) (f ∘ S) σ h))
    (hF : TotallyBounded (α := EmpSpace S) (wordBall F₀ k))
    (hsg : SubGaussianIncrements S H (semigroupClosure F₀) AH L)
    (hint : IntervalIntegrable
      (fun ε : ℝ => √(metricEntropy (X := EmpSpace S) ε.toNNReal (wordBall F₀ k)))
      volume 0 (empDiam S (wordBall F₀ k))) {B : ℝ}
    (hB : entropyIntegral (Y := EmpSpace S) (empDiam S (wordBall F₀ k)) (wordBall F₀ k) ≤ B) :
    empRademacher S (hypothesisClass H F₀ k) ≤
      empRademacher S H + 12 * AH * L / Real.sqrt n * B := by
  /-- `lem:hidden-decomp-var` and $12A_HL/\sqrt n \ge 0$. -/
  refine (hidden_decomp_var S H hn F₀ k hAH hL hbdd hF hsg hint).trans ?_
  unfold varTerm
  gcongr

end VarianceTerm

/-! ### Table of profiles: P1 (saturation) -/

section P1

variable {F : Set (X → X)}

@[blueprint "cor:profile-p1-totallyBounded"
  (statement := /-- \textbf{(P1 $\Rightarrow$ saturation; general form.)} Let the state metric be
    bounded, $d(x,y) \le D_{\mathcal X}$ ($D_{\mathcal X} \ge 0$), and let the semigroup
    $\langle F\rangle$ be totally bounded in $d_\infty$ (`cond:p1`).  Put
    $N_\infty(\varepsilon) := N^{\mathrm{ext}}\bigl(\overline{\langle F\rangle}, d_\infty,
    \varepsilon/2\bigr)$ (finite for $\varepsilon > 0$; the factor $\tfrac12$ comes from comparing
    internal with external covers) and assume
    $\mathsf V_\infty := \int_0^{D_{\mathcal X}} \sqrt{\log N_\infty(\varepsilon)}\,d\varepsilon
    < \infty$ (interval-integrability of the majorant).  Then for every $k$ and every sample $S$,
    $\mathsf V_k(S) \le \mathsf V_\infty$: profile (i), $\mathrm{var}(k,n) = O(n^{-1/2})$. -/)]
theorem profile_p1_of_totallyBounded
    (hF : TotallyBounded (α := UnifMaps X) (semigroupClosure F)) {Dx : ℝ} (hDx : 0 ≤ Dx)
    (hX : ∀ x y : X, dist x y ≤ Dx)
    (hint : IntervalIntegrable (fun ε : ℝ => √(Real.log (externalCoveringNumber (X := UnifMaps X)
      (ε.toNNReal / 2) (closure (X := UnifMaps X) (semigroupClosure F)) : ℝ≥0∞).toReal))
      volume 0 Dx) (k : ℕ) :
    entropyIntegral (Y := EmpSpace S) (empDiam S (wordBall F k)) (wordBall F k) ≤
      ∫ ε in (0 : ℝ)..Dx, √(Real.log (externalCoveringNumber (X := UnifMaps X)
        (ε.toNNReal / 2) (closure (X := UnifMaps X) (semigroupClosure F)) : ℝ≥0∞).toReal) := by
  /-- `prop:profiles-i` with $A_k = B(k,F)$, $D_k = D_k(S) \le D_{\mathcal X}$
    (`lem:empDiam-le-of-bounded`) and the majorant $N_\infty$:
    $N(B(k,F), d_S, \varepsilon) \le N^{\mathrm{ext}}(B(k,F), d_\infty, \varepsilon/2)
    \le N^{\mathrm{ext}}(\overline{\langle F\rangle}, d_\infty, \varepsilon/2)$
    (`lem:covering-empSpace-le-external-unifMaps` and monotonicity), finite by `cond:p1`. -/
  refine profile_saturation (Y := EmpSpace S) (A := fun k => wordBall F k)
    (D := fun k => empDiam S (wordBall F k))
    (Ninf := fun ε => externalCoveringNumber (X := UnifMaps X) (ε / 2)
      (closure (X := UnifMaps X) (semigroupClosure F)))
    (fun k => empDiam_nonneg S (wordBall F k))
    (fun k => empDiam_le_of_bounded S hDx hX (wordBall F k)) ?_ ?_ hint k
  · intro k ε
    exact (coveringNumber_empSpace_le_externalCoveringNumber_unifMaps S ε _).trans
      (externalCoveringNumber_mono_set
        (subset_semigroupClosure.trans (subset_closure (X := UnifMaps X))))
  · intro ε hε
    exact (cond_p1_of_totallyBounded hF (ε / 2) (by positivity) 0).2

@[blueprint "cor:profile-p1"
  (statement := /-- \textbf{(P1 $\Rightarrow$ saturation; table row ``P1 (compact,
    equicontinuous)''.)} Let $\mathcal X$ be compact and the semigroup $\langle F\rangle$
    equicontinuous.  With $N_\infty(\varepsilon) := N^{\mathrm{ext}}\bigl(\overline{\langle
    F\rangle}, d_\infty, \varepsilon/2\bigr)$ and
    $\mathsf V_\infty := \int_0^{\mathrm{diam}(\mathcal X)} \sqrt{\log N_\infty(\varepsilon)}\,
    d\varepsilon < \infty$ (assumed interval-integrable), $D_k(S) \le \mathrm{diam}(\mathcal X)$
    and $\mathsf V_k(S) \le \mathsf V_\infty$ for all $k$: profile (i), $\mathsf V_k = O(1)$,
    $\mathrm{var}(k,n) = O(n^{-1/2})$. -/)]
theorem profile_p1_of_equicontinuous [CompactSpace X]
    (hF : Equicontinuous (fun f : semigroupClosure F => (f : X → X)))
    (hint : IntervalIntegrable (fun ε : ℝ => √(Real.log (externalCoveringNumber (X := UnifMaps X)
      (ε.toNNReal / 2) (closure (X := UnifMaps X) (semigroupClosure F)) : ℝ≥0∞).toReal))
      volume 0 (Metric.diam (Set.univ : Set X))) (k : ℕ) :
    entropyIntegral (Y := EmpSpace S) (empDiam S (wordBall F k)) (wordBall F k) ≤
      ∫ ε in (0 : ℝ)..Metric.diam (Set.univ : Set X),
        √(Real.log (externalCoveringNumber (X := UnifMaps X) (ε.toNNReal / 2)
          (closure (X := UnifMaps X) (semigroupClosure F)) : ℝ≥0∞).toReal) :=
  /- Arzelà–Ascoli (`thm:caa`): the semigroup is totally bounded in $d_\infty$; the state
    space is bounded by $\mathrm{diam}(\mathcal X)$. -/
  profile_p1_of_totallyBounded S (totallyBounded_unifMaps_of_equicontinuous hF) Metric.diam_nonneg
    (fun x y => Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ y))
    hint k

@[blueprint "cor:profile-p1-nonexpanding"
  (statement := /-- \textbf{(P1 with non-expanding generators.)} Let $\mathcal X$ be compact and
    every $f \in F$ be $1$-Lipschitz.  Then the conclusion of `cor:profile-p1` holds. -/)]
theorem profile_p1_of_nonexpanding [CompactSpace X] (hF : ∀ f ∈ F, LipschitzWith 1 f)
    (hint : IntervalIntegrable (fun ε : ℝ => √(Real.log (externalCoveringNumber (X := UnifMaps X)
      (ε.toNNReal / 2) (closure (X := UnifMaps X) (semigroupClosure F)) : ℝ≥0∞).toReal))
      volume 0 (Metric.diam (Set.univ : Set X))) (k : ℕ) :
    entropyIntegral (Y := EmpSpace S) (empDiam S (wordBall F k)) (wordBall F k) ≤
      ∫ ε in (0 : ℝ)..Metric.diam (Set.univ : Set X),
        √(Real.log (externalCoveringNumber (X := UnifMaps X) (ε.toNNReal / 2)
          (closure (X := UnifMaps X) (semigroupClosure F)) : ℝ≥0∞).toReal) :=
  /- Non-expanding generators generate a uniformly $1$-Lipschitz, hence equicontinuous,
    semigroup (`cond:p1-2c`). -/
  profile_p1_of_equicontinuous S
    ((LipschitzWith.uniformEquicontinuous (fun g : semigroupClosure F => (g : X → X)) 1
      fun g => lipschitzWith_one_of_mem_semigroupClosure hF g.2).equicontinuous) hint k

end P1

/-! ### Table of profiles: P2 (polynomial growth) -/

section P2

variable {Γ : Type*} [Group Γ] [PseudoEMetricSpace Γ] {F : Set (X → X)}

@[blueprint "lem:p2-empSpace-covering"
  (statement := /-- (P2 in the empirical metric.) Under the hypotheses of `cond:p2-nilp`, for
    every $k$ and $\varepsilon > 0$,
    $$N(B(k,F), d_S, \varepsilon) \le C_0 \Bigl(1 + \frac k\varepsilon\Bigr)^D,\qquad
    C_0 := 2^D\, C_H \max(1, R_S L_\alpha)^D,$$
    as real numbers.  (The factor $2^D$ comes from
    $N(\cdot, d_S, \varepsilon) \le N^{\mathrm{ext}}(\cdot, d_\infty, \varepsilon/2)$ and
    $1 + 2k/\varepsilon \le 2(1 + k/\varepsilon)$.) -/)]
theorem toReal_coveringNumber_empSpace_wordBall_le_of_p2 (α : Γ →* Function.End X)
    (hsub : ∀ g h : Γ, edist 1 (g * h) ≤ edist 1 g + edist 1 h)
    {D : ℝ} (hD : 0 ≤ D) {CH : ℝ} (hCH : 1 ≤ CH)
    (hball : ∀ R δ : ℝ≥0, 0 < δ →
      (externalCoveringNumber δ (closedEBall (1 : Γ) R) : ℝ≥0∞) ≤
        ENNReal.ofReal (CH * (1 + R / δ) ^ D))
    {Sg : Set Γ} {RS : ℝ≥0} (hS : ∀ s ∈ Sg, edist 1 s ≤ RS) (hF : F ⊆ orbitMap α '' Sg)
    {Lα : ℝ≥0} (hLα : 0 < Lα) (hα : LipschitzWith Lα (fun g => toUnifMaps (orbitMap α g)))
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (coveringNumber (X := EmpSpace S) ε.toNNReal (wordBall F k) : ℝ≥0∞).toReal ≤
      2 ^ D * (CH * max 1 (RS * Lα) ^ D) * (1 + k / ε) ^ D := by
  /-- Apply `cond:p2-nilp` at scale $\varepsilon/2$ and
    `lem:covering-empSpace-toReal-le`. -/
  have hCH0 : 0 ≤ CH := zero_le_one.trans hCH
  have hM : (0 : ℝ) ≤ max 1 (RS * Lα) ^ D := by positivity
  have h := cond_p2_nilp α hsub hD hCH hball hS hF hLα hα (ε.toNNReal / 2) (by positivity) k
  refine toReal_coveringNumber_empSpace_le S (by positivity) (h.trans (ENNReal.ofReal_le_ofReal ?_))
  have hcoe : ((ε.toNNReal / 2 : ℝ≥0) : ℝ) = ε / 2 := by
    rw [NNReal.coe_div, Real.coe_toNNReal _ hε.le, NNReal.coe_ofNat]
  rw [hcoe]
  have hk0 : (0 : ℝ) ≤ k / ε := by positivity
  have h1 : (1 + k / (ε / 2)) ^ D ≤ 2 ^ D * (1 + k / ε) ^ D := by
    rw [← Real.mul_rpow zero_le_two (by positivity)]
    refine Real.rpow_le_rpow (by positivity) ?_ hD
    have : (k : ℝ) / (ε / 2) = 2 * (k / ε) := by field_simp
    rw [this]
    linarith
  calc CH * max 1 (RS * Lα) ^ D * (1 + k / (ε / 2)) ^ D
      ≤ CH * max 1 (RS * Lα) ^ D * (2 ^ D * (1 + k / ε) ^ D) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 2 ^ D * (CH * max 1 (RS * Lα) ^ D) * (1 + k / ε) ^ D := by ring

@[blueprint "lem:p2-constant-one-le"
  (statement := /-- $C_0 = 2^D C_H \max(1, R_S L_\alpha)^D \ge 1$. -/)]
theorem one_le_p2_constant {D CH : ℝ} (hD : 0 ≤ D) (hCH : 1 ≤ CH) (RS Lα : ℝ≥0) :
    1 ≤ 2 ^ D * (CH * max 1 (RS * Lα) ^ D) :=
  one_le_mul_of_one_le_of_one_le (Real.one_le_rpow one_le_two hD)
    (one_le_mul_of_one_le_of_one_le hCH (Real.one_le_rpow (le_max_left _ _) hD))

@[blueprint "cor:profile-p2-compact"
  (statement := /-- \textbf{(P2 on a bounded state space; table row ``P2, compact
    $\mathcal X$''.)} Under the hypotheses of `cond:p2-nilp`, if moreover
    $d(x,y) \le D_{\mathcal X}$ for all $x, y$ ($D_{\mathcal X} > 0$), then
    $D_k(S) \le D_{\mathcal X}$ and for every $k \ge 1$
    $$\mathsf V_k(S) \le D_{\mathcal X}\sqrt D\Bigl(\sqrt{\log(1 + k/D_{\mathcal X})}
    + \tfrac{\sqrt\pi}{2}\Bigr) + D_{\mathcal X}\sqrt{\log C_0} = O\bigl(\sqrt{D\log k}\bigr),$$
    with $C_0 = 2^D C_H\max(1, R_SL_\alpha)^D$: profile (ii),
    $\mathrm{var}(k,n) = O(\sqrt{D\log k/n})$. -/)]
theorem profile_p2_bounded (α : Γ →* Function.End X)
    (hsub : ∀ g h : Γ, edist 1 (g * h) ≤ edist 1 g + edist 1 h)
    {D : ℝ} (hD : 0 ≤ D) {CH : ℝ} (hCH : 1 ≤ CH)
    (hball : ∀ R δ : ℝ≥0, 0 < δ →
      (externalCoveringNumber δ (closedEBall (1 : Γ) R) : ℝ≥0∞) ≤
        ENNReal.ofReal (CH * (1 + R / δ) ^ D))
    {Sg : Set Γ} {RS : ℝ≥0} (hS : ∀ s ∈ Sg, edist 1 s ≤ RS) (hF : F ⊆ orbitMap α '' Sg)
    {Lα : ℝ≥0} (hLα : 0 < Lα) (hα : LipschitzWith Lα (fun g => toUnifMaps (orbitMap α g)))
    {Dx : ℝ} (hDx : 0 < Dx) (hX : ∀ x y : X, dist x y ≤ Dx) {k : ℕ} (hk : 1 ≤ k) :
    entropyIntegral (Y := EmpSpace S) (empDiam S (wordBall F k)) (wordBall F k) ≤
      Dx * √D * (√(Real.log (1 + k / Dx)) + √π / 2) +
        Dx * √(Real.log (2 ^ D * (CH * max 1 (RS * Lα) ^ D))) :=
  /- `prop:profiles-ii` with `lem:p2-empSpace-covering` and `lem:empDiam-le-of-bounded`. -/
  profile_poly_bounded (Y := EmpSpace S) (A := fun k => wordBall F k)
    (D := fun k => empDiam S (wordBall F k)) (fun k => empDiam_nonneg S (wordBall F k))
    (fun k => empDiam_le_of_bounded S hDx.le hX (wordBall F k)) hDx
    (one_le_p2_constant hD hCH RS Lα) hD
    (fun k _ ε hε =>
      toReal_coveringNumber_empSpace_wordBall_le_of_p2 S α hsub hD hCH hball hS hF hLα hα k
        (ε := ε) hε)
    hk

@[blueprint "cor:profile-p2-noncompact"
  (statement := /-- \textbf{(P2 on a general state space; table row ``P2, non-compact
    $\mathcal X$''.)} Under the hypotheses of `cond:p2-nilp` with $R_S > 0$,
    $D_k(S) \le 2L_\alpha R_S k$ and for every $k \ge 1$
    $$\mathsf V_k(S) \le 2L_\alpha R_S k\Bigl(\sqrt D\bigl(\sqrt{\log(1 + 1/(2L_\alpha R_S))}
    + \tfrac{\sqrt\pi}{2}\bigr) + \sqrt{\log C_0}\Bigr) = O(k\sqrt D),$$
    with $C_0 = 2^D C_H\max(1, R_SL_\alpha)^D$: profile (iv),
    $\mathrm{var}(k,n) = O(k\sqrt{D/n})$. -/)]
theorem profile_p2_linear (α : Γ →* Function.End X)
    (hsub : ∀ g h : Γ, edist 1 (g * h) ≤ edist 1 g + edist 1 h)
    {D : ℝ} (hD : 0 ≤ D) {CH : ℝ} (hCH : 1 ≤ CH)
    (hball : ∀ R δ : ℝ≥0, 0 < δ →
      (externalCoveringNumber δ (closedEBall (1 : Γ) R) : ℝ≥0∞) ≤
        ENNReal.ofReal (CH * (1 + R / δ) ^ D))
    {Sg : Set Γ} {RS : ℝ≥0} (hRS : 0 < RS) (hS : ∀ s ∈ Sg, edist 1 s ≤ RS)
    (hF : F ⊆ orbitMap α '' Sg)
    {Lα : ℝ≥0} (hLα : 0 < Lα) (hα : LipschitzWith Lα (fun g => toUnifMaps (orbitMap α g)))
    {k : ℕ} (hk : 1 ≤ k) :
    entropyIntegral (Y := EmpSpace S) (empDiam S (wordBall F k)) (wordBall F k) ≤
      2 * Lα * RS * k * (√D * (√(Real.log (1 + 1 / (2 * Lα * RS))) + √π / 2) +
        √(Real.log (2 ^ D * (CH * max 1 (RS * Lα) ^ D)))) :=
  /- `prop:profiles-iv` with `lem:p2-empSpace-covering` and `lem:empDiam-wordBall-le-of-p2`. -/
  profile_poly_linear (Y := EmpSpace S) (A := fun k => wordBall F k)
    (D := fun k => empDiam S (wordBall F k)) (fun k => empDiam_nonneg S (wordBall F k))
    (fun k => empDiam_wordBall_le_of_p2 S α hsub hS hF hα k) (by positivity)
    (one_le_p2_constant hD hCH RS Lα) hD
    (fun k _ ε hε =>
      toReal_coveringNumber_empSpace_wordBall_le_of_p2 S α hsub hD hCH hball hS hF hLα hα k
        (ε := ε) hε)
    hk

end P2

/-! ### Table of profiles: finite generator sets -/

section Finite

variable {F : Set (X → X)}

@[blueprint "cor:profile-finite"
  (statement := /-- \textbf{(Finite hidden-layer classes; table row ``E1', E2 with
    $|F| = r$''.)} If $F$ is finite with $|F| = r \ge 2$ and the state metric is bounded,
    $d(x,y) \le D_{\mathcal X}$ ($D_{\mathcal X} \ge 0$), then $|B(k,F)| \le r^{k+1}$, hence
    $N(B(k,F), d_S, \varepsilon) \le r^{k+1}$ for every $\varepsilon > 0$, and
    $$\mathsf V_k(S) \le D_{\mathcal X}\sqrt{(k+1)\log r} = O\bigl(\sqrt{k\log r}\bigr)$$
    for every $k$: profile (iii), $\mathrm{var}(k,n) = O(\sqrt{k/n})$. -/)]
theorem profile_finite_wordBall {r : ℕ} (hF : F.Finite) (hr : F.ncard = r) (h2 : 2 ≤ r)
    {Dx : ℝ} (hDx : 0 ≤ Dx) (hX : ∀ x y : X, dist x y ≤ Dx) (k : ℕ) :
    entropyIntegral (Y := EmpSpace S) (empDiam S (wordBall F k)) (wordBall F k) ≤
      Dx * √((k + 1) * Real.log r) :=
  /- `prop:profiles-finite` with `lem:wordball-card` and `lem:empDiam-le-of-bounded`. -/
  profile_finite (Y := EmpSpace S) (A := fun k => wordBall F k)
    (D := fun k => empDiam S (wordBall F k)) (fun k => empDiam_nonneg S (wordBall F k))
    (fun k => empDiam_le_of_bounded S hDx hX (wordBall F k))
    (fun k => encard_wordBall_le_pow (k := k) hF hr h2) k

end Finite

/-! ### Integrability of the entropy integrand under each profile -/

section Integrability

variable {F : Set (X → X)}

@[blueprint "lem:sqrt-metric-entropy-integrable-of-le-of-le"
  (statement := /-- If $0 \le D \le \overline D$ and $\sqrt{\log N(A,\varepsilon)} \le
    g(\varepsilon)$ on $(0, \overline D]$ for an interval-integrable $g$ on $[0, \overline D]$,
    then $\varepsilon \mapsto \sqrt{\log N(A,\varepsilon)}$ is interval-integrable on
    $[0, D]$. -/)]
theorem intervalIntegrable_sqrt_metricEntropy_of_le_of_le {Y : Type*} [PseudoEMetricSpace Y]
    {A : Set Y} {D D' : ℝ} (hD : 0 ≤ D) (hDD' : D ≤ D') {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume 0 D')
    (hle : ∀ ε ∈ Ioc 0 D', √(metricEntropy ε.toNNReal A) ≤ g ε) :
    IntervalIntegrable (fun ε : ℝ => √(metricEntropy ε.toNNReal A)) volume 0 D :=
  /- `lem:sqrt-metric-entropy-integrable-of-le` on $[0, \overline D]$, restricted to
    $[0, D]$. -/
  (intervalIntegrable_sqrt_metricEntropy_of_le (hD.trans hDD') hg hle).mono_set
    (by rw [uIcc_of_le hD, uIcc_of_le (hD.trans hDD')]; exact Icc_subset_Icc le_rfl hDD')

@[blueprint "lem:p1-integrand-integrable"
  (statement := /-- \textbf{(Integrability under P1.)} Under the hypotheses of
    `cor:profile-p1-totallyBounded` (in particular the interval-integrability of the majorant
    $\sqrt{\log N_\infty}$ on $[0, D_{\mathcal X}]$), the entropy integrand
    $\varepsilon \mapsto \sqrt{\log N(B(k,F), d_S, \varepsilon)}$ is interval-integrable on
    $[0, D_k(S)]$ for every $k$: the hypothesis of `thm:hidden-decomp-depth` is automatic. -/)]
theorem intervalIntegrable_wordBall_of_p1
    (hF : TotallyBounded (α := UnifMaps X) (semigroupClosure F)) {Dx : ℝ} (hDx : 0 ≤ Dx)
    (hX : ∀ x y : X, dist x y ≤ Dx)
    (hint : IntervalIntegrable (fun ε : ℝ => √(Real.log (externalCoveringNumber (X := UnifMaps X)
      (ε.toNNReal / 2) (closure (X := UnifMaps X) (semigroupClosure F)) : ℝ≥0∞).toReal))
      volume 0 Dx) (k : ℕ) :
    IntervalIntegrable
      (fun ε : ℝ => √(metricEntropy (X := EmpSpace S) ε.toNNReal (wordBall F k)))
      volume 0 (empDiam S (wordBall F k)) := by
  /-- Domination by the majorant $N_\infty$, as in `cor:profile-p1-totallyBounded`. -/
  refine intervalIntegrable_sqrt_metricEntropy_of_le_of_le (empDiam_nonneg S _)
    (empDiam_le_of_bounded S hDx hX _) hint fun ε hε => ?_
  refine Real.sqrt_le_sqrt (log_toReal_toENNReal_mono
    (cond_p1_of_totallyBounded hF (ε.toNNReal / 2)
      (div_pos (Real.toNNReal_pos.2 hε.1) two_pos) 0).2 ?_)
  exact (coveringNumber_empSpace_le_externalCoveringNumber_unifMaps S _ _).trans
    (externalCoveringNumber_mono_set
      (subset_semigroupClosure.trans (subset_closure (X := UnifMaps X))))

@[blueprint "lem:p2-integrand-integrable"
  (statement := /-- \textbf{(Integrability under P2.)} Under the hypotheses of `cond:p2-nilp`,
    if $D_k(S) \le \overline D$ with $\overline D > 0$, then the entropy integrand of $B(k,F)$
    is interval-integrable on $[0, D_k(S)]$ (it is dominated by
    $\sqrt{\log C_0} + \sqrt D\sqrt{\log(1 + k/\overline D)}
    + \sqrt D\sqrt{\log(\overline D/\varepsilon)}$, `lem:sqrt-metric-entropy-le-of-poly`). -/)]
theorem intervalIntegrable_wordBall_of_p2 {Γ : Type*} [Group Γ] [PseudoEMetricSpace Γ]
    (α : Γ →* Function.End X)
    (hsub : ∀ g h : Γ, edist 1 (g * h) ≤ edist 1 g + edist 1 h)
    {D : ℝ} (hD : 0 ≤ D) {CH : ℝ} (hCH : 1 ≤ CH)
    (hball : ∀ R δ : ℝ≥0, 0 < δ →
      (externalCoveringNumber δ (closedEBall (1 : Γ) R) : ℝ≥0∞) ≤
        ENNReal.ofReal (CH * (1 + R / δ) ^ D))
    {Sg : Set Γ} {RS : ℝ≥0} (hS : ∀ s ∈ Sg, edist 1 s ≤ RS) (hF : F ⊆ orbitMap α '' Sg)
    {Lα : ℝ≥0} (hLα : 0 < Lα) (hα : LipschitzWith Lα (fun g => toUnifMaps (orbitMap α g)))
    {k : ℕ} {Dbar : ℝ} (hDbar : 0 < Dbar) (hDk : empDiam S (wordBall F k) ≤ Dbar) :
    IntervalIntegrable
      (fun ε : ℝ => √(metricEntropy (X := EmpSpace S) ε.toNNReal (wordBall F k)))
      volume 0 (empDiam S (wordBall F k)) := by
  /-- The polynomial majorant is interval-integrable on $[0, \overline D]$
    (`intervalIntegrable_sqrt_log_div`). -/
  have hgint : IntervalIntegrable
      (fun ε : ℝ => √(Real.log (2 ^ D * (CH * max 1 (RS * Lα) ^ D))) +
        √D * √(Real.log (1 + k / Dbar)) + √D * √(Real.log (Dbar / ε))) volume 0 Dbar :=
    (intervalIntegrable_const.add intervalIntegrable_const).add
      ((intervalIntegrable_sqrt_log_div hDbar).const_mul _)
  refine intervalIntegrable_sqrt_metricEntropy_of_le_of_le (empDiam_nonneg S _) hDk hgint
    fun ε hε => sqrt_metricEntropy_le_of_poly hDbar (one_le_p2_constant hD hCH RS Lα) hD
      (fun ε hε =>
        toReal_coveringNumber_empSpace_wordBall_le_of_p2 S α hsub hD hCH hball hS hF hLα hα k
          (ε := ε) hε) hε

@[blueprint "lem:finite-integrand-integrable"
  (statement := /-- \textbf{(Integrability for finite hidden-layer classes.)} If $F$ is finite
    with $|F| = r \ge 2$ and $d(x,y) \le D_{\mathcal X}$, then the entropy integrand of $B(k,F)$
    is bounded by the constant $\sqrt{(k+1)\log r}$, hence interval-integrable on
    $[0, D_k(S)]$. -/)]
theorem intervalIntegrable_wordBall_of_finite {r : ℕ} (hF : F.Finite) (hr : F.ncard = r)
    (h2 : 2 ≤ r) {Dx : ℝ} (hDx : 0 ≤ Dx) (hX : ∀ x y : X, dist x y ≤ Dx) (k : ℕ) :
    IntervalIntegrable
      (fun ε : ℝ => √(metricEntropy (X := EmpSpace S) ε.toNNReal (wordBall F k)))
      volume 0 (empDiam S (wordBall F k)) := by
  /-- $N(B(k,F), d_S, \varepsilon) \le |B(k,F)| \le r^{k+1}$ (`lem:wordball-card`). -/
  refine intervalIntegrable_sqrt_metricEntropy_of_le_of_le (empDiam_nonneg S _)
    (empDiam_le_of_bounded S hDx hX _)
    (intervalIntegrable_const (c := √((k + 1) * Real.log r))) fun ε _ => ?_
  refine Real.sqrt_le_sqrt ?_
  have h1 : coveringNumber (X := EmpSpace S) ε.toNNReal (wordBall F k) ≤
      ((r ^ (k + 1) : ℕ) : ℕ∞) := by
    rw [Nat.cast_pow]
    exact (coveringNumber_le_encard_self _).trans (encard_wordBall_le_pow hF hr h2)
  have h3 := log_toReal_toENNReal_mono (ENat.coe_ne_top _) h1
  rw [ENat.toENNReal_coe, ENNReal.toReal_natCast, Nat.cast_pow, Real.log_pow] at h3
  exact h3.trans (le_of_eq (by push_cast; ring))

end Integrability

/-! ### The estimation term under each profile -/

section VarProfiles

variable (H : Set (X → ℝ)) {F : Set (X → X)}

@[blueprint "cor:var-profiles-p1"
  (statement := /-- \textbf{(Estimation term under P1.)} Let $\mathcal X$ be compact, the
    semigroup $\langle F\rangle$ equicontinuous, and $\mathsf V_\infty$ as in `cor:profile-p1`.
    Under the hypotheses of `thm:hidden-decomp-depth`,
    $\hat{\mathfrak R}_S(\mathcal H_k) \le \hat{\mathfrak R}_S(H) + \frac{12A_HL}{\sqrt n}
    \mathsf V_\infty$ for every $k$: $\mathrm{var}(k,n) = O(n^{-1/2})$ uniformly in the
    depth. -/)]
theorem var_profile_p1 [CompactSpace X] (hn : 0 < n) (k : ℕ) {AH L : ℝ} (hAH : 0 < AH)
    (hL : 0 < L)
    (hbdd : ∀ f ∈ wordBall F k, ∀ σ : Signs n,
      BddAbove (Set.range fun h : H =>
        normalizedRademacherSum n (fun h : H => (h : X → ℝ)) (f ∘ S) σ h))
    (hFtb : TotallyBounded (α := EmpSpace S) (wordBall F k))
    (hsg : SubGaussianIncrements S H (semigroupClosure F) AH L)
    (hF : Equicontinuous (fun f : semigroupClosure F => (f : X → X)))
    (hint : IntervalIntegrable (fun ε : ℝ => √(Real.log (externalCoveringNumber (X := UnifMaps X)
      (ε.toNNReal / 2) (closure (X := UnifMaps X) (semigroupClosure F)) : ℝ≥0∞).toReal))
      volume 0 (Metric.diam (Set.univ : Set X))) :
    empRademacher S (hypothesisClass H F k) ≤
      empRademacher S H + 12 * AH * L / Real.sqrt n *
        ∫ ε in (0 : ℝ)..Metric.diam (Set.univ : Set X),
          √(Real.log (externalCoveringNumber (X := UnifMaps X) (ε.toNNReal / 2)
            (closure (X := UnifMaps X) (semigroupClosure F)) : ℝ≥0∞).toReal) :=
  /- The integrability of the entropy integrand follows from `lem:p1-integrand-integrable`
    (Arzelà–Ascoli gives total boundedness of the semigroup in $d_\infty$). -/
  empRademacher_le_of_entropyIntegral_le S H hn F k hAH hL hbdd hFtb hsg
    (intervalIntegrable_wordBall_of_p1 S (totallyBounded_unifMaps_of_equicontinuous hF)
      Metric.diam_nonneg
      (fun x y => Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ y))
      hint k)
    (profile_p1_of_equicontinuous S hF hint k)

@[blueprint "cor:var-profiles-p2-compact"
  (statement := /-- \textbf{(Estimation term under P2, bounded state space.)} Under the
    hypotheses of `cor:profile-p2-compact` and `thm:hidden-decomp-depth`, for $k \ge 1$,
    $\hat{\mathfrak R}_S(\mathcal H_k) \le \hat{\mathfrak R}_S(H) + \frac{12A_HL}{\sqrt n}\Bigl(
    D_{\mathcal X}\sqrt D\bigl(\sqrt{\log(1 + k/D_{\mathcal X})} + \tfrac{\sqrt\pi}{2}\bigr)
    + D_{\mathcal X}\sqrt{\log C_0}\Bigr)$: $\mathrm{var}(k,n) = O(\sqrt{D\log k/n})$. -/)]
theorem var_profile_p2_bounded {Γ : Type*} [Group Γ] [PseudoEMetricSpace Γ] (hn : 0 < n)
    (k : ℕ) {AH L : ℝ} (hAH : 0 < AH) (hL : 0 < L)
    (hbdd : ∀ f ∈ wordBall F k, ∀ σ : Signs n,
      BddAbove (Set.range fun h : H =>
        normalizedRademacherSum n (fun h : H => (h : X → ℝ)) (f ∘ S) σ h))
    (hFtb : TotallyBounded (α := EmpSpace S) (wordBall F k))
    (hsg : SubGaussianIncrements S H (semigroupClosure F) AH L)
    (α : Γ →* Function.End X)
    (hsub : ∀ g h : Γ, edist 1 (g * h) ≤ edist 1 g + edist 1 h)
    {D : ℝ} (hD : 0 ≤ D) {CH : ℝ} (hCH : 1 ≤ CH)
    (hball : ∀ R δ : ℝ≥0, 0 < δ →
      (externalCoveringNumber δ (closedEBall (1 : Γ) R) : ℝ≥0∞) ≤
        ENNReal.ofReal (CH * (1 + R / δ) ^ D))
    {Sg : Set Γ} {RS : ℝ≥0} (hS : ∀ s ∈ Sg, edist 1 s ≤ RS) (hF : F ⊆ orbitMap α '' Sg)
    {Lα : ℝ≥0} (hLα : 0 < Lα) (hα : LipschitzWith Lα (fun g => toUnifMaps (orbitMap α g)))
    {Dx : ℝ} (hDx : 0 < Dx) (hX : ∀ x y : X, dist x y ≤ Dx) (hk : 1 ≤ k) :
    empRademacher S (hypothesisClass H F k) ≤
      empRademacher S H + 12 * AH * L / Real.sqrt n *
        (Dx * √D * (√(Real.log (1 + k / Dx)) + √π / 2) +
          Dx * √(Real.log (2 ^ D * (CH * max 1 (RS * Lα) ^ D)))) :=
  /- Integrability from `lem:p2-integrand-integrable` with $\overline D = D_{\mathcal X}$. -/
  empRademacher_le_of_entropyIntegral_le S H hn F k hAH hL hbdd hFtb hsg
    (intervalIntegrable_wordBall_of_p2 S α hsub hD hCH hball hS hF hLα hα hDx
      (empDiam_le_of_bounded S hDx.le hX _))
    (profile_p2_bounded S α hsub hD hCH hball hS hF hLα hα hDx hX hk)

@[blueprint "cor:var-profiles-p2-noncompact"
  (statement := /-- \textbf{(Estimation term under P2, general state space.)} Under the
    hypotheses of `cor:profile-p2-noncompact` and `thm:hidden-decomp-depth`, for $k \ge 1$,
    $\hat{\mathfrak R}_S(\mathcal H_k) \le \hat{\mathfrak R}_S(H) + \frac{12A_HL}{\sqrt n}\,
    2L_\alpha R_Sk\Bigl(\sqrt D\bigl(\sqrt{\log(1 + 1/(2L_\alpha R_S))} + \tfrac{\sqrt\pi}{2}\bigr)
    + \sqrt{\log C_0}\Bigr)$: $\mathrm{var}(k,n) = O(k\sqrt{D/n})$. -/)]
theorem var_profile_p2_linear {Γ : Type*} [Group Γ] [PseudoEMetricSpace Γ] (hn : 0 < n)
    (k : ℕ) {AH L : ℝ} (hAH : 0 < AH) (hL : 0 < L)
    (hbdd : ∀ f ∈ wordBall F k, ∀ σ : Signs n,
      BddAbove (Set.range fun h : H =>
        normalizedRademacherSum n (fun h : H => (h : X → ℝ)) (f ∘ S) σ h))
    (hFtb : TotallyBounded (α := EmpSpace S) (wordBall F k))
    (hsg : SubGaussianIncrements S H (semigroupClosure F) AH L)
    (α : Γ →* Function.End X)
    (hsub : ∀ g h : Γ, edist 1 (g * h) ≤ edist 1 g + edist 1 h)
    {D : ℝ} (hD : 0 ≤ D) {CH : ℝ} (hCH : 1 ≤ CH)
    (hball : ∀ R δ : ℝ≥0, 0 < δ →
      (externalCoveringNumber δ (closedEBall (1 : Γ) R) : ℝ≥0∞) ≤
        ENNReal.ofReal (CH * (1 + R / δ) ^ D))
    {Sg : Set Γ} {RS : ℝ≥0} (hRS : 0 < RS) (hS : ∀ s ∈ Sg, edist 1 s ≤ RS)
    (hF : F ⊆ orbitMap α '' Sg)
    {Lα : ℝ≥0} (hLα : 0 < Lα) (hα : LipschitzWith Lα (fun g => toUnifMaps (orbitMap α g)))
    (hk : 1 ≤ k) :
    empRademacher S (hypothesisClass H F k) ≤
      empRademacher S H + 12 * AH * L / Real.sqrt n *
        (2 * Lα * RS * k * (√D * (√(Real.log (1 + 1 / (2 * Lα * RS))) + √π / 2) +
          √(Real.log (2 ^ D * (CH * max 1 (RS * Lα) ^ D))))) :=
  /- Integrability from `lem:p2-integrand-integrable` with $\overline D = 2L_\alpha R_S k$. -/
  empRademacher_le_of_entropyIntegral_le S H hn F k hAH hL hbdd hFtb hsg
    (intervalIntegrable_wordBall_of_p2 S α hsub hD hCH hball hS hF hLα hα
      (by have : (0 : ℝ) < k := by exact_mod_cast hk
          positivity)
      (empDiam_wordBall_le_of_p2 S α hsub hS hF hα k))
    (profile_p2_linear S α hsub hD hCH hball hRS hS hF hLα hα hk)

@[blueprint "cor:var-profiles-finite"
  (statement := /-- \textbf{(Estimation term for finite hidden-layer classes.)} Under the
    hypotheses of `cor:profile-finite` and `thm:hidden-decomp-depth`,
    $\hat{\mathfrak R}_S(\mathcal H_k) \le \hat{\mathfrak R}_S(H) + \frac{12A_HL}{\sqrt n}\,
    D_{\mathcal X}\sqrt{(k+1)\log r}$ for every $k$: $\mathrm{var}(k,n) = O(\sqrt{k/n})$. -/)]
theorem var_profile_finite (hn : 0 < n) (k : ℕ) {AH L : ℝ} (hAH : 0 < AH) (hL : 0 < L)
    (hbdd : ∀ f ∈ wordBall F k, ∀ σ : Signs n,
      BddAbove (Set.range fun h : H =>
        normalizedRademacherSum n (fun h : H => (h : X → ℝ)) (f ∘ S) σ h))
    (hFtb : TotallyBounded (α := EmpSpace S) (wordBall F k))
    (hsg : SubGaussianIncrements S H (semigroupClosure F) AH L)
    {r : ℕ} (hF : F.Finite) (hr : F.ncard = r) (h2 : 2 ≤ r)
    {Dx : ℝ} (hDx : 0 ≤ Dx) (hX : ∀ x y : X, dist x y ≤ Dx) :
    empRademacher S (hypothesisClass H F k) ≤
      empRademacher S H + 12 * AH * L / Real.sqrt n * (Dx * √((k + 1) * Real.log r)) :=
  /- Integrability from `lem:finite-integrand-integrable`. -/
  empRademacher_le_of_entropyIntegral_le S H hn F k hAH hL hbdd hFtb hsg
    (intervalIntegrable_wordBall_of_finite S hF hr h2 hDx hX k)
    (profile_finite_wordBall S hF hr h2 hDx hX k)

end VarProfiles

end LeanDeepgen
