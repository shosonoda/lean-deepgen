/-
Comparator solution: the statements of `comparator/Challenge.lean`, verbatim, each proved by the
corresponding theorem of the library `LeanDeepgen` (see `comparator/README.md` for the mapping).
-/
import LeanDeepgen

universe u

namespace LeanDeepgen.Challenge

/-! ## Sec. 3 / App. B: bias–variance decomposition (`Bounds/BiasVariance`) -/

section BiasVariance

open MeasureTheory
open scoped ENNReal UniformConvergence

/-- **thm:bv-general** (App. B). General bias–variance decomposition of the excess risk
with an abstract implementation pseudo-metric `dT`; explicit deviation constant
`6 b √(2 log(4/δ)/n)` (D1, D3). -/
theorem thm_bv_general {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}
    (P : Measure (X × Y)) [IsProbabilityMeasure P] (L : BoundedLipschitzLoss Y)
    {𝓗 𝒞 : Set (X → ℝ)} (ι : (X → ℝ) → (X → ℝ)) (dT : (X → ℝ) → (X → ℝ) → ℝ)
    {βL βLhat εimp η δ : ℝ}
    (hn : 0 < n) (hℓ : Measurable (Function.uncurry L.ℓ)) (hb : 0 < L.b)
    (hβ : 0 ≤ L.β) (h𝓗 : ∀ f ∈ 𝓗, Measurable f) (hsep : IsSupSeparable 𝓗)
    (h𝓗b : ∀ x, ∃ M : ℝ, ∀ f ∈ 𝓗, |f x| ≤ M)
    (h𝒞 : 𝒞.Nonempty) (h𝒞m : ∀ c ∈ 𝒞, Measurable c)
    (hdT : ∀ f g, 0 ≤ dT f g) (hβL : 0 ≤ βL) (hβLhat : 0 ≤ βLhat) (hεimp : 0 ≤ εimp)
    (himp : ∀ f ∈ 𝓗, dT (ι f) f ≤ εimp)
    (hL : ∀ f ∈ 𝓗, |risk L P (ι f) - risk L P f| ≤ βL * dT (ι f) f)
    (hLhat : ∀ f ∈ 𝓗, ∀ D : Fin n → X × Y,
      |empRisk L D (ι f) - empRisk L D f| ≤ βLhat * dT (ι f) f)
    (hη : 0 ≤ η) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ((Measure.pi fun _ : Fin n => P) {D | ¬ ∀ fhat, IsEmpMinimizer L D 𝓗 η fhat →
        risk L P (ι fhat) - sInf (risk L P '' 𝒞) ≤
          βL * εimp + modelError L P 𝓗 𝒞 + η
            + 4 * L.β * empRademacher (fun i => (D i).1) 𝓗
            + 6 * L.b * Real.sqrt (2 * Real.log (4 / δ) / n)}).toReal ≤ δ :=
  LeanDeepgen.bv_general P L ι dT hn hℓ hb hβ h𝓗 hsep h𝓗b h𝒞 h𝒞m hdT hβL hβLhat hεimp himp hL
    hLhat hη hδ hδ1

/-- **thm:bv-general** (gap form, App. B). Generalization gap `L[ιf] − L̂[ιf]` for *every*
`f ∈ 𝓗` (D2), with constants `2β_ℓ` and `3b√(2 log(4/δ)/n)`. -/
theorem thm_bv_general_gap {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}
    (P : Measure (X × Y)) [IsProbabilityMeasure P] (L : BoundedLipschitzLoss Y)
    {𝓗 : Set (X → ℝ)} (ι : (X → ℝ) → (X → ℝ)) (dT : (X → ℝ) → (X → ℝ) → ℝ)
    {βL βLhat εimp δ : ℝ}
    (hn : 0 < n) (hℓ : Measurable (Function.uncurry L.ℓ)) (hb : 0 < L.b)
    (hβ : 0 ≤ L.β) (h𝓗 : ∀ f ∈ 𝓗, Measurable f) (hsep : IsSupSeparable 𝓗)
    (h𝓗b : ∀ x, ∃ M : ℝ, ∀ f ∈ 𝓗, |f x| ≤ M)
    (hdT : ∀ f g, 0 ≤ dT f g) (hβL : 0 ≤ βL) (hβLhat : 0 ≤ βLhat) (hεimp : 0 ≤ εimp)
    (himp : ∀ f ∈ 𝓗, dT (ι f) f ≤ εimp)
    (hL : ∀ f ∈ 𝓗, |risk L P (ι f) - risk L P f| ≤ βL * dT (ι f) f)
    (hLhat : ∀ f ∈ 𝓗, ∀ D : Fin n → X × Y,
      |empRisk L D (ι f) - empRisk L D f| ≤ βLhat * dT (ι f) f)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ((Measure.pi fun _ : Fin n => P) {D | ¬ ∀ f ∈ 𝓗,
        risk L P (ι f) - empRisk L D (ι f) ≤
          (βL + βLhat) * εimp + 2 * L.β * empRademacher (fun i => (D i).1) 𝓗
            + 3 * L.b * Real.sqrt (2 * Real.log (4 / δ) / n)}).toReal ≤ δ :=
  LeanDeepgen.bv_general_gap P L ι dT hn hℓ hb hβ h𝓗 hsep h𝓗b hdT hβL hβLhat hεimp himp hL hLhat
    hδ hδ1

/-- **thm:bv** (Sec. 3). Implementation-independent bias–variance decomposition for the depth-`k`
hypothesis class `ℋ_k = H ∘ B(k,F)` with `d_T = ‖·‖_∞` and `β_L = β_L̂ = β_ℓ`. -/
theorem thm_bv {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}
    (P : Measure (X × Y)) [IsProbabilityMeasure P] (L : BoundedLipschitzLoss Y)
    {H : Set (X → ℝ)} {F : Set (X → X)} {k : ℕ} {𝒞 : Set (X → ℝ)} (ι : (X → ℝ) → (X → ℝ))
    {εimp η δ : ℝ}
    (hn : 0 < n) (hℓ : Measurable (Function.uncurry L.ℓ)) (hb : 0 < L.b) (hβ : 0 ≤ L.β)
    (h𝓗 : ∀ f ∈ hypothesisClass H F k, Measurable f)
    (hsep : IsSupSeparable (hypothesisClass H F k))
    (h𝓗b : ∀ x, ∃ M : ℝ, ∀ f ∈ hypothesisClass H F k, |f x| ≤ M)
    (h𝒞 : 𝒞.Nonempty) (h𝒞m : ∀ c ∈ 𝒞, Measurable c)
    (hι : ∀ f ∈ hypothesisClass H F k, Measurable (ι f))
    (hεimp : 0 ≤ εimp) (himp : implError ι (hypothesisClass H F k) ≤ ENNReal.ofReal εimp)
    (hη : 0 ≤ η) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ((Measure.pi fun _ : Fin n => P) {D | ¬ ∀ fhat,
        IsEmpMinimizer L D (hypothesisClass H F k) η fhat →
        risk L P (ι fhat) - sInf (risk L P '' 𝒞) ≤
          L.β * εimp + modelError L P (hypothesisClass H F k) 𝒞 + η
            + 4 * L.β * empRademacher (fun i => (D i).1) (hypothesisClass H F k)
            + 6 * L.b * Real.sqrt (2 * Real.log (4 / δ) / n)}).toReal ≤ δ :=
  LeanDeepgen.bv P L ι hn hℓ hb hβ h𝓗 hsep h𝓗b h𝒞 h𝒞m hι hεimp himp hη hδ hδ1

/-- **thm:bv** (gap form, Sec. 3). Generalization gap of every `ι f`, `f ∈ ℋ_k`. -/
theorem thm_bv_gap {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}
    (P : Measure (X × Y)) [IsProbabilityMeasure P] (L : BoundedLipschitzLoss Y)
    {H : Set (X → ℝ)} {F : Set (X → X)} {k : ℕ} (ι : (X → ℝ) → (X → ℝ))
    {εimp δ : ℝ}
    (hn : 0 < n) (hℓ : Measurable (Function.uncurry L.ℓ)) (hb : 0 < L.b)
    (hβ : 0 ≤ L.β) (h𝓗 : ∀ f ∈ hypothesisClass H F k, Measurable f)
    (hsep : IsSupSeparable (hypothesisClass H F k))
    (h𝓗b : ∀ x, ∃ M : ℝ, ∀ f ∈ hypothesisClass H F k, |f x| ≤ M)
    (hι : ∀ f ∈ hypothesisClass H F k, Measurable (ι f))
    (hεimp : 0 ≤ εimp) (himp : implError ι (hypothesisClass H F k) ≤ ENNReal.ofReal εimp)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ((Measure.pi fun _ : Fin n => P) {D | ¬ ∀ f ∈ hypothesisClass H F k,
        risk L P (ι f) - empRisk L D (ι f) ≤
          2 * L.β * εimp + 2 * L.β * empRademacher (fun i => (D i).1) (hypothesisClass H F k)
            + 3 * L.b * Real.sqrt (2 * Real.log (4 / δ) / n)}).toReal ≤ δ :=
  LeanDeepgen.bv_gap P L ι hn hℓ hb hβ h𝓗 hsep h𝓗b hι hεimp himp hδ hδ1

end BiasVariance

/-! ## Sec. 3: hidden/output decomposition and sub-Gaussian output layers
(`Bounds/HiddenOutput`) -/

section HiddenOutput

open scoped NNReal ENNReal

/-- **thm:hidden-decomp** (= thm:mixed-sg, Sec. 3). Dudley-type decomposition
`R̂_S(H∘F) ≤ R̂_S(H∘f₀) + (12 A_H L/√n) ∫₀^{diam_S F} √log N(F,d_S,ε) dε` for an arbitrary anchor
`f₀ ∈ F` (W5), assuming integrability of the entropy integrand (D5). -/
theorem thm_hidden_decomp {X : Type*} [PseudoMetricSpace X] {n : ℕ} (S : Fin n → X)
    (H : Set (X → ℝ))
    (hn : 0 < n) (F 𝔉 : Set (X → X)) {AH L : ℝ} (hAH : 0 < AH) (hL : 0 < L)
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
          Real.sqrt (metricEntropy (X := EmpSpace S) (Real.toNNReal ε) F) :=
  LeanDeepgen.hidden_decomp S H hn F 𝔉 hAH hL hbdd f₀ hf₀ hF hF𝔉 hsg hint

/-- **thm:hidden-decomp** for the depth-`k` class (Sec. 3, eq. for `ℋ_k`): anchor `id ∈ B(k,F₀)`,
so the first term is `R̂_S(H)`. -/
theorem thm_hidden_decomp_depth {X : Type*} [PseudoMetricSpace X] {n : ℕ} (S : Fin n → X)
    (H : Set (X → ℝ))
    (hn : 0 < n) (F₀ : Set (X → X)) (k : ℕ) {AH L : ℝ} (hAH : 0 < AH)
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
          Real.sqrt (metricEntropy (X := EmpSpace S) (Real.toNNReal ε) (wordBall F₀ k)) :=
  LeanDeepgen.hidden_decomp_depth S H hn F₀ k hAH hL hbdd hF hsg hint

/-- **prop:hilbert-sg** (Sec. 3). Linear output layers over an `L`-Lipschitz feature map into a
real inner product space (completeness not needed, W6) satisfy the sub-Gaussian increment
assumption with `A_H = 1`. -/
theorem prop_hilbert_sg {X : Type*} [PseudoMetricSpace X] {n : ℕ} (S : Fin n → X)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (Φ : X → E)
    {L : ℝ≥0} (hΦ : LipschitzWith L Φ) (𝔉 : Set (X → X)) :
    SubGaussianIncrements S (hilbertReadoutClass Φ) 𝔉 1 L :=
  LeanDeepgen.hilbert_sg S Φ hΦ 𝔉

/-- **prop:finite-lipschitz-sg** (Sec. 3). A finite class of `m` `L`-Lipschitz output maps
satisfies the sub-Gaussian increment assumption with `A_H = (1 + log m / log 2)^{1/2}`. -/
theorem prop_finite_lipschitz_sg {X : Type*} [PseudoMetricSpace X] {n : ℕ} (S : Fin n → X)
    (H : Set (X → ℝ))
    (hH : H.Finite) {m : ℕ} (hm : H.ncard = m) {L : ℝ≥0}
    (hlip : ∀ h ∈ H, LipschitzWith L h) (𝔉 : Set (X → X)) :
    SubGaussianIncrements S H 𝔉 (Real.sqrt (1 + Real.log m / Real.log 2)) L :=
  LeanDeepgen.finite_lipschitz_sg S H hH hm hlip 𝔉

end HiddenOutput

/-! ## Sec. 3: Sudakov-type lower bounds (`Bounds/Sudakov`) -/

section Sudakov

open scoped NNReal ENNReal

/-- **thm:sudakov-type** (= thm:sudakov, Sec. 3). Conditional Sudakov-type lower bound
`R̂_S(H∘B) ≥ c sup_ε min{κ ε √(log M(B,d_S,2ε)/n), κ²ε²/R_out}` for an arbitrary hidden class
`B` (W7), assuming the Rademacher suprema are finite (D7). -/
theorem thm_sudakov_type :
    ∃ c : ℝ, 0 < c ∧ ∀ (𝒳 : Type u) [PseudoMetricSpace 𝒳] (n : ℕ) (S : Fin n → 𝒳)
      (H : Set (𝒳 → ℝ)) (B : Set (𝒳 → 𝒳)) (κ Rout : ℝ),
      0 < κ → 0 < Rout → 0 < n → ReadoutRealization S H B κ Rout →
      (∀ σ : Signs n, BddAbove (Set.range fun g : compClass H B =>
        normalizedRademacherSum n (fun g : compClass H B => (g : 𝒳 → ℝ)) S σ g)) →
      ∀ ε : ℝ≥0, 0 < ε →
        c * min (κ * ε * Real.sqrt (Real.log
              (Metric.packingNumber (X := EmpSpace S) (2 * ε) B : ℝ≥0∞).toReal / n))
            (κ ^ 2 * ε ^ 2 / Rout) ≤
          empRademacher S (compClass H B) :=
  LeanDeepgen.sudakov_type

/-- **cor:sudakov-rates** (i) (Sec. 3). Exponential packing growth `M(B_k, 2ε₀) ≥ e^{αk}` gives
the rate `min{κ ε₀ √(αk/n), κ²ε₀²/R_out}`. -/
theorem cor_sudakov_rates :
    ∃ c : ℝ, 0 < c ∧ ∀ (𝒳 : Type u) [PseudoMetricSpace 𝒳] (n : ℕ) (S : Fin n → 𝒳)
      (H : Set (𝒳 → ℝ)) (F : Set (𝒳 → 𝒳)) (k : ℕ) (κ Rout : ℝ),
      0 < κ → 0 < Rout → 0 < n → ReadoutRealization S H (wordBall F k) κ Rout →
      (∀ σ : Signs n, BddAbove (Set.range fun g : hypothesisClass H F k =>
        normalizedRademacherSum n (fun g : hypothesisClass H F k => (g : 𝒳 → ℝ)) S σ g)) →
      ∀ (ε₀ : ℝ≥0) (α : ℝ), 0 < ε₀ → 0 < α →
        Real.exp (α * k) ≤
          (Metric.packingNumber (X := EmpSpace S) (2 * ε₀) (wordBall F k) : ℝ≥0∞).toReal →
        c * min (κ * ε₀ * Real.sqrt (α * k / n)) (κ ^ 2 * ε₀ ^ 2 / Rout) ≤
          empRademacher S (hypothesisClass H F k) :=
  LeanDeepgen.sudakov_rates_exp

/-- **cor:sudakov-rates** (ii) (Sec. 3). Polynomial packing growth `M(B_k, 2ε₀) ≥ k^β`, `k ≥ 1`
(D32), gives the rate `min{κ ε₀ √(β log k/n), κ²ε₀²/R_out}`. -/
theorem cor_sudakov_rates_poly :
    ∃ c : ℝ, 0 < c ∧ ∀ (𝒳 : Type u) [PseudoMetricSpace 𝒳] (n : ℕ) (S : Fin n → 𝒳)
      (H : Set (𝒳 → ℝ)) (F : Set (𝒳 → 𝒳)) (k : ℕ) (κ Rout : ℝ),
      0 < κ → 0 < Rout → 0 < n → ReadoutRealization S H (wordBall F k) κ Rout →
      (∀ σ : Signs n, BddAbove (Set.range fun g : hypothesisClass H F k =>
        normalizedRademacherSum n (fun g : hypothesisClass H F k => (g : 𝒳 → ℝ)) S σ g)) →
      ∀ (ε₀ : ℝ≥0) (β : ℝ), 0 < ε₀ → 0 < β → 1 ≤ k →
        (k : ℝ) ^ β ≤
          (Metric.packingNumber (X := EmpSpace S) (2 * ε₀) (wordBall F k) : ℝ≥0∞).toReal →
        c * min (κ * ε₀ * Real.sqrt (β * Real.log k / n)) (κ ^ 2 * ε₀ ^ 2 / Rout) ≤
          empRademacher S (hypothesisClass H F k) :=
  LeanDeepgen.sudakov_rates_poly

/-- **cor:matching** (i) (Sec. 3). In the exponential regime, once `n ≥ R_out² αk/(κ²ε₀²)` the
lower bound is `c κ ε₀ √(αk/n)`, matching the upper bound up to constants. -/
theorem cor_matching :
    ∃ c : ℝ, 0 < c ∧ ∀ (𝒳 : Type u) [PseudoMetricSpace 𝒳] (n : ℕ) (S : Fin n → 𝒳)
      (H : Set (𝒳 → ℝ)) (F : Set (𝒳 → 𝒳)) (k : ℕ) (κ Rout : ℝ),
      0 < κ → 0 < Rout → 0 < n → ReadoutRealization S H (wordBall F k) κ Rout →
      (∀ σ : Signs n, BddAbove (Set.range fun g : hypothesisClass H F k =>
        normalizedRademacherSum n (fun g : hypothesisClass H F k => (g : 𝒳 → ℝ)) S σ g)) →
      ∀ (ε₀ : ℝ≥0) (α : ℝ), 0 < ε₀ → 0 < α →
        Real.exp (α * k) ≤
          (Metric.packingNumber (X := EmpSpace S) (2 * ε₀) (wordBall F k) : ℝ≥0∞).toReal →
        Rout ^ 2 * (α * k) / (κ ^ 2 * ε₀ ^ 2) ≤ n →
        c * (κ * ε₀ * Real.sqrt (α * k / n)) ≤ empRademacher S (hypothesisClass H F k) :=
  LeanDeepgen.matching_exp

/-- **cor:matching** (ii) (Sec. 3). Polynomial regime: for `n ≥ R_out² β log k/(κ²ε₀²)` and
`k ≥ 1` (D32) the lower bound is `c κ ε₀ √(β log k/n)`. -/
theorem cor_matching_poly :
    ∃ c : ℝ, 0 < c ∧ ∀ (𝒳 : Type u) [PseudoMetricSpace 𝒳] (n : ℕ) (S : Fin n → 𝒳)
      (H : Set (𝒳 → ℝ)) (F : Set (𝒳 → 𝒳)) (k : ℕ) (κ Rout : ℝ),
      0 < κ → 0 < Rout → 0 < n → ReadoutRealization S H (wordBall F k) κ Rout →
      (∀ σ : Signs n, BddAbove (Set.range fun g : hypothesisClass H F k =>
        normalizedRademacherSum n (fun g : hypothesisClass H F k => (g : 𝒳 → ℝ)) S σ g)) →
      ∀ (ε₀ : ℝ≥0) (β : ℝ), 0 < ε₀ → 0 < β → 1 ≤ k →
        (k : ℝ) ^ β ≤
          (Metric.packingNumber (X := EmpSpace S) (2 * ε₀) (wordBall F k) : ℝ≥0∞).toReal →
        Rout ^ 2 * (β * Real.log k) / (κ ^ 2 * ε₀ ^ 2) ≤ n →
        c * (κ * ε₀ * Real.sqrt (β * Real.log k / n)) ≤
          empRademacher S (hypothesisClass H F k) :=
  LeanDeepgen.matching_poly

end Sudakov

/-! ## App. D: deterministic entropy decomposition (`Bounds/EntropyDecomp*`) -/

section EntropyDecomp

open scoped NNReal ENNReal UniformConvergence
open FoML.ToMathlib

/-- **thm:rad.decomp.ent.ent** (App. D), sup-norm form. Under `ass:ent-readout` /
`ass:ent-transition`, `R̂_S(H∘F) ≤ (12/√n) ∫₀^{B_H/2} (𝓔_H(x/4) + 𝓔_F(x/(4L_H))) dx`, with the
covering-number convention fixed (D6, D34) and integrability assumed (D5). -/
theorem thm_rad_decomp_ent_ent {X : Type*} [PseudoMetricSpace X] {n : ℕ}
    (hn : 0 < n) (S : Fin n → X) (H : Set (X → ℝ))
    (F : Set (X → X)) {BH : ℝ} {LH : ℝ≥0} (hLH : 0 < LH) (hH : EntReadout H BH LH)
    (hF : EntTransition F) (hBH : 0 < BH)
    (hint : IntervalIntegrable (fun x => entH H (x / 4) + entF F (x / (4 * LH)))
      MeasureTheory.volume 0 (BH / 2)) :
    empRademacher S (compClass H F) ≤
      12 / Real.sqrt n *
        ∫ x in (0 : ℝ)..(BH / 2), (entH H (x / 4) + entF F (x / (4 * LH))) :=
  LeanDeepgen.rad_decomp_ent_ent hn S H F hLH hH hF hBH hint

end EntropyDecomp

section EntropyDecompSample

open scoped NNReal ENNReal
open Metric
open FoML.ToMathlib

/-- **thm:rad.decomp.ent.ent** (sample form, App. D; W8). Readout class bounded/Lipschitz only on
the reached sample points, covering numbers in the empirical norms:
`R̂_S(H∘F) ≤ (12/√n) ∫₀^{B_H/2} (𝓔_{H,S}(x/4) + 𝓔_{F,S}(x/(8L_H))) dx`. -/
theorem thm_rad_decomp_ent_ent_sample {X : Type*} [PseudoMetricSpace X] {n : ℕ}
    (hn : 0 < n) (S : Fin n → X) (H : Set (X → ℝ))
    (F : Set (X → X)) {BH : ℝ} {LH : ℝ≥0} (hLH : 0 < LH) (hH : EntReadoutSample S F H BH LH)
    (hF : EntTransitionSample S F) (hBH : 0 < BH)
    (hint : IntervalIntegrable (fun x => entHS S F H (x / 4) + entFS S F (x / (8 * LH)))
      MeasureTheory.volume 0 (BH / 2)) :
    empRademacher S (compClass H F) ≤
      12 / Real.sqrt n *
        ∫ x in (0 : ℝ)..(BH / 2), (entHS S F H (x / 4) + entFS S F (x / (8 * LH))) :=
  LeanDeepgen.rad_decomp_ent_ent_sample hn S H F hLH hH hF hBH hint

end EntropyDecompSample

/-! ## App. F: growth conditions (`Growth/*`) -/

section ArzelaAscoli

open scoped NNReal ENNReal UniformConvergence Topology
open Metric Filter
open FoML.ToMathlib

/-- **thm:caa** (App. F, self-map Arzelà–Ascoli). On a compact metric space, a class of
continuous self-maps is `d_∞`-totally bounded iff it is equicontinuous (W9). -/
theorem thm_caa {X : Type*} [PseudoMetricSpace X] [CompactSpace X] {Hs : Set (X → X)}
    (hcont : ∀ f ∈ Hs, Continuous f) :
    TotallyBounded (α := UnifMaps X) Hs ↔ Equicontinuous (fun f : Hs => (f : X → X)) :=
  LeanDeepgen.totallyBounded_unifMaps_iff_equicontinuous hcont

end ArzelaAscoli

section Saturation

open scoped NNReal ENNReal UniformConvergence
open Metric
open FoML.ToMathlib

/-- **cond:p1** (1) (Sec. 4 / App. F). If the semigroup `⟨F⟩` is `d_∞`-precompact then
`N(B(k,F), ε) ≤ N(cl ⟨F⟩, ε) < ∞` for every `k`; no compactness of `X` needed (W10, D11). -/
theorem cond_p1 {X : Type*} [PseudoMetricSpace X] {F : Set (X → X)}
    (h : TotallyBounded (α := UnifMaps X) (semigroupClosure F))
    (ε : ℝ≥0) (hε : 0 < ε) (k : ℕ) :
    externalCoveringNumber (X := UnifMaps X) ε (wordBall F k) ≤
        externalCoveringNumber (X := UnifMaps X) ε
          (closure (X := UnifMaps X) (semigroupClosure F)) ∧
      externalCoveringNumber (X := UnifMaps X) ε
        (closure (X := UnifMaps X) (semigroupClosure F)) ≠ ⊤ :=
  LeanDeepgen.cond_p1_of_totallyBounded h ε hε k

/-- **cond:p1** (2a). `X` compact and `⟨F⟩` equicontinuous ⇒ saturation. -/
theorem cond_p1_2a {X : Type*} [PseudoMetricSpace X] {F : Set (X → X)} [CompactSpace X]
    (h : Equicontinuous (fun f : semigroupClosure F => (f : X → X)))
    (ε : ℝ≥0) (hε : 0 < ε) (k : ℕ) :
    externalCoveringNumber (X := UnifMaps X) ε (wordBall F k) ≤
        externalCoveringNumber (X := UnifMaps X) ε
          (closure (X := UnifMaps X) (semigroupClosure F)) ∧
      externalCoveringNumber (X := UnifMaps X) ε
        (closure (X := UnifMaps X) (semigroupClosure F)) ≠ ⊤ :=
  LeanDeepgen.cond_p1_of_equicontinuous h ε hε k

/-- **cond:p1** (2b). `X` compact and `⟨F⟩` uniformly `K`-Lipschitz ⇒ saturation. -/
theorem cond_p1_2b {X : Type*} [PseudoMetricSpace X] {F : Set (X → X)} [CompactSpace X]
    (K : ℝ≥0)
    (h : ∀ g ∈ semigroupClosure F, LipschitzWith K g) (ε : ℝ≥0) (hε : 0 < ε) (k : ℕ) :
    externalCoveringNumber (X := UnifMaps X) ε (wordBall F k) ≤
        externalCoveringNumber (X := UnifMaps X) ε
          (closure (X := UnifMaps X) (semigroupClosure F)) ∧
      externalCoveringNumber (X := UnifMaps X) ε
        (closure (X := UnifMaps X) (semigroupClosure F)) ≠ ⊤ :=
  LeanDeepgen.cond_p1_of_uniformLipschitz K h ε hε k

/-- **cond:p1** (2c). `X` compact and `F` non-expanding ⇒ saturation. -/
theorem cond_p1_2c {X : Type*} [PseudoMetricSpace X] {F : Set (X → X)} [CompactSpace X]
    (h : ∀ f ∈ F, LipschitzWith 1 f)
    (ε : ℝ≥0) (hε : 0 < ε) (k : ℕ) :
    externalCoveringNumber (X := UnifMaps X) ε (wordBall F k) ≤
        externalCoveringNumber (X := UnifMaps X) ε
          (closure (X := UnifMaps X) (semigroupClosure F)) ∧
      externalCoveringNumber (X := UnifMaps X) ε
        (closure (X := UnifMaps X) (semigroupClosure F)) ≠ ⊤ :=
  LeanDeepgen.cond_p1_of_nonexpanding h ε hε k

/-- **cond:p1-ucont** (P1', App. F). Uniform `c`-contractions (`0 < c < 1`) with a nonempty
invariant set `A` and a bounded absorbing set `K` for words of length `L`:
`N(B(k,F), ε) ≤ N(A, ε/2) + Σ_{l < m(ε)} N(F^l, ε)` for *all* `k` (D12, W11). -/
theorem cond_p1_ucont {X : Type*} [PseudoMetricSpace X] {F : Set (X → X)}
    {c : ℝ≥0} (hF : ∀ f ∈ F, LipschitzWith c f) (hc0 : 0 < c) (hc1 : c < 1)
    {A : Set X} (hA : A.Nonempty) (hAinv : ∀ f ∈ F, f '' A ⊆ A)
    {L : ℕ} {K : Set X} (hK : Bornology.IsBounded K) (hKL : ∀ f ∈ words F L, Set.range f ⊆ K)
    (ε : ℝ≥0) (hε : 0 < ε) (k : ℕ) :
    externalCoveringNumber (X := UnifMaps X) ε (wordBall F k) ≤
      externalCoveringNumber (ε / 2) A +
        ∑ l ∈ Finset.range (memoryLength c L K ε),
          externalCoveringNumber (X := UnifMaps X) ε (words F l) :=
  LeanDeepgen.cond_p1_ucont hF hc0 hc1 hA hAinv hK hKL ε hε k

end Saturation

section Polynomial

open scoped NNReal ENNReal
open Metric
open FoML.ToMathlib

/-- **cond:p2-nilp** (P2, Sec. 4 / App. F). Nilpotent (polynomial-entropy) control: if the group
balls satisfy `N(B_G(e,R), δ) ≤ C_H (1 + R/δ)^D`, the action is `L_α`-Lipschitz and `F ⊆ α(S_g)`
with `S_g` in the `R_S`-ball, then `N(B(k,F), d_∞, ε) ≤ C_H max(1, R_S L_α)^D (1 + k/ε)^D` for
every `k ≥ 0` (D13, W12). -/
theorem cond_p2_nilp {X : Type*} [PseudoEMetricSpace X] {G : Type*} [Group G]
    [PseudoEMetricSpace G] (α : G →* Function.End X) {F : Set (X → X)}
    (hsub : ∀ g h : G, edist 1 (g * h) ≤ edist 1 g + edist 1 h)
    {D : ℝ} (hD : 0 ≤ D) {CH : ℝ} (hCH : 1 ≤ CH)
    (hball : ∀ R δ : ℝ≥0, 0 < δ →
      (externalCoveringNumber δ (closedEBall (1 : G) R) : ℝ≥0∞) ≤
        ENNReal.ofReal (CH * (1 + R / δ) ^ D))
    {Sg : Set G} {RS : ℝ≥0} (hS : ∀ s ∈ Sg, edist 1 s ≤ RS) (hF : F ⊆ orbitMap α '' Sg)
    {Lα : ℝ≥0} (hLα : 0 < Lα) (hα : LipschitzWith Lα (fun g => toUnifMaps (orbitMap α g))) :
    ∀ ε : ℝ≥0, 0 < ε → ∀ k : ℕ,
      (externalCoveringNumber (X := UnifMaps X) ε (wordBall F k) : ℝ≥0∞) ≤
        ENNReal.ofReal (CH * max 1 (RS * Lα) ^ D * (1 + k / ε) ^ D) :=
  LeanDeepgen.cond_p2_nilp α hsub hD hCH hball hS hF hLα hα

end Polynomial

section Exponential

open scoped NNReal ENNReal
open Metric

/-- **cond:e1-free-iso** (E1, App. F). One-point uniform separation of words of equal length
(freeness follows, W13/D14) gives `N(B(k,F), d_∞, ε) ≥ r^k` for `2ε < δ`. -/
theorem cond_e1_free_iso {X : Type*} {r : ℕ} [PseudoEMetricSpace X]
    (_hr : 2 ≤ r) (f : Fin r → X → X) (x₀ : X) {δ : ℝ≥0} (hδ : 0 < δ)
    (hsep : ∀ k, ∀ u v : List (Fin r), u.length = k → v.length = k → u ≠ v →
      (δ : ℝ≥0∞) ≤ edist (wordOf f u x₀) (wordOf f v x₀)) :
    ∀ k, ∀ ε : ℝ≥0, 2 * ε < δ →
      (r : ℕ∞) ^ k ≤ externalCoveringNumber (X := UnifMaps X) ε (wordBall (Set.range f) k) :=
  LeanDeepgen.cond_e1_free_iso _hr f x₀ hδ hsep

/-- **cond:e1p-theoremC** (E1', App. F). Equal-length coding with `r ≥ 2` generators (D15):
isometry and finiteness of `d_∞` are not needed (W14). -/
theorem cond_e1p {X : Type*} {r : ℕ} [PseudoEMetricSpace X]
    (hr : 2 ≤ r) (f : Fin r → X → X)
    (x₀ : X) {δ : ℝ≥0} (hδ : 0 < δ)
    (hsep : ∀ k, ∀ u v : List (Fin r), u.length = k → v.length = k → u ≠ v →
      (δ : ℝ≥0∞) ≤ edist (wordOf f u x₀) (wordOf f v x₀)) :
    ∀ k, ∀ ε : ℝ≥0, 2 * ε < δ →
      (r : ℕ∞) ^ k ≤ externalCoveringNumber (X := UnifMaps X) ε (wordBall (Set.range f) k) :=
  LeanDeepgen.cond_e1p_theoremC hr f x₀ hδ hsep

/-- **cond:e2-pingpong** (E2, App. F). Ping–pong coding with pairwise disjoint chambers (W15/D16),
coding cores, resets and `α`-separated markers gives `N(B(k,F), d_∞, ε) ≥ r^k` for `2ε < α`
and injectivity of the coding on words of each length. -/
theorem cond_e2_pingpong {X : Type*} {r : ℕ} [PseudoEMetricSpace X]
    (_hr : 2 ≤ r) (f : Fin r → X → X) (U V : Fin r → Set X)
    (hVU : ∀ i, V i ⊆ U i) (a : Fin r → X) (q : X) {α : ℝ≥0} (hα : 0 < α)
    (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hcore : ∀ i, ({q} ∪ ⋃ j, V j) ⊆ f i '' V i)
    (hreset : ∀ i, ∀ x, x ∉ U i → f i x = a i)
    (hanchor : ∀ i, f i '' Set.range a ⊆ Set.range a)
    (hmark : ∀ i, (α : ℝ≥0∞) ≤ edist q (a i)) :
    (∀ k, ∀ ε : ℝ≥0, 2 * ε < α →
      (r : ℕ∞) ^ k ≤ externalCoveringNumber (X := UnifMaps X) ε (wordBall (Set.range f) k)) ∧
    (∀ k, Set.InjOn (wordOf f) {u : List (Fin r) | u.length = k}) :=
  LeanDeepgen.cond_e2_pingpong _hr f U V hVU a q hα hdisj hcore hreset hanchor hmark

end Exponential

section MemoryExpansion

open scoped NNReal ENNReal
open Metric
open FoML.ToMathlib

/-- **cond:e3** (E3, App. F). Memory-preserving expansion on `ℓ_∞(E)`: for `λ > 1` and
`0 < ε < 1/2` (D17), the word set `W_k` satisfies
`∏_j M(G, 2ε/λ^{j+1}) ≤ N(W_k, ε) ≤ ∏_j N(G, ε/λ^{j+1})` and `N(W_k, ε) ≤ N(B(2k+1,F), ε)`. -/
theorem cond_e3 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {G : Set E} {lam : ℝ≥0}
    {k : ℕ}
    (hlam : 1 < lam) {ε : ℝ≥0} (_hε : 0 < ε) (hε1 : ε < 1 / 2) :
    (∏ j : Fin k, packingNumber (2 * ε / lam ^ ((j : ℕ) + 1)) G ≤
        externalCoveringNumber (X := UnifMaps (MemState E)) ε (memWords G lam k) ∧
      externalCoveringNumber (X := UnifMaps (MemState E)) ε (memWords G lam k) ≤
        ∏ j : Fin k, externalCoveringNumber (ε / lam ^ ((j : ℕ) + 1)) G) ∧
    externalCoveringNumber (X := UnifMaps (MemState E)) ε (memWords G lam k) ≤
      externalCoveringNumber (X := UnifMaps (MemState E)) ε
        (wordBall (memGen G lam) (2 * k + 1)) :=
  LeanDeepgen.cond_e3 hlam _hε hε1

/-- **cor:superexp** (App. F). Logarithmic entropy of `G` (`c₋ log(1/δ) ≤ log M(G,δ)`,
`log N(G,δ) ≤ c₊ log(1/δ)`) gives `log N(W_k, ε) ≍ k²` for `ε < min{1/2, λδ₀/2}`
(D17, D18, W16). -/
theorem cor_superexp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {G : Set E}
    {lam : ℝ≥0}
    (hlam : 1 < lam)
    (hfin : ∀ δ : ℝ≥0, 0 < δ → externalCoveringNumber δ G ≠ ⊤)
    {cLow cUp δ₀ : ℝ} (hcLow : 0 < cLow) (hcUp : 0 < cUp) (hδ₀ : 0 < δ₀)
    (hlow : ∀ δ : ℝ≥0, 0 < δ → (δ : ℝ) < δ₀ →
      cLow * Real.log (1 / (δ : ℝ)) ≤ Real.log (packingNumber δ G : ℝ≥0∞).toReal)
    (hup : ∀ δ : ℝ≥0, 0 < δ → (δ : ℝ) < δ₀ →
      Real.log (externalCoveringNumber δ G : ℝ≥0∞).toReal ≤ cUp * Real.log (1 / (δ : ℝ)))
    {ε : ℝ≥0} (hε : 0 < ε) (hε1 : ε < 1 / 2) (hεδ : (ε : ℝ) < lam * δ₀ / 2) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      C₁ * (k : ℝ) ^ 2 ≤
        Real.log (externalCoveringNumber (X := UnifMaps (MemState E)) ε (memWords G lam k) :
          ℝ≥0∞).toReal ∧
      Real.log (externalCoveringNumber (X := UnifMaps (MemState E)) ε (memWords G lam k) :
          ℝ≥0∞).toReal ≤ C₂ * (k : ℝ) ^ 2 :=
  LeanDeepgen.cor_superexp hlam hfin hcLow hcUp hδ₀ hlow hup hε hε1 hεδ

/-- **cor:doubleexp** (App. F). Power-type entropy of `G` (`c₋ δ^{-p} ≤ log M(G,δ)`,
`log N(G,δ) ≤ c₊ δ^{-p}`) gives `log N(W_k, ε) ≍ λ^{pk}` for `ε < min{1/2, λδ₀/2}`
(D17, D18, W16). -/
theorem cor_doubleexp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {G : Set E}
    {lam : ℝ≥0}
    (hlam : 1 < lam)
    (hfin : ∀ δ : ℝ≥0, 0 < δ → externalCoveringNumber δ G ≠ ⊤)
    {p cLow cUp δ₀ : ℝ} (hp : 0 < p) (hcLow : 0 < cLow) (hcUp : 0 < cUp) (hδ₀ : 0 < δ₀)
    (hlow : ∀ δ : ℝ≥0, 0 < δ → (δ : ℝ) < δ₀ →
      cLow * (δ : ℝ) ^ (-p) ≤ Real.log (packingNumber δ G : ℝ≥0∞).toReal)
    (hup : ∀ δ : ℝ≥0, 0 < δ → (δ : ℝ) < δ₀ →
      Real.log (externalCoveringNumber δ G : ℝ≥0∞).toReal ≤ cUp * (δ : ℝ) ^ (-p))
    {ε : ℝ≥0} (hε : 0 < ε) (hε1 : ε < 1 / 2) (hεδ : (ε : ℝ) < lam * δ₀ / 2) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      C₁ * (lam : ℝ) ^ (p * k) ≤
        Real.log (externalCoveringNumber (X := UnifMaps (MemState E)) ε (memWords G lam k) :
          ℝ≥0∞).toReal ∧
      Real.log (externalCoveringNumber (X := UnifMaps (MemState E)) ε (memWords G lam k) :
          ℝ≥0∞).toReal ≤ C₂ * (lam : ℝ) ^ (p * k) :=
  LeanDeepgen.cor_doubleexp hlam hfin hp hcLow hcUp hδ₀ hlow hup hε hε1 hεδ

end MemoryExpansion

/-! ## Sec. 4.2: entropy profiles (`Profiles/*`) -/

section LogSplit

open FoML.ToMathlib

/-- **lem:log-split** (inequality part, Sec. 4.2). `log(1 + k/ε) ≤ log(1 + k/D) + log(D/ε)` for
`0 < ε ≤ D`, `k ≥ 0`. -/
theorem lem_log_split {D k ε : ℝ} (hD : 0 < D) (hk : 0 ≤ k) (hε : 0 < ε)
    (hεD : ε ≤ D) :
    Real.log (1 + k / ε) ≤ Real.log (1 + k / D) + Real.log (D / ε) :=
  LeanDeepgen.log_one_add_div_le hD hk hε hεD

end LogSplit

section Profiles

open scoped NNReal ENNReal Real
open MeasureTheory Set intervalIntegral Metric
open FoML.ToMathlib

/-- **prop:profiles** (i) (Sec. 4.2), saturation: a depth-independent covering bound `N_∞` with
`D_k ≤ D̄` gives `V_k ≤ ∫₀^{D̄} √log N_∞(ε) dε` (`D̄ ≥ 0` suffices, W19). -/
theorem prop_profiles_i {Y : Type*} [PseudoEMetricSpace Y] {A : ℕ → Set Y} {D : ℕ → ℝ}
    {Dbar : ℝ}
    (hD0 : ∀ k, 0 ≤ D k) (hD : ∀ k, D k ≤ Dbar) {Ninf : ℝ≥0 → ℕ∞}
    (hN : ∀ k ε, coveringNumber ε (A k) ≤ Ninf ε)
    (hNtop : ∀ ε : ℝ≥0, 0 < ε → Ninf ε ≠ ⊤)
    (hint : IntervalIntegrable
      (fun ε : ℝ => √(Real.log (Ninf ε.toNNReal : ℝ≥0∞).toReal)) volume 0 Dbar)
    (k : ℕ) :
    entropyIntegral (D k) (A k) ≤
      ∫ ε in (0 : ℝ)..Dbar, √(Real.log (Ninf ε.toNNReal : ℝ≥0∞).toReal) :=
  LeanDeepgen.profile_saturation hD0 hD hN hNtop hint k

/-- **prop:profiles** (ii) (Sec. 4.2), polynomial growth with bounded diameter:
`N_k(ε) ≤ C₀(1 + k/ε)^D`, `D_k ≤ D̄` gives
`V_k ≤ D̄ √D (√log(1 + k/D̄) + √π/2) + D̄ √log C₀` (`C₀ ≥ 1`, `D ≥ 0`, `D̄ > 0`; D20). -/
theorem prop_profiles_ii {Y : Type*} [PseudoEMetricSpace Y] {A : ℕ → Set Y} {D : ℕ → ℝ}
    {Dbar C₀ Dd : ℝ}
    (hD0 : ∀ k, 0 ≤ D k) (hD : ∀ k, D k ≤ Dbar) (hDbar : 0 < Dbar) (hC₀ : 1 ≤ C₀)
    (hDd : 0 ≤ Dd)
    (hN : ∀ k, 1 ≤ k → ∀ ε : ℝ, 0 < ε →
      (coveringNumber ε.toNNReal (A k) : ℝ≥0∞).toReal ≤ C₀ * (1 + k / ε) ^ Dd)
    {k : ℕ} (hk : 1 ≤ k) :
    entropyIntegral (D k) (A k) ≤
      Dbar * √Dd * (√(Real.log (1 + k / Dbar)) + √π / 2) + Dbar * √(Real.log C₀) :=
  LeanDeepgen.profile_poly_bounded hD0 hD hDbar hC₀ hDd hN hk

/-- **prop:profiles** (iii) (Sec. 4.2), exponential growth with bounded diameter:
`log N_k(ε) ≤ αk + ψ(ε)` gives `V_k ≤ D̄ √(αk) + ∫₀^{D̄} √ψ` (no sign conditions on `α, ψ`, W18). -/
theorem prop_profiles_iii {Y : Type*} [PseudoEMetricSpace Y] {A : ℕ → Set Y} {D : ℕ → ℝ}
    {Dbar α : ℝ} {ψ : ℝ → ℝ}
    (hD0 : ∀ k, 0 ≤ D k) (hD : ∀ k, D k ≤ Dbar)
    (hΨ : IntervalIntegrable (fun ε => √(ψ ε)) volume 0 Dbar)
    (hN : ∀ k, ∀ ε : ℝ, 0 < ε → metricEntropy ε.toNNReal (A k) ≤ α * k + ψ ε)
    (k : ℕ) :
    entropyIntegral (D k) (A k) ≤ Dbar * √(α * k) + ∫ ε in (0 : ℝ)..Dbar, √(ψ ε) :=
  LeanDeepgen.profile_exp_bounded hD0 hD hΨ hN k

/-- **prop:profiles** (iv) (Sec. 4.2), polynomial growth with linear diameter `D_k ≤ D₁ k`:
`V_k ≤ D₁ k (√D (√log(1 + 1/D₁) + √π/2) + √log C₀)` (D20). -/
theorem prop_profiles_iv {Y : Type*} [PseudoEMetricSpace Y] {A : ℕ → Set Y} {D : ℕ → ℝ}
    {D₁ C₀ Dd : ℝ}
    (hD0 : ∀ k, 0 ≤ D k) (hD : ∀ k, D k ≤ D₁ * k) (hD₁ : 0 < D₁) (hC₀ : 1 ≤ C₀)
    (hDd : 0 ≤ Dd)
    (hN : ∀ k, 1 ≤ k → ∀ ε : ℝ, 0 < ε →
      (coveringNumber ε.toNNReal (A k) : ℝ≥0∞).toReal ≤ C₀ * (1 + k / ε) ^ Dd)
    {k : ℕ} (hk : 1 ≤ k) :
    entropyIntegral (D k) (A k) ≤
      D₁ * k * (√Dd * (√(Real.log (1 + 1 / D₁)) + √π / 2) + √(Real.log C₀)) :=
  LeanDeepgen.profile_poly_linear hD0 hD hD₁ hC₀ hDd hN hk

/-- **prop:profiles-finite** (Sec. 4.2). `|A_k| ≤ r^{k+1}` gives `V_k ≤ D̄ √((k+1) log r)`
(no metric structure on `F` needed, W20). -/
theorem prop_profiles_finite {Y : Type*} [PseudoEMetricSpace Y] {A : ℕ → Set Y} {D : ℕ → ℝ}
    {Dbar : ℝ} {r : ℕ}
    (hD0 : ∀ k, 0 ≤ D k) (hD : ∀ k, D k ≤ Dbar)
    (hA : ∀ k, (A k).encard ≤ (r : ℕ∞) ^ (k + 1)) (k : ℕ) :
    entropyIntegral (D k) (A k) ≤ Dbar * √((k + 1) * Real.log r) :=
  LeanDeepgen.profile_finite hD0 hD hA k

end Profiles

/-! ## Sec. 5 / App. J: depth–sample-size trade-off (`Tradeoff/Regimes`) -/

section Tradeoff

open Filter Asymptotics
open scoped Topology
open LeanDeepgen.Tradeoff

/-- **tab:tradeoff**, PP regime (polynomial bias `k^{-β}`, polynomial variance `√(k^γ/n)`):
at `k* = n^{1/(2β+γ)}` the bound equals `2 n^{-β/(2β+γ)}` and every depth `k > 0` has bound
`≥ n^{-β/(2β+γ)}` (exact balancing, W21/W22). -/
theorem thm_tradeoff_pp {β γ n : ℝ} (hβ : 0 < β) (hγ : 0 < γ) (hn : 0 < n) :
    genBound (biasPoly β) (varPoly γ) n (kPP β γ n) = 2 * n ^ (-β / (2 * β + γ)) ∧
    ∀ k > 0, n ^ (-β / (2 * β + γ)) ≤ genBound (biasPoly β) (varPoly γ) n k :=
  LeanDeepgen.Tradeoff.tradeoff_PP hβ hγ hn

/-- **tab:tradeoff**, EP regime (exponential bias, polynomial variance): at
`k* = (log n − γ log log n)/(2α)` the bound is `Θ(n^{-1/2} (log n)^{γ/2})` (two-sided, W21/D22). -/
theorem thm_tradeoff_ep {α γ : ℝ} (hα : 0 < α) (hγ : 0 < γ) :
    (fun n => genBound (biasExp α) (varPoly γ) n (kEP α γ n)) =Θ[atTop]
      (fun n => n ^ (-(1 : ℝ) / 2) * Real.log n ^ (γ / 2)) :=
  LeanDeepgen.Tradeoff.tradeoff_EP hα hγ

/-- **tab:tradeoff**, EL regime (exponential bias, logarithmic variance `√(log k/n)`): at `k*`
the bound is `Θ(√(log log n / n))` (two-sided, W21/D22). -/
theorem thm_tradeoff_el {α : ℝ} (hα : 0 < α) :
    (fun n => genBound (biasExp α) varLog n (kEL α n)) =Θ[atTop]
      (fun n => √(Real.log (Real.log n) / n)) :=
  LeanDeepgen.Tradeoff.tradeoff_EL hα

/-- **tab:tradeoff**, PL regime (polynomial bias, logarithmic variance): at
`k* = (2βn/log(2βn))^{1/(2β)}` (no Lambert W, D22) the bound is `Θ(√(log n / n))`. -/
theorem thm_tradeoff_pl {β : ℝ} (hβ : 0 < β) :
    (fun n => genBound (biasPoly β) varLog n (kPL β n)) =Θ[atTop]
      (fun n => √(Real.log n / n)) :=
  LeanDeepgen.Tradeoff.tradeoff_PL hβ

end Tradeoff

/-! ## App. G: implementation (`Examples/Implementation`) -/

section Implementation

open scoped ENNReal NNReal UniformConvergence Matrix
open Metric
open FoML.ToMathlib

/-- **prop:implementation** (a) (App. G). A sup-norm totally bounded class `𝓗` and a family `𝒜`
uniformly dense in it admit a finite implementation class `H_imp ⊆ 𝒜` of size `≤ N(𝓗, ε/2)` and
an implementation map with `ε_imp ≤ ε` (no compactness, D24/W23). -/
theorem prop_implementation_a {X : Type*} (𝓗 𝒜 : Set (X → ℝ))
    (h𝓗 : TotallyBounded (α := X →ᵤ ℝ) 𝓗)
    (h𝒜 : ∀ g ∈ 𝓗, ∀ η : ℝ, 0 < η → ∃ a ∈ 𝒜, ∀ x, |g x - a x| ≤ η) (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ Himp : Set (X → ℝ), Himp ⊆ 𝒜 ∧ Himp.Finite ∧
      Himp.encard ≤ coveringNumber (X := X →ᵤ ℝ) (ε / 2) 𝓗 ∧
      ∃ ι : (X → ℝ) → (X → ℝ), (∀ g ∈ 𝓗, ι g ∈ Himp) ∧ ∀ g ∈ 𝓗, ∀ x, |g x - ι g x| ≤ ε :=
  LeanDeepgen.prop_implementation_a 𝓗 𝒜 h𝓗 h𝒜 ε hε

/-- **prop:implementation** (b) (App. G). Layerwise errors `δ` (hidden) and `δ_H` (output) with
Lipschitz constants `Λ`, `L_H` give `ε_imp(k) ≤ δ_H + L_H δ Σ_{i<k} Λ^i` (D25/W24). -/
theorem prop_implementation_b {X : Type*} [PseudoMetricSpace X] {F : Set (X → X)}
    {H : Set (X → ℝ)} {k : ℕ}
    {Λ LH : ℝ≥0} {δ δH : ℝ} (hδ : 0 ≤ δ)
    (hF : ∀ f ∈ F, LipschitzWith Λ f) (hH : ∀ h ∈ H, LipschitzWith LH h)
    (tf : (X → X) → (X → X)) (htf : ∀ f ∈ F, uniformDist f (tf f) ≤ ENNReal.ofReal δ)
    (th : (X → ℝ) → (X → ℝ)) (hth : ∀ h ∈ H, ∀ x, |h x - th h x| ≤ δH)
    (ι : (X → ℝ) → (X → ℝ))
    (hι : ∀ g ∈ hypothesisClass H F k, ∃ h ∈ H, ∃ u : List (X → X),
      (∀ f ∈ u, f ∈ F) ∧ u.length ≤ k ∧ g = h ∘ compList u ∧ ι g = th h ∘ implWord tf u) :
    implError ι (hypothesisClass H F k) ≤
      ENNReal.ofReal (δH + LH * δ * ∑ i ∈ Finset.range k, (Λ : ℝ) ^ i) :=
  LeanDeepgen.prop_implementation_b hδ hF hH tf htf th hth ι hι

/-- **prop:implementation** (c) (App. G). Affine transitions on `ℝ^d` are realized exactly by
depth-`k` ReLU networks of width `2d`, so `ε_imp = 0`. -/
theorem prop_implementation_c {d : ℕ} {F : Set ((Fin d → ℝ) → (Fin d → ℝ))}
    (hF : ∀ f ∈ F, ∃ (A : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ), f = fun x => A *ᵥ x + b)
    (H : Set ((Fin d → ℝ) → ℝ)) (k : ℕ) :
    (∀ g ∈ wordBall F k, IsReluNet d k g) ∧ implError id (hypothesisClass H F k) = 0 :=
  LeanDeepgen.prop_implementation_c hF H k

end Implementation

/-! ## App. H: readout realization (`Examples/Readout`) -/

section Readout

open scoped NNReal ENNReal

/-- **prop:global_scalar_observable** (App. H). A bounded feature map and a global scalar
observable `u` that is `κ`-co-Lipschitz on the reachable set make the linear readouts satisfy
`ass:readout-realization` with `R_out = R_H R_Φ` (`R_Φ > 0`, D31). -/
theorem prop_global_scalar_observable {X : Type*} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [PseudoMetricSpace X] {n : ℕ} (S : Fin n → X)
    (Bk : Set (X → X)) (Φ : X → E)
    {RH RΦ κ : ℝ} (u : E) (hu : ‖u‖ ≤ RH) (hκ : 0 < κ) (hRΦ : 0 < RΦ)
    (hcolip : ∀ x ∈ reachableSet S Bk, ∀ y ∈ reachableSet S Bk,
      κ * dist x y ≤ |inner ℝ (u) (Φ x - Φ y)|)
    (hbdd : ∀ x, ‖Φ x‖ ≤ RΦ) :
    ReadoutRealization S (linearReadouts Φ RH) Bk κ (RH * RΦ) :=
  LeanDeepgen.global_scalar_observable S Bk Φ u hu hκ hRΦ hcolip hbdd

/-- **prop:linear-interpolation** (App. H). Map-wise finite-set interpolation: right inverses of
norm `≤ Λ_j` realize prescribed codes `c^{(j)}` by linear readouts, with `ρ`-separation and
`R_out`-boundedness of the pushed-forward readouts (distinctness assumption dropped, W27/D30). -/
theorem prop_linear_interpolation {X : Type*} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {n M : ℕ} (S : Fin n → X) (f : Fin M → X → X) (Φ : X → E)
    (Λ : Fin M → ℝ)
    (hinv : ∀ j, ∀ c : Fin n → ℝ, ∃ w : E, ‖w‖ ≤ Λ j * Real.sqrt (∑ i, c i ^ 2) ∧
      ∀ i, inner ℝ (w) (Φ (f j (S i))) = c i)
    (cd : Fin M → Fin n → ℝ) {ρ Rout RH : ℝ}
    (hsep : ∀ j l, j ≠ l → ρ ≤ Real.sqrt ((1 / (n : ℝ)) * ∑ i, (cd j i - cd l i) ^ 2))
    (hbdd : ∀ j i, |cd j i| ≤ Rout) (hRout : 0 ≤ Rout)
    (hRH : ∀ j, Λ j * Real.sqrt (∑ i, cd j i ^ 2) ≤ RH) :
    ∃ h : Fin M → (X → ℝ), (∀ j, h j ∈ linearReadouts Φ RH) ∧
      (∀ j i, h j (f j (S i)) = cd j i) ∧
      (∀ j l, j ≠ l → ρ ≤ empNorm S (h j ∘ f j) (h l ∘ f l)) ∧
      (∀ j, empSupNorm S (h j ∘ f j) ≤ Rout) :=
  LeanDeepgen.linear_interpolation S f Φ Λ hinv cd hsep hbdd hRout hRH

/-- **cor:rkhs-readout** (App. H). Kernel readouts: Gram matrices with smallest eigenvalue
`≥ λ_min(j) > 0` give the interpolation of `prop:linear-interpolation` with
`Λ_j = λ_min(j)^{-1/2}`. -/
theorem cor_rkhs_readout {X : Type*} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {n M : ℕ} (S : Fin n → X) (f : Fin M → X → X) (Φ : X → E)
    (lmin : Fin M → ℝ) (hl : ∀ j, 0 < lmin j)
    (hG : ∀ j, ∀ c : Fin n → ℝ, lmin j * ∑ i, c i ^ 2 ≤
      ∑ i, ∑ i', c i * c i' * inner ℝ (Φ (f j (S i))) (Φ (f j (S i'))))
    (cd : Fin M → Fin n → ℝ) {ρ Rout RH : ℝ}
    (hsep : ∀ j l, j ≠ l → ρ ≤ Real.sqrt ((1 / (n : ℝ)) * ∑ i, (cd j i - cd l i) ^ 2))
    (hbdd : ∀ j i, |cd j i| ≤ Rout) (hRout : 0 ≤ Rout)
    (hRH : ∀ j, (Real.sqrt (lmin j))⁻¹ * Real.sqrt (∑ i, cd j i ^ 2) ≤ RH) :
    ∃ h : Fin M → (X → ℝ), (∀ j, h j ∈ linearReadouts Φ RH) ∧
      (∀ j i, h j (f j (S i)) = cd j i) ∧
      (∀ j l, j ≠ l → ρ ≤ empNorm S (h j ∘ f j) (h l ∘ f l)) ∧
      (∀ j, empSupNorm S (h j ∘ f j) ≤ Rout) :=
  LeanDeepgen.rkhs_readout S f Φ lmin hl hG cd hsep hbdd hRout hRH

end Readout

/-! ## App. K: chain-of-thought scratchpads (`Examples/ChainOfThought`) -/

section ChainOfThought

open scoped NNReal ENNReal UniformConvergence Topology Real
open Metric
open FoML.ToMathlib
open MeasureTheory

/-- **lem:cot-append-growth** (App. K). Append-only steps over an alphabet of size `m ≥ 2`:
`N(B(k,F_w), d_∞, ε) ≤ m^{min{k, ℓ(ε)} + 1}` for every `ε > 0` (W25/D27). -/
theorem lem_cot_append_growth {𝒜 : Type*} {θ : ℝ≥0} [Fact (0 < θ)] [Fact (θ < 1)]
    [Fintype 𝒜] (hm : 2 ≤ Fintype.card 𝒜) {ε : ℝ≥0} (hε : 0 < ε)
    (k : ℕ) :
    externalCoveringNumber (X := UnifMaps (SeqSpace 𝒜 θ)) ε (wordBall (appendClass θ) k) ≤
      (Fintype.card 𝒜 : ℕ∞) ^ (min k (cotLength θ ε) + 1) :=
  LeanDeepgen.cot_append_growth hm hε k

/-- **lem:cot-branch-growth** (App. K). Branching (guarded) steps with `r ≥ 2` active symbols
(D26): `r^k ≤ N(B(k,F_b), d_∞, ε) ≤ r^{k+1}` for `2ε < 1`. -/
theorem lem_cot_branch_growth {θ : ℝ≥0} {r : ℕ} [Fact (0 < θ)] [Fact (θ < 1)]
    (hr : 2 ≤ r) (k : ℕ) {ε : ℝ≥0} (hε : 2 * ε < 1) :
    (r : ℕ∞) ^ k ≤ externalCoveringNumber (X := UnifMaps (SeqSpace (BranchAlphabet r) θ)) ε
        (wordBall (branchClass θ) k) ∧
      externalCoveringNumber (X := UnifMaps (SeqSpace (BranchAlphabet r) θ)) ε
        (wordBall (branchClass θ) k) ≤ (r : ℕ∞) ^ (k + 1) :=
  LeanDeepgen.cot_branch_growth hr k hε

/-- **lem:cot-output** (App. K; window version, W28). The window one-hot feature map `Φ_L` on
`𝒜^ℕ` is `√2 θ^{1−L}`-Lipschitz. -/
theorem lem_cot_output {𝒜 : Type*} [Fintype 𝒜] [DecidableEq 𝒜] {θ : ℝ≥0}
    [Fact (0 < θ)] [Fact (θ < 1)] (L : ℕ) :
    LipschitzWith (NNReal.sqrt 2 * θ⁻¹ ^ (L - 1)) (windowFeature (𝒜 := 𝒜) θ L) :=
  LeanDeepgen.lipschitzWith_windowFeature L

/-- **prop:cot-append** (App. K), rigorous form (D33). For the append-only scratchpad with linear
readouts over an `L_Φ`-Lipschitz bounded feature map, the excess risk at depth `k` is at most
`β_ℓ R L_Φ θ^k + η + bvDev(R M/√n + 12 R L_Φ V_∞/√n)` with probability `1 − δ` (EL regime). -/
theorem prop_cot_append {𝒜 : Type*} [Fintype 𝒜] {θ : ℝ≥0} [Fact (0 < θ)] [Fact (θ < 1)]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace (SeqSpace 𝒜 θ)] [OpensMeasurableSpace (SeqSpace 𝒜 θ)]
    [TopologicalSpace.SeparableSpace E] {Y : Type*} [MeasurableSpace Y]
    (hm : 2 ≤ Fintype.card 𝒜) {n : ℕ} (hn : 0 < n) (P : Measure (SeqSpace 𝒜 θ × Y))
    [IsProbabilityMeasure P] (L : BoundedLipschitzLoss Y) (hℓ : Measurable (Function.uncurry L.ℓ))
    (hb : 0 < L.b) (hβ : 0 ≤ L.β) (Φ : SeqSpace 𝒜 θ → E) {LΦ : ℝ≥0} (hLΦ : 0 < LΦ)
    (hΦ : LipschitzWith LΦ Φ) {M : ℝ} (hM : 0 ≤ M) (hΦM : ∀ x, ‖Φ x‖ ≤ M) {R : ℝ} (hR : 0 < R)
    (k : ℕ) {η δ : ℝ} (hη : 0 ≤ η) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ((Measure.pi fun _ : Fin n => P) {D | ¬ ∀ fhat,
        IsEmpMinimizer L D (hypothesisClass (linearReadouts Φ R) (appendClass θ) k) η fhat →
        risk L P fhat - sInf (risk L P '' cotTargetClass Φ R) ≤
          L.β * (R * LΦ * (θ : ℝ) ^ k) + η +
            bvDev L n δ (R * M / √n + 12 * 1 * (R * LΦ) / √n * cotVinf (Fintype.card 𝒜) θ)}
      ).toReal ≤ δ :=
  LeanDeepgen.prop_cot_append hm hn P L hℓ hb hβ Φ hLΦ hΦ hM hΦM hR k hη hδ hδ1

end ChainOfThought

/-! ## App. L–M: fixed-point iterations and ODE solvers (`Examples/ODE`) -/

section ODE

open scoped NNReal ENNReal UniformConvergence Topology RealInnerProductSpace
open Metric
open FoML.ToMathlib
open MeasureTheory

/-- **lem:fp-contraction** (App. L). For a `μ`-strongly concave, `Λ`-smooth field `s` and a step
`0 < h ≤ 2/(μ+Λ)`, the projected gradient step `Π_K(x + h s(x))` is `(1 − hμ)`-Lipschitz (D28). -/
theorem lem_fp_contraction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K : Set E} {proj : E → E}
    (hP : IsProjectionOnto K proj) {s : K → E} {μ Λ h : ℝ} (hμ : 0 < μ)
    (hμΛ : μ ≤ Λ) (hs : StronglyConcaveSmooth μ Λ s) (hh0 : 0 < h) (hh : h ≤ 2 / (μ + Λ)) :
    LipschitzWith (Real.toNNReal (1 - h * μ)) (gradStep hP s h) :=
  LeanDeepgen.fp_contraction hP hμ hμΛ hs hh0 hh

/-- **lem:ode-saturation** (App. M). Euler schemes with uniformly Lipschitz fields on a compact
`K` form a `d_∞`-totally bounded class (even without time-stamp consistency, W26/D29), hence the
depth-`k` scheme classes saturate. -/
theorem lem_ode_saturation {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K : Set E} {proj : E → E}
    (hK : IsCompact K) (hP : IsProjectionOnto K proj) {𝒮 : Set (K → ℝ → E)}
    {Λ : ℝ≥0} (h𝒮 : ∀ s ∈ 𝒮, ∀ τ, LipschitzWith Λ (fun x => s x τ)) (h₀ T : ℝ) :
    TotallyBounded (α := UnifMaps K) (schemeSet hP 𝒮 h₀ T) ∧
    ∀ ε : ℝ≥0, 0 < ε → ∀ k,
      externalCoveringNumber (X := UnifMaps K) ε (schemeBall hP 𝒮 h₀ T k) ≤
          externalCoveringNumber (X := UnifMaps K) ε (schemeSet hP 𝒮 h₀ T) ∧
        externalCoveringNumber (X := UnifMaps K) ε (schemeSet hP 𝒮 h₀ T) ≠ ⊤ :=
  LeanDeepgen.ode_saturation hK hP h𝒮 h₀ T

/-- **lem:ode-euler-error** (App. M). Global Euler error over horizon `T` with `k` steps:
`‖x(T) − Euler_k(x₀)‖ ≤ (Λ_s M_s + Λ_τ) e^{Λ_s T} T² / (2k)`. -/
theorem lem_ode_euler_error {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {s : E → ℝ → E} {Λs Λτ Ms : ℝ≥0}
    (hsx : ∀ τ, LipschitzWith Λs (fun x => s x τ)) (hsτ : ∀ x, LipschitzWith Λτ (s x))
    (hMs : ∀ x τ, ‖s x τ‖ ≤ Ms) {T : ℝ} (hT : 0 ≤ T) {x : ℝ → E}
    (hx : ∀ t ∈ Set.Icc 0 T, HasDerivAt x (s (x t) t) t) {k : ℕ} (hk : 0 < k) :
    ‖x T - eulerIter s (T / k) k (x 0)‖ ≤
      (Λs * Ms + Λτ) * Real.exp (Λs * T) / 2 * T ^ 2 / k :=
  LeanDeepgen.euler_global_error hsx hsτ hMs hT hx hk

/-- **prop:ode-fixedpoint** (App. L), rigorous form (D33). Fixed-point iterations of contractive
gradient steps with linear readouts: excess risk at depth `k` at most
`β_ℓ R diam(K) (1 − hμ)^k + η + bvDev(R M_K/√n + 12 R V_∞/√n)` with probability `1 − δ`
(EL regime). -/
theorem prop_ode_fixedpoint {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K : Set E} {proj : E → E} [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace.SeparableSpace E] {Y : Type*} [MeasurableSpace Y]
    (hK : IsCompact K) (hP : IsProjectionOnto K proj) {𝒮 : Set (K → E)} {μ Λ h : ℝ}
    (hμ : 0 < μ) (hμΛ : μ ≤ Λ) (h𝒮 : ∀ s ∈ 𝒮, StronglyConcaveSmooth μ Λ s) (hh0 : 0 < h)
    (hh : h ≤ 2 / (μ + Λ)) {n : ℕ} (hn : 0 < n) (P : Measure (K × Y)) [IsProbabilityMeasure P]
    (L : BoundedLipschitzLoss Y) (hℓ : Measurable (Function.uncurry L.ℓ)) (hb : 0 < L.b)
    (hβ : 0 ≤ L.β) {R MK : ℝ} (hR : 0 < R) (hMK : 0 ≤ MK) (hK' : ∀ x : K, ‖(x : E)‖ ≤ MK)
    (hint : SatIntegrable (fpClass hP 𝒮 h)) (k : ℕ) {η δ : ℝ} (hη : 0 ≤ η) (hδ : 0 < δ)
    (hδ1 : δ < 1) :
    ((Measure.pi fun _ : Fin n => P) {D | ¬ ∀ fhat,
        IsEmpMinimizer L D
          (hypothesisClass (linearReadouts (ambientFeature K) R) (fpClass hP 𝒮 h) k) η fhat →
        risk L P fhat - sInf (risk L P '' fpTargetClass hP 𝒮 h R) ≤
          L.β * (R * Metric.diam (Set.univ : Set K) * (1 - h * μ) ^ k) + η +
            bvDev L n δ (R * MK / √n + 12 * 1 * R / √n * satVinf (fpClass hP 𝒮 h))}
      ).toReal ≤ δ :=
  LeanDeepgen.prop_ode_fixedpoint hK hP hμ hμΛ h𝒮 hh0 hh hn P L hℓ hb hβ hR hMK hK' hint k hη hδ
    hδ1

/-- **prop:ode-horizon** (App. M), rigorous form (D33). Fixed-horizon Euler integration with
linear readouts: excess risk at depth `k` at most
`β_ℓ R (Λ_s M_s + Λ_τ) e^{Λ_s T} T²/(2k) + η + bvDev(R M_K/√n + 12 R V_∞/√n)` with probability
`1 − δ` (PL regime). -/
theorem prop_ode_horizon {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K : Set E} {proj : E → E} [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace.SeparableSpace E] {Y : Type*} [MeasurableSpace Y]
    (hK : IsCompact K) (hP : IsProjectionOnto K proj) {𝒮 : Set (K → ℝ → E)} {Λs : ℝ≥0}
    (h𝒮 : ∀ s ∈ 𝒮, ∀ τ, LipschitzWith Λs (fun x => s x τ)) {h₀ T : ℝ} (hT : 0 ≤ T)
    {s : K → ℝ → E} (hs : s ∈ 𝒮) {s' : E → ℝ → E} (hss' : ∀ (x : K) (τ : ℝ), s x τ = s' x τ)
    {Λτ Ms : ℝ≥0} (hs'x : ∀ τ, LipschitzWith Λs (fun x => s' x τ))
    (hs'τ : ∀ x, LipschitzWith Λτ (s' x)) (hMs : ∀ x τ, ‖s' x τ‖ ≤ Ms) {flow : K → E}
    (hflowm : Measurable flow)
    (hflow : ∀ x₀ : K, ∃ x : ℝ → E, x 0 = x₀ ∧ (∀ t ∈ Set.Icc 0 T, HasDerivAt x (s' (x t) t) t) ∧
      flow x₀ = x T)
    {k : ℕ} (hk : 0 < k) (hkh : T / k ≤ h₀)
    (hinv : ∀ (x : K) (τ : ℝ), (x : E) + (T / k) • s x τ ∈ K)
    {n : ℕ} (hn : 0 < n) (P : Measure (K × Y)) [IsProbabilityMeasure P]
    (L : BoundedLipschitzLoss Y) (hℓ : Measurable (Function.uncurry L.ℓ)) (hb : 0 < L.b)
    (hβ : 0 ≤ L.β) {R MK : ℝ} (hR : 0 < R) (hMK : 0 ≤ MK) (hK' : ∀ x : K, ‖(x : E)‖ ≤ MK)
    (hint : SchemeIntegrable hP 𝒮 h₀ T) {η δ : ℝ} (hη : 0 ≤ η) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ((Measure.pi fun _ : Fin n => P) {D | ¬ ∀ fhat,
        IsEmpMinimizer L D
          (compClass (linearReadouts (ambientFeature K) R) (schemeBall hP 𝒮 h₀ T k)) η fhat →
        risk L P fhat - sInf (risk L P '' linearReadouts flow R) ≤
          L.β * (R * ((Λs * Ms + Λτ) * Real.exp (Λs * T) / 2 * T ^ 2 / k)) + η +
            bvDev L n δ (R * MK / √n + 12 * 1 * R / √n * schemeVinf hP 𝒮 h₀ T)}
      ).toReal ≤ δ :=
  LeanDeepgen.prop_ode_horizon hK hP h𝒮 hT hs hss' hs'x hs'τ hMs hflowm hflow hk hkh hinv hn P L
    hℓ hb hβ hR hMK hK' hint hη hδ hδ1

end ODE

/-! ## Bonus general results (`FoML/ToFoML/*`) -/

section BernoulliSudakov

open Real
open scoped BigOperators

/-- **thm:bernoulli-sudakov** (Talagrand's Bernoulli minoration, App. C). For `M` vectors that
are `ρ`-separated in the normalized Euclidean metric and bounded by `R`, the Rademacher supremum
is at least `c min{ρ √(log M / n), ρ²/R}`. -/
theorem thm_bernoulli_sudakov :
    ∃ c : ℝ, 0 < c ∧ ∀ (n M : ℕ) (u : Fin M → Fin n → ℝ) (ρ R : ℝ), 0 < n → 0 < ρ → 0 < R →
      (∀ j l, j ≠ l → ρ ≤ Real.sqrt ((1 / (n : ℝ)) * ∑ i, |u j i - u l i| ^ 2)) →
      (∀ j i, |u j i| ≤ R) →
      c * min (ρ * Real.sqrt (Real.log M / n)) (ρ ^ 2 / R) ≤
        (Fintype.card (Signs n) : ℝ)⁻¹ *
          ∑ σ : Signs n, ⨆ j, (n : ℝ)⁻¹ * ∑ i : Fin n, (σ i : ℝ) * u j i :=
  FoML.ToFoML.bernoulli_sudakov

end BernoulliSudakov

section Dudley

open scoped NNReal ENNReal BigOperators
open Metric MeasureTheory Real
open FoML.ToMathlib

/-- **thm:dudley-subgaussian** (Dudley's entropy bound on a finite probability space; W4).
Stated with the auxiliary definitions of `FoML/ToFoML/DudleySubGaussian` unfolded: for a process
`Y` on a totally bounded index set `F` with sub-Gaussian increments (tail
`ℙ(|Y_s − Y_t| > u) ≤ 2 exp(−u²/(2σ² d(s,t)²))` under the uniform measure on `Ω`) and `Y_{t₀} = 0`,
`𝔼 sup_{t∈F} Y_t ≤ 12 σ ∫₀^{diam F} √log N(F, ε) dε`. -/
theorem thm_dudley_subgaussian {Ω : Type*} [Fintype Ω] {T : Type*} [PseudoMetricSpace T]
    [Nonempty Ω] {F : Set T} (hF : TotallyBounded F)
    {t₀ : T} (ht₀ : t₀ ∈ F) (Y : T → Ω → ℝ) (hY₀ : ∀ ω, Y t₀ ω = 0) {σ : ℝ} (hσ : 0 < σ)
    (hY : (∀ s ∈ F, ∀ t ∈ F, dist s t = 0 → ∀ ω, Y s ω = Y t ω) ∧
      ∀ s ∈ F, ∀ t ∈ F, ∀ u : ℝ, 0 < u →
        ((Finset.univ.filter fun ω => u < |Y s ω - Y t ω|).card : ℝ) / Fintype.card Ω ≤
          2 * Real.exp (-(u ^ 2 / (2 * σ ^ 2 * dist s t ^ 2))))
    (hint : IntervalIntegrable
      (fun ε => Real.sqrt (Real.log ((coveringNumber (Real.toNNReal ε) F : ℝ≥0∞).toReal)))
      volume 0 (diam F)) :
    (Fintype.card Ω : ℝ)⁻¹ * ∑ ω, (⨆ t : F, Y t ω) ≤
      12 * σ * ∫ ε in (0 : ℝ)..(diam F),
        Real.sqrt (Real.log ((coveringNumber (Real.toNNReal ε) F : ℝ≥0∞).toReal)) :=
  FoML.ToFoML.dudley_subgaussian_finite_space hF ht₀ Y hY₀ hσ hY hint

end Dudley

/-! ## Sec. 4 / App. F: the covering envelope and the reachable radius (`Growth/Envelope`) -/

section Envelope

open scoped NNReal ENNReal Real UniformConvergence
open Metric MeasureTheory Set
open FoML.ToMathlib

/-- **prop:envelope** (= `prop:envelope-restated`, App. "Proof of prop:envelope"). Layerwise covering
envelope: for `Λ`-Lipschitz layers, `N(B(k,F), d_∞, ε) ≤ 1 + ∑_{m=1}^k N(F, d_∞, ε/S_m(Λ))^m
≤ 1 + k N(F, d_∞, ε/S_k(Λ))^k` (external covering numbers; all `k ≥ 0`, N1). -/
theorem prop_envelope {X : Type*} [PseudoEMetricSpace X] {F : Set (X → X)} {Λ : ℝ≥0} (hF : ∀ f ∈ F, LipschitzWith Λ f) (ε : ℝ≥0) (k : ℕ) :
    externalCoveringNumber (X := UnifMaps X) ε (wordBall F k) ≤
        1 + ∑ m ∈ Finset.Icc 1 k,
          externalCoveringNumber (X := UnifMaps X) (ε / geomSum Λ m) F ^ m ∧
      1 + ∑ m ∈ Finset.Icc 1 k,
          externalCoveringNumber (X := UnifMaps X) (ε / geomSum Λ m) F ^ m ≤
        1 + k * externalCoveringNumber (X := UnifMaps X) (ε / geomSum Λ k) F ^ k :=
  LeanDeepgen.prop_envelope hF ε k

/-- **cor:envelope-profiles** (a), (b). Entropy bounds in `d_∞` and entropy-integral bounds for
`V_k(S)` under parametric (`log N(F,ε) ≤ p log(C/ε)`) and nonparametric (`log N(F,ε) ≤ c ε^{-q}`)
layer classes; finiteness of `N(F, ε)` is assumed and the `V_k(S)` bounds carry a factor `2` in the
scale (`2C`, `(2 S_k)^{q/2}`) from the internal/external comparison (N2). -/
theorem cor_envelope_profiles {X : Type*} [PseudoMetricSpace X] {F : Set (X → X)} {Λ : ℝ≥0} (hF : ∀ f ∈ F, LipschitzWith Λ f) {Dbar : ℝ} (hDbar : 0 < Dbar)
    {n : ℕ} (S : Fin n → X) {k : ℕ} (hk : 1 ≤ k) (hD : empDiam S (wordBall F k) ≤ Dbar) :
    (∀ p C : ℝ, 0 ≤ p → Dbar ≤ C →
      (∀ ε : ℝ≥0, 0 < ε → (ε : ℝ) ≤ C → externalCoveringNumber (X := UnifMaps X) ε F ≠ ⊤) →
      (∀ ε : ℝ≥0, 0 < ε → (ε : ℝ) ≤ C →
        Real.log (externalCoveringNumber (X := UnifMaps X) ε F : ℝ≥0∞).toReal ≤
          p * Real.log (C / ε)) →
      (∀ ε : ℝ≥0, 0 < ε → (ε : ℝ) ≤ Dbar →
        Real.log (externalCoveringNumber (X := UnifMaps X) ε (wordBall F k) : ℝ≥0∞).toReal ≤
          Real.log (k + 1) + k * p * (Real.log (C / ε) + Real.log (geomSum Λ k))) ∧
      entropyIntegral (Y := EmpSpace S) (empDiam S (wordBall F k)) (wordBall F k) ≤
        Dbar * (√(Real.log (k + 1)) + √(k * p * Real.log k)
          + k * √(p * Real.log ((max 1 Λ : ℝ≥0) : ℝ))
          + √(k * p) * (√(Real.log (2 * C / Dbar)) + √π / 2))) ∧
    (∀ c q : ℝ, 0 ≤ c → 0 < q → q < 2 →
      (∀ ε : ℝ≥0, 0 < ε → externalCoveringNumber (X := UnifMaps X) ε F ≠ ⊤) →
      (∀ ε : ℝ≥0, 0 < ε →
        Real.log (externalCoveringNumber (X := UnifMaps X) ε F : ℝ≥0∞).toReal ≤
          c * (ε : ℝ) ^ (-q)) →
      (∀ ε : ℝ≥0, 0 < ε →
        Real.log (externalCoveringNumber (X := UnifMaps X) ε (wordBall F k) : ℝ≥0∞).toReal ≤
          Real.log (k + 1) + k * c * ((geomSum Λ k : ℝ) ^ q * (ε : ℝ) ^ (-q))) ∧
      entropyIntegral (Y := EmpSpace S) (empDiam S (wordBall F k)) (wordBall F k) ≤
        Dbar * √(Real.log (k + 1)) +
          √(k * c) * (2 * (geomSum Λ k : ℝ)) ^ (q / 2) * Dbar ^ (1 - q / 2) / (1 - q / 2)) :=
  LeanDeepgen.cor_envelope_profiles hF hDbar S hk hD

/-- **lem:reachable-radius**. Every `g ∈ B(k,F)` maps `B(x₀,R)` into `B(x₀, Λ^k R + c S_k(Λ))` for
`Λ ≥ 1` and into `B(x₀, R + c S_k(Λ))` for `Λ ≤ 1`, and `D_k(S) ≤ 2(Λ₊^k R + c S_k(Λ))` for a
sample in `B(x₀,R)` (`c ≥ 0` made explicit, N3). -/
theorem lem_reachable_radius {X : Type*} [PseudoMetricSpace X] {F : Set (X → X)} {Λ : ℝ≥0} (hF : ∀ f ∈ F, LipschitzWith Λ f) {x₀ : X} {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ f ∈ F, dist (f x₀) x₀ ≤ c) {R : ℝ} (hR : 0 ≤ R) (k : ℕ) :
    (1 ≤ Λ → ∀ g ∈ wordBall F k, ∀ x, dist x x₀ ≤ R →
      dist (g x) x₀ ≤ (Λ : ℝ) ^ k * R + c * geomSum Λ k) ∧
    (Λ ≤ 1 → ∀ g ∈ wordBall F k, ∀ x, dist x x₀ ≤ R →
      dist (g x) x₀ ≤ R + c * geomSum Λ k) ∧
    (∀ {n : ℕ} (S : Fin n → X), (∀ i, dist (S i) x₀ ≤ R) →
      empDiam S (wordBall F k) ≤ 2 * (((max 1 Λ : ℝ≥0) : ℝ) ^ k * R + c * geomSum Λ k)) :=
  LeanDeepgen.lem_reachable_radius hF hc0 hc hR k

end Envelope

/-! ## App. ODE: explicit entropy of equal-step schemes (`Examples/ODE`) -/

section ODEScheme

open scoped NNReal ENNReal UniformConvergence Topology RealInnerProductSpace
open Metric
open FoML.ToMathlib
open MeasureTheory

/-- **lem:ode-scheme-entropy** (App. ODE). Equal-step Euler schemes with a common drift:
`d_∞(Φ_{s,m}, Φ_{s',m}) ≤ T e^{Λ_s T} ‖s − s'‖_∞` (sup over `K × [0,T]`) and
`N(E_T(k), d_∞, ε) ≤ 1 + k N(𝒮_T, ‖·‖_∞, ε e^{−Λ_s T}/T)` (N4). -/
theorem lem_ode_scheme_entropy {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {K : Set E} {proj : E → E} (hP : IsProjectionOnto K proj) {𝒮 : Set (K → ℝ → E)}
    {Λ : ℝ≥0} (h𝒮 : ∀ s ∈ 𝒮, ∀ τ, LipschitzWith Λ (fun x => s x τ)) {T : ℝ} (hT : 0 ≤ T) :
    (∀ s ∈ 𝒮, ∀ s' ∈ 𝒮, ∀ m : ℕ,
      uniformDist (equalScheme hP s T m) (equalScheme hP s' T m) ≤
        ENNReal.ofReal (T * Real.exp (Λ * T)) *
          edist (restrictDrift T s) (restrictDrift T s')) ∧
    (∀ (k : ℕ) (ε : ℝ≥0),
      externalCoveringNumber (X := UnifMaps K) ε (equalSchemeClass hP 𝒮 T k) ≤
        1 + k * externalCoveringNumber (X := DriftSpace K T)
          (ε / (T * Real.exp (Λ * T)).toNNReal) (restrictDrift T '' 𝒮)) :=
  LeanDeepgen.lem_ode_scheme_entropy hP h𝒮 hT

/-- **lem:ode-scheme-entropy** (entropy-integral consequence). `V_k(S) ≤ D_K √log(k+1)
+ ∫_0^{D_K} √log N(𝒮_T, ‖·‖_∞, ε e^{−Λ_s T}/(2T)) dε` for the class `E_T(k)` (`T > 0`, finite covering
numbers of the drift class and integrability of the majorant assumed; factor `2` in the radius, N4). -/
theorem equalSchemeClass_profile {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {K : Set E} {proj : E → E} (hK : IsCompact K) (hP : IsProjectionOnto K proj)
    {𝒮 : Set (K → ℝ → E)} {Λ : ℝ≥0} (h𝒮 : ∀ s ∈ 𝒮, ∀ τ, LipschitzWith Λ (fun x => s x τ))
    {T : ℝ} (hT : 0 < T) {n : ℕ} (S : Fin n → K) (k : ℕ)
    (hfin : ∀ ρ : ℝ≥0, 0 < ρ →
      externalCoveringNumber (X := DriftSpace K T) ρ (restrictDrift T '' 𝒮) ≠ ⊤)
    (hint : IntervalIntegrable (fun ε : ℝ => √(Real.log (externalCoveringNumber
      (X := DriftSpace K T) (ε.toNNReal / 2 / (T * Real.exp (Λ * T)).toNNReal)
      (restrictDrift T '' 𝒮) : ℝ≥0∞).toReal)) volume 0 (Metric.diam (Set.univ : Set K))) :
    entropyIntegral (Y := EmpSpace S) (empDiam S (equalSchemeClass hP 𝒮 T k))
        (equalSchemeClass hP 𝒮 T k) ≤
      Metric.diam (Set.univ : Set K) * √(Real.log (k + 1)) +
        ∫ ε in (0 : ℝ)..Metric.diam (Set.univ : Set K), √(Real.log (externalCoveringNumber
          (X := DriftSpace K T) (ε.toNNReal / 2 / (T * Real.exp (Λ * T)).toNNReal)
          (restrictDrift T '' 𝒮) : ℝ≥0∞).toReal) :=
  LeanDeepgen.equalSchemeClass_profile hK hP h𝒮 hT S k hfin hint

end ODEScheme

/-! ## App. CoT: empirical saturation for branching steps (`Examples/ChainOfThought`) -/

section CoTSample

open scoped NNReal ENNReal UniformConvergence Topology Real
open Metric
open FoML.ToMathlib
open MeasureTheory

/-- **lem:cot-branch-sample** (App. CoT). Empirical saturation for branching steps: for every sample
and every `ε > 0`, `N(B(k,F_b), d_S, ε) ≤ 1 + r + ∑_{j=1}^k min{r^j, n, ⌊ε^{-2}⌋} ≤ 1 + r + k min{n, ⌊ε^{-2}⌋}`,
and `V_k(S) ≤ √log(k+1) + √log(1+r) + √(2 log 2) + √(π/2)` (additive `√(2 log 2)` from the
internal/external comparison, N5). -/
theorem lem_cot_branch_sample {θ : ℝ≥0} {r : ℕ} [Fact (0 < θ)] [Fact (θ < 1)] {n : ℕ} (S : Fin n → SeqSpace (BranchAlphabet r) θ) (k : ℕ) :
    (∀ ε : ℝ≥0, 0 < ε →
      externalCoveringNumber (X := EmpSpace S) ε (wordBall (branchClass θ) k) ≤
          1 + r + ∑ j ∈ Finset.Icc 1 k, ((min (r ^ j) (min n ⌊ε⁻¹ ^ 2⌋₊) : ℕ) : ℕ∞) ∧
        1 + (r : ℕ∞) + ∑ j ∈ Finset.Icc 1 k, ((min (r ^ j) (min n ⌊ε⁻¹ ^ 2⌋₊) : ℕ) : ℕ∞) ≤
          1 + r + k * ((min n ⌊ε⁻¹ ^ 2⌋₊ : ℕ) : ℕ∞)) ∧
    entropyIntegral (Y := EmpSpace S) (empDiam S (wordBall (branchClass θ) k))
        (wordBall (branchClass θ) k) ≤
      √(Real.log (k + 1)) + √(Real.log (1 + r)) + √(2 * Real.log 2) + √(π / 2) :=
  LeanDeepgen.lem_cot_branch_sample S k

end CoTSample

/-! ## App. ReLU: deep ReLU networks (`Examples/ReLU`) -/

section ReLU

open scoped NNReal ENNReal UniformConvergence Real
open Metric MeasureTheory Set
open FoML.ToMathlib

/-- **lem:relu-layer-covering** (App. ReLU). One ReLU block `Π_K(V relu(Wx+b)+c)` on a bounded state
space `K ⊆ E` (`‖x‖ ≤ R_K`): (a) the parameter-Lipschitz estimate
`d_∞(f_θ, f_θ') ≤ β_W R_K ‖W−W'‖ + β_W ‖b−b'‖ + (β_W R_K+β) ‖V−V'‖ + ‖c−c'‖`; (b) for every `ε > 0`,
`N(F_Λ, d_∞, ε) < ∞` and `log N(F_Λ, d_∞, ε) ≤ p log(1 + C_F/ε)`, `p = 2mw+w+m`,
`C_F = 2(2β_W R_K + β_W + β + 1) max{β_W, β}` (R1). -/
theorem lem_relu_layer_covering {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {K : Set E} {proj : E → E} {w : ℕ} (hP : IsProjectionOnto K proj) {R : ℝ}
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
          Real.log (1 + reluCoverConst R βW β / ε)) := LeanDeepgen.lem_relu_layer_covering hP hR hR0 βW β Λ

/-- **prop:relu-regimes** (App. ReLU), upper bounds. (i) `0 < Λ < 1`: P1' with `A = K`, `L = 0` gives
`N(B(k,F_Λ), d_∞, ε) ≤ N(K, ε/2) + m(ε) N(F_Λ, d_∞, (1−Λ)ε)^{m(ε)} < ∞` for every `k`;
(ii) `Λ ≤ 1`, `K` compact: P1 (2c) saturation, and the envelope profile `O(√(kp log k))`;
(iii) `Λ > 1`: the envelope profile `O(k √(p log Λ))` (`K ≠ ∅`, `D_K ≤ D̄`, `k ≥ 1`; factor `2` in
`log(1 + 2C_F/D̄)` from the internal/external comparison, R2). -/
theorem prop_relu_regimes {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {K : Set E} {proj : E → E} {w : ℕ} (hP : IsProjectionOnto K proj) (hK : Bornology.IsBounded K)
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
            * (√(Real.log (1 + 2 * reluCoverConst R βW β / Dbar)) + √π / 2))) := LeanDeepgen.prop_relu_regimes hP hK hKne hR hR0 βW β Λ

/-- **prop:relu-regimes** (App. ReLU), (iii) lower bound. For `m = 1`, `K = [0,1]` with the clipping
retraction, width `w ≥ 4`, `Λ ≥ 20`, `β_W ≥ 41`, `β ≥ 2`, the two expand-and-reset maps lie in
`F_Λ` and satisfy E2 with separation `1/8`, so `N(B(k,F_Λ), d_∞, ε) ≥ 2^k` for `ε < 1/16` (R3). -/
theorem prop_relu_regimes_iii_lower {w : ℕ} (hw : 4 ≤ w) {βW β Λ : ℝ≥0} (hβW : 41 ≤ βW)
    (hβ : 2 ≤ β) (hΛ : 20 ≤ Λ) (k : ℕ) {ε : ℝ≥0} (hε : ε < 1 / 16) :
    (2 : ℕ∞) ^ k ≤ externalCoveringNumber (X := UnifMaps (Icc (0 : ℝ) 1)) ε
      (wordBall (reluClass isProjectionOnto_clipUnit w βW β Λ) k) := LeanDeepgen.prop_relu_regimes_iii_lower hw hβW hβ hΛ k hε

end ReLU

end LeanDeepgen.Challenge
