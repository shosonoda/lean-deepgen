import Mathlib
import Architect
import LeanDeepgen.Setting.WordBall
import LeanDeepgen.Setting.Metrics
import LeanDeepgen.Setting.Covering
import LeanDeepgen.Growth.Defs
import LeanDeepgen.Profiles.Profiles
import LeanDeepgen.Profiles.LogSplit
import LeanDeepgen.Bounds.Variance
import LeanDeepgen.Examples.Implementation

/-!
# The layerwise covering envelope (paper `prop:envelope`, App. "Proof of prop:envelope")

For a hidden-layer class `F` of `Λ`-Lipschitz self-maps and `S_m(Λ) = ∑_{i<m} Λ^i`
(`geomSum Λ m`, `LeanDeepgen.Growth.Defs`), the external covering numbers of the word balls in
the uniform metric satisfy the *covering envelope*
`N(B(k,F), d_∞, ε) ≤ 1 + ∑_{m=1}^k N(F, d_∞, ε/S_m(Λ))^m ≤ 1 + k N(F, d_∞, ε/S_k(Λ))^k`
(`prop:envelope-restated`, `prop_envelope`).  The proof covers the words of length exactly `m`
by the compositions of the centres of an `ε/S_m`-cover of `F`, using the telescoping estimate
`lem:impl-word-error` of `prop:implementation`(b) (`LeanDeepgen.Examples.Implementation`); only
the Lipschitz constant of the maps of `F` is used, and the centres need not lie in `F`.

* `cor:envelope-profiles` (a) parametric layers (`log N(F, ε) ≤ p log(C/ε)`):
  `envelope_entropy_parametric` (entropy of `B(k,F)` in `d_∞`) and `envelope_profile_parametric`
  (the entropy integral `V_k(S)`); (b) nonparametric layers (`log N(F, ε) ≤ c ε^{-q}`, `q < 2`):
  `envelope_entropy_nonparametric`, `envelope_profile_nonparametric`.
* `lem:reachable-radius`: every `g ∈ B(k,F)` maps `B(x₀, R)` into
  `B(x₀, Λ₊^k R + c S_k(Λ))` with `Λ₊ = max{1, Λ}` (`dist_wordBall_le`,
  `reachable_radius_of_one_le`, `reachable_radius_of_le_one`) and the resulting bound on the
  empirical diameter `D_k(S) ≤ 2(Λ₊^k R + c S_k(Λ))` (`empDiam_wordBall_le_of_reachable`).

## Conventions

The paper's covering numbers are external (closed balls); `V_k(S)` is defined through Mathlib's
*internal* covering number in the empirical metric `d_S` (`entropyIntegral`, `metricEntropy`).
As in `LeanDeepgen.Bounds.Variance`, the two are compared through
`N(A, d_S, ε) ≤ N^ext(A, d_∞, ε/2)` (`lem:covering-empSpace-le-external-unifMaps`), so the
entropy-integral bounds of `cor:envelope-profiles` hold with the scale `ε/2` in the hypothesis
on `F`: in (a) the constant `C` inside the integrated logarithm becomes `2C`, in (b) the factor
`S_k(Λ)^{q/2}` becomes `(2 S_k(Λ))^{q/2}`.  The hypotheses `log N(F, ε) ≤ …` are stated together
with the finiteness `N(F, ε) < ∞` (in Lean `log ∞ = log 0 = 0`, so the logarithmic form alone
would be vacuous at infinite covering numbers).
-/

open scoped NNReal ENNReal Real UniformConvergence
open Metric MeasureTheory Set

open FoML.ToMathlib

namespace LeanDeepgen

/-! ### Elementary properties of the geometric sum -/

section GeomSum

variable {Λ : ℝ≥0} {m k : ℕ}

@[blueprint "lem:envelope-geom-sum-succ"
  (statement := /-- $S_{m+1}(\Lambda) = 1 + \Lambda\,S_m(\Lambda)$. -/)]
theorem geomSum_succ (Λ : ℝ≥0) (m : ℕ) : geomSum Λ (m + 1) = 1 + Λ * geomSum Λ m := by
  simp only [geomSum, Finset.sum_range_succ', pow_zero, Finset.mul_sum, pow_succ']
  ring

@[blueprint "lem:envelope-geom-sum-mono"
  (statement := /-- $m \mapsto S_m(\Lambda)$ is nondecreasing. -/)]
theorem geomSum_mono (Λ : ℝ≥0) : Monotone (geomSum Λ) :=
  monotone_nat_of_le_succ fun m => by
    simp only [geomSum, Finset.sum_range_succ]; exact le_self_add

@[blueprint "lem:envelope-geom-sum-one-le"
  (statement := /-- $S_m(\Lambda) \ge 1$ for $m \ge 1$. -/)]
theorem one_le_geomSum (hm : 1 ≤ m) : 1 ≤ geomSum Λ m := by
  simpa using geomSum_mono Λ hm

@[blueprint "lem:envelope-geom-sum-pos"
  (statement := /-- $S_m(\Lambda) > 0$ for $m \ge 1$. -/)]
theorem geomSum_pos (hm : 1 ≤ m) : 0 < geomSum Λ m :=
  one_pos.trans_le (one_le_geomSum hm)

@[blueprint "lem:envelope-geom-sum-le"
  (statement := /-- With $\Lambda_+ := \max\{1, \Lambda\}$, $S_k(\Lambda) \le k\,\Lambda_+^k$
    (since $\Lambda^i \le \Lambda_+^k$ for $i < k$). -/)]
theorem geomSum_le_mul_pow (Λ : ℝ≥0) (k : ℕ) : geomSum Λ k ≤ k * max 1 Λ ^ k := by
  unfold geomSum
  refine (Finset.sum_le_card_nsmul _ _ (max 1 Λ ^ k) fun i hi => ?_).trans ?_
  · calc Λ ^ i ≤ max 1 Λ ^ i := pow_le_pow_left₀ zero_le (le_max_right _ _) i
      _ ≤ max 1 Λ ^ k := pow_le_pow_right₀ (le_max_left _ _) (Finset.mem_range.1 hi).le
  · simp [nsmul_eq_mul]

end GeomSum

/-! ### Words of length `m` and their representations -/

section Words

variable {X : Type*} {F : Set (X → X)}

@[blueprint "lem:envelope-comp-list-mem-words"
  (statement := /-- If all layers of $u$ lie in $F$ then $f_u \in F^{|u|}$. -/)]
theorem compList_mem_words {u : List (X → X)} (hu : ∀ f ∈ u, f ∈ F) :
    compList u ∈ words F u.length := by
  induction u with
  | nil => simp [words]
  | cons f u ih =>
    exact ⟨f, hu f (List.mem_cons_self ..), compList u,
      ih fun g hg => hu g (List.mem_cons_of_mem f hg), rfl⟩

@[blueprint "lem:envelope-exists-comp-list-of-mem-words"
  (statement := /-- Every $g \in F^m$ is $f_u$ for a list $u$ of elements of $F$ with
    $|u| = m$. -/)]
theorem exists_compList_of_mem_words {m : ℕ} {g : X → X} (hg : g ∈ words F m) :
    ∃ u : List (X → X), (∀ f ∈ u, f ∈ F) ∧ u.length = m ∧ g = compList u := by
  induction m generalizing g with
  | zero =>
    simp only [words, Set.mem_singleton_iff] at hg
    exact ⟨[], by simp, rfl, hg⟩
  | succ m ih =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hg
    obtain ⟨u, hu, hlen, rfl⟩ := ih hb
    refine ⟨a :: u, ?_, by simp [hlen], rfl⟩
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ha
    · exact hu f hf

@[blueprint "lem:envelope-wordball-empty"
  (statement := /-- $B(k, \emptyset) = \{\mathrm{id}\}$. -/)]
theorem wordBall_empty (k : ℕ) : wordBall (∅ : Set (X → X)) k = {id} := by
  induction k with
  | zero => rfl
  | succ k ih => rw [wordBall_succ, ih]; simp

end Words

/-! ### Two generic counting facts -/

section Generic

@[blueprint "lem:one-add-mul-ne-top"
  (statement := /-- If $N < \infty$ then $1 + kN < \infty$ (in $\mathbb N \cup \{\infty\}$). -/)]
theorem one_add_mul_ne_top {N : ℕ∞} (hN : N ≠ ⊤) (k : ℕ) : 1 + k * N ≠ ⊤ := by
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.1 hN
  exact_mod_cast ENat.coe_ne_top (1 + k * n)

@[blueprint "lem:log-one-add-mul-le"
  (statement := /-- For natural numbers $k, N$: $\log(1 + kN) \le \log(k+1) + \log N$
    (with $\log 0 = 0$): $1 + kN \le (k+1)N$ when $N \ge 1$, and $\log 1 = 0$ when $N = 0$. -/)]
theorem log_one_add_mul_le (k N : ℕ) :
    Real.log (1 + k * N) ≤ Real.log (k + 1) + Real.log N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [Nat.cast_zero, mul_zero, add_zero, Real.log_one, Real.log_zero, add_zero]
    exact Real.log_nonneg (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  · have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    calc Real.log (1 + k * N) ≤ Real.log ((k + 1) * N) :=
          Real.log_le_log (by positivity) (by nlinarith)
      _ = Real.log (k + 1) + Real.log N := Real.log_mul (by positivity) (by positivity)

@[blueprint "lem:log-toReal-le-of-le-one-add-mul"
  (statement := /-- If $A \le 1 + kN$ in $\mathbb N \cup \{\infty\}$ with $N < \infty$, then
    $\log A \le \log(k+1) + \log N$ (as real numbers, with $\log \infty = \log 0 = 0$). -/)]
theorem log_toReal_le_of_le_one_add_mul {A N : ℕ∞} (hN : N ≠ ⊤) {k : ℕ} (h : A ≤ 1 + k * N) :
    Real.log (A : ℝ≥0∞).toReal ≤ Real.log (k + 1) + Real.log (N : ℝ≥0∞).toReal := by
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.1 hN
  have h' : A ≤ ((1 + k * n : ℕ) : ℕ∞) := by push_cast; exact h
  have h2 := log_toReal_toENNReal_mono (ENat.coe_ne_top _) h'
  rw [ENat.toENNReal_coe, ENNReal.toReal_natCast] at h2
  rw [ENat.toENNReal_coe, ENNReal.toReal_natCast]
  refine h2.trans ?_
  push_cast
  exact log_one_add_mul_le k n

end Generic

/-! ### The covering envelope -/

section Envelope

variable {X : Type*} [PseudoEMetricSpace X] {F : Set (X → X)} {Λ : ℝ≥0}

@[blueprint "lem:envelope-uniformdist-word"
  (statement := /-- (Uniform form of the telescoping estimate `lem:impl-word-error`.) If every
    $f \in F$ is $\Lambda$-Lipschitz and $d_\infty(f, \tilde f) \le \delta$ for $f \in F$, then
    $d_\infty(f_u, \tilde f_u) \le \delta \sum_{i<|u|} \Lambda^i$ for every list $u$ of layers
    in $F$. -/)]
theorem uniformDist_compList_implWord_le (hF : ∀ f ∈ F, LipschitzWith Λ f)
    (tf : (X → X) → (X → X)) {δ : ℝ} (hδ : 0 ≤ δ)
    (htf : ∀ f ∈ F, uniformDist f (tf f) ≤ ENNReal.ofReal δ)
    (u : List (X → X)) (hu : ∀ f ∈ u, f ∈ F) :
    uniformDist (compList u) (implWord tf u) ≤
      ENNReal.ofReal (δ * ∑ i ∈ Finset.range u.length, (Λ : ℝ) ^ i) :=
  iSup_le fun x => edist_compList_implWord_le hF tf hδ htf u hu x

@[blueprint "lem:envelope-words"
  (statement := /-- (Covering the words of length $m$.) If every $f \in F$ is
    $\Lambda$-Lipschitz then for every $\varepsilon \ge 0$ and $m \ge 0$,
    $$N^{\mathrm{ext}}(F^m, d_\infty, \varepsilon)
      \le N^{\mathrm{ext}}\bigl(F, d_\infty, \varepsilon/S_m(\Lambda)\bigr)^m .$$
    The $M^m$ compositions $c_{i_m} \circ \cdots \circ c_{i_1}$ of the centres of an
    $\varepsilon/S_m(\Lambda)$-cover $\{c_1, \dots, c_M\}$ of $F$ form an $\varepsilon$-cover
    of $F^m$ by the telescoping estimate. -/)]
theorem externalCoveringNumber_words_le (hF : ∀ f ∈ F, LipschitzWith Λ f) (ε : ℝ≥0) (m : ℕ) :
    externalCoveringNumber (X := UnifMaps X) ε (words F m) ≤
      externalCoveringNumber (X := UnifMaps X) (ε / geomSum Λ m) F ^ m := by
  /-- Take a minimal $\varepsilon/S_m$-cover $C$ of $F$ and choose for each $f \in F$ a centre
    $\tilde f \in C$ with $d_\infty(f, \tilde f) \le \varepsilon/S_m$. For a word
    $f_u \in F^m$, $\tilde f_u \in C^m$ and $d_\infty(f_u, \tilde f_u) \le
    (\varepsilon/S_m)\sum_{i<m}\Lambda^i = \varepsilon$; hence $C^m$ is an $\varepsilon$-cover
    of $F^m$ with $|C^m| \le |C|^m$. -/
  set ρ : ℝ≥0 := ε / geomSum Λ m with hρ
  obtain ⟨C, hC, hCe⟩ :=
    exists_isCover_encard_eq_externalCoveringNumber (X := UnifMaps X) ρ F
  have hchoice : ∀ f : X → X, ∃ c : X → X, f ∈ F → c ∈ C ∧ uniformDist f c ≤ ρ := by
    intro f
    by_cases hf : f ∈ F
    · obtain ⟨c, hc, hfc⟩ := hC hf
      exact ⟨c, fun _ => ⟨hc, hfc⟩⟩
    · exact ⟨f, fun h => absurd h hf⟩
  choose tf htf using hchoice
  have htf' : ∀ f ∈ F, uniformDist f (tf f) ≤ ENNReal.ofReal ((ρ : ℝ≥0) : ℝ) := by
    intro f hf
    rw [ENNReal.ofReal_coe_nnreal]
    exact (htf f hf).2
  have hcover : IsCover (X := UnifMaps X) ε (words F m) (words C m) := by
    intro g hg
    obtain ⟨u, hu, hlen, rfl⟩ := exists_compList_of_mem_words hg
    refine ⟨implWord tf u, ?_, ?_⟩
    · have h := compList_mem_words (F := C) (u := u.map tf) (by
        intro c hc
        obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hc
        exact (htf f (hu f hf)).1)
      rwa [List.length_map, hlen] at h
    · calc edist (toUnifMaps (compList u)) (toUnifMaps (implWord tf u))
          = uniformDist (compList u) (implWord tf u) := rfl
        _ ≤ ENNReal.ofReal ((ρ : ℝ) * ∑ i ∈ Finset.range u.length, (Λ : ℝ) ^ i) :=
            uniformDist_compList_implWord_le hF tf ρ.coe_nonneg htf' u hu
        _ = ((ρ * geomSum Λ m : ℝ≥0) : ℝ≥0∞) := by
            rw [hlen, ← coe_geomSum, ← NNReal.coe_mul, ENNReal.ofReal_coe_nnreal]
        _ ≤ ε := by
            rw [ENNReal.coe_le_coe, hρ]
            by_cases hS : geomSum Λ m = 0
            · simp [hS]
            · rw [div_mul_cancel₀ _ hS]
  rw [← hCe]
  exact hcover.externalCoveringNumber_le_encard.trans encard_words_le

@[blueprint "lem:envelope-sum"
  (statement := /-- (First inequality of `prop:envelope`.) If every $f \in F$ is
    $\Lambda$-Lipschitz then for every $k \ge 0$ and $\varepsilon \ge 0$,
    $$N^{\mathrm{ext}}\bigl(B(k,F), d_\infty, \varepsilon\bigr)
      \le 1 + \sum_{m=1}^{k} N^{\mathrm{ext}}\bigl(F, d_\infty,
      \varepsilon/S_m(\Lambda)\bigr)^m .$$ -/)]
theorem envelope_sum (hF : ∀ f ∈ F, LipschitzWith Λ f) (ε : ℝ≥0) (k : ℕ) :
    externalCoveringNumber (X := UnifMaps X) ε (wordBall F k) ≤
      1 + ∑ m ∈ Finset.Icc 1 k,
        externalCoveringNumber (X := UnifMaps X) (ε / geomSum Λ m) F ^ m := by
  /-- $B(k,F) = \{\mathrm{id}\} \cup \bigcup_{m=1}^k F^m$; subadditivity of the external
    covering number under unions and `lem:envelope-words`. Induction on $k$ with
    $B(k+1,F) = B(k,F) \cup F^{k+1}$. -/
  induction k with
  | zero =>
    refine (externalCoveringNumber_le_encard_self _).trans ?_
    simp only [Finset.sum_empty, add_zero, Finset.Icc_eq_empty_of_lt zero_lt_one]
    exact (Set.encard_singleton _).le
  | succ k ih =>
    rw [wordBall_succ_eq_union_words, Finset.sum_Icc_succ_top (by omega), ← add_assoc]
    exact (externalCoveringNumber_union_le _ _ _).trans
      (add_le_add ih (externalCoveringNumber_words_le hF ε (k + 1)))

@[blueprint "lem:envelope-sum-le"
  (statement := /-- (Second inequality of `prop:envelope`.) For every $k \ge 0$ and
    $\varepsilon \ge 0$,
    $$\sum_{m=1}^{k} N^{\mathrm{ext}}\bigl(F, \varepsilon/S_m(\Lambda)\bigr)^m
      \le k\, N^{\mathrm{ext}}\bigl(F, \varepsilon/S_k(\Lambda)\bigr)^k ,$$
    because $S_m(\Lambda) \le S_k(\Lambda)$ for $m \le k$, covering numbers are nonincreasing
    in the radius, and $N^m \le N^k$ for $N \ge 1$ (or $N = 0$, $m, k \ge 1$). -/)]
theorem sum_envelope_le (F : Set (X → X)) (Λ : ℝ≥0) (ε : ℝ≥0) (k : ℕ) :
    ∑ m ∈ Finset.Icc 1 k, externalCoveringNumber (X := UnifMaps X) (ε / geomSum Λ m) F ^ m ≤
      k * externalCoveringNumber (X := UnifMaps X) (ε / geomSum Λ k) F ^ k := by
  calc ∑ m ∈ Finset.Icc 1 k, externalCoveringNumber (X := UnifMaps X) (ε / geomSum Λ m) F ^ m
      ≤ ∑ _m ∈ Finset.Icc 1 k,
          externalCoveringNumber (X := UnifMaps X) (ε / geomSum Λ k) F ^ k := by
        refine Finset.sum_le_sum fun m hm => ?_
        obtain ⟨hm1, hmk⟩ := Finset.mem_Icc.1 hm
        have h1 : externalCoveringNumber (X := UnifMaps X) (ε / geomSum Λ m) F ≤
            externalCoveringNumber (X := UnifMaps X) (ε / geomSum Λ k) F :=
          externalCoveringNumber_anti
            (div_le_div_of_nonneg_left zero_le (geomSum_pos hm1) (geomSum_mono Λ hmk))
        refine (pow_le_pow_left₀ zero_le h1 m).trans ?_
        by_cases hN : externalCoveringNumber (X := UnifMaps X) (ε / geomSum Λ k) F = 0
        · rw [hN, zero_pow (by omega), zero_pow (by omega)]
        · exact pow_le_pow_right₀ (Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 hN)) hmk
    _ = k * externalCoveringNumber (X := UnifMaps X) (ε / geomSum Λ k) F ^ k := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        simp

@[blueprint "lem:envelope"
  (statement := /-- (Simplified envelope.) If every $f \in F$ is $\Lambda$-Lipschitz then
    for every $k \ge 0$ and $\varepsilon \ge 0$,
    $$N^{\mathrm{ext}}\bigl(B(k,F), d_\infty, \varepsilon\bigr)
      \le 1 + k\, N^{\mathrm{ext}}\bigl(F, d_\infty, \varepsilon/S_k(\Lambda)\bigr)^k .$$ -/)]
theorem envelope (hF : ∀ f ∈ F, LipschitzWith Λ f) (ε : ℝ≥0) (k : ℕ) :
    externalCoveringNumber (X := UnifMaps X) ε (wordBall F k) ≤
      1 + k * externalCoveringNumber (X := UnifMaps X) (ε / geomSum Λ k) F ^ k :=
  (envelope_sum hF ε k).trans (add_le_add le_rfl (sum_envelope_le F Λ ε k))

@[blueprint "prop:envelope-restated"
  (statement := /-- \textbf{(Covering envelope, `prop:envelope` restated.)} Let
    $F \subseteq \mathcal X^{\mathcal X}$ consist of $\Lambda$-Lipschitz maps, $\Lambda \ge 0$,
    and $S_m(\Lambda) = \sum_{i=0}^{m-1}\Lambda^i$. For every $k \ge 0$ and
    $\varepsilon \ge 0$,
    $$N^{\mathrm{ext}}\bigl(B(k,F), d_\infty, \varepsilon\bigr)
      \le 1 + \sum_{m=1}^{k} N^{\mathrm{ext}}\bigl(F, d_\infty, \varepsilon/S_m(\Lambda)\bigr)^m
      \le 1 + k\, N^{\mathrm{ext}}\bigl(F, d_\infty, \varepsilon/S_k(\Lambda)\bigr)^k .$$
    The centres of the covers of $F$ need not belong to $F$ nor be Lipschitz; only the
    Lipschitz constant of the maps in $F$ is used. (In Lean $\varepsilon/S_0 = 0$ and the
    statement holds for $k = 0$ as well.) -/)]
theorem prop_envelope (hF : ∀ f ∈ F, LipschitzWith Λ f) (ε : ℝ≥0) (k : ℕ) :
    externalCoveringNumber (X := UnifMaps X) ε (wordBall F k) ≤
        1 + ∑ m ∈ Finset.Icc 1 k,
          externalCoveringNumber (X := UnifMaps X) (ε / geomSum Λ m) F ^ m ∧
      1 + ∑ m ∈ Finset.Icc 1 k,
          externalCoveringNumber (X := UnifMaps X) (ε / geomSum Λ m) F ^ m ≤
        1 + k * externalCoveringNumber (X := UnifMaps X) (ε / geomSum Λ k) F ^ k :=
  ⟨envelope_sum hF ε k, add_le_add le_rfl (sum_envelope_le F Λ ε k)⟩

end Envelope

/-! ### Profiles from the envelope (`cor:envelope-profiles`) -/

section Profiles

variable {X : Type*} [PseudoEMetricSpace X] {F : Set (X → X)} {Λ : ℝ≥0}

@[blueprint "lem:envelope-ne-top"
  (statement := /-- If $N^{\mathrm{ext}}(F, \varepsilon/S_k(\Lambda)) < \infty$ then
    $N^{\mathrm{ext}}(B(k,F), \varepsilon) < \infty$. -/)]
theorem envelope_ne_top (hF : ∀ f ∈ F, LipschitzWith Λ f) {k : ℕ} {ε : ℝ≥0}
    (hfin : externalCoveringNumber (X := UnifMaps X) (ε / geomSum Λ k) F ≠ ⊤) :
    externalCoveringNumber (X := UnifMaps X) ε (wordBall F k) ≠ ⊤ := by
  obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.1 hfin
  refine ne_top_of_le_ne_top (ENat.coe_ne_top (1 + k * N ^ k)) ((envelope hF ε k).trans ?_)
  rw [← hN]; push_cast; exact le_rfl

@[blueprint "lem:envelope-log"
  (statement := /-- (Logarithmic form of the envelope.) If every $f \in F$ is
    $\Lambda$-Lipschitz, $k \ge 1$ and $N := N^{\mathrm{ext}}(F, \varepsilon/S_k(\Lambda))
    < \infty$, then $\log N^{\mathrm{ext}}(B(k,F), \varepsilon) \le \log(k+1) + k\log N$
    (using $1 + kN^k \le (k+1)N^k$ for $N \ge 1$; for $N = 0$ both sides are $\ge 0 = \log 1$). -/)]
theorem log_envelope_le (hF : ∀ f ∈ F, LipschitzWith Λ f) {k : ℕ} (hk : 1 ≤ k) {ε : ℝ≥0}
    (hfin : externalCoveringNumber (X := UnifMaps X) (ε / geomSum Λ k) F ≠ ⊤) :
    Real.log (externalCoveringNumber (X := UnifMaps X) ε (wordBall F k) : ℝ≥0∞).toReal ≤
      Real.log (k + 1) + k * Real.log
        (externalCoveringNumber (X := UnifMaps X) (ε / geomSum Λ k) F : ℝ≥0∞).toReal := by
  obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.1 hfin
  have h : externalCoveringNumber (X := UnifMaps X) ε (wordBall F k) ≤
      ((1 + k * N ^ k : ℕ) : ℕ∞) := by
    refine (envelope hF ε k).trans ?_
    rw [← hN]; push_cast; exact le_rfl
  have h2 := log_toReal_toENNReal_mono (ENat.coe_ne_top _) h
  rw [ENat.toENNReal_coe, ENNReal.toReal_natCast] at h2
  rw [← hN, ENat.toENNReal_coe, ENNReal.toReal_natCast]
  refine h2.trans ?_
  push_cast
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · rw [Nat.cast_zero, zero_pow (by omega), mul_zero, add_zero, Real.log_one, Real.log_zero,
      mul_zero, add_zero]
    exact Real.log_nonneg (by linarith)
  · have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
    have hNk : (1 : ℝ) ≤ (N : ℝ) ^ k := one_le_pow₀ hN1
    calc Real.log (1 + k * (N : ℝ) ^ k) ≤ Real.log ((k + 1) * (N : ℝ) ^ k) :=
          Real.log_le_log (by positivity) (by nlinarith)
      _ = Real.log (k + 1) + k * Real.log N := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]

@[blueprint "cor:envelope-profiles-a-entropy"
  (statement := /-- (\textbf{Parametric layers}, entropy form of `cor:envelope-profiles`(a).)
    Let every $f \in F$ be $\Lambda$-Lipschitz and suppose $N^{\mathrm{ext}}(F, d_\infty,
    \varepsilon) < \infty$ and $\log N^{\mathrm{ext}}(F, d_\infty, \varepsilon)
    \le p\log(C/\varepsilon)$ for all $0 < \varepsilon \le C$, with $p \ge 0$. Then for
    $k \ge 1$ and
    $0 < \varepsilon \le C$,
    $$\log N^{\mathrm{ext}}\bigl(B(k,F), d_\infty, \varepsilon\bigr)
      \le \log(k+1) + kp\bigl[\log(C/\varepsilon) + \log S_k(\Lambda)\bigr] .$$ -/)]
theorem envelope_entropy_parametric (hF : ∀ f ∈ F, LipschitzWith Λ f) {p C : ℝ}
    (hfin : ∀ ε : ℝ≥0, 0 < ε → (ε : ℝ) ≤ C →
      externalCoveringNumber (X := UnifMaps X) ε F ≠ ⊤)
    (hN : ∀ ε : ℝ≥0, 0 < ε → (ε : ℝ) ≤ C →
      Real.log (externalCoveringNumber (X := UnifMaps X) ε F : ℝ≥0∞).toReal ≤
        p * Real.log (C / ε))
    {k : ℕ} (hk : 1 ≤ k) {ε : ℝ≥0} (hε : 0 < ε) (hεC : (ε : ℝ) ≤ C) :
    Real.log (externalCoveringNumber (X := UnifMaps X) ε (wordBall F k) : ℝ≥0∞).toReal ≤
      Real.log (k + 1) + k * p * (Real.log (C / ε) + Real.log (geomSum Λ k)) := by
  /-- Apply the logarithmic envelope at the radius $\varepsilon/S_k(\Lambda) \le \varepsilon
    \le C$ and the hypothesis on $F$ there; $\log\bigl(C/(\varepsilon/S_k)\bigr)
    = \log(C/\varepsilon) + \log S_k$. -/
  have hS1 : (1 : ℝ) ≤ geomSum Λ k := by exact_mod_cast one_le_geomSum (Λ := Λ) hk
  have hSpos : (0 : ℝ) < geomSum Λ k := by linarith
  have hε' : (0 : ℝ) < ε := hε
  have hεne : (ε : ℝ) ≠ 0 := hε'.ne'
  have hSne : (geomSum Λ k : ℝ) ≠ 0 := hSpos.ne'
  have hC : 0 < C := hε'.trans_le hεC
  have hρ : 0 < ε / geomSum Λ k := div_pos hε (geomSum_pos hk)
  have hρC : ((ε / geomSum Λ k : ℝ≥0) : ℝ) ≤ C := by
    rw [NNReal.coe_div]; exact (div_le_self hε'.le hS1).trans hεC
  have h1 := log_envelope_le hF hk (hfin _ hρ hρC)
  have h2 := hN _ hρ hρC
  have h3 : Real.log (C / ((ε / geomSum Λ k : ℝ≥0) : ℝ)) =
      Real.log (C / ε) + Real.log (geomSum Λ k) := by
    rw [NNReal.coe_div, ← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  rw [h3] at h2
  calc Real.log (externalCoveringNumber (X := UnifMaps X) ε (wordBall F k) : ℝ≥0∞).toReal
      ≤ Real.log (k + 1) + k * Real.log
          (externalCoveringNumber (X := UnifMaps X) (ε / geomSum Λ k) F : ℝ≥0∞).toReal := h1
    _ ≤ Real.log (k + 1) + k * (p * (Real.log (C / ε) + Real.log (geomSum Λ k))) := by
        gcongr
    _ = _ := by ring

@[blueprint "cor:envelope-profiles-b-entropy"
  (statement := /-- (\textbf{Nonparametric layers}, entropy form of
    `cor:envelope-profiles`(b).) Let every $f \in F$ be $\Lambda$-Lipschitz and suppose
    $N^{\mathrm{ext}}(F, d_\infty, \varepsilon) < \infty$ and
    $\log N^{\mathrm{ext}}(F, d_\infty, \varepsilon) \le c\,\varepsilon^{-q}$ for all
    $\varepsilon > 0$, with $c \ge 0$. Then for $k \ge 1$ and $\varepsilon > 0$,
    $$\log N^{\mathrm{ext}}\bigl(B(k,F), d_\infty, \varepsilon\bigr)
      \le \log(k+1) + kc\,S_k(\Lambda)^q\,\varepsilon^{-q} .$$ -/)]
theorem envelope_entropy_nonparametric (hF : ∀ f ∈ F, LipschitzWith Λ f) {c q : ℝ}
    (hfin : ∀ ε : ℝ≥0, 0 < ε → externalCoveringNumber (X := UnifMaps X) ε F ≠ ⊤)
    (hN : ∀ ε : ℝ≥0, 0 < ε →
      Real.log (externalCoveringNumber (X := UnifMaps X) ε F : ℝ≥0∞).toReal ≤
        c * (ε : ℝ) ^ (-q))
    {k : ℕ} (hk : 1 ≤ k) {ε : ℝ≥0} (hε : 0 < ε) :
    Real.log (externalCoveringNumber (X := UnifMaps X) ε (wordBall F k) : ℝ≥0∞).toReal ≤
      Real.log (k + 1) + k * c * ((geomSum Λ k : ℝ) ^ q * (ε : ℝ) ^ (-q)) := by
  /-- Apply the logarithmic envelope at the radius $\varepsilon/S_k(\Lambda)$ and the
    hypothesis on $F$ there; $(\varepsilon/S_k)^{-q} = S_k^q\varepsilon^{-q}$. -/
  have hSpos : (0 : ℝ) < geomSum Λ k := by exact_mod_cast geomSum_pos (Λ := Λ) hk
  have hε' : (0 : ℝ) < ε := hε
  have hρ : 0 < ε / geomSum Λ k := div_pos hε (geomSum_pos hk)
  have h1 := log_envelope_le hF hk (hfin _ hρ)
  have h2 := hN _ hρ
  have h3 : ((ε / geomSum Λ k : ℝ≥0) : ℝ) ^ (-q) = (geomSum Λ k : ℝ) ^ q * (ε : ℝ) ^ (-q) := by
    rw [NNReal.coe_div, Real.rpow_neg (by positivity), Real.div_rpow hε'.le hSpos.le, inv_div,
      div_eq_mul_inv, ← Real.rpow_neg hε'.le]
  rw [h3] at h2
  calc Real.log (externalCoveringNumber (X := UnifMaps X) ε (wordBall F k) : ℝ≥0∞).toReal
      ≤ Real.log (k + 1) + k * Real.log
          (externalCoveringNumber (X := UnifMaps X) (ε / geomSum Λ k) F : ℝ≥0∞).toReal := h1
    _ ≤ Real.log (k + 1) + k * (c * ((geomSum Λ k : ℝ) ^ q * (ε : ℝ) ^ (-q))) := by gcongr
    _ = _ := by ring

end Profiles

section ProfilesIntegral

variable {X : Type*} [PseudoMetricSpace X] {F : Set (X → X)} {Λ : ℝ≥0}

@[blueprint "lem:envelope-metric-entropy-le"
  (statement := /-- (Transfer to the empirical metric.) If every $f \in F$ is
    $\Lambda$-Lipschitz and $N^{\mathrm{ext}}(F, d_\infty, \varepsilon/(2S_k(\Lambda))) < \infty$,
    then $\log N(B(k,F), d_S, \varepsilon) \le \log N^{\mathrm{ext}}(B(k,F), d_\infty,
    \varepsilon/2)$ for every sample $S$ (`lem:covering-empSpace-le-external-unifMaps`). -/)]
theorem metricEntropy_wordBall_le_envelope (hF : ∀ f ∈ F, LipschitzWith Λ f) {n : ℕ}
    (S : Fin n → X) {k : ℕ} {ε : ℝ≥0}
    (hfin : externalCoveringNumber (X := UnifMaps X) (ε / 2 / geomSum Λ k) F ≠ ⊤) :
    metricEntropy (X := EmpSpace S) ε (wordBall F k) ≤
      Real.log (externalCoveringNumber (X := UnifMaps X) (ε / 2) (wordBall F k) : ℝ≥0∞).toReal :=
  log_toReal_toENNReal_mono (envelope_ne_top hF hfin)
    (coveringNumber_empSpace_le_externalCoveringNumber_unifMaps S ε (wordBall F k))

@[blueprint "cor:envelope-profiles-a"
  (statement := /-- \textbf{(Profiles from the envelope: parametric layers,
    `cor:envelope-profiles`(a).)} Let every $f \in F$ be $\Lambda$-Lipschitz, let
    $\overline D > 0$, $C \ge \overline D$, $p \ge 0$, and suppose $N^{\mathrm{ext}}(F, d_\infty,
    \varepsilon) < \infty$ and $\log N^{\mathrm{ext}}(F, d_\infty, \varepsilon) \le
    p\log(C/\varepsilon)$ for all $0 < \varepsilon \le C$. If $D_k(S) \le \overline D$ then,
    for $k \ge 1$, with $\Lambda_+ := \max\{1,\Lambda\}$,
    $$\mathsf V_k(S) \le \overline D\Bigl(\sqrt{\log(k+1)} + \sqrt{kp\log k}
      + k\sqrt{p\log\Lambda_+} + \sqrt{kp}\bigl(\sqrt{\log(2C/\overline D)}
      + \tfrac{\sqrt\pi}{2}\bigr)\Bigr).$$
    (The paper has $C$ in place of $2C$: the factor $2$ is the price of comparing the internal
    covering number in $d_S$ defining $\mathsf V_k(S)$ with the external one in $d_\infty$,
    `lem:covering-empSpace-le-external-unifMaps`.) -/)]
theorem envelope_profile_parametric (hF : ∀ f ∈ F, LipschitzWith Λ f) {p C Dbar : ℝ}
    (hp : 0 ≤ p) (hDbar : 0 < Dbar) (hCD : Dbar ≤ C)
    (hfin : ∀ ε : ℝ≥0, 0 < ε → (ε : ℝ) ≤ C →
      externalCoveringNumber (X := UnifMaps X) ε F ≠ ⊤)
    (hN : ∀ ε : ℝ≥0, 0 < ε → (ε : ℝ) ≤ C →
      Real.log (externalCoveringNumber (X := UnifMaps X) ε F : ℝ≥0∞).toReal ≤
        p * Real.log (C / ε))
    {n : ℕ} (S : Fin n → X) {k : ℕ} (hk : 1 ≤ k) (hD : empDiam S (wordBall F k) ≤ Dbar) :
    entropyIntegral (Y := EmpSpace S) (empDiam S (wordBall F k)) (wordBall F k) ≤
      Dbar * (√(Real.log (k + 1)) + √(k * p * Real.log k)
        + k * √(p * Real.log ((max 1 Λ : ℝ≥0) : ℝ))
        + √(k * p) * (√(Real.log (2 * C / Dbar)) + √π / 2)) := by
  /-- Pointwise, for $0 < \varepsilon \le \overline D$: $\log N(B(k,F), d_S, \varepsilon)
    \le \log N^{\mathrm{ext}}(B(k,F), d_\infty, \varepsilon/2) \le \log(k+1)
    + kp[\log(2C/\varepsilon) + \log S_k]$, with $\log(2C/\varepsilon) = \log(2C/\overline D)
    + \log(\overline D/\varepsilon)$ and $\log S_k \le \log k + k\log\Lambda_+$; take square
    roots termwise and integrate, using $\int_0^{\overline D}\sqrt{\log(\overline D/\varepsilon)}
    \,d\varepsilon = \tfrac{\sqrt\pi}{2}\overline D$. -/
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := by linarith
  have hkp : (0 : ℝ) ≤ k * p := by positivity
  have hC : 0 < C := hDbar.trans_le hCD
  have hΛ1 : (1 : ℝ) ≤ ((max 1 Λ : ℝ≥0) : ℝ) := by exact_mod_cast le_max_left 1 Λ
  have hlogS : Real.log (geomSum Λ k) ≤ Real.log k + k * Real.log ((max 1 Λ : ℝ≥0) : ℝ) := by
    have h := geomSum_le_mul_pow Λ k
    have h' : ((geomSum Λ k : ℝ≥0) : ℝ) ≤ k * ((max 1 Λ : ℝ≥0) : ℝ) ^ k := by
      exact_mod_cast h
    have hS1 : (1 : ℝ) ≤ geomSum Λ k := by exact_mod_cast one_le_geomSum (Λ := Λ) hk
    calc Real.log (geomSum Λ k) ≤ Real.log (k * ((max 1 Λ : ℝ≥0) : ℝ) ^ k) :=
          Real.log_le_log (by linarith) h'
      _ = Real.log k + k * Real.log ((max 1 Λ : ℝ≥0) : ℝ) := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  set A : ℝ := √(Real.log (k + 1)) + √(k * p * Real.log k)
    + k * √(p * Real.log ((max 1 Λ : ℝ≥0) : ℝ)) + √(k * p) * √(Real.log (2 * C / Dbar)) with hA
  have hgint : IntervalIntegrable (fun ε : ℝ => A + √(k * p) * √(Real.log (Dbar / ε)))
      volume 0 Dbar :=
    intervalIntegrable_const.add ((intervalIntegrable_sqrt_log_div hDbar).const_mul _)
  refine (entropyIntegral_le_integral_of_le (empDiam_nonneg S _) hD hgint
    fun ε hε => ?_).trans (le_of_eq ?_)
  · have hε0 : 0 < ε := hε.1
    have hεD : ε ≤ Dbar := hε.2
    have hεr : ((ε.toNNReal : ℝ≥0) : ℝ) = ε := Real.coe_toNNReal ε hε0.le
    have hε2 : 0 < ε.toNNReal / 2 := by positivity
    have hε2C : ((ε.toNNReal / 2 : ℝ≥0) : ℝ) ≤ C := by
      rw [NNReal.coe_div, hεr]; push_cast; linarith
    have hρ : 0 < ε.toNNReal / 2 / geomSum Λ k := div_pos hε2 (geomSum_pos hk)
    have hρC : ((ε.toNNReal / 2 / geomSum Λ k : ℝ≥0) : ℝ) ≤ C := by
      have hS1 : (1 : ℝ) ≤ geomSum Λ k := by exact_mod_cast one_le_geomSum (Λ := Λ) hk
      rw [NNReal.coe_div]
      exact (div_le_self (by positivity) hS1).trans hε2C
    have h1 := metricEntropy_wordBall_le_envelope hF S (k := k) (ε := ε.toNNReal)
      (hfin _ hρ hρC)
    have h2 := envelope_entropy_parametric hF hfin hN hk hε2 hε2C
    have h3 : Real.log (C / ((ε.toNNReal / 2 : ℝ≥0) : ℝ)) =
        Real.log (2 * C / Dbar) + Real.log (Dbar / ε) := by
      rw [NNReal.coe_div, hεr, ← Real.log_mul (by positivity) (by positivity)]
      congr 1
      push_cast
      field_simp
    rw [h3] at h2
    have h4 : metricEntropy (X := EmpSpace S) ε.toNNReal (wordBall F k) ≤
        Real.log (k + 1) + k * p * Real.log k + (k : ℝ) ^ 2 * (p * Real.log ((max 1 Λ : ℝ≥0) : ℝ))
          + k * p * Real.log (2 * C / Dbar) + k * p * Real.log (Dbar / ε) := by
      have h5 : k * p * Real.log (geomSum Λ k) ≤
          k * p * (Real.log k + k * Real.log ((max 1 Λ : ℝ≥0) : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogS hkp
      nlinarith
    calc √(metricEntropy (X := EmpSpace S) ε.toNNReal (wordBall F k))
        ≤ √(Real.log (k + 1) + k * p * Real.log k
            + (k : ℝ) ^ 2 * (p * Real.log ((max 1 Λ : ℝ≥0) : ℝ))
            + k * p * Real.log (2 * C / Dbar) + k * p * Real.log (Dbar / ε)) :=
          Real.sqrt_le_sqrt h4
      _ ≤ √(Real.log (k + 1) + k * p * Real.log k
            + (k : ℝ) ^ 2 * (p * Real.log ((max 1 Λ : ℝ≥0) : ℝ))
            + k * p * Real.log (2 * C / Dbar)) + √(k * p * Real.log (Dbar / ε)) :=
          sqrt_add_le _ _
      _ ≤ √(Real.log (k + 1) + k * p * Real.log k
            + (k : ℝ) ^ 2 * (p * Real.log ((max 1 Λ : ℝ≥0) : ℝ)))
            + √(k * p * Real.log (2 * C / Dbar)) + √(k * p * Real.log (Dbar / ε)) :=
          add_le_add_left (sqrt_add_le _ _) _
      _ ≤ √(Real.log (k + 1)) + √(k * p * Real.log k)
            + √((k : ℝ) ^ 2 * (p * Real.log ((max 1 Λ : ℝ≥0) : ℝ)))
            + √(k * p * Real.log (2 * C / Dbar)) + √(k * p * Real.log (Dbar / ε)) :=
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

@[blueprint "cor:envelope-profiles-b"
  (statement := /-- \textbf{(Profiles from the envelope: nonparametric layers,
    `cor:envelope-profiles`(b).)} Let every $f \in F$ be $\Lambda$-Lipschitz, let
    $\overline D > 0$, $c \ge 0$, $0 < q < 2$, and suppose $N^{\mathrm{ext}}(F, d_\infty,
    \varepsilon) < \infty$ and $\log N^{\mathrm{ext}}(F, d_\infty, \varepsilon) \le
    c\,\varepsilon^{-q}$ for all $\varepsilon > 0$. If $D_k(S) \le \overline D$ then, for
    $k \ge 1$,
    $$\mathsf V_k(S) \le \overline D\sqrt{\log(k+1)}
      + \sqrt{kc}\,\bigl(2S_k(\Lambda)\bigr)^{q/2}\,\frac{\overline D^{\,1-q/2}}{1-q/2} .$$
    (The paper has $S_k(\Lambda)^{q/2}$ in place of $(2S_k(\Lambda))^{q/2}$: the factor $2$ is
    the price of comparing the internal covering number in $d_S$ with the external one in
    $d_\infty$.) -/)]
theorem envelope_profile_nonparametric (hF : ∀ f ∈ F, LipschitzWith Λ f) {c q Dbar : ℝ}
    (hc : 0 ≤ c) (_hq0 : 0 < q) (hq2 : q < 2) (_hDbar : 0 < Dbar)
    (hfin : ∀ ε : ℝ≥0, 0 < ε → externalCoveringNumber (X := UnifMaps X) ε F ≠ ⊤)
    (hN : ∀ ε : ℝ≥0, 0 < ε →
      Real.log (externalCoveringNumber (X := UnifMaps X) ε F : ℝ≥0∞).toReal ≤
        c * (ε : ℝ) ^ (-q))
    {n : ℕ} (S : Fin n → X) {k : ℕ} (hk : 1 ≤ k) (hD : empDiam S (wordBall F k) ≤ Dbar) :
    entropyIntegral (Y := EmpSpace S) (empDiam S (wordBall F k)) (wordBall F k) ≤
      Dbar * √(Real.log (k + 1)) +
        √(k * c) * (2 * (geomSum Λ k : ℝ)) ^ (q / 2) * Dbar ^ (1 - q / 2) / (1 - q / 2) := by
  /-- Pointwise, $\log N(B(k,F), d_S, \varepsilon) \le \log N^{\mathrm{ext}}(B(k,F), d_\infty,
    \varepsilon/2) \le \log(k+1) + kc\,(2S_k)^q\varepsilon^{-q}$, so
    $\sqrt{\log N} \le \sqrt{\log(k+1)} + \sqrt{kc}(2S_k)^{q/2}\varepsilon^{-q/2}$; integrate,
    using $\int_0^{\overline D}\varepsilon^{-q/2}\,d\varepsilon = \overline D^{1-q/2}/(1-q/2)$
    for $q < 2$. -/
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hkc : (0 : ℝ) ≤ k * c := by positivity
  have hSpos : (0 : ℝ) < geomSum Λ k := by exact_mod_cast geomSum_pos (Λ := Λ) hk
  have h2S : (0 : ℝ) ≤ 2 * (geomSum Λ k : ℝ) := by positivity
  have hr : (-1 : ℝ) < -q / 2 := by linarith
  set B : ℝ := √(k * c) * (2 * (geomSum Λ k : ℝ)) ^ (q / 2) with hB
  have hgint : IntervalIntegrable (fun ε : ℝ => √(Real.log (k + 1)) + B * ε ^ (-q / 2))
      volume 0 Dbar :=
    intervalIntegrable_const.add ((intervalIntegral.intervalIntegrable_rpow' hr).const_mul _)
  refine (entropyIntegral_le_integral_of_le (empDiam_nonneg S _) hD hgint
    fun ε hε => ?_).trans (le_of_eq ?_)
  · have hε0 : 0 < ε := hε.1
    have hεr : ((ε.toNNReal : ℝ≥0) : ℝ) = ε := Real.coe_toNNReal ε hε0.le
    have hε2 : 0 < ε.toNNReal / 2 := by positivity
    have hρ : 0 < ε.toNNReal / 2 / geomSum Λ k := div_pos hε2 (geomSum_pos hk)
    have h1 := metricEntropy_wordBall_le_envelope hF S (k := k) (ε := ε.toNNReal) (hfin _ hρ)
    have h2 := envelope_entropy_nonparametric hF hfin hN hk hε2
    have h3 : (geomSum Λ k : ℝ) ^ q * ((ε.toNNReal / 2 : ℝ≥0) : ℝ) ^ (-q) =
        (2 * (geomSum Λ k : ℝ)) ^ q * ε ^ (-q) := by
      rw [NNReal.coe_div, hεr, Real.rpow_neg (by positivity), Real.div_rpow hε0.le (by norm_num),
        Real.mul_rpow (by norm_num) hSpos.le, Real.rpow_neg hε0.le]
      push_cast
      field_simp
    rw [h3] at h2
    have h4 : metricEntropy (X := EmpSpace S) ε.toNNReal (wordBall F k) ≤
        Real.log (k + 1) + k * c * ((2 * (geomSum Λ k : ℝ)) ^ q * ε ^ (-q)) := h1.trans h2
    calc √(metricEntropy (X := EmpSpace S) ε.toNNReal (wordBall F k))
        ≤ √(Real.log (k + 1) + k * c * ((2 * (geomSum Λ k : ℝ)) ^ q * ε ^ (-q))) :=
          Real.sqrt_le_sqrt h4
      _ ≤ √(Real.log (k + 1)) + √(k * c * ((2 * (geomSum Λ k : ℝ)) ^ q * ε ^ (-q))) :=
          sqrt_add_le _ _
      _ = √(Real.log (k + 1)) + B * ε ^ (-q / 2) := by
          have e1 : √((2 * (geomSum Λ k : ℝ)) ^ q) = (2 * (geomSum Λ k : ℝ)) ^ (q / 2) := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_mul h2S]; congr 1; ring
          have e2 : √(ε ^ (-q)) = ε ^ (-q / 2) := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hε0.le]; congr 1; ring
          rw [Real.sqrt_mul hkc, Real.sqrt_mul (Real.rpow_nonneg h2S q), e1, e2, hB]
          ring
  · rw [intervalIntegral.integral_add intervalIntegrable_const
        ((intervalIntegral.intervalIntegrable_rpow' hr).const_mul _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl hr), Real.zero_rpow (by linarith), hB]
    simp only [smul_eq_mul, sub_zero]
    rw [show -q / 2 + 1 = 1 - q / 2 by ring]
    ring

@[blueprint "cor:envelope-profiles"
  (statement := /-- \textbf{(Profiles from the envelope, `cor:envelope-profiles`.)} Let every
    $f \in F$ be $\Lambda$-Lipschitz, $\overline D > 0$, $k \ge 1$ and $D_k(S) \le \overline D$.
    \begin{enumerate}
    \item[(a)] (Parametric layers.) If $N^{\mathrm{ext}}(F, d_\infty, \varepsilon) < \infty$ and
    $\log N^{\mathrm{ext}}(F, d_\infty, \varepsilon) \le p\log(C/\varepsilon)$ for all
    $0 < \varepsilon \le C$, with $p \ge 0$ and $C \ge \overline D$, then for
    $0 < \varepsilon \le \overline D$,
    $\log N^{\mathrm{ext}}(B(k,F), d_\infty, \varepsilon) \le \log(k+1)
    + kp[\log(C/\varepsilon) + \log S_k(\Lambda)]$, and
    $\mathsf V_k(S) \le \overline D\bigl(\sqrt{\log(k+1)} + \sqrt{kp\log k}
    + k\sqrt{p\log\Lambda_+} + \sqrt{kp}\,(\sqrt{\log(2C/\overline D)} + \sqrt\pi/2)\bigr)$.
    \item[(b)] (Nonparametric layers.) If $N^{\mathrm{ext}}(F, d_\infty, \varepsilon) < \infty$
    and $\log N^{\mathrm{ext}}(F, d_\infty, \varepsilon) \le c\,\varepsilon^{-q}$ for all
    $\varepsilon > 0$, with $c \ge 0$ and $0 < q < 2$, then for $\varepsilon > 0$,
    $\log N^{\mathrm{ext}}(B(k,F), d_\infty, \varepsilon) \le \log(k+1)
    + kc\,S_k(\Lambda)^q\varepsilon^{-q}$, and
    $\mathsf V_k(S) \le \overline D\sqrt{\log(k+1)} + \sqrt{kc}\,(2S_k(\Lambda))^{q/2}\,
    \overline D^{\,1-q/2}/(1-q/2)$.
    \end{enumerate}
    See `cor:envelope-profiles-a` and `cor:envelope-profiles-b` for the factors $2$. -/)]
theorem cor_envelope_profiles (hF : ∀ f ∈ F, LipschitzWith Λ f) {Dbar : ℝ} (hDbar : 0 < Dbar)
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
  ⟨fun _p _C hp hCD hfin hN =>
    ⟨fun _ε hε hεD => envelope_entropy_parametric hF hfin hN hk hε (hεD.trans hCD),
      envelope_profile_parametric hF hp hDbar hCD hfin hN S hk hD⟩,
    fun _c _q hc hq0 hq2 hfin hN =>
    ⟨fun _ε hε => envelope_entropy_nonparametric hF hfin hN hk hε,
      envelope_profile_nonparametric hF hc hq0 hq2 hDbar hfin hN S hk hD⟩⟩

end ProfilesIntegral

/-! ### The reachable radius (`lem:reachable-radius`) -/

section Reachable

variable {X : Type*} [PseudoMetricSpace X] {F : Set (X → X)} {Λ : ℝ≥0}

@[blueprint "lem:reachable-radius-core"
  (statement := /-- (Reachable radius, unified form.) Let every $f \in F$ be
    $\Lambda$-Lipschitz, $x_0 \in \mathcal X$, $c \ge 0$ with $d(f(x_0), x_0) \le c$ for all
    $f \in F$, and $R \ge 0$. Then every $g \in B(k,F)$ maps $B(x_0, R)$ into
    $B\bigl(x_0, \Lambda_+^kR + c\,S_k(\Lambda)\bigr)$, $\Lambda_+ := \max\{1,\Lambda\}$:
    for $d(x,x_0) \le \rho$, $d(f(x), x_0) \le d(f(x), f(x_0)) + d(f(x_0), x_0)
    \le \Lambda\rho + c$; iterate. -/)]
theorem dist_wordBall_le (hF : ∀ f ∈ F, LipschitzWith Λ f) {x₀ : X} {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ f ∈ F, dist (f x₀) x₀ ≤ c) {R : ℝ} (hR : 0 ≤ R) {k : ℕ} {g : X → X}
    (hg : g ∈ wordBall F k) {x : X} (hx : dist x x₀ ≤ R) :
    dist (g x) x₀ ≤ ((max 1 Λ : ℝ≥0) : ℝ) ^ k * R + c * geomSum Λ k := by
  induction k generalizing g with
  | zero =>
    simp only [wordBall_zero, Set.mem_singleton_iff] at hg
    subst hg
    simpa using hx
  | succ k ih =>
    have hΛ1 : (1 : ℝ) ≤ ((max 1 Λ : ℝ≥0) : ℝ) := by exact_mod_cast le_max_left 1 Λ
    have hΛle : (Λ : ℝ) ≤ ((max 1 Λ : ℝ≥0) : ℝ) := by exact_mod_cast le_max_right 1 Λ
    have hpow : ((max 1 Λ : ℝ≥0) : ℝ) ^ k ≤ ((max 1 Λ : ℝ≥0) : ℝ) ^ (k + 1) :=
      pow_le_pow_right₀ hΛ1 (Nat.le_succ k)
    have hS : ((geomSum Λ k : ℝ≥0) : ℝ) ≤ geomSum Λ (k + 1) := by
      exact_mod_cast geomSum_mono Λ (Nat.le_succ k)
    have hSsucc : ((geomSum Λ (k + 1) : ℝ≥0) : ℝ) = 1 + Λ * geomSum Λ k := by
      rw [geomSum_succ]; push_cast; ring
    have hS0 : (0 : ℝ) ≤ geomSum Λ k := NNReal.coe_nonneg _
    rcases hg with hg | ⟨a, ha, b, hb, rfl⟩
    · calc dist (g x) x₀ ≤ ((max 1 Λ : ℝ≥0) : ℝ) ^ k * R + c * geomSum Λ k := ih hg
        _ ≤ ((max 1 Λ : ℝ≥0) : ℝ) ^ (k + 1) * R + c * geomSum Λ (k + 1) := by gcongr
    · have hb' := ih hb
      calc dist ((a ∘ b) x) x₀ ≤ dist (a (b x)) (a x₀) + dist (a x₀) x₀ := dist_triangle _ _ _
        _ ≤ Λ * dist (b x) x₀ + c := add_le_add ((hF a ha).dist_le_mul _ _) (hc a ha)
        _ ≤ Λ * (((max 1 Λ : ℝ≥0) : ℝ) ^ k * R + c * geomSum Λ k) + c := by gcongr
        _ = Λ * ((max 1 Λ : ℝ≥0) : ℝ) ^ k * R + c * (1 + Λ * geomSum Λ k) := by ring
        _ ≤ ((max 1 Λ : ℝ≥0) : ℝ) * ((max 1 Λ : ℝ≥0) : ℝ) ^ k * R
              + c * (1 + Λ * geomSum Λ k) := by gcongr
        _ = ((max 1 Λ : ℝ≥0) : ℝ) ^ (k + 1) * R + c * geomSum Λ (k + 1) := by
            rw [hSsucc, pow_succ']

@[blueprint "lem:reachable-radius-expansive"
  (statement := /-- (Reachable radius, $\Lambda \ge 1$.) Under the hypotheses of
    `lem:reachable-radius-core`, if $\Lambda \ge 1$ then every $g \in B(k,F)$ maps $B(x_0,R)$
    into $B\bigl(x_0, \Lambda^kR + c\,S_k(\Lambda)\bigr)$. -/)]
theorem reachable_radius_of_one_le (hF : ∀ f ∈ F, LipschitzWith Λ f) (hΛ : 1 ≤ Λ) {x₀ : X}
    {c : ℝ} (hc0 : 0 ≤ c) (hc : ∀ f ∈ F, dist (f x₀) x₀ ≤ c) {R : ℝ} (hR : 0 ≤ R) {k : ℕ}
    {g : X → X} (hg : g ∈ wordBall F k) {x : X} (hx : dist x x₀ ≤ R) :
    dist (g x) x₀ ≤ (Λ : ℝ) ^ k * R + c * geomSum Λ k := by
  have h := dist_wordBall_le hF hc0 hc hR hg hx
  rwa [max_eq_right hΛ] at h

@[blueprint "lem:reachable-radius-contractive"
  (statement := /-- (Reachable radius, $\Lambda \le 1$.) Under the hypotheses of
    `lem:reachable-radius-core`, if $\Lambda \le 1$ then every $g \in B(k,F)$ maps $B(x_0,R)$
    into $B\bigl(x_0, R + c\,S_k(\Lambda)\bigr)$. -/)]
theorem reachable_radius_of_le_one (hF : ∀ f ∈ F, LipschitzWith Λ f) (hΛ : Λ ≤ 1) {x₀ : X}
    {c : ℝ} (hc0 : 0 ≤ c) (hc : ∀ f ∈ F, dist (f x₀) x₀ ≤ c) {R : ℝ} (hR : 0 ≤ R) {k : ℕ}
    {g : X → X} (hg : g ∈ wordBall F k) {x : X} (hx : dist x x₀ ≤ R) :
    dist (g x) x₀ ≤ R + c * geomSum Λ k := by
  have h := dist_wordBall_le hF hc0 hc hR hg hx
  rwa [max_eq_left hΛ, NNReal.coe_one, one_pow, one_mul] at h

@[blueprint "lem:empdist-le-of-forall"
  (statement := /-- If $d(f(x_i), g(x_i)) \le D$ for every sample point, with $D \ge 0$, then
    $d_S(f,g) \le D$. -/)]
theorem empDist_le_of_forall {n : ℕ} {S : Fin n → X} {f g : X → X} {D : ℝ} (hD : 0 ≤ D)
    (h : ∀ i, dist (f (S i)) (g (S i)) ≤ D) : empDist S f g ≤ D := by
  rw [empDist, Real.sqrt_le_left hD]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [sq_nonneg]
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    calc (1 / (n : ℝ)) * ∑ i, dist (f (S i)) (g (S i)) ^ 2
        ≤ (1 / (n : ℝ)) * ∑ _i : Fin n, D ^ 2 := by
          gcongr with i
          exact h i
      _ = D ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp

@[blueprint "lem:reachable-radius-diam"
  (statement := /-- (Diameter of the reachable states.) Under the hypotheses of
    `lem:reachable-radius-core`, if the sample lies in $B(x_0, R)$ then
    $D_k(S) \le 2\bigl(\Lambda_+^kR + c\,S_k(\Lambda)\bigr)$: bounded in $k$ if
    $\Lambda < 1$, at most linear if $\Lambda = 1$, at most exponential if $\Lambda > 1$. -/)]
theorem empDiam_wordBall_le_of_reachable (hF : ∀ f ∈ F, LipschitzWith Λ f) {x₀ : X} {c : ℝ}
    (hc0 : 0 ≤ c) (hc : ∀ f ∈ F, dist (f x₀) x₀ ≤ c) {R : ℝ} (hR : 0 ≤ R) {n : ℕ}
    {S : Fin n → X} (hS : ∀ i, dist (S i) x₀ ≤ R) (k : ℕ) :
    empDiam S (wordBall F k) ≤ 2 * (((max 1 Λ : ℝ≥0) : ℝ) ^ k * R + c * geomSum Λ k) := by
  /-- $d(f(x_i), g(x_i)) \le d(f(x_i), x_0) + d(x_0, g(x_i)) \le 2\rho$ for
    $f, g \in B(k,F)$; take the supremum. -/
  have hρ : 0 ≤ ((max 1 Λ : ℝ≥0) : ℝ) ^ k * R + c * geomSum Λ k :=
    add_nonneg (mul_nonneg (pow_nonneg (NNReal.coe_nonneg _) _) hR)
      (mul_nonneg hc0 (NNReal.coe_nonneg _))
  refine Real.sSup_le ?_ (by linarith)
  rintro _ ⟨f, hf, g, hg, rfl⟩
  refine empDist_le_of_forall (by linarith) fun i => ?_
  calc dist (f (S i)) (g (S i)) ≤ dist (f (S i)) x₀ + dist x₀ (g (S i)) := dist_triangle _ _ _
    _ = dist (f (S i)) x₀ + dist (g (S i)) x₀ := by rw [dist_comm x₀]
    _ ≤ (((max 1 Λ : ℝ≥0) : ℝ) ^ k * R + c * geomSum Λ k)
          + (((max 1 Λ : ℝ≥0) : ℝ) ^ k * R + c * geomSum Λ k) :=
        add_le_add (dist_wordBall_le hF hc0 hc hR hf (hS i))
          (dist_wordBall_le hF hc0 hc hR hg (hS i))
    _ = _ := by ring

@[blueprint "lem:reachable-radius"
  (statement := /-- \textbf{(Reachable radius.)} Let every $f \in F$ be $\Lambda$-Lipschitz,
    $x_0 \in \mathcal X$, $R \ge 0$, and suppose $d(f(x_0), x_0) \le c$ for all $f \in F$
    (with $c \ge 0$). Then every $g \in B(k,F)$ maps the ball $B(x_0,R)$ into
    $B\bigl(x_0, \Lambda^kR + c\,S_k(\Lambda)\bigr)$ when $\Lambda \ge 1$, and into
    $B\bigl(x_0, R + c\,S_k(\Lambda)\bigr)$ when $\Lambda \le 1$. Consequently, if
    $S \subset B(x_0,R)$, then $D_k(S) \le 2\bigl(\Lambda_+^kR + c\,S_k(\Lambda)\bigr)$ with
    $\Lambda_+ = \max\{1,\Lambda\}$: bounded in $k$ if $\Lambda < 1$, at most linear if
    $\Lambda = 1$, and at most exponential if $\Lambda > 1$. -/)]
theorem lem_reachable_radius (hF : ∀ f ∈ F, LipschitzWith Λ f) {x₀ : X} {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ f ∈ F, dist (f x₀) x₀ ≤ c) {R : ℝ} (hR : 0 ≤ R) (k : ℕ) :
    (1 ≤ Λ → ∀ g ∈ wordBall F k, ∀ x, dist x x₀ ≤ R →
      dist (g x) x₀ ≤ (Λ : ℝ) ^ k * R + c * geomSum Λ k) ∧
    (Λ ≤ 1 → ∀ g ∈ wordBall F k, ∀ x, dist x x₀ ≤ R →
      dist (g x) x₀ ≤ R + c * geomSum Λ k) ∧
    (∀ {n : ℕ} (S : Fin n → X), (∀ i, dist (S i) x₀ ≤ R) →
      empDiam S (wordBall F k) ≤ 2 * (((max 1 Λ : ℝ≥0) : ℝ) ^ k * R + c * geomSum Λ k)) :=
  ⟨fun hΛ _g hg _x hx => reachable_radius_of_one_le hF hΛ hc0 hc hR hg hx,
    fun hΛ _g hg _x hx => reachable_radius_of_le_one hF hΛ hc0 hc hR hg hx,
    fun _S hS => empDiam_wordBall_le_of_reachable hF hc0 hc hR hS k⟩

end Reachable

end LeanDeepgen
