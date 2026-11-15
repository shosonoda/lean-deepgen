import Mathlib
import Architect
import LeanDeepgen.Setting.WordBall
import LeanDeepgen.Setting.Metrics
import LeanDeepgen.Setting.Covering
import LeanDeepgen.Setting.Assumptions
import LeanDeepgen.Growth.Defs
import LeanDeepgen.Profiles.Profiles
import LeanDeepgen.Bounds.Variance
import LeanDeepgen.Examples.ChainOfThought
import LeanDeepgen.Examples.ReLU

/-!
# Worked example: deep ReLU networks, the expand-and-reset maps on a sample
(paper `lem:relu-reset-sample`)

The two expand-and-reset maps `g₀, g₁` of `[0,1]` (`erGen`, `LeanDeepgen.Examples.ReLU`) are a
ping–pong family: `N^ext(B(k,{g₀,g₁}), d_∞, ε) ≥ 2^k` for every `k` and every `ε < 1/16`
(`expandReset_pingpong`, `prop_relu_regimes_iii_lower`).  This file proves that on a sample the
same family saturates, exactly as the branching steps of the chain-of-thought example
(`lem_cot_branch_sample`, `LeanDeepgen.Examples.ChainOfThought`): for every sample
`S = (X₁, …, X_n)` in `[0,1]`, every `k` and every `ε > 0`,

`N^ext(B(k,{g₀,g₁}), d_S, ε) ≤ 1 + 2 + ∑_{j=1}^k min{2^j, n, ⌊ε^{-2}⌋} ≤ 3 + k min{n, ⌊ε^{-2}⌋}`,
`V_k(S) ≤ √log(k+1) + √log 3 + √(2 log 2) + √(π/2)`

(`lem_relu_reset_sample_bounds`, part (ii) of the paper's lemma; the whole lemma, with the closed
form and the disjointness of part (i), is `lem_relu_reset_sample`).  The argument is organized in
three layers.

* **Words that are constant off pairwise disjoint success sets** (section `ResetWords`).  Let
  `f = (f_1, …, f_r)` be self-maps of a pseudometric space of diameter at most `1`, let
  `c_1, …, c_r` be points and let `(C_u)_u` be sets indexed by words such that (a) a nonempty word
  `f_u` equals the constant `c_{u_j}` of its last letter off `C_u` and (b) the sets `C_u` of
  words of the same length are pairwise disjoint.  Then `d_S(f_u, c_{u_j})² ≤ P̂_n(C_u)`
  (`sq_empDist_wordOf_le_of_reset`), `∑_{|u|=j} P̂_n(C_u) ≤ 1`
  (`sum_card_mem_le_of_pairwiseDisjoint`), at most `min{r^j, n, ⌊ε^{-2}⌋}` words of length `j`
  have `P̂_n(C_u) > ε²`, and the covering bound and the entropy-integral bound follow
  (`reset_words_covering`, `reset_words_profile`, `reset_words_sample`).  This is the counting
  argument of `lem:cot-branch-sample`, which uses only (a), (b) and the diameter bound.
* **Ping–pong families with reset** (section `PingPongReset`).  For chambers `U_i` and anchors
  `a_i` with disjoint chambers, reset `f_i(x) = a_i` off `U_i` and `f_i(a_j) = a_i`, the success
  set `C_u` of a word is the set of inputs whose trajectory stays in the chambers
  (`successSet`, `mem_successSet_iff`); it satisfies (a) (`wordOf_eq_anchor_getLast`) and (b)
  (`pairwiseDisjoint_successSet`), whence `pingpong_reset_sample`.  The first two hypotheses are
  those of `cond_e2_pingpong`; the third strengthens its anchor invariance `f_i(A) ⊆ A` and is
  what makes a failed word a constant map (not only an anchor-valued one) off `C_u`.
* **The expand-and-reset maps** (section `ExpandResetSample`).  The chambers `[0,1/4]`,
  `[3/4,1]` are disjoint, the maps reset to the anchors `3/8`, `5/8` off their chambers, and the
  anchors lie outside both chambers, so `g_i(a_j) = a_i` (`erGen_erAnchor`); the state space
  `[0,1]` has diameter `1` (`dist_unitInterval_le_one`).  The closed form and the disjointness of
  the paper's statement (part (i)) are `relu_reset_closed_form` and `relu_reset_disjoint`, the
  two bounds (part (ii)) are `lem_relu_reset_sample_bounds`, and their conjunction is the
  statement of the paper, `lem_relu_reset_sample` (`lem:relu-reset-sample`).

## Conventions

`N^ext(·, d_S, ε)` is the external covering number of the empirical pseudometric space
`EmpSpace S`; `V_k(S)` is `entropyIntegral (empDiam S (wordBall F k)) (wordBall F k)` on
`EmpSpace S`, defined through the internal covering number, which is compared with the external
one at half the scale (the additive `√(2 log 2)`).  Words act from the left, the first letter
first: `wordOf f (i :: u) = wordOf f u ∘ f i`.
-/

open scoped NNReal ENNReal Real
open Metric MeasureTheory

open FoML.ToMathlib

namespace LeanDeepgen

/-! ### Words that are constant off pairwise disjoint success sets -/

section ResetWords

variable {X : Type*} [PseudoMetricSpace X] {r : ℕ} {f : Fin r → X → X} {c : Fin r → X}
  {C : List (Fin r) → Set X}

omit [PseudoMetricSpace X] in
@[blueprint "lem:reset-words-sum-card-le"
  (statement := /-- (Disjoint success sets carry at most the whole sample.) Let $(C_u)_u$ be
    subsets of $\mathcal X$ indexed by words $u \in [r]^{*}$ such that the sets $C_u$,
    $|u| = j$, are pairwise disjoint for every $j$. For every sample $S = (X_1, \dots, X_n)$
    and every $j \ge 0$, $\sum_{|u| = j} \#\{i : X_i \in C_u\} \le n$, i.e.
    $\sum_{|u| = j} \hat P_n(C_u) \le 1$: each $X_i$ lies in at most one set $C_u$ with
    $|u| = j$. -/)]
theorem sum_card_mem_le_of_pairwiseDisjoint [∀ u : List (Fin r), DecidablePred (· ∈ C u)]
    (hdisj : ∀ j : ℕ, {u : List (Fin r) | u.length = j}.PairwiseDisjoint C)
    {n : ℕ} (S : Fin n → X) (j : ℕ) :
    ∑ σ : Fin j → Fin r, (Finset.univ.filter fun i => S i ∈ C (List.ofFn σ)).card ≤ n := by
  /-- Exchange the two sums: for each $i$, at most one word $u$ of length $j$ has
    $X_i \in C_u$, because the sets $C_u$, $|u| = j$, are pairwise disjoint. -/
  calc ∑ σ : Fin j → Fin r, (Finset.univ.filter fun i => S i ∈ C (List.ofFn σ)).card
      = ∑ σ : Fin j → Fin r, ∑ i : Fin n, if S i ∈ C (List.ofFn σ) then 1 else 0 := by
        simp only [Finset.card_filter]
    _ = ∑ i : Fin n, ∑ σ : Fin j → Fin r, if S i ∈ C (List.ofFn σ) then 1 else 0 :=
        Finset.sum_comm
    _ ≤ ∑ _i : Fin n, 1 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← Finset.card_filter]
        refine Finset.card_le_one.2 fun σ hσ σ' hσ' => ?_
        rw [Finset.mem_filter] at hσ hσ'
        by_contra hne
        have hne' : List.ofFn σ ≠ List.ofFn σ' := fun h => hne (List.ofFn_injective h)
        exact Set.disjoint_left.1 (hdisj j (by simp) (by simp) hne') hσ.2 hσ'.2
    _ = n := by simp

@[blueprint "lem:reset-words-sq-empdist-le"
  (statement := /-- \textbf{(Words are close to constants on the sample.)} Let
    $\mathrm{diam}(\mathcal X) \le 1$ and suppose that every nonempty word
    $f_u = f_{u_j} \circ \cdots \circ f_{u_1}$ equals the constant $c_{u_j}$ of its last letter
    off a set $C_u$. Then, for every sample $S$ and every nonempty word $u$,
    $$d_S(f_u, c_{u_j})^2 = \frac1n\sum_{i : X_i \in C_u} d(f_u(X_i), c_{u_j})^2
      \le \hat P_n(C_u) = \frac1n\#\{i : X_i \in C_u\} .$$ -/)]
theorem sq_empDist_wordOf_le_of_reset [∀ u : List (Fin r), DecidablePred (· ∈ C u)]
    (hdiam : ∀ x y : X, dist x y ≤ 1)
    (hreset : ∀ (u : List (Fin r)) (hu : u ≠ []) (x : X), x ∉ C u →
      wordOf f u x = c (u.getLast hu))
    {n : ℕ} (S : Fin n → X) (u : List (Fin r)) (hu : u ≠ []) :
    empDist S (wordOf f u) (fun _ => c (u.getLast hu)) ^ 2 ≤
      (1 / (n : ℝ)) * (Finset.univ.filter fun i => S i ∈ C u).card := by
  /-- The $i$-th term $d(f_u(X_i), c_{u_j})^2$ is at most $1$ if $X_i \in C_u$ (the diameter
    is at most $1$) and vanishes otherwise ($f_u = c_{u_j}$ off $C_u$). -/
  rw [empDist, Real.sq_sqrt (by positivity)]
  gcongr
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_le_sum fun i _ => ?_
  split_ifs with h
  · exact pow_le_one₀ dist_nonneg (hdiam _ _)
  · rw [hreset u hu (S i) h]
    simp

@[blueprint "lem:reset-words-empdist-le"
  (statement := /-- In the setting of `lem:reset-words-sq-empdist-le`, if
    $\#\{i : X_i \in C_u\} \le \varepsilon^2 n$ then $d_S(f_u, c_{u_j}) \le \varepsilon$. -/)]
theorem empDist_wordOf_le_of_reset [∀ u : List (Fin r), DecidablePred (· ∈ C u)]
    (hdiam : ∀ x y : X, dist x y ≤ 1)
    (hreset : ∀ (u : List (Fin r)) (hu : u ≠ []) (x : X), x ∉ C u →
      wordOf f u x = c (u.getLast hu))
    {n : ℕ} (S : Fin n → X) (u : List (Fin r)) (hu : u ≠ []) {ε : ℝ≥0}
    (h : ((Finset.univ.filter fun i => S i ∈ C u).card : ℝ) ≤ (ε : ℝ) ^ 2 * n) :
    empDist S (wordOf f u) (fun _ => c (u.getLast hu)) ≤ ε := by
  have h1 := sq_empDist_wordOf_le_of_reset hdiam hreset S u hu
  have h2 : (1 / (n : ℝ)) * (Finset.univ.filter fun i => S i ∈ C u).card ≤ (ε : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      calc (1 / (n : ℝ)) * (Finset.univ.filter fun i => S i ∈ C u).card
          ≤ (1 / (n : ℝ)) * ((ε : ℝ) ^ 2 * n) := by gcongr
        _ = (ε : ℝ) ^ 2 := by field_simp
  exact (pow_le_pow_iff_left₀ empDist_nonneg ε.coe_nonneg two_ne_zero).1 (h1.trans h2)

@[blueprint "lem:reset-words-covering"
  (statement := /-- \textbf{(Empirical saturation of words that are constant off disjoint
    success sets.)} Let $(\mathcal X, d)$ have diameter at most $1$, let
    $f = (f_1, \dots, f_r)$ be self-maps of $\mathcal X$, $c_1, \dots, c_r \in \mathcal X$, and
    let $(C_u)_u$ be subsets of $\mathcal X$ indexed by words such that (a) (constant off the
    success set) for every nonempty word $u = (u_1, \dots, u_j)$, $f_u(x) = c_{u_j}$ for all
    $x \notin C_u$, and (b) (disjoint success sets) for every $j$ the sets $C_u$, $|u| = j$,
    are pairwise disjoint. Then for every sample $S = (X_1, \dots, X_n)$, every $k \ge 0$ and
    every $\varepsilon > 0$,
    $$N^{\mathrm{ext}}\bigl(B(k,\{f_1, \dots, f_r\}), d_S, \varepsilon\bigr)
      \le 1 + r + \sum_{j=1}^{k}\min\bigl\{r^j,\ n,\ \lfloor\varepsilon^{-2}\rfloor\bigr\} .$$
    Centres: the identity, the $r$ constant maps $c_a$, and for each $1 \le j \le k$ the words
    $u$ of length $j$ with $\hat P_n(C_u) > \varepsilon^2$ (fewer than $\varepsilon^{-2}$ of
    them, at most $n$, at most $r^j$); every other word of length $j$ is within
    $d_S$-distance $\varepsilon$ of the constant map $c_{u_j}$. -/)]
theorem reset_words_covering (hdiam : ∀ x y : X, dist x y ≤ 1)
    (hreset : ∀ (u : List (Fin r)) (hu : u ≠ []) (x : X), x ∉ C u →
      wordOf f u x = c (u.getLast hu))
    (hdisj : ∀ j : ℕ, {u : List (Fin r) | u.length = j}.PairwiseDisjoint C)
    {n : ℕ} (S : Fin n → X) (k : ℕ) {ε : ℝ≥0} (hε : 0 < ε) :
    externalCoveringNumber (X := EmpSpace S) ε (wordBall (Set.range f) k) ≤
      1 + r + ∑ j ∈ Finset.Icc 1 k, ((min (r ^ j) (min n ⌊ε⁻¹ ^ 2⌋₊) : ℕ) : ℕ∞) := by
  classical
  /-- The heavy words of length $j$: those with $\#\{i : X_i \in C_u\} > \varepsilon^2 n$. -/
  set cnt : List (Fin r) → Finset (Fin n) := fun u =>
    Finset.univ.filter fun i => S i ∈ C u with hcnt
  set H : (j : ℕ) → Finset (Fin j → Fin r) := fun j =>
    Finset.univ.filter fun σ => (ε : ℝ) ^ 2 * n < (cnt (List.ofFn σ)).card with hH
  set Ctr : Finset (X → X) :=
    {id} ∪ Finset.univ.image (fun a : Fin r => fun _ => c a) ∪
      (Finset.Icc 1 k).biUnion (fun j => (H j).image fun σ => wordOf f (List.ofFn σ))
    with hCtr
  /-- Counting the heavy words: at most $r^j$, at most $n$, at most
    $\lfloor\varepsilon^{-2}\rfloor$ (the success sets of length $j$ are disjoint). -/
  have hHj : ∀ j, (H j).card ≤ min (r ^ j) (min n ⌊ε⁻¹ ^ 2⌋₊) := by
    intro j
    have hsum := sum_card_mem_le_of_pairwiseDisjoint hdisj S j
    have hsumH : ∑ σ ∈ H j, (cnt (List.ofFn σ)).card ≤ n :=
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun _ _ _ => Nat.zero_le _).trans hsum
    refine le_min ?_ (le_min ?_ ?_)
    · exact (Finset.card_le_univ _).trans (by simp)
    · calc (H j).card = ∑ σ ∈ H j, 1 := Finset.card_eq_sum_ones _
        _ ≤ ∑ σ ∈ H j, (cnt (List.ofFn σ)).card := by
            refine Finset.sum_le_sum fun σ hσ => ?_
            have h := (Finset.mem_filter.1 hσ).2
            have : (0 : ℝ) < (cnt (List.ofFn σ)).card := lt_of_le_of_lt (by positivity) h
            exact_mod_cast this
        _ ≤ n := hsumH
    · rcases (H j).eq_empty_or_nonempty with hHe | hHne
      · rw [hHe, Finset.card_empty]; exact Nat.zero_le _
      · refine Nat.le_floor ?_
        have hn : (0 : ℝ) < n := by
          obtain ⟨σ, hσ⟩ := hHne
          have h := (Finset.mem_filter.1 hσ).2
          have hc : ((cnt (List.ofFn σ)).card : ℝ) ≤ n := by
            exact_mod_cast (Finset.card_le_univ _).trans (by simp)
          by_contra hn
          have hn0 : (n : ℝ) = 0 := le_antisymm (not_lt.1 hn) (Nat.cast_nonneg n)
          rw [hn0, mul_zero] at h
          rw [hn0] at hc
          linarith
        have hlt : ∑ _σ ∈ H j, (ε : ℝ) ^ 2 * n < ∑ σ ∈ H j, ((cnt (List.ofFn σ)).card : ℝ) :=
          Finset.sum_lt_sum_of_nonempty hHne fun σ hσ => (Finset.mem_filter.1 hσ).2
        have hle : ∑ σ ∈ H j, ((cnt (List.ofFn σ)).card : ℝ) ≤ n := by exact_mod_cast hsumH
        rw [Finset.sum_const, nsmul_eq_mul] at hlt
        have hε' : (0 : ℝ) < ε := hε
        have hkey : ((H j).card : ℝ) < ((ε : ℝ)⁻¹) ^ 2 := by
          have h1 : ((H j).card : ℝ) * (ε : ℝ) ^ 2 < 1 := by
            have h := hlt.trans_le hle
            by_contra hcon
            have hcon' : 1 ≤ ((H j).card : ℝ) * (ε : ℝ) ^ 2 := not_lt.1 hcon
            nlinarith [mul_le_mul_of_nonneg_right hcon' hn.le]
          rw [inv_pow, ← one_div, lt_div_iff₀ (by positivity)]
          exact h1
        have : ((H j).card : ℝ≥0) ≤ ε⁻¹ ^ 2 := by
          rw [← NNReal.coe_le_coe]; push_cast; exact hkey.le
        exact this
  have hcard : Ctr.card ≤ 1 + r + ∑ j ∈ Finset.Icc 1 k, min (r ^ j) (min n ⌊ε⁻¹ ^ 2⌋₊) := by
    refine (Finset.card_union_le _ _).trans (add_le_add ?_ ?_)
    · refine (Finset.card_union_le _ _).trans (add_le_add ?_ ?_)
      · simp
      · exact Finset.card_image_le.trans (by simp)
    · refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun j _ => ?_)
      exact Finset.card_image_le.trans (hHj j)
  /-- The cover: a word is its own centre if it is heavy, and is within $\varepsilon$ of the
    constant of its last letter otherwise (`lem:reset-words-empdist-le`). -/
  let Cs : Set (EmpSpace S) := (Ctr : Set (X → X))
  have hcover : IsCover (X := EmpSpace S) ε (wordBall (Set.range f) k) Cs := by
    intro g hg
    obtain ⟨u, hu, rfl⟩ := exists_wordOf_of_mem_wordBall_range hg
    rcases u with _ | ⟨a, u⟩
    · refine ⟨id, Finset.mem_coe.2 ?_, by simp⟩
      rw [hCtr]
      exact Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl (Finset.mem_singleton.2 rfl))))
    · set σ : Fin (a :: u).length → Fin r := fun i => (a :: u).get i with hσ
      have hσu : List.ofFn σ = a :: u := List.ofFn_get _
      have hne : a :: u ≠ [] := List.cons_ne_nil a u
      by_cases hheavy : σ ∈ H (a :: u).length
      · refine ⟨wordOf f (a :: u), Finset.mem_coe.2 ?_, by simp⟩
        rw [hCtr]
        refine Finset.mem_union.2 (Or.inr (Finset.mem_biUnion.2 ⟨(a :: u).length, ?_, ?_⟩))
        · exact Finset.mem_Icc.2 ⟨by simp, hu⟩
        · exact Finset.mem_image.2 ⟨σ, hheavy, by rw [hσu]⟩
      · refine ⟨fun _ => c ((a :: u).getLast hne), Finset.mem_coe.2 ?_, ?_⟩
        · rw [hCtr]
          exact Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inr
            (Finset.mem_image.2 ⟨(a :: u).getLast hne, Finset.mem_univ _, rfl⟩))))
        · have hlight : ((cnt (a :: u)).card : ℝ) ≤ (ε : ℝ) ^ 2 * n := by
            have h := hheavy
            rw [hH, Finset.mem_filter, hσu] at h
            exact not_lt.1 (not_and.1 h (Finset.mem_univ _))
          change edist (toEmpSpace S (wordOf f (a :: u)))
            (toEmpSpace S fun _ => c ((a :: u).getLast hne)) ≤ ε
          rw [edist_dist, dist_empSpace, ← ENNReal.ofReal_coe_nnreal]
          exact ENNReal.ofReal_le_ofReal
            (empDist_wordOf_le_of_reset hdiam hreset S (a :: u) hne hlight)
  calc externalCoveringNumber (X := EmpSpace S) ε (wordBall (Set.range f) k)
      ≤ Cs.encard := hcover.externalCoveringNumber_le_encard
    _ = (Ctr.card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard Ctr
    _ ≤ ((1 + r + ∑ j ∈ Finset.Icc 1 k, min (r ^ j) (min n ⌊ε⁻¹ ^ 2⌋₊) : ℕ) : ℕ∞) := by
        exact_mod_cast hcard
    _ = _ := by push_cast; rfl

@[blueprint "lem:reset-words-profile"
  (statement := /-- \textbf{(Root-logarithmic empirical entropy integral.)} In the setting of
    `lem:reset-words-covering`, for every sample $S$ and every $k$,
    $$\mathsf V_k(S) \le \sqrt{\log(k+1)} + \sqrt{\log(1+r)} + \sqrt{2\log 2} + \sqrt{\pi/2} .$$
    (The additive constant $\sqrt{2\log 2}$ is the price of comparing the internal covering
    number in $d_S$, which defines $\mathsf V_k(S)$, with the external one at half the scale:
    $N(B, d_S, \varepsilon) \le N^{\mathrm{ext}}(B, d_S, \varepsilon/2)
    \le 1 + r + 4k\varepsilon^{-2}$.) -/)]
theorem reset_words_profile (hdiam : ∀ x y : X, dist x y ≤ 1)
    (hreset : ∀ (u : List (Fin r)) (hu : u ≠ []) (x : X), x ∉ C u →
      wordOf f u x = c (u.getLast hu))
    (hdisj : ∀ j : ℕ, {u : List (Fin r) | u.length = j}.PairwiseDisjoint C)
    {n : ℕ} (S : Fin n → X) (k : ℕ) :
    entropyIntegral (Y := EmpSpace S) (empDiam S (wordBall (Set.range f) k))
        (wordBall (Set.range f) k) ≤
      √(Real.log (k + 1)) + √(Real.log (1 + r)) + √(2 * Real.log 2) + √(π / 2) := by
  /-- For $0 < \varepsilon \le 1$: $N(B, d_S, \varepsilon) \le N^{\mathrm{ext}}(B, d_S,
    \varepsilon/2) \le 1 + r + k\lfloor 4\varepsilon^{-2}\rfloor \le (1+r)(k+1)(2/\varepsilon)^2$,
    so $\sqrt{\log N} \le \sqrt{\log(k+1)} + \sqrt{\log(1+r)} + \sqrt{2\log 2}
    + \sqrt2\sqrt{\log(1/\varepsilon)}$; integrate over $(0,1]$ (recall $D_k(S) \le 1$) with
    $\int_0^1\sqrt{\log(1/\varepsilon)}\,d\varepsilon = \sqrt\pi/2$. -/
  set A : ℝ := √(Real.log (k + 1)) + √(Real.log (1 + r)) + √(2 * Real.log 2) with hA
  have hgint : IntervalIntegrable (fun ε : ℝ => A + √2 * √(Real.log (1 / ε))) volume 0 1 :=
    intervalIntegrable_const.add ((intervalIntegrable_sqrt_log_div one_pos).const_mul _)
  refine (entropyIntegral_le_integral_of_le (empDiam_nonneg S _)
    (empDiam_le_of_bounded S zero_le_one hdiam _) hgint fun ε hε => ?_).trans (le_of_eq ?_)
  · have hε0 : 0 < ε := hε.1
    have hε1 : ε ≤ 1 := hε.2
    have hεr : ((ε.toNNReal : ℝ≥0) : ℝ) = ε := Real.coe_toNNReal ε hε0.le
    have hε2 : 0 < ε.toNNReal / 2 := by positivity
    set M : ℕ := 1 + r + k * min n ⌊(ε.toNNReal / 2)⁻¹ ^ 2⌋₊ with hM
    have hcov : coveringNumber (X := EmpSpace S) ε.toNNReal (wordBall (Set.range f) k) ≤
        (M : ℕ∞) := by
      have h := coveringNumber_two_mul_le_externalCoveringNumber (X := EmpSpace S)
        (ε.toNNReal / 2) (wordBall (Set.range f) k)
      rw [show 2 * (ε.toNNReal / 2) = ε.toNNReal by ring] at h
      refine h.trans ((reset_words_covering hdiam hreset hdisj S k hε2).trans ?_)
      refine (cot_branch_sample_sum_le n r k _).trans (le_of_eq ?_)
      rw [hM]; push_cast; rfl
    have h1 := log_toReal_toENNReal_mono (ENat.coe_ne_top M) hcov
    rw [ENat.toENNReal_coe, ENNReal.toReal_natCast] at h1
    have hfloor : ((min n ⌊(ε.toNNReal / 2)⁻¹ ^ 2⌋₊ : ℕ) : ℝ) ≤ (2 * (1 / ε)) ^ 2 := by
      have h2 : ((⌊(ε.toNNReal / 2)⁻¹ ^ 2⌋₊ : ℕ) : ℝ≥0) ≤ (ε.toNNReal / 2)⁻¹ ^ 2 :=
        Nat.floor_le zero_le
      have h3 : (((ε.toNNReal / 2)⁻¹ ^ 2 : ℝ≥0) : ℝ) = (2 * (1 / ε)) ^ 2 := by
        push_cast; rw [hεr]; field_simp
      calc ((min n ⌊(ε.toNNReal / 2)⁻¹ ^ 2⌋₊ : ℕ) : ℝ)
          ≤ ((⌊(ε.toNNReal / 2)⁻¹ ^ 2⌋₊ : ℕ) : ℝ) := by exact_mod_cast min_le_right _ _
        _ ≤ (((ε.toNNReal / 2)⁻¹ ^ 2 : ℝ≥0) : ℝ) := by exact_mod_cast h2
        _ = (2 * (1 / ε)) ^ 2 := h3
    have hsq : (1 : ℝ) ≤ (2 * (1 / ε)) ^ 2 := by
      have : (1 : ℝ) ≤ 2 * (1 / ε) := by
        rw [← div_eq_mul_one_div]; exact (one_le_div hε0).2 (by linarith)
      nlinarith
    have hM' : (M : ℝ) ≤ (1 + r) * (k + 1) * (2 * (1 / ε)) ^ 2 := by
      rw [hM, Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
      have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hQ0 : (0 : ℝ) ≤ (2 * (1 / ε)) ^ 2 := zero_le_one.trans hsq
      nlinarith [mul_le_mul_of_nonneg_left hfloor hk0,
        mul_le_mul_of_nonneg_left hsq (add_nonneg zero_le_one hr0),
        mul_nonneg (mul_nonneg hk0 hr0) hQ0]
    have hlog : Real.log M ≤ Real.log (k + 1) + Real.log (1 + r) + 2 * Real.log 2 +
        2 * Real.log (1 / ε) := by
      have hMpos : (0 : ℝ) < M := by rw [hM]; push_cast; positivity
      calc Real.log M ≤ Real.log ((1 + r) * (k + 1) * (2 * (1 / ε)) ^ 2) :=
            Real.log_le_log hMpos hM'
        _ = Real.log (1 + r) + Real.log (k + 1) + 2 * (Real.log 2 + Real.log (1 / ε)) := by
            rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
              (by positivity), Real.log_pow, Real.log_mul (by norm_num) (by positivity)]
            push_cast; ring
        _ = _ := by ring
    calc √(metricEntropy (X := EmpSpace S) ε.toNNReal (wordBall (Set.range f) k))
        ≤ √(Real.log (k + 1) + Real.log (1 + r) + 2 * Real.log 2 + 2 * Real.log (1 / ε)) :=
          Real.sqrt_le_sqrt (h1.trans hlog)
      _ ≤ √(Real.log (k + 1) + Real.log (1 + r) + 2 * Real.log 2) + √(2 * Real.log (1 / ε)) :=
          sqrt_add_le _ _
      _ ≤ √(Real.log (k + 1)) + √(Real.log (1 + r)) + √(2 * Real.log 2)
            + √(2 * Real.log (1 / ε)) := add_le_add_left (sqrt_add_add_le _ _ _) _
      _ = A + √2 * √(Real.log (1 / ε)) := by
          rw [hA, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) (Real.log (1 / ε))]
  · rw [intervalIntegral.integral_add intervalIntegrable_const
        ((intervalIntegrable_sqrt_log_div one_pos).const_mul _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      integral_sqrt_log_div one_pos, hA]
    simp only [smul_eq_mul, sub_zero, mul_one, one_mul]
    have h22 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
    have h2 : √2 * (√π / 2) = √(π / 2) := by
      rw [Real.sqrt_div Real.pi_pos.le, eq_div_iff (Real.sqrt_pos.2 two_pos).ne']
      linear_combination (√π / 2) * h22
    rw [h2]

@[blueprint "lem:reset-words-sample"
  (statement := /-- \textbf{(Empirical saturation, abstract form of `lem:cot-branch-sample` and
    `lem:relu-reset-sample`(ii).)} Let $(\mathcal X, d)$ have diameter at most $1$, let
    $f = (f_1, \dots, f_r)$ be self-maps of $\mathcal X$, $c_1, \dots, c_r \in \mathcal X$, and
    let $(C_u)_u$ be subsets of $\mathcal X$ indexed by words such that (a) every nonempty word
    $f_u$ equals the constant $c_{u_j}$ of its last letter off $C_u$, and (b) the sets $C_u$ of
    words of the same length are pairwise disjoint. Then for every sample
    $S = (X_1,\dots,X_n)$, every $k \ge 0$ and every $\varepsilon > 0$,
    $$N^{\mathrm{ext}}\bigl(B(k,\{f_1,\dots,f_r\}), d_S, \varepsilon\bigr)
      \le 1 + r + \sum_{j=1}^{k}\min\{r^j, n, \lfloor\varepsilon^{-2}\rfloor\}
      \le 1 + r + k\min\{n, \lfloor\varepsilon^{-2}\rfloor\},$$
    and consequently $\mathsf V_k(S) \le \sqrt{\log(k+1)} + \sqrt{\log(1+r)} + \sqrt{2\log2}
    + \sqrt{\pi/2}$, for every sample and without any assumption on the input distribution. -/)]
theorem reset_words_sample (hdiam : ∀ x y : X, dist x y ≤ 1)
    (hreset : ∀ (u : List (Fin r)) (hu : u ≠ []) (x : X), x ∉ C u →
      wordOf f u x = c (u.getLast hu))
    (hdisj : ∀ j : ℕ, {u : List (Fin r) | u.length = j}.PairwiseDisjoint C)
    {n : ℕ} (S : Fin n → X) (k : ℕ) :
    (∀ ε : ℝ≥0, 0 < ε →
      externalCoveringNumber (X := EmpSpace S) ε (wordBall (Set.range f) k) ≤
          1 + r + ∑ j ∈ Finset.Icc 1 k, ((min (r ^ j) (min n ⌊ε⁻¹ ^ 2⌋₊) : ℕ) : ℕ∞) ∧
        1 + (r : ℕ∞) + ∑ j ∈ Finset.Icc 1 k, ((min (r ^ j) (min n ⌊ε⁻¹ ^ 2⌋₊) : ℕ) : ℕ∞) ≤
          1 + r + k * ((min n ⌊ε⁻¹ ^ 2⌋₊ : ℕ) : ℕ∞)) ∧
    entropyIntegral (Y := EmpSpace S) (empDiam S (wordBall (Set.range f) k))
        (wordBall (Set.range f) k) ≤
      √(Real.log (k + 1)) + √(Real.log (1 + r)) + √(2 * Real.log 2) + √(π / 2) :=
  ⟨fun ε hε => ⟨reset_words_covering hdiam hreset hdisj S k hε,
      cot_branch_sample_sum_le n r k ε⟩,
    reset_words_profile hdiam hreset hdisj S k⟩

end ResetWords

/-! ### Ping–pong families with reset: the success sets of the words -/

section PingPongReset

variable {X : Type*} {r : ℕ} {f : Fin r → X → X} {U : Fin r → Set X} {a : Fin r → X}

@[blueprint "def:reset-success-set"
  (statement := /-- The success set of a word $u = (u_1, \dots, u_j)$ for maps
    $f = (f_1, \dots, f_r)$ and chambers $U_1, \dots, U_r \subseteq \mathcal X$: the set $C_u$
    of inputs whose trajectory stays in the chambers,
    $x \in U_{u_1}$, $f_{u_1}(x) \in U_{u_2}$, \dots,
    $f_{u_{j-1}} \circ \cdots \circ f_{u_1}(x) \in U_{u_j}$. In Lean it is defined by recursion
    on $u$: $C_{\emptyset} = \mathcal X$ and $C_{(i, u)} = U_i \cap f_i^{-1}(C_u)$. -/)]
def successSet (f : Fin r → X → X) (U : Fin r → Set X) : List (Fin r) → Set X
  | [] => Set.univ
  | i :: u => U i ∩ f i ⁻¹' successSet f U u

@[simp, blueprint "lem:reset-success-set-nil"
  (statement := /-- $C_{\emptyset} = \mathcal X$. -/)]
theorem successSet_nil (f : Fin r → X → X) (U : Fin r → Set X) :
    successSet f U [] = Set.univ := rfl

@[simp, blueprint "lem:reset-success-set-cons"
  (statement := /-- $C_{(i, u)} = U_i \cap f_i^{-1}(C_u)$. -/)]
theorem successSet_cons (f : Fin r → X → X) (U : Fin r → Set X) (i : Fin r)
    (u : List (Fin r)) : successSet f U (i :: u) = U i ∩ f i ⁻¹' successSet f U u := rfl

@[blueprint "lem:reset-success-set-iff"
  (statement := /-- (The recursive definition is the trajectory description.)
    $x \in C_u$ if and only if $f_{u_m} \circ \cdots \circ f_{u_1}(x) \in U_{u_{m+1}}$ for
    every $0 \le m < |u|$. -/)]
theorem mem_successSet_iff (u : List (Fin r)) (x : X) :
    x ∈ successSet f U u ↔
      ∀ (m : ℕ) (hm : m < u.length), wordOf f (u.take m) x ∈ U (u[m]'hm) := by
  /-- Induction on $u$. For $u = (i, u')$ the condition at $m = 0$ is $x \in U_i$ and the
    conditions at $m + 1$ are those of $u'$ at the point $f_i(x)$. -/
  induction u generalizing x with
  | nil => simp
  | cons i u ih =>
    rw [successSet_cons, Set.mem_inter_iff, Set.mem_preimage, ih]
    constructor
    · rintro ⟨h0, h⟩ m hm
      cases m with
      | zero => exact h0
      | succ m => exact h m (Nat.lt_of_succ_lt_succ hm)
    · intro h
      exact ⟨h 0 (Nat.succ_pos _), fun m hm => h (m + 1) (Nat.succ_lt_succ hm)⟩

@[blueprint "lem:reset-wordof-anchor"
  (statement := /-- If $f_i(a_j) = a_i$ for all $i, j$ then, on an anchor,
    $f_u(a_b) = a_{u_j}$ where $u_j$ is the last letter of $u$ (and $a_b$ if $u$ is
    empty). -/)]
theorem wordOf_anchor_of_reset (hanchor : ∀ i j, f i (a j) = a i) (u : List (Fin r))
    (b : Fin r) : wordOf f u (a b) = a (u.getLastD b) := by
  /-- Induction on $u$: the first letter $i$ sends $a_b$ to $a_i$. -/
  induction u generalizing b with
  | nil => rfl
  | cons i u ih => rw [wordOf_cons_apply, hanchor, ih, List.getLastD_cons]

@[blueprint "lem:reset-wordof-of-not-mem"
  (statement := /-- (Closed form, failure.) Suppose $f_i(x) = a_i$ for $x \notin U_i$ and
    $f_i(a_j) = a_i$ for all $i, j$. If $x \notin C_u$ then $f_u(x) = a_{u_j}$, the anchor of the
    last letter of $u$: a trajectory that leaves a chamber is reset to an anchor, and each
    later map sends an anchor to its own anchor. -/)]
theorem wordOf_of_not_mem_successSet (hreset : ∀ i, ∀ x, x ∉ U i → f i x = a i)
    (hanchor : ∀ i j, f i (a j) = a i) {u : List (Fin r)} {x : X}
    (hx : x ∉ successSet f U u) (b : Fin r) : wordOf f u x = a (u.getLastD b) := by
  /-- Induction on $u = (i, u')$. If $x \in U_i$ then $f_i(x) \notin C_{u'}$ and the induction
    hypothesis applies at $f_i(x)$; otherwise $f_i(x) = a_i$ (reset) and
    `lem:reset-wordof-anchor` applies. -/
  induction u generalizing x b with
  | nil => exact absurd (Set.mem_univ x) hx
  | cons i u ih =>
    rw [wordOf_cons_apply, List.getLastD_cons]
    by_cases h0 : x ∈ U i
    · exact ih (fun h => hx ⟨h0, h⟩) i
    · rw [hreset i x h0, wordOf_anchor_of_reset hanchor]

@[blueprint "lem:reset-wordof-eq-anchor"
  (statement := /-- \textbf{(Property (a): words are constant off their success sets.)}
    Suppose $f_i(x) = a_i$ for $x \notin U_i$ and $f_i(a_j) = a_i$ for all $i, j$. For a
    nonempty word $u = (u_1, \dots, u_j)$ and $x \notin C_u$,
    $f_u(x) = a_{u_j}$. -/)]
theorem wordOf_eq_anchor_getLast (hreset : ∀ i, ∀ x, x ∉ U i → f i x = a i)
    (hanchor : ∀ i j, f i (a j) = a i) (u : List (Fin r)) (hu : u ≠ []) (x : X)
    (hx : x ∉ successSet f U u) : wordOf f u x = a (u.getLast hu) := by
  obtain ⟨i, u, rfl⟩ := List.exists_cons_of_ne_nil hu
  rw [wordOf_of_not_mem_successSet hreset hanchor hx i, List.getLast_eq_getLastD,
    List.getLastD_cons]

@[blueprint "lem:reset-success-set-unique"
  (statement := /-- If the chambers are pairwise disjoint, words of the same length with a
    common successful input coincide: if $x \in C_u \cap C_v$ and $|u| = |v|$ then
    $u = v$. -/)]
theorem successSet_unique (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j)) {u v : List (Fin r)}
    {x : X} (hu : x ∈ successSet f U u) (hv : x ∈ successSet f U v)
    (hlen : u.length = v.length) : u = v := by
  /-- Induction on the common length. The first letters agree because
    $x \in U_{u_1} \cap U_{v_1}$ and distinct chambers are disjoint; the tails agree by the
    induction hypothesis at $f_{u_1}(x)$. -/
  induction u generalizing v x with
  | nil =>
    cases v with
    | nil => rfl
    | cons j v => simp at hlen
  | cons i u ih =>
    cases v with
    | nil => simp at hlen
    | cons j v =>
      obtain ⟨hi, hu'⟩ := hu
      obtain ⟨hj, hv'⟩ := hv
      have hij : i = j := by
        by_contra hne
        exact Set.disjoint_left.1 (hdisj i j hne) hi hj
      subst hij
      rw [ih hu' hv' (by simpa using hlen)]

@[blueprint "lem:reset-success-set-disjoint"
  (statement := /-- \textbf{(Property (b): disjoint success sets.)} If the chambers are
    pairwise disjoint then, for every $j$, the success sets $C_u$, $|u| = j$, are pairwise
    disjoint. -/)]
theorem pairwiseDisjoint_successSet (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j)) (j : ℕ) :
    {u : List (Fin r) | u.length = j}.PairwiseDisjoint (successSet f U) := by
  intro u hu v hv hne
  exact Set.disjoint_left.2 fun x hxu hxv =>
    hne (successSet_unique hdisj hxu hxv (hu.trans hv.symm))

@[blueprint "lem:pingpong-reset-sample"
  (statement := /-- \textbf{(Empirical saturation of ping–pong families with reset.)} Let
    $(\mathcal X, d)$ have diameter at most $1$ and let $f = (f_1, \dots, f_r)$ be self-maps
    with chambers $U_i \subseteq \mathcal X$ and anchors $a_i \in \mathcal X$ such that
    (1) $U_i \cap U_j = \emptyset$ for $i \ne j$, (2) $f_i(x) = a_i$ for $x \notin U_i$, and
    (3) $f_i(a_j) = a_i$ for all $i, j$ (e.g. the anchors lie outside all chambers). Then for
    every sample $S = (X_1,\dots,X_n)$, every $k \ge 0$ and every $\varepsilon > 0$,
    $$N^{\mathrm{ext}}\bigl(B(k,\{f_1,\dots,f_r\}), d_S, \varepsilon\bigr)
      \le 1 + r + \sum_{j=1}^{k}\min\{r^j, n, \lfloor\varepsilon^{-2}\rfloor\}
      \le 1 + r + k\min\{n, \lfloor\varepsilon^{-2}\rfloor\},$$
    and $\mathsf V_k(S) \le \sqrt{\log(k+1)} + \sqrt{\log(1+r)} + \sqrt{2\log2}
    + \sqrt{\pi/2}$. (Conditions (1) and (2) are those of `cond:e2-pingpong`; (3) strengthens
    its anchor invariance $f_i(A) \subseteq A$.) -/)]
theorem pingpong_reset_sample [PseudoMetricSpace X] (f : Fin r → X → X) (U : Fin r → Set X)
    (a : Fin r → X) (hdiam : ∀ x y : X, dist x y ≤ 1)
    (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hreset : ∀ i, ∀ x, x ∉ U i → f i x = a i) (hanchor : ∀ i j, f i (a j) = a i)
    {n : ℕ} (S : Fin n → X) (k : ℕ) :
    (∀ ε : ℝ≥0, 0 < ε →
      externalCoveringNumber (X := EmpSpace S) ε (wordBall (Set.range f) k) ≤
          1 + r + ∑ j ∈ Finset.Icc 1 k, ((min (r ^ j) (min n ⌊ε⁻¹ ^ 2⌋₊) : ℕ) : ℕ∞) ∧
        1 + (r : ℕ∞) + ∑ j ∈ Finset.Icc 1 k, ((min (r ^ j) (min n ⌊ε⁻¹ ^ 2⌋₊) : ℕ) : ℕ∞) ≤
          1 + r + k * ((min n ⌊ε⁻¹ ^ 2⌋₊ : ℕ) : ℕ∞)) ∧
    entropyIntegral (Y := EmpSpace S) (empDiam S (wordBall (Set.range f) k))
        (wordBall (Set.range f) k) ≤
      √(Real.log (k + 1)) + √(Real.log (1 + r)) + √(2 * Real.log 2) + √(π / 2) :=
  reset_words_sample hdiam (wordOf_eq_anchor_getLast hreset hanchor)
    (pairwiseDisjoint_successSet hdisj) S k

end PingPongReset

/-! ### The expand-and-reset maps on a sample (`lem:relu-reset-sample`) -/

section ExpandResetSample

@[blueprint "lem:relu-unit-interval-diam"
  (statement := /-- The state space $[0,1]$ has diameter $1$: $|x - y| \le 1$ for
    $x, y \in [0,1]$. -/)]
theorem dist_unitInterval_le_one (x y : Set.Icc (0 : ℝ) 1) : dist x y ≤ 1 := by
  rw [Subtype.dist_eq, Real.dist_eq, abs_sub_le_iff]
  constructor <;> linarith [x.2.1, x.2.2, y.2.1, y.2.2]

@[blueprint "lem:relu-er-anchor-reset"
  (statement := /-- $g_i(a_j) = a_i$ for all $i, j \in \{0, 1\}$: the anchors lie outside both
    chambers (`lem:relu-er-anchor-not-mem`), and each map sends every point outside its chamber
    to its own anchor (`lem:relu-er-reset`). -/)]
theorem erGen_erAnchor (i j : Fin 2) : erGen i (erAnchor j) = erAnchor i :=
  erGen_reset i (erAnchor j) (erAnchor_not_mem_erChamber i j)

@[blueprint "def:relu-reset-success-set"
  (statement := /-- The success set $C_u$ of a word $u = (u_1, \dots, u_j)$ in the two
    expand-and-reset maps: the set of inputs $x \in [0,1]$ whose trajectory stays in the
    chambers, $x \in U_{u_1}$, $g_{u_1}(x) \in U_{u_2}$, \dots,
    $g_{u_{j-1}} \circ \cdots \circ g_{u_1}(x) \in U_{u_j}$ (`def:reset-success-set` for the
    generators `def:relu-er-generators` and the chambers `def:relu-er-chambers`). -/)]
def erSuccess : List (Fin 2) → Set (Set.Icc (0 : ℝ) 1) := successSet erGen erChamber

@[blueprint "lem:relu-reset-success-set-iff"
  (statement := /-- $x \in C_u$ if and only if
    $g_{u_m} \circ \cdots \circ g_{u_1}(x) \in U_{u_{m+1}}$ for every $0 \le m < |u|$. -/)]
theorem mem_erSuccess_iff (u : List (Fin 2)) (x : Set.Icc (0 : ℝ) 1) :
    x ∈ erSuccess u ↔
      ∀ (m : ℕ) (hm : m < u.length), wordOf erGen (u.take m) x ∈ erChamber (u[m]'hm) :=
  mem_successSet_iff u x

@[blueprint "eq:relu-reset-closed-form"
  (statement := /-- \textbf{(`lem:relu-reset-sample`(i), closed form of the words off their
    success sets.)} For a
    nonempty word $u = (u_1, \dots, u_j)$, $g_u := g_{u_j} \circ \cdots \circ g_{u_1}$ and
    $x \notin C_u$, $$g_u(x) = a_{u_j} :$$ a trajectory that leaves a chamber is reset to an
    anchor, the anchors lie outside both chambers, and each map sends every point outside its
    chamber, in particular both anchors, to its own anchor. -/)]
theorem relu_reset_closed_form (u : List (Fin 2)) (hu : u ≠ []) (x : Set.Icc (0 : ℝ) 1)
    (hx : x ∉ erSuccess u) : wordOf erGen u x = erAnchor (u.getLast hu) :=
  wordOf_eq_anchor_getLast erGen_reset erGen_erAnchor u hu x hx

@[blueprint "lem:relu-reset-disjoint"
  (statement := /-- \textbf{(`lem:relu-reset-sample`(i), disjoint success sets.)} For every
    $j$ the sets $C_u$,
    $|u| = j$, are pairwise disjoint (the chambers $[0,1/4]$ and $[3/4,1]$ are disjoint). -/)]
theorem relu_reset_disjoint (j : ℕ) :
    {u : List (Fin 2) | u.length = j}.PairwiseDisjoint erSuccess :=
  pairwiseDisjoint_successSet erChamber_disjoint j

@[blueprint "lem:relu-reset-sample-covering"
  (statement := /-- \textbf{(Empirical saturation of the expand-and-reset maps.)} For every
    sample $S = (X_1, \dots, X_n)$ in $[0,1]$, every $k \ge 0$ and every $\varepsilon > 0$,
    $$N^{\mathrm{ext}}\bigl(B(k,\{g_0,g_1\}), d_S, \varepsilon\bigr)
      \le 1 + 2 + \sum_{j=1}^{k}\min\bigl\{2^j,\ n,\ \lfloor\varepsilon^{-2}\rfloor\bigr\} .$$
    Centres: the identity, the two constant maps $a_0, a_1$, and for each $1 \le j \le k$ the
    words $u$ of length $j$ with $\hat P_n(C_u) > \varepsilon^2$; every other word of length
    $j$ is within $d_S$-distance $\varepsilon$ of the constant map $a_{u_j}$
    (`lem:reset-words-covering` with `eq:relu-reset-closed-form` and
    `lem:relu-reset-disjoint`). -/)]
theorem relu_reset_sample_covering {n : ℕ} (S : Fin n → Set.Icc (0 : ℝ) 1) (k : ℕ) {ε : ℝ≥0}
    (hε : 0 < ε) :
    externalCoveringNumber (X := EmpSpace S) ε (wordBall (Set.range erGen) k) ≤
      1 + 2 + ∑ j ∈ Finset.Icc 1 k, ((min (2 ^ j) (min n ⌊ε⁻¹ ^ 2⌋₊) : ℕ) : ℕ∞) :=
  reset_words_covering dist_unitInterval_le_one relu_reset_closed_form relu_reset_disjoint S k hε

@[blueprint "lem:relu-reset-sample-profile"
  (statement := /-- \textbf{(Root-logarithmic empirical entropy integral of the
    expand-and-reset maps.)} For every sample $S$ in $[0,1]$ and every $k$,
    $$\mathsf V_k(S) \le \sqrt{\log(k+1)} + \sqrt{\log 3} + \sqrt{2\log 2} + \sqrt{\pi/2}$$
    (`lem:reset-words-profile` with $r = 2$). -/)]
theorem relu_reset_sample_profile {n : ℕ} (S : Fin n → Set.Icc (0 : ℝ) 1) (k : ℕ) :
    entropyIntegral (Y := EmpSpace S) (empDiam S (wordBall (Set.range erGen) k))
        (wordBall (Set.range erGen) k) ≤
      √(Real.log (k + 1)) + √(Real.log 3) + √(2 * Real.log 2) + √(π / 2) := by
  have h := reset_words_profile dist_unitInterval_le_one relu_reset_closed_form
    relu_reset_disjoint S k
  have h3 : (1 : ℝ) + ((2 : ℕ) : ℝ) = 3 := by norm_num
  rwa [h3] at h

@[blueprint "lem:relu-reset-sample-ii"
  (statement := /-- \textbf{(`lem:relu-reset-sample`(ii), entropy on a sample: empirical
    saturation of the expand-and-reset maps.)} Let $g_0, g_1$ be the two expand-and-reset maps
    of $[0,1]$
    (`def:relu-er-generators`), with chambers $U_0 = [0,1/4]$, $U_1 = [3/4,1]$ and anchors
    $a_0 = 3/8$, $a_1 = 5/8$. For a word $u = (u_1, \dots, u_j)$, $j \ge 1$, let
    $g_u = g_{u_j} \circ \cdots \circ g_{u_1}$ and let $C_u$ be the set of inputs whose
    trajectory stays in the chambers (`def:relu-reset-success-set`). Then
    $g_u(x) = a_{u_j}$ for every $x \notin C_u$ (`eq:relu-reset-closed-form`) and the sets
    $C_u$, $|u| = j$, are pairwise disjoint (`lem:relu-reset-disjoint`). Consequently, for
    every sample $S = (X_1,\dots,X_n)$ in $[0,1]$, every $k \ge 0$ and every
    $\varepsilon > 0$,
    $$N^{\mathrm{ext}}\bigl(B(k,\{g_0,g_1\}), d_S, \varepsilon\bigr)
      \le 1 + 2 + \sum_{j=1}^{k}\min\{2^j, n, \lfloor\varepsilon^{-2}\rfloor\}
      \le 3 + k\min\{n, \lfloor\varepsilon^{-2}\rfloor\},$$
    and $\mathsf V_k(S) \le \sqrt{\log(k+1)} + \sqrt{\log 3} + \sqrt{2\log2} + \sqrt{\pi/2}$,
    for every sample and without any assumption on the input distribution, although
    $N^{\mathrm{ext}}(B(k,\{g_0,g_1\}), d_\infty, \varepsilon) \ge 2^k$ for
    $\varepsilon < 1/16$ (`lem:relu-er-pingpong`). -/)]
theorem lem_relu_reset_sample_bounds {n : ℕ} (S : Fin n → Set.Icc (0 : ℝ) 1) (k : ℕ) :
    (∀ ε : ℝ≥0, 0 < ε →
      externalCoveringNumber (X := EmpSpace S) ε (wordBall (Set.range erGen) k) ≤
          1 + 2 + ∑ j ∈ Finset.Icc 1 k, ((min (2 ^ j) (min n ⌊ε⁻¹ ^ 2⌋₊) : ℕ) : ℕ∞) ∧
        1 + (2 : ℕ∞) + ∑ j ∈ Finset.Icc 1 k, ((min (2 ^ j) (min n ⌊ε⁻¹ ^ 2⌋₊) : ℕ) : ℕ∞) ≤
          1 + 2 + k * ((min n ⌊ε⁻¹ ^ 2⌋₊ : ℕ) : ℕ∞)) ∧
    entropyIntegral (Y := EmpSpace S) (empDiam S (wordBall (Set.range erGen) k))
        (wordBall (Set.range erGen) k) ≤
      √(Real.log (k + 1)) + √(Real.log 3) + √(2 * Real.log 2) + √(π / 2) :=
  ⟨fun ε hε => ⟨relu_reset_sample_covering S k hε, cot_branch_sample_sum_le n 2 k ε⟩,
    relu_reset_sample_profile S k⟩

@[blueprint "lem:relu-reset-sample"
  (statement := /-- \textbf{(Expand-and-reset maps on a sample.)} Let $g_0, g_1$ be the two
    expand-and-reset maps of $[0,1]$ (`def:relu-er-generators`; the paper writes $e_0, e_1$),
    with chambers $U_0 = [0, \tfrac14]$, $U_1 = [\tfrac34, 1]$ and anchors $a_0 = \tfrac38$,
    $a_1 = \tfrac58$. For a word $u = (u_1, \dots, u_j)$ with $j \ge 1$, let
    $g_u := g_{u_j} \circ \cdots \circ g_{u_1}$, and let $C_u$ be the set of inputs
    $x \in [0,1]$ such that $g_{u_{i-1}} \circ \cdots \circ g_{u_1}(x) \in U_{u_i}$ for every
    $i \le j$ (`def:relu-reset-success-set`, `lem:relu-reset-success-set-iff`).
    \begin{enumerate}
    \item[(i)] (Closed form.) $g_u(x) = a_{u_j}$ for every $x \notin C_u$, and the sets $C_u$
      of the words of a fixed length are pairwise disjoint.
    \item[(ii)] (Entropy on a sample.) For every sample $S$ of $n$ points of $[0,1]$, every
      $k \ge 0$ and every $\varepsilon > 0$,
      $$N^{\mathrm{ext}}\bigl(B(k,\{g_0,g_1\}), d_S, \varepsilon\bigr)
        \le 3 + \sum_{j=1}^{k}\min\bigl\{2^j,\ n,\ \lfloor\varepsilon^{-2}\rfloor\bigr\}
        \le 3 + k\min\{n, \lfloor\varepsilon^{-2}\rfloor\},$$
      and
      $\mathsf V_k(S) \le \sqrt{\log(k+1)} + \sqrt{\log 3} + \sqrt{2\log2} + \sqrt{\pi/2}$.
    \end{enumerate}
    The Lean statement is the conjunction of (i) (`eq:relu-reset-closed-form` and
    `lem:relu-reset-disjoint`) and (ii) (`lem:relu-reset-sample-ii`). -/)]
theorem lem_relu_reset_sample :
    ((∀ (u : List (Fin 2)) (hu : u ≠ []) (x : Set.Icc (0 : ℝ) 1), x ∉ erSuccess u →
        wordOf erGen u x = erAnchor (u.getLast hu)) ∧
      ∀ j : ℕ, {u : List (Fin 2) | u.length = j}.PairwiseDisjoint erSuccess) ∧
    ∀ (n : ℕ) (S : Fin n → Set.Icc (0 : ℝ) 1) (k : ℕ),
      (∀ ε : ℝ≥0, 0 < ε →
        externalCoveringNumber (X := EmpSpace S) ε (wordBall (Set.range erGen) k) ≤
            1 + 2 + ∑ j ∈ Finset.Icc 1 k, ((min (2 ^ j) (min n ⌊ε⁻¹ ^ 2⌋₊) : ℕ) : ℕ∞) ∧
          1 + (2 : ℕ∞) + ∑ j ∈ Finset.Icc 1 k, ((min (2 ^ j) (min n ⌊ε⁻¹ ^ 2⌋₊) : ℕ) : ℕ∞) ≤
            1 + 2 + k * ((min n ⌊ε⁻¹ ^ 2⌋₊ : ℕ) : ℕ∞)) ∧
      entropyIntegral (Y := EmpSpace S) (empDiam S (wordBall (Set.range erGen) k))
          (wordBall (Set.range erGen) k) ≤
        √(Real.log (k + 1)) + √(Real.log 3) + √(2 * Real.log 2) + √(π / 2) :=
  ⟨⟨relu_reset_closed_form, relu_reset_disjoint⟩,
    fun _ S k => lem_relu_reset_sample_bounds S k⟩

end ExpandResetSample

end LeanDeepgen
