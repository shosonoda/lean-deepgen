import Mathlib
import Architect
import LeanDeepgen.Setting.WordBall
import LeanDeepgen.Setting.Metrics
import LeanDeepgen.Setting.Hypothesis
import LeanDeepgen.Setting.Covering
import LeanDeepgen.Growth.ArzelaAscoli

/-!
# Implementation with controlled uniform error (paper `prop:implementation`)

The three explicit implementation maps of `prop:implementation` (App. "Proof of
`prop:implementation`", restated as `prop:implementation-restated`):

* (b) `prop:implementation-b` (layerwise implementation): if every transition is `Λ`-Lipschitz,
  every output layer is `L_H`-Lipschitz and each layer is implemented within uniform error `δ`
  (transitions) and `δ_H` (output layers), then composing the implemented layers gives
  `ε_imp(k) ≤ δ_H + L_H δ ∑_{i<k} Λ^i`. The core is the telescoping induction
  `lem:impl-word-error` on the list of layers.
* (c) `prop:implementation-c` (exact ReLU realization of affine transitions on `ℝ^d`):
  `A x + b = [A, -A] relu([I; -I] x) + b`, a one-hidden-layer ReLU layer of width `2d`; hence
  every element of `B(k,F)` is a depth-`≤ k` ReLU network of width `2d` and `ε_imp = 0` for the
  identity implementation map.
* (a) `prop:implementation-a` (net-based implementation): if `𝓗` is totally bounded for the sup
  metric and `𝒜` is sup-dense on `𝓗`, then for every `ε > 0` there is a finite implementation
  class `H_imp ⊆ 𝒜` of cardinality `≤ N(𝓗, ‖·‖_∞, ε/2)` with `ε_imp ≤ ε`.

## Conventions

A *representation* of a word is a list `u = [f_m, …, f_1]` of layers and its composition is
`compList u = f_m ∘ ⋯ ∘ f_1` (`compList (f :: u) = f ∘ compList u`: the head of the list acts
*last*). This is `List.foldr (· ∘ ·) id` and matches the recursion `B(k+1,F) = B(k,F) ∪ F ∘ B(k,F)`
of `wordBall`. (It is the reverse of the convention of `wordOf` in `Growth/Exponential.lean`,
where the head of the letter list acts first; the two are related by `List.reverse`.) The
implemented word is `implWord tf u = compList (u.map tf) = tf f_m ∘ ⋯ ∘ tf f_1`.

For (b) we state the result for an arbitrary implementation map `ι` that agrees on `ℋ_k` with
"choose a representation `h ∘ f_m ∘ ⋯ ∘ f_1` with `m ≤ k` and implement it layerwise"
(hypothesis `hι`), and we prove separately (`lem:impl-map-exists`) that such an `ι` exists (by
choice); `cor:implementation-b-exists` combines the two. The paper's implementation map is exactly
such an `ι`.
-/

open scoped ENNReal NNReal UniformConvergence Matrix
open Metric

open FoML.ToMathlib

namespace LeanDeepgen

section CompList

variable {X : Type*}

@[blueprint "def:comp-list"
  (statement := /-- For a list of layers $u = [f_m, \dots, f_1]$ (an explicit representation of a
    word) the composed map is $f_u = f_m \circ \cdots \circ f_1$, with $f_{[]} = \mathrm{id}$.
    In Lean: `compList [] = id` and `compList (f :: u) = f ∘ compList u` (the head of the list
    acts last, matching the recursion $B(k+1,F) = B(k,F) \cup F \circ B(k,F)$). -/)]
def compList : List (X → X) → X → X
  | [] => id
  | f :: u => f ∘ compList u

@[simp, blueprint "lem:comp-list-nil"
  (statement := /-- $f_{[]} = \mathrm{id}$. -/)]
theorem compList_nil : compList ([] : List (X → X)) = id := rfl

@[simp, blueprint "lem:comp-list-cons"
  (statement := /-- $f_{f :: u} = f \circ f_u$. -/)]
theorem compList_cons (f : X → X) (u : List (X → X)) : compList (f :: u) = f ∘ compList u := rfl

@[blueprint "def:impl-word"
  (statement := /-- Given an implementation $f \mapsto \tilde f$ of the layers, the implemented
    word of a representation $u = [f_m, \dots, f_1]$ is
    $\tilde f_u = \tilde f_m \circ \cdots \circ \tilde f_1$. -/)]
def implWord (tf : (X → X) → (X → X)) (u : List (X → X)) : X → X := compList (u.map tf)

@[simp, blueprint "lem:impl-word-nil"
  (statement := /-- $\tilde f_{[]} = \mathrm{id}$. -/)]
theorem implWord_nil (tf : (X → X) → (X → X)) : implWord tf [] = id := rfl

@[simp, blueprint "lem:impl-word-cons"
  (statement := /-- $\tilde f_{f :: u} = \tilde f \circ \tilde f_u$. -/)]
theorem implWord_cons (tf : (X → X) → (X → X)) (f : X → X) (u : List (X → X)) :
    implWord tf (f :: u) = tf f ∘ implWord tf u := rfl

variable {F : Set (X → X)}

@[blueprint "lem:comp-list-mem-wordball"
  (statement := /-- If all layers of $u$ lie in $F$ and $|u| \le k$ then $f_u \in B(k,F)$. -/)]
theorem compList_mem_wordBall {u : List (X → X)} (hu : ∀ f ∈ u, f ∈ F) {k : ℕ}
    (hlen : u.length ≤ k) : compList u ∈ wordBall F k := by
  /-- Induction on $u$: $\mathrm{id} \in B(k,F)$, and $f \circ f_u \in B(k'+1,F)$ when
    $f \in F$ and $f_u \in B(k',F)$. -/
  induction u generalizing k with
  | nil => exact id_mem_wordBall
  | cons f u ih =>
    simp only [List.length_cons] at hlen
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    exact mem_wordBall_succ_of_mem_of_mem (hu f (List.mem_cons_self ..))
      (ih (fun g hg => hu g (List.mem_cons_of_mem f hg)) (by omega))

@[blueprint "lem:exists-comp-list-of-mem-wordball"
  (statement := /-- Every $g \in B(k,F)$ has a representation $g = f_m \circ \cdots \circ f_1$
    with $f_i \in F$ and $m \le k$, i.e. $g = f_u$ for a list $u$ of elements of $F$ with
    $|u| \le k$. -/)]
theorem exists_compList_of_mem_wordBall {k : ℕ} {g : X → X} (hg : g ∈ wordBall F k) :
    ∃ u : List (X → X), (∀ f ∈ u, f ∈ F) ∧ u.length ≤ k ∧ g = compList u := by
  /-- Induction on $k$ along the recursion $B(k+1,F) = B(k,F) \cup F \circ B(k,F)$. -/
  induction k generalizing g with
  | zero =>
    simp only [wordBall_zero, Set.mem_singleton_iff] at hg
    exact ⟨[], by simp, le_rfl, hg⟩
  | succ k ih =>
    rcases hg with hg | ⟨a, ha, b, hb, rfl⟩
    · obtain ⟨u, hu, hlen, rfl⟩ := ih hg
      exact ⟨u, hu, hlen.trans (Nat.le_succ k), rfl⟩
    · obtain ⟨u, hu, hlen, rfl⟩ := ih hb
      refine ⟨a :: u, ?_, by simpa using hlen, rfl⟩
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact ha
      · exact hu f hf

end CompList

/-! ### (b) Layerwise implementation -/

section Layerwise

variable {X : Type*} [PseudoEMetricSpace X] {F : Set (X → X)}

@[blueprint "lem:impl-word-error"
  (statement := /-- (Telescoping error propagation.) Let every $f \in F$ be $\Lambda$-Lipschitz
    and let $\tilde f$ satisfy $d_\infty(f, \tilde f) \le \delta$ for $f \in F$, where
    $\delta \ge 0$. Then for every representation $u = [f_m, \dots, f_1]$ of layers in $F$ and
    every $x$,
    $$d\bigl(f_m \circ \cdots \circ f_1(x),\ \tilde f_m \circ \cdots \circ \tilde f_1(x)\bigr)
      \le \delta \sum_{i=0}^{m-1} \Lambda^i .$$ -/)]
theorem edist_compList_implWord_le {Λ : ℝ≥0} (hF : ∀ f ∈ F, LipschitzWith Λ f)
    (tf : (X → X) → (X → X)) {δ : ℝ} (hδ : 0 ≤ δ)
    (htf : ∀ f ∈ F, uniformDist f (tf f) ≤ ENNReal.ofReal δ)
    (u : List (X → X)) (hu : ∀ f ∈ u, f ∈ F) (x : X) :
    edist (compList u x) (implWord tf u x) ≤
      ENNReal.ofReal (δ * ∑ i ∈ Finset.range u.length, (Λ : ℝ) ^ i) := by
  /-- Induction on $u$. For $u = f :: u'$ write $y = f_{u'}(x)$, $\tilde y = \tilde f_{u'}(x)$; then
    $d(f(y), \tilde f(\tilde y)) \le d(f(y), f(\tilde y)) + d(f(\tilde y), \tilde f(\tilde y))
    \le \Lambda\, d(y, \tilde y) + \delta \le \Lambda \delta \sum_{i<m} \Lambda^i + \delta
    = \delta \sum_{i<m+1} \Lambda^i$. -/
  induction u with
  | nil => simp
  | cons f u ih =>
    have hf : f ∈ F := hu f (List.mem_cons_self ..)
    have ih' := ih fun g hg => hu g (List.mem_cons_of_mem f hg)
    set s : ℝ := ∑ i ∈ Finset.range u.length, (Λ : ℝ) ^ i with hs
    have hs0 : 0 ≤ s := Finset.sum_nonneg fun i _ => by positivity
    have hsum : ∑ i ∈ Finset.range (f :: u).length, (Λ : ℝ) ^ i = (Λ : ℝ) * s + 1 := by
      rw [List.length_cons, Finset.sum_range_succ', hs, Finset.mul_sum]
      simp [pow_succ']
    rw [hsum]
    calc edist (compList (f :: u) x) (implWord tf (f :: u) x)
        = edist (f (compList u x)) (tf f (implWord tf u x)) := rfl
      _ ≤ edist (f (compList u x)) (f (implWord tf u x)) +
            edist (f (implWord tf u x)) (tf f (implWord tf u x)) := edist_triangle _ _ _
      _ ≤ Λ * edist (compList u x) (implWord tf u x) + uniformDist f (tf f) :=
          add_le_add ((hF f hf).edist_le_mul _ _) (edist_le_uniformDist _)
      _ ≤ Λ * ENNReal.ofReal (δ * s) + ENNReal.ofReal δ :=
          add_le_add (by gcongr) (htf f hf)
      _ = ENNReal.ofReal (δ * ((Λ : ℝ) * s + 1)) := by
          rw [show δ * ((Λ : ℝ) * s + 1) = (Λ : ℝ) * (δ * s) + δ by ring,
            ENNReal.ofReal_add (by positivity) hδ, ENNReal.ofReal_mul Λ.coe_nonneg,
            ENNReal.ofReal_coe_nnreal]

end Layerwise

section LayerwiseMetric

variable {X : Type*} [PseudoMetricSpace X] {F : Set (X → X)} {H : Set (X → ℝ)} {k : ℕ}

omit [PseudoMetricSpace X] in
@[blueprint "lem:impl-map-exists"
  (statement := /-- (Existence of the layerwise implementation map.) Given implementations
    $f \mapsto \tilde f$ of the transitions and $h \mapsto \tilde h$ of the output layers, there
    is a map $\iota : \mathbb R^{\mathcal X} \to \mathbb R^{\mathcal X}$ such that every
    $g \in \mathcal H_k$ has a representation $g = h \circ f_m \circ \cdots \circ f_1$ with
    $h \in H$, $f_i \in F$, $m \le k$ and
    $\iota(g) = \tilde h \circ \tilde f_m \circ \cdots \circ \tilde f_1$. -/)]
theorem exists_implMap (F : Set (X → X)) (H : Set (X → ℝ)) (k : ℕ) (tf : (X → X) → (X → X))
    (th : (X → ℝ) → (X → ℝ)) :
    ∃ ι : (X → ℝ) → (X → ℝ), ∀ g ∈ hypothesisClass H F k, ∃ h ∈ H, ∃ u : List (X → X),
      (∀ f ∈ u, f ∈ F) ∧ u.length ≤ k ∧ g = h ∘ compList u ∧ ι g = th h ∘ implWord tf u := by
  /-- For each $g \in \mathcal H_k$ choose (by the axiom of choice) a representation, using
    `lem:exists-comp-list-of-mem-wordball`; outside $\mathcal H_k$ the value of $\iota$ is
    irrelevant. -/
  classical
  have key : ∀ g : X → ℝ, ∃ p : (X → ℝ) × List (X → X), g ∈ hypothesisClass H F k →
      p.1 ∈ H ∧ (∀ f ∈ p.2, f ∈ F) ∧ p.2.length ≤ k ∧ g = p.1 ∘ compList p.2 := by
    intro g
    by_cases hg : g ∈ hypothesisClass H F k
    · obtain ⟨h, hh, f, hf, rfl⟩ := hg
      obtain ⟨u, hu, hlen, rfl⟩ := exists_compList_of_mem_wordBall hf
      exact ⟨(h, u), fun _ => ⟨hh, hu, hlen, rfl⟩⟩
    · exact ⟨(fun _ => 0, []), fun h => absurd h hg⟩
  choose p hp using key
  refine ⟨fun g => th (p g).1 ∘ implWord tf (p g).2, fun g hg => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hp g hg
  exact ⟨(p g).1, h1, (p g).2, h2, h3, h4, rfl⟩

@[blueprint "prop:implementation-b"
  (statement := /-- \textbf{(Layerwise implementation.)} Let $F \subseteq \mathcal X^{\mathcal X}$
    with $\mathrm{lip}(f) \le \Lambda$ for all $f \in F$, and $H \subseteq \mathbb R^{\mathcal X}$
    with $\mathrm{lip}(h) \le L_H$ for all $h \in H$. Suppose every $f \in F$ is assigned an
    implemented map $\tilde f$ with $d_\infty(f, \tilde f) \le \delta$ ($\delta \ge 0$) and every
    $h \in H$ an implemented $\tilde h$ with $\|h - \tilde h\|_\infty \le \delta_H$. Let $\iota$
    be an implementation map that sends each $g \in \mathcal H_k$, for one representation
    $g = h \circ f_m \circ \cdots \circ f_1$ with $m \le k$, to
    $\tilde h \circ \tilde f_m \circ \cdots \circ \tilde f_1$. Then
    $$\varepsilon_{\mathrm{imp}}(k) \le \delta_H + L_H\,\delta \sum_{i=0}^{k-1} \Lambda^i .$$
    (Stated for an arbitrary $\iota$ with this property; such an $\iota$ exists by
    `lem:impl-map-exists`.) -/)]
theorem prop_implementation_b {Λ LH : ℝ≥0} {δ δH : ℝ} (hδ : 0 ≤ δ)
    (hF : ∀ f ∈ F, LipschitzWith Λ f) (hH : ∀ h ∈ H, LipschitzWith LH h)
    (tf : (X → X) → (X → X)) (htf : ∀ f ∈ F, uniformDist f (tf f) ≤ ENNReal.ofReal δ)
    (th : (X → ℝ) → (X → ℝ)) (hth : ∀ h ∈ H, ∀ x, |h x - th h x| ≤ δH)
    (ι : (X → ℝ) → (X → ℝ))
    (hι : ∀ g ∈ hypothesisClass H F k, ∃ h ∈ H, ∃ u : List (X → X),
      (∀ f ∈ u, f ∈ F) ∧ u.length ≤ k ∧ g = h ∘ compList u ∧ ι g = th h ∘ implWord tf u) :
    implError ι (hypothesisClass H F k) ≤
      ENNReal.ofReal (δH + LH * δ * ∑ i ∈ Finset.range k, (Λ : ℝ) ^ i) := by
  /-- Fix $g = h \circ f_u \in \mathcal H_k$ and $x$; put $T_0 = f_u(x)$, $T_m = \tilde f_u(x)$.
    By `lem:impl-word-error`, $d(T_0, T_m) \le \delta \sum_{i<m} \Lambda^i \le \delta \sum_{i<k}
    \Lambda^i$ (as $\Lambda \ge 0$ and $m \le k$). Then
    $|h(T_0) - \tilde h(T_m)| \le |h(T_0) - h(T_m)| + |h(T_m) - \tilde h(T_m)|
    \le L_H\, d(T_0, T_m) + \delta_H$; take suprema over $x$ and $g$. -/
  refine iSup₂_le fun g hg => iSup_le fun x => ?_
  obtain ⟨h, hh, u, hu, hlen, rfl, hιg⟩ := hι g hg
  rw [hιg]
  simp only [Function.comp_apply]
  set T0 := compList u x
  set Tm := implWord tf u x
  have hsum_le : ∑ i ∈ Finset.range u.length, (Λ : ℝ) ^ i ≤ ∑ i ∈ Finset.range k, (Λ : ℝ) ^ i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hlen) fun i _ _ => by positivity
  have hs0 : 0 ≤ ∑ i ∈ Finset.range u.length, (Λ : ℝ) ^ i :=
    Finset.sum_nonneg fun i _ => by positivity
  have hdist : dist T0 Tm ≤ δ * ∑ i ∈ Finset.range u.length, (Λ : ℝ) ^ i :=
    (edist_le_ofReal (by positivity)).1 (edist_compList_implWord_le hF tf hδ htf u hu x)
  have h1 : |h T0 - h Tm| ≤ LH * (δ * ∑ i ∈ Finset.range u.length, (Λ : ℝ) ^ i) := by
    have := (hH h hh).dist_le_mul T0 Tm
    rw [Real.dist_eq] at this
    exact this.trans (mul_le_mul_of_nonneg_left hdist LH.coe_nonneg)
  have h2 := hth h hh Tm
  have hδH : 0 ≤ δH := (abs_nonneg _).trans h2
  refine ENNReal.ofReal_le_ofReal ?_
  calc |h T0 - th h Tm| ≤ |h T0 - h Tm| + |h Tm - th h Tm| := abs_sub_le _ _ _
    _ ≤ LH * (δ * ∑ i ∈ Finset.range u.length, (Λ : ℝ) ^ i) + δH := add_le_add h1 h2
    _ ≤ δH + LH * δ * ∑ i ∈ Finset.range k, (Λ : ℝ) ^ i := by
        rw [← mul_assoc, add_comm]
        gcongr

@[blueprint "cor:implementation-b-exists"
  (statement := /-- Under the hypotheses of `prop:implementation-b` there exists an implementation
    map $\iota$ with $\varepsilon_{\mathrm{imp}}(k) \le \delta_H + L_H\,\delta \sum_{i<k}
    \Lambda^i$. -/)]
theorem exists_implMap_implError_le {Λ LH : ℝ≥0} {δ δH : ℝ} (hδ : 0 ≤ δ)
    (hF : ∀ f ∈ F, LipschitzWith Λ f) (hH : ∀ h ∈ H, LipschitzWith LH h)
    (tf : (X → X) → (X → X)) (htf : ∀ f ∈ F, uniformDist f (tf f) ≤ ENNReal.ofReal δ)
    (th : (X → ℝ) → (X → ℝ)) (hth : ∀ h ∈ H, ∀ x, |h x - th h x| ≤ δH) :
    ∃ ι : (X → ℝ) → (X → ℝ), implError ι (hypothesisClass H F k) ≤
      ENNReal.ofReal (δH + LH * δ * ∑ i ∈ Finset.range k, (Λ : ℝ) ^ i) := by
  /-- Combine `lem:impl-map-exists` and `prop:implementation-b`. -/
  obtain ⟨ι, hι⟩ := exists_implMap F H k tf th
  exact ⟨ι, prop_implementation_b hδ hF hH tf htf th hth ι hι⟩

@[blueprint "lem:geom-sum-le-of-le-one"
  (statement := /-- If $0 \le \Lambda \le 1$ then $\sum_{i<k} \Lambda^i \le k$. -/)]
theorem sum_pow_le_of_le_one {Λ : ℝ≥0} (hΛ : Λ ≤ 1) (k : ℕ) :
    ∑ i ∈ Finset.range k, (Λ : ℝ) ^ i ≤ k := by
  calc ∑ i ∈ Finset.range k, (Λ : ℝ) ^ i ≤ ∑ _i ∈ Finset.range k, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => pow_le_one₀ Λ.coe_nonneg (by exact_mod_cast hΛ)
    _ = k := by simp

@[blueprint "lem:geom-sum-le-of-lt-one"
  (statement := /-- If $0 \le \Lambda < 1$ then $\sum_{i<k} \Lambda^i \le 1/(1-\Lambda)$. -/)]
theorem sum_pow_le_of_lt_one {Λ : ℝ≥0} (hΛ : Λ < 1) (k : ℕ) :
    ∑ i ∈ Finset.range k, (Λ : ℝ) ^ i ≤ 1 / (1 - Λ) := by
  /-- $\sum_{i<k} \Lambda^i = (1 - \Lambda^k)/(1 - \Lambda) \le 1/(1-\Lambda)$. -/
  have hΛ' : (Λ : ℝ) < 1 := by exact_mod_cast hΛ
  have h1 : 0 < 1 - (Λ : ℝ) := by linarith
  rw [geom_sum_eq hΛ'.ne k, ← neg_sub, ← neg_sub (1 : ℝ), neg_div_neg_eq]
  gcongr
  exact sub_le_self _ (by positivity)

@[blueprint "cor:implementation-b-nonexpanding"
  (statement := /-- (Non-expanding transitions.) If moreover $\Lambda \le 1$, then
    $\varepsilon_{\mathrm{imp}}(k) \le \delta_H + L_H\, k\, \delta$. -/)]
theorem implError_le_of_le_one {Λ LH : ℝ≥0} {δ δH : ℝ} (hδ : 0 ≤ δ) (hΛ : Λ ≤ 1)
    (hF : ∀ f ∈ F, LipschitzWith Λ f) (hH : ∀ h ∈ H, LipschitzWith LH h)
    (tf : (X → X) → (X → X)) (htf : ∀ f ∈ F, uniformDist f (tf f) ≤ ENNReal.ofReal δ)
    (th : (X → ℝ) → (X → ℝ)) (hth : ∀ h ∈ H, ∀ x, |h x - th h x| ≤ δH)
    (ι : (X → ℝ) → (X → ℝ))
    (hι : ∀ g ∈ hypothesisClass H F k, ∃ h ∈ H, ∃ u : List (X → X),
      (∀ f ∈ u, f ∈ F) ∧ u.length ≤ k ∧ g = h ∘ compList u ∧ ι g = th h ∘ implWord tf u) :
    implError ι (hypothesisClass H F k) ≤ ENNReal.ofReal (δH + LH * k * δ) := by
  /-- `prop:implementation-b` and $\sum_{i<k} \Lambda^i \le k$. -/
  refine (prop_implementation_b hδ hF hH tf htf th hth ι hι).trans (ENNReal.ofReal_le_ofReal ?_)
  have := mul_le_mul_of_nonneg_left (sum_pow_le_of_le_one hΛ k) (by positivity : (0 : ℝ) ≤ LH * δ)
  linarith

@[blueprint "cor:implementation-b-contractive"
  (statement := /-- (Contractive transitions.) If moreover $\Lambda < 1$, then
    $\varepsilon_{\mathrm{imp}}(k) \le \delta_H + L_H\, \delta / (1 - \Lambda)$. -/)]
theorem implError_le_of_lt_one {Λ LH : ℝ≥0} {δ δH : ℝ} (hδ : 0 ≤ δ) (hΛ : Λ < 1)
    (hF : ∀ f ∈ F, LipschitzWith Λ f) (hH : ∀ h ∈ H, LipschitzWith LH h)
    (tf : (X → X) → (X → X)) (htf : ∀ f ∈ F, uniformDist f (tf f) ≤ ENNReal.ofReal δ)
    (th : (X → ℝ) → (X → ℝ)) (hth : ∀ h ∈ H, ∀ x, |h x - th h x| ≤ δH)
    (ι : (X → ℝ) → (X → ℝ))
    (hι : ∀ g ∈ hypothesisClass H F k, ∃ h ∈ H, ∃ u : List (X → X),
      (∀ f ∈ u, f ∈ F) ∧ u.length ≤ k ∧ g = h ∘ compList u ∧ ι g = th h ∘ implWord tf u) :
    implError ι (hypothesisClass H F k) ≤ ENNReal.ofReal (δH + LH * δ / (1 - Λ)) := by
  /-- `prop:implementation-b` and $\sum_{i<k} \Lambda^i \le 1/(1-\Lambda)$. -/
  refine (prop_implementation_b hδ hF hH tf htf th hth ι hι).trans (ENNReal.ofReal_le_ofReal ?_)
  have := mul_le_mul_of_nonneg_left (sum_pow_le_of_lt_one hΛ k) (by positivity : (0 : ℝ) ≤ LH * δ)
  rw [div_eq_mul_one_div]
  linarith

end LayerwiseMetric

/-! ### (c) Exact ReLU realization of affine transitions -/

section Relu

variable {d : ℕ}

@[blueprint "def:relu"
  (statement := /-- $\mathrm{relu}(t) = \max\{0, t\}$. -/)]
def relu (t : ℝ) : ℝ := max 0 t

@[blueprint "def:relu-layer"
  (statement := /-- A one-hidden-layer ReLU layer on $\mathbb R^d$ with hidden index set $m$
    (width $|m|$) is $x \mapsto W_2\, \mathrm{relu}(W_1 x) + b$, with $W_1 \in \mathbb R^{m \times
    d}$, $W_2 \in \mathbb R^{d \times m}$, $b \in \mathbb R^d$ and $\mathrm{relu}$ applied
    coordinatewise. -/)]
def reluLayer {m : Type*} [Fintype m] (W₂ : Matrix (Fin d) m ℝ) (W₁ : Matrix m (Fin d) ℝ)
    (b : Fin d → ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  W₂ *ᵥ (fun j => relu ((W₁ *ᵥ x) j)) + b

@[blueprint "lem:relu-sub-relu-neg"
  (statement := /-- $t = \mathrm{relu}(t) - \mathrm{relu}(-t)$. -/)]
theorem relu_sub_relu_neg (t : ℝ) : relu t - relu (-t) = t := by
  simp only [relu, max_comm (0 : ℝ)]
  exact max_zero_sub_max_neg_zero_eq_self t

@[blueprint "lem:affine-eq-relu"
  (statement := /-- (Exact realization of an affine map.) For $A \in \mathbb R^{d \times d}$ and
    $b \in \mathbb R^d$, with $W_1 = [I_d; -I_d] \in \mathbb R^{2d \times d}$ and
    $W_2 = [A, -A] \in \mathbb R^{d \times 2d}$,
    $$W_2\, \mathrm{relu}(W_1 x) + b = A x + b \qquad (x \in \mathbb R^d),$$
    i.e. $x \mapsto Ax + b$ is one ReLU layer of width $2d$. -/)]
theorem reluLayer_fromCols_fromRows (A : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ)
    (x : Fin d → ℝ) :
    reluLayer (Matrix.fromCols A (-A)) (Matrix.fromRows 1 (-1)) b x = A *ᵥ x + b := by
  /-- $\mathrm{relu}(W_1 x) = (\mathrm{relu}(x), \mathrm{relu}(-x))$ and
    $[A,-A](v_1, v_2) = A(v_1 - v_2)$; conclude with $\mathrm{relu}(t) - \mathrm{relu}(-t) = t$. -/
  unfold reluLayer
  congr 1
  have hrelu : (fun j => relu ((Matrix.fromRows (1 : Matrix (Fin d) (Fin d) ℝ) (-1) *ᵥ x) j)) =
      Sum.elim (fun i => relu (x i)) (fun i => relu (-x i)) := by
    funext j
    rcases j with i | i <;> simp [Matrix.fromRows_mulVec, Matrix.neg_mulVec]
  rw [hrelu, Matrix.fromCols_mulVec_sumElim, Matrix.neg_mulVec, ← sub_eq_add_neg,
    ← Matrix.mulVec_sub]
  congr 1
  funext i
  simp [relu_sub_relu_neg]

@[blueprint "def:relu-params"
  (statement := /-- The parameters $(W_2, W_1, b)$ of a ReLU layer of width $2d$ on
    $\mathbb R^d$. -/)]
abbrev ReluParams (d : ℕ) : Type :=
  Matrix (Fin d) (Fin d ⊕ Fin d) ℝ × Matrix (Fin d ⊕ Fin d) (Fin d) ℝ × (Fin d → ℝ)

@[blueprint "def:relu-layer-of"
  (statement := /-- The ReLU layer of width $2d$ with parameters $(W_2, W_1, b)$. -/)]
def reluLayerOf (p : ReluParams d) : (Fin d → ℝ) → (Fin d → ℝ) := reluLayer p.1 p.2.1 p.2.2

@[blueprint "def:is-relu-net"
  (statement := /-- A map $g : \mathbb R^d \to \mathbb R^d$ is a ReLU network of depth $\le k$
    and width $2d$ if it is a composition of at most $k$ ReLU layers of width $2d$. -/)]
def IsReluNet (d k : ℕ) (g : (Fin d → ℝ) → (Fin d → ℝ)) : Prop :=
  ∃ u : List (ReluParams d), u.length ≤ k ∧ g = compList (u.map reluLayerOf)

@[blueprint "lem:comp-list-affine-eq-relu-net"
  (statement := /-- If every layer of the representation $u$ is affine, then $f_u$ is a
    composition of $|u|$ ReLU layers of width $2d$. -/)]
theorem exists_reluParams_of_affine {F : Set ((Fin d → ℝ) → (Fin d → ℝ))}
    (hF : ∀ f ∈ F, ∃ (A : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ), f = fun x => A *ᵥ x + b)
    (u : List ((Fin d → ℝ) → (Fin d → ℝ))) (hu : ∀ f ∈ u, f ∈ F) :
    ∃ v : List (ReluParams d), v.length = u.length ∧ compList u = compList (v.map reluLayerOf) := by
  /-- Induction on $u$, replacing each affine layer by the ReLU layer of `lem:affine-eq-relu`. -/
  induction u with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons f u ih =>
    obtain ⟨v, hlen, hv⟩ := ih fun g hg => hu g (List.mem_cons_of_mem f hg)
    obtain ⟨A, b, rfl⟩ := hF f (hu f (List.mem_cons_self ..))
    refine ⟨(Matrix.fromCols A (-A), Matrix.fromRows 1 (-1), b) :: v, by simp [hlen], ?_⟩
    rw [List.map_cons, compList_cons, compList_cons, hv]
    congr 1
    funext x
    exact (reluLayer_fromCols_fromRows A b x).symm

@[blueprint "lem:impl-error-id"
  (statement := /-- The identity implementation map has zero implementation error:
    $\varepsilon_{\mathrm{imp}} = 0$ for $\iota = \mathrm{id}$ on any class. -/)]
theorem implError_id {X : Type*} (𝓗 : Set (X → ℝ)) : implError id 𝓗 = 0 := by
  refine le_antisymm (iSup₂_le fun f _ => iSup_le fun x => ?_) bot_le
  simp

@[blueprint "prop:implementation-c"
  (statement := /-- \textbf{(Exact implementation of affine transitions.)} Let
    $\mathcal X = \mathbb R^d$ and let every $f \in F$ be affine, $f(x) = Ax + b$. Then every
    element of $B(k,F)$ is a ReLU network of depth $\le k$ and width $2d$, and with the identity
    implementation map $\iota = \mathrm{id}$ (the abstract class $\mathcal H_k$ is itself the
    implemented class) one has $\varepsilon_{\mathrm{imp}}(k) = 0$. -/)]
theorem prop_implementation_c {F : Set ((Fin d → ℝ) → (Fin d → ℝ))}
    (hF : ∀ f ∈ F, ∃ (A : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ), f = fun x => A *ᵥ x + b)
    (H : Set ((Fin d → ℝ) → ℝ)) (k : ℕ) :
    (∀ g ∈ wordBall F k, IsReluNet d k g) ∧ implError id (hypothesisClass H F k) = 0 := by
  /-- Take a representation of $g \in B(k,F)$ (`lem:exists-comp-list-of-mem-wordball`) and apply
    `lem:comp-list-affine-eq-relu-net`; the second claim is `lem:impl-error-id`. -/
  refine ⟨fun g hg => ?_, implError_id _⟩
  obtain ⟨u, hu, hlen, rfl⟩ := exists_compList_of_mem_wordBall hg
  obtain ⟨v, hvlen, hv⟩ := exists_reluParams_of_affine hF u hu
  exact ⟨v, hvlen ▸ hlen, hv⟩

end Relu

/-! ### (a) Net-based implementation -/

section NetBased

variable {X : Type*}

@[blueprint "prop:implementation-a"
  (statement := /-- \textbf{(Net-based implementation.)} Let $\mathcal H \subseteq
    \mathbb R^{\mathcal X}$ be totally bounded in the uniform norm and let $\mathcal A \subseteq
    \mathbb R^{\mathcal X}$ be uniformly dense on $\mathcal H$ (for every $g \in \mathcal H$ and
    $\eta > 0$ there is $a \in \mathcal A$ with $\|g - a\|_\infty \le \eta$). Then for every
    $\varepsilon > 0$ there exist a finite class $\mathcal H_{\mathrm{imp}}^\varepsilon \subseteq
    \mathcal A$ with $|\mathcal H_{\mathrm{imp}}^\varepsilon| \le N(\mathcal H, \|\cdot\|_\infty,
    \varepsilon/2)$ and an implementation map $\iota : \mathcal H \to
    \mathcal H_{\mathrm{imp}}^\varepsilon$ with $\sup_{g \in \mathcal H} \|g - \iota(g)\|_\infty
    \le \varepsilon$. (The paper's compact domain $K$ and the continuity of the functions are
    only used to guarantee total boundedness and density, which are the hypotheses here.) -/)]
theorem prop_implementation_a (𝓗 𝒜 : Set (X → ℝ)) (h𝓗 : TotallyBounded (α := X →ᵤ ℝ) 𝓗)
    (h𝒜 : ∀ g ∈ 𝓗, ∀ η : ℝ, 0 < η → ∃ a ∈ 𝒜, ∀ x, |g x - a x| ≤ η) (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ Himp : Set (X → ℝ), Himp ⊆ 𝒜 ∧ Himp.Finite ∧
      Himp.encard ≤ coveringNumber (X := X →ᵤ ℝ) (ε / 2) 𝓗 ∧
      ∃ ι : (X → ℝ) → (X → ℝ), (∀ g ∈ 𝓗, ι g ∈ Himp) ∧ ∀ g ∈ 𝓗, ∀ x, |g x - ι g x| ≤ ε := by
  /-- Let $C \subseteq \mathcal H$ be a minimal internal $\varepsilon/2$-net (finite by total
    boundedness). For each $c \in C$ choose $a_c \in \mathcal A$ with
    $\|c - a_c\|_\infty \le \varepsilon/2$, set $\mathcal H_{\mathrm{imp}} = \{a_c : c \in C\}$
    and $\iota(g) = a_{c(g)}$ where $c(g) \in C$ satisfies $\|g - c(g)\|_\infty \le \varepsilon/2$.
    Then $\|g - \iota(g)\|_\infty \le \varepsilon/2 + \varepsilon/2$. -/
  classical
  have hne : coveringNumber (X := X →ᵤ ℝ) (ε / 2) 𝓗 ≠ ⊤ :=
    coveringNumber_ne_top_of_totallyBounded h𝓗 (by positivity)
  obtain ⟨C, hCsub, hCfin, hCcov, hCcard⟩ := exists_set_encard_eq_coveringNumber hne
  have key1 : ∀ c : X → ℝ, ∃ a : X → ℝ, c ∈ 𝓗 → a ∈ 𝒜 ∧ ∀ x, |c x - a x| ≤ (ε : ℝ) / 2 := by
    intro c
    by_cases hc : c ∈ 𝓗
    · obtain ⟨a, ha, hax⟩ := h𝒜 c hc ((ε : ℝ) / 2) (by positivity)
      exact ⟨a, fun _ => ⟨ha, hax⟩⟩
    · exact ⟨c, fun h => absurd h hc⟩
  choose a ha using key1
  have key2 : ∀ g : X → ℝ, ∃ c : X → ℝ, g ∈ 𝓗 → c ∈ C ∧ ∀ x, |g x - c x| ≤ (ε : ℝ) / 2 := by
    intro g
    by_cases hg : g ∈ 𝓗
    · obtain ⟨c, hc, hgc⟩ := hCcov hg
      refine ⟨c, fun _ => ⟨hc, fun x => ?_⟩⟩
      have h1 : edist (UniformFun.ofFun g) (UniformFun.ofFun c) ≤ ((ε / 2 : ℝ≥0) : ℝ≥0∞) := hgc
      have h2 := UniformFun.edist_le.1 h1 x
      have h3 : dist (g x) (c x) ≤ ((ε / 2 : ℝ≥0) : ℝ) := dist_le_coe.2 (edist_le_coe.1 h2)
      rw [Real.dist_eq] at h3
      simpa using h3
    · exact ⟨g, fun h => absurd h hg⟩
  choose c hc using key2
  refine ⟨a '' C, ?_, hCfin.image a, (Set.encard_image_le a C).trans hCcard.le,
    fun g => a (c g), fun g hg => ⟨c g, (hc g hg).1, rfl⟩, fun g hg x => ?_⟩
  · rintro _ ⟨c', hc', rfl⟩
    exact (ha c' (hCsub hc')).1
  · calc |g x - a (c g) x| ≤ |g x - c g x| + |c g x - a (c g) x| := abs_sub_le _ _ _
      _ ≤ (ε : ℝ) / 2 + (ε : ℝ) / 2 :=
          add_le_add ((hc g hg).2 x) ((ha (c g) (hCsub (hc g hg).1)).2 x)
      _ = ε := by ring

end NetBased

end LeanDeepgen
