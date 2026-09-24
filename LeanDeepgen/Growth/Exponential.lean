import Mathlib
import Architect
import LeanDeepgen.Setting.WordBall
import LeanDeepgen.Setting.Metrics
import LeanDeepgen.Setting.Covering
import LeanDeepgen.Growth.Defs
import LeanDeepgen.Growth.Lemmas

/-!
# Exponential growth: conditions E1, E1', E2 (paper Sec. 4 / App. F)

A finite generator family is `f : Fin r → X → X` with `F = Set.range f`. The word
`wordOf f u` of a list `u = [i₁, …, i_k]` (defined in `LeanDeepgen.Growth.Defs`) is
`f i_k ∘ ⋯ ∘ f i₁` (the head of the list acts first, as in the paper's `f_{i_k} ∘ ⋯ ∘ f_{i_1}`).

* `cond:e1-free-iso` (E1): uniform separation of the words of each length at a base point
  gives `N^ext(B(k,F), d_∞, ε) ≥ r^k` for `2ε < δ`.
* `cond:e1p-theoremC` (E1'): the isometric variant.
* `cond:e2-pingpong` (E2): a ping–pong coding (separated chambers, coding cores, reset to
  anchors, a marker separated from the anchors) gives `N^ext(B(k,F), d_∞, ε) ≥ r^k` for
  `2ε < α`, and the words of each length are pairwise distinct.

All lower bounds are obtained from `lem:probes-packing` (in its indexed form
`card_le_externalCoveringNumber_of_probes`).
-/

open scoped NNReal ENNReal
open Metric

namespace LeanDeepgen

variable {X : Type*} {r : ℕ}

section Words

@[blueprint "lem:comp-mem-words-succ"
  (statement := /-- If $w \in F^m$ and $g \in F$ then $w \circ g \in F^{m+1}$: the words of
    length $m$ are also closed under right composition with generators. -/)]
theorem comp_mem_words_succ {F : Set (X → X)} {m : ℕ} {w g : X → X} (hw : w ∈ words F m)
    (hg : g ∈ F) : w ∘ g ∈ words F (m + 1) := by
  /-- Induction on $m$: $\mathrm{id} \circ g = g \circ \mathrm{id}$, and
    $(a \circ b) \circ g = a \circ (b \circ g)$. -/
  induction m generalizing w with
  | zero =>
    simp only [words, Set.mem_singleton_iff] at hw
    subst hw
    exact ⟨g, hg, id, rfl, rfl⟩
  | succ m ih =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hw
    exact ⟨a, ha, b ∘ g, ih hb, rfl⟩

@[blueprint "lem:wordof-mem-words"
  (statement := /-- $f_u \in F^{|u|}$ where $F = \{f_1, \dots, f_r\}$. -/)]
theorem wordOf_mem_words (f : Fin r → X → X) (u : List (Fin r)) :
    wordOf f u ∈ words (Set.range f) u.length := by
  /-- Induction on $u$ using the previous lemma. -/
  induction u with
  | nil => simp [words]
  | cons i u ih => exact comp_mem_words_succ ih ⟨i, rfl⟩

@[blueprint "lem:words-subset-wordball"
  (statement := /-- $F^m \subseteq B(m,F)$. -/)]
theorem words_subset_wordBall {F : Set (X → X)} {m : ℕ} : words F m ⊆ wordBall F m := by
  cases m with
  | zero => exact le_rfl
  | succ m => rw [wordBall_succ_eq_union_words]; exact Set.subset_union_right

@[blueprint "lem:wordof-mem-wordball"
  (statement := /-- If $|u| \le k$ then $f_u \in B(k,F)$ where $F = \{f_1, \dots, f_r\}$. -/)]
theorem wordOf_mem_wordBall (f : Fin r → X → X) {u : List (Fin r)} {k : ℕ} (hu : u.length ≤ k) :
    wordOf f u ∈ wordBall (Set.range f) k :=
  wordBall_mono hu (words_subset_wordBall (wordOf_mem_words f u))

end Words

section LowerBounds

variable [PseudoEMetricSpace X]

@[blueprint "lem:pow-le-covering-of-probes"
  (statement := /-- Let $f = (f_1,\dots,f_r)$ and let $P$ be a finite family of probes such that
    the evaluations $\mathrm{ev}_P(f_u)$, $u \in [r]^k$, are pairwise at sup-distance
    $\ge \delta > 0$. Then $N^{\mathrm{ext}}(B(k,F), d_\infty, \varepsilon) \ge r^k$ for every
    $\varepsilon$ with $2\varepsilon < \delta$. -/)]
theorem pow_le_externalCoveringNumber_wordBall_of_probes (f : Fin r → X → X) {k : ℕ}
    {κ : Type*} [Fintype κ] (P : κ → X) {δ : ℝ≥0} (hδ : 0 < δ)
    (hsep : ∀ u v : List (Fin r), u.length = k → v.length = k → u ≠ v →
      (δ : ℝ≥0∞) ≤ edist (evalProbes P (wordOf f u)) (evalProbes P (wordOf f v)))
    {ε : ℝ≥0} (hε : 2 * ε < δ) :
    (r : ℕ∞) ^ k ≤ externalCoveringNumber (X := UnifMaps X) ε (wordBall (Set.range f) k) := by
  /-- Index the words of length $k$ by $[r]^{[k]}$ (`List.ofFn`), which has $r^k$ elements, and
    apply `lem:probes-packing-family`. -/
  classical
  have h := card_le_externalCoveringNumber_of_probes P (A := wordBall (Set.range f) k)
    (fun σ : Fin k → Fin r => toUnifMaps (wordOf f (List.ofFn σ)))
    (fun σ => wordOf_mem_wordBall f (by simp)) hδ
    (fun σ τ hne => hsep _ _ List.length_ofFn List.length_ofFn (List.ofFn_injective.ne hne)) hε
  rwa [ENat.card_eq_coe_fintype_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    Nat.cast_pow] at h

@[blueprint "cond:e1-free-iso"
  (statement := /-- \textbf{(E1: free semigroup with one-point uniform separation.)}
    Let $F = \{f_1, \dots, f_r\}$, $r \ge 2$, and suppose there are a base point
    $x_* \in \mathcal X$ and $\delta > 0$ such that for every $k$ and all distinct words
    $u \ne v \in [r]^k$,
    $$d(f_u(x_*), f_v(x_*)) \ge \delta .$$
    Then for every $k$ and every $\varepsilon < \delta/2$,
    $N^{\mathrm{ext}}(B(k,F), d_\infty, \varepsilon) \ge r^k$.
    (The paper's hypothesis (1), that $u \mapsto f_u$ is injective on $[r]^k$, follows from the
    separation hypothesis since $\delta > 0$, so it is omitted; the hypothesis $r \ge 2$ is not
    used in the proof.) -/)]
theorem cond_e1_free_iso (_hr : 2 ≤ r) (f : Fin r → X → X) (x₀ : X) {δ : ℝ≥0} (hδ : 0 < δ)
    (hsep : ∀ k, ∀ u v : List (Fin r), u.length = k → v.length = k → u ≠ v →
      (δ : ℝ≥0∞) ≤ edist (wordOf f u x₀) (wordOf f v x₀)) :
    ∀ k, ∀ ε : ℝ≥0, 2 * ε < δ →
      (r : ℕ∞) ^ k ≤ externalCoveringNumber (X := UnifMaps X) ε (wordBall (Set.range f) k) := by
  /-- Apply `lem:pow-le-covering-of-probes` with the single probe $x_*$. -/
  intro k ε hε
  refine pow_le_externalCoveringNumber_wordBall_of_probes f (fun _ : Fin 1 => x₀) hδ
    (fun u v hu hv huv => ?_) hε
  exact (hsep k u v hu hv huv).trans
    (edist_le_pi_edist (evalProbes (fun _ : Fin 1 => x₀) (wordOf f u))
      (evalProbes (fun _ : Fin 1 => x₀) (wordOf f v)) 0)

@[blueprint "cond:e1p-theoremC"
  (statement := /-- \textbf{(E1': equal-length coding.)}
    Let $F = \{f_1, \dots, f_r\}$, $r \ge 2$, and suppose
    there are $x_* \in \mathcal X$ and $\delta > 0$ with $d(f_u(x_*), f_v(x_*)) \ge \delta$ for
    all distinct $u, v \in [r]^k$ and all $k$. Then
    $N^{\mathrm{ext}}(B(k,F), d_\infty, \varepsilon) \ge r^k$ for all $k$ and all
    $\varepsilon < \delta/2$.
    (This generalizes the paper, which assumes in addition that the generators are isometries,
    that $d_\infty$ is finite on $\langle F\rangle$ and that $u \mapsto f_u$ is injective on
    $[r]^k$: none of these is needed for the lower bound, which follows from
    `cond:e1-free-iso` in one line; the isometry hypothesis only serves, in the paper, to make
    the covering numbers meaningful.) -/)]
theorem cond_e1p_theoremC (hr : 2 ≤ r) (f : Fin r → X → X)
    (x₀ : X) {δ : ℝ≥0} (hδ : 0 < δ)
    (hsep : ∀ k, ∀ u v : List (Fin r), u.length = k → v.length = k → u ≠ v →
      (δ : ℝ≥0∞) ≤ edist (wordOf f u x₀) (wordOf f v x₀)) :
    ∀ k, ∀ ε : ℝ≥0, 2 * ε < δ →
      (r : ℕ∞) ^ k ≤ externalCoveringNumber (X := UnifMaps X) ε (wordBall (Set.range f) k) :=
  cond_e1_free_iso hr f x₀ hδ hsep

end LowerBounds

section PingPong

variable [PseudoEMetricSpace X]

omit [PseudoEMetricSpace X] in
@[blueprint "lem:wordof-mem-of-invariant"
  (statement := /-- If $A \subseteq \mathcal X$ satisfies $f_i(A) \subseteq A$ for all $i$, then
    $f_u(A) \subseteq A$ for every word $u$. -/)]
theorem wordOf_mem_of_forall_image_subset (f : Fin r → X → X) {A : Set X}
    (hA : ∀ i, f i '' A ⊆ A) (u : List (Fin r)) {y : X} (hy : y ∈ A) : wordOf f u y ∈ A := by
  /-- Induction on $u$. -/
  induction u generalizing y with
  | nil => simpa using hy
  | cons i u ih => exact ih (hA i ⟨y, hy, rfl⟩)

omit [PseudoEMetricSpace X] in
@[blueprint "lem:e2-probe"
  (statement := /-- (Probe construction for E2.) Under the hypotheses of `cond:e2-pingpong`,
    for every word $u$ there is a point $x_u \in Q = \{q\} \cup \bigcup_j V_j$ with
    $f_u(x_u) = q$ and $f_v(x_u) \in A = \{a_1, \dots, a_r\}$ for every word $v \ne u$ of the
    same length. -/)]
theorem exists_probe_of_pingpong (f : Fin r → X → X) (U V : Fin r → Set X)
    (hVU : ∀ i, V i ⊆ U i) (a : Fin r → X) (q : X)
    (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hcore : ∀ i, ({q} ∪ ⋃ j, V j) ⊆ f i '' V i)
    (hreset : ∀ i, ∀ x, x ∉ U i → f i x = a i)
    (hanchor : ∀ i, f i '' Set.range a ⊆ Set.range a) (u : List (Fin r)) :
    ∃ x ∈ ({q} ∪ ⋃ j, V j), wordOf f u x = q ∧
      ∀ v : List (Fin r), v.length = u.length → v ≠ u → wordOf f v x ∈ Set.range a := by
  /-- Induction on $u$, building the probe backwards. For $u = \emptyset$ take $x = q$.
    For $u = (i, u')$ with probe $x'$ of $u'$, pick $x \in V_i$ with $f_i(x) = x'$ (coding core).
    Then $f_u(x) = f_{u'}(x') = q$. If $v = (j, v') \ne u$: when $j = i$, $v' \ne u'$ and
    $f_v(x) = f_{v'}(x') \in A$ by induction; when $j \ne i$, $x \in U_i$ lies outside $U_j$
    (chambers are disjoint), so $f_j(x) = a_j \in A$ (reset) and
    $f_{v'}(a_j) \in A$ (invariance of $A$). -/
  have hdisj' : ∀ i j, i ≠ j → ∀ x ∈ U i, x ∉ U j := fun i j hij x hxi hxj =>
    Set.disjoint_left.mp (hdisj i j hij) hxi hxj
  induction u with
  | nil =>
    refine ⟨q, Set.mem_union_left _ rfl, rfl, fun v hv hne => ?_⟩
    exact absurd (List.length_eq_zero_iff.mp hv) hne
  | cons i u ih =>
    obtain ⟨x', hx'Q, hx'u, hx'v⟩ := ih
    obtain ⟨x, hxV, hxx'⟩ := hcore i hx'Q
    refine ⟨x, Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨i, hxV⟩), ?_, fun v hv hne => ?_⟩
    · rw [wordOf_cons_apply, hxx', hx'u]
    · obtain ⟨j, v', rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos
        (by rw [hv]; exact Nat.succ_pos _))
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hv
      by_cases hji : j = i
      · subst hji
        have hv'u : v' ≠ u := fun h => hne (by rw [h])
        rw [wordOf_cons_apply, hxx']
        exact hx'v v' hv hv'u
      · rw [wordOf_cons_apply, hreset j x (hdisj' i j (Ne.symm hji) x (hVU i hxV))]
        exact wordOf_mem_of_forall_image_subset f hanchor v' ⟨j, rfl⟩

@[blueprint "cond:e2-pingpong"
  (statement := /-- \textbf{(E2: ping–pong coding.)} Let $F = \{f_1, \dots, f_r\}$, $r \ge 2$,
    and suppose there are sets $V_i \subseteq U_i \subseteq \mathcal X$,
    anchors $a_1, \dots, a_r \in \mathcal X$, a marker $q \in \mathcal X$ and a constant
    $\alpha > 0$ such that, with $A = \{a_1, \dots, a_r\}$ and
    $Q = \{q\} \cup \bigcup_j V_j$:
    \begin{enumerate}
    \item (disjoint chambers) $U_i \cap U_j = \emptyset$ for $i \ne j$;
    \item (coding cores) $Q \subseteq f_i(V_i)$ for every $i$;
    \item (reset) $f_i(x) = a_i$ for $x \notin U_i$, and $f_i(A) \subseteq A$;
    \item (marker separation) $d(q, a_i) \ge \alpha$ for every $i$.
    \end{enumerate}
    Then (a) $N^{\mathrm{ext}}(B(k,F), d_\infty, \varepsilon) \ge r^k$ for every $k$ and every
    $\varepsilon < \alpha/2$, and (b) $u \mapsto f_u$ is injective on $[r]^k$ for every $k$.
    (This generalizes the paper, which assumes in (1) a uniform separation
    $d(U_i, U_j) \ge \Delta > 0$ and additionally $V_i \ne \emptyset$: the proof uses of (1) only
    the disjointness of the chambers, and $V_i \ne \emptyset$ follows from (2) since
    $q \in f_i(V_i)$; the hypothesis $r \ge 2$ is not used.) -/)]
theorem cond_e2_pingpong (_hr : 2 ≤ r) (f : Fin r → X → X) (U V : Fin r → Set X)
    (hVU : ∀ i, V i ⊆ U i) (a : Fin r → X) (q : X) {α : ℝ≥0} (hα : 0 < α)
    (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hcore : ∀ i, ({q} ∪ ⋃ j, V j) ⊆ f i '' V i)
    (hreset : ∀ i, ∀ x, x ∉ U i → f i x = a i)
    (hanchor : ∀ i, f i '' Set.range a ⊆ Set.range a)
    (hmark : ∀ i, (α : ℝ≥0∞) ≤ edist q (a i)) :
    (∀ k, ∀ ε : ℝ≥0, 2 * ε < α →
      (r : ℕ∞) ^ k ≤ externalCoveringNumber (X := UnifMaps X) ε (wordBall (Set.range f) k)) ∧
    (∀ k, Set.InjOn (wordOf f) {u : List (Fin r) | u.length = k}) := by
  /-- Choose the probes $x_u$ of `lem:e2-probe`. For (a), use the $r^k$ probes
    $P = (x_v)_{v \in [r]^k}$: for $u \ne w$ in $[r]^k$ the evaluations differ at the coordinate
    $w$, where $f_u(x_w) \in A$ and $f_w(x_w) = q$, so they are at distance $\ge \alpha$; conclude
    by `lem:pow-le-covering-of-probes`. For (b), if $f_u = f_v$ with $u \ne v$ of the same
    length then $q = f_u(x_u) = f_v(x_u) \in A$, contradicting $\alpha > 0$. -/
  choose x hxQ hxu hxv using
    exists_probe_of_pingpong f U V hVU a q hdisj hcore hreset hanchor
  have hgap : ∀ u v : List (Fin r), u.length = v.length → u ≠ v →
      (α : ℝ≥0∞) ≤ edist (wordOf f u (x v)) (wordOf f v (x v)) := by
    intro u v huv hne
    obtain ⟨i, hi⟩ := hxv v u huv hne
    rw [hxu v, ← hi, edist_comm]
    exact hmark i
  refine ⟨fun k ε hε => ?_, fun k u hu v hv huv => ?_⟩
  · classical
    refine pow_le_externalCoveringNumber_wordBall_of_probes f
      (fun τ : Fin k → Fin r => x (List.ofFn τ)) hα (fun u v hu hv hne => ?_) hε
    subst hv
    refine le_trans ?_ (edist_le_pi_edist
      (evalProbes (fun τ : Fin v.length → Fin r => x (List.ofFn τ)) (wordOf f u))
      (evalProbes (fun τ : Fin v.length → Fin r => x (List.ofFn τ)) (wordOf f v)) v.get)
    change (α : ℝ≥0∞) ≤ edist (wordOf f u (x (List.ofFn v.get))) (wordOf f v (x (List.ofFn v.get)))
    rw [List.ofFn_get]
    exact hgap u v hu hne
  · by_contra hne
    have h := hgap v u (by rw [hu, hv]) (Ne.symm hne)
    rw [← huv, edist_self, nonpos_iff_eq_zero, ENNReal.coe_eq_zero] at h
    exact hα.ne' h

end PingPong

end LeanDeepgen
