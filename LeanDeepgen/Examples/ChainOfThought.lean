import Mathlib
import Architect
import LeanDeepgen.Setting.WordBall
import LeanDeepgen.Setting.Metrics
import LeanDeepgen.Setting.Covering
import LeanDeepgen.Growth.Lemmas
import LeanDeepgen.Growth.Exponential
import LeanDeepgen.Growth.Saturation
import LeanDeepgen.Profiles.Profiles
import LeanDeepgen.Bounds.HiddenOutput
import LeanDeepgen.Bounds.Variance
import LeanDeepgen.Examples.Regimes

/-!
# Worked example: chain-of-thought style symbolic computation (paper App. `sec:app-cot`)

The scratchpad space is `SeqSpace 𝒜 θ = ℕ → 𝒜` (infinite symbol sequences over a finite alphabet)
with the ultrametric `d_θ(x,y) = θ^{n(x,y)}`, `n(x,y) = min {j : x_j ≠ y_j}`, `0 < θ < 1`.

* `def:cot-state-space`, `def:cot-metric`, `lem:cot-metric-prefix`: the state space, its metric
  (a `MetricSpace` instance), `d_θ ≤ 1`, and the prefix characterization
  `d_θ(x,y) ≤ θ^L ↔ x, y agree on the first L symbols`; compactness (`lem:cot-compact`).
* Append-only steps `F_w = {g_a : a ∈ 𝒜}` (`def:cot-append-step`): each `g_a` is `θ`-Lipschitz
  (`lem:cot-append-lipschitz`), the covering bound `N^ext(B(k,F_w), d_∞, ε) ≤ m^{min{k,ℓ(ε)}+1}`
  (`lem:cot-append-growth`), saturation via P1 (`lem:cot-append-saturation`) and the entropy
  integral bound `V_k(S) ≤ V_∞` (`lem:cot-append-profile`).
* Branching (guarded) steps `F_b = {f_a : a ∈ [r]}` on `𝒜 = [r] ⊔ {•}` (`def:cot-branch-step`):
  the ping–pong hypotheses of `cond:e2-pingpong` hold with `Δ = α = 1`
  (`lem:cot-branch-pingpong`), whence `r^k ≤ N^ext(B(k,F_b), d_∞, ε) ≤ r^{k+1}` for `ε < 1/2`
  and `V_k(S) ≤ √((k+1) log r)` (`lem:cot-branch-growth`, `lem:cot-branch-profile`).
* Window one-hot output features `Φ_L` (`def:cot-window-feature`): `‖Φ_L‖ = 1` and `Φ_L` is
  `√2 θ^{1-L}`-Lipschitz (`lem:cot-output`), so the linear readout class satisfies the
  sub-Gaussian increment condition with `A_H = 1` (`cor:cot-output-sg`, via `prop:hilbert-sg`).

* The rigorous form of `prop:cot-append` (EL regime): for a Lipschitz, bounded feature map `Φ`
  into a separable Hilbert space (e.g. the window features `Φ_L`, scaled) and the linear readout
  class `H_R(Φ)`, the depth-`k` hypothesis class `H_R(Φ) ∘ B(k, F_w)` is measurable, bounded and
  sup-separable (`lem:cot-class-*`), its Rademacher complexity is at most
  `R M_Φ/√n + 12 R L_Φ V_∞/√n` (`lem:cot-append-var`), the bias against the teacher–student class
  `cl(H_R(Φ) ∘ ⟨F_w⟩)` is at most `β_ℓ R L_Φ θ^k` (`lem:cot-append-bias`, truncation), and
  `thm:bv` gives the explicit high-probability excess-risk bound `prop:cot-append`; the depth
  `k = ⌈log n/(2 log(1/θ))⌉` makes `θ^k ≤ n^{-1/2}` (`lem:cot-append-balance`) and the whole bound
  `O(n^{-1/2})` (`cor:cot-append-depth`).

The geometrically weighted feature map `Φ_∞` is not formalized (the propositions above take an
arbitrary Lipschitz bounded feature map).
-/

open scoped NNReal ENNReal UniformConvergence Topology Real
open Metric

open FoML.ToMathlib

namespace LeanDeepgen

/-! ### The scratchpad space and its ultrametric -/

@[blueprint "def:cot-state-space"
  (statement := /-- The scratchpad space is $\mathcal X = \mathcal A^{\mathbb N}
    = \{x = (x_0, x_1, \dots) : x_j \in \mathcal A\}$, the space of infinite symbol sequences
    over the alphabet $\mathcal A$ (a type synonym of $\mathbb N \to \mathcal A$ carrying the
    parameter $\theta$ of the metric below). -/)]
def SeqSpace (𝒜 : Type*) (_θ : ℝ≥0) : Type _ := ℕ → 𝒜

section StateSpace

variable {𝒜 : Type*} {θ : ℝ≥0}

open Classical in
@[blueprint "def:cot-first-diff"
  (statement := /-- For $x \ne y$ the first mismatch index is
    $n(x,y) := \min\{j \ge 0 : x_j \ne y_j\}$. -/)]
noncomputable def firstDiff {x y : SeqSpace 𝒜 θ} (h : x ≠ y) : ℕ :=
  Nat.find (Function.ne_iff.1 h)

open Classical in
@[blueprint "lem:cot-first-diff-spec"
  (statement := /-- $x_{n(x,y)} \ne y_{n(x,y)}$. -/)]
theorem apply_firstDiff_ne {x y : SeqSpace 𝒜 θ} (h : x ≠ y) :
    x (firstDiff h) ≠ y (firstDiff h) :=
  Nat.find_spec (Function.ne_iff.1 h)

open Classical in
@[blueprint "lem:cot-le-first-diff-iff"
  (statement := /-- $L \le n(x,y)$ if and only if $x_j = y_j$ for all $j < L$. -/)]
theorem le_firstDiff_iff {x y : SeqSpace 𝒜 θ} (h : x ≠ y) {L : ℕ} :
    L ≤ firstDiff h ↔ ∀ j < L, x j = y j := by
  unfold firstDiff
  rw [Nat.le_find_iff]
  simp only [not_not]

@[blueprint "lem:cot-first-diff-min"
  (statement := /-- $x_j = y_j$ for all $j < n(x,y)$. -/)]
theorem apply_eq_of_lt_firstDiff {x y : SeqSpace 𝒜 θ} (h : x ≠ y) {j : ℕ}
    (hj : j < firstDiff h) : x j = y j :=
  (le_firstDiff_iff h).1 le_rfl j hj

@[blueprint "lem:cot-first-diff-symm"
  (statement := /-- $n(x,y) = n(y,x)$. -/)]
theorem firstDiff_symm {x y : SeqSpace 𝒜 θ} (h : x ≠ y) :
    firstDiff h = firstDiff (Ne.symm h) := by
  /-- Both indices are characterized by the same prefix-agreement property. -/
  apply le_antisymm
  · exact (le_firstDiff_iff _).2 fun j hj => (apply_eq_of_lt_firstDiff h hj).symm
  · exact (le_firstDiff_iff _).2 fun j hj => (apply_eq_of_lt_firstDiff _ hj).symm

open Classical in
@[blueprint "def:cot-metric"
  (statement := /-- The ultrametric on $\mathcal A^{\mathbb N}$:
    $d_\theta(x,y) = \theta^{n(x,y)}$ for $x \ne y$ and $d_\theta(x,x) = 0$, for a fixed
    $\theta \in (0,1)$. -/)]
noncomputable def seqDist (θ : ℝ≥0) (x y : SeqSpace 𝒜 θ) : ℝ :=
  if h : x = y then 0 else (θ : ℝ) ^ firstDiff h

@[blueprint "lem:cot-theta-pos"
  (statement := /-- $0 < \theta$ (as a real number). -/)]
theorem theta_pos [hθ0 : Fact (0 < θ)] : (0 : ℝ) < θ := hθ0.out

@[blueprint "lem:cot-theta-lt-one"
  (statement := /-- $\theta < 1$ (as a real number). -/)]
theorem theta_lt_one [hθ1 : Fact (θ < 1)] : (θ : ℝ) < 1 := by exact_mod_cast hθ1.out

@[blueprint "lem:cot-seqdist-eq-pow"
  (statement := /-- For $x \ne y$, $d_\theta(x,y) = \theta^{n(x,y)}$. -/)]
theorem seqDist_eq_pow {x y : SeqSpace 𝒜 θ} (h : x ≠ y) :
    seqDist θ x y = (θ : ℝ) ^ firstDiff h := by
  unfold seqDist
  rw [dif_neg h]

@[blueprint "lem:cot-seqdist-comm"
  (statement := /-- $d_\theta(x,y) = d_\theta(y,x)$. -/)]
theorem seqDist_comm (x y : SeqSpace 𝒜 θ) : seqDist θ x y = seqDist θ y x := by
  by_cases h : x = y
  · subst h; rfl
  · rw [seqDist_eq_pow h, seqDist_eq_pow (Ne.symm h), firstDiff_symm h]

variable [Fact (0 < θ)] [Fact (θ < 1)]

@[blueprint "lem:cot-seqdist-le-pow-iff"
  (statement := /-- (Prefix characterization.) $d_\theta(x,y) \le \theta^L$ if and only if
    $x_j = y_j$ for all $j < L$. -/)]
theorem seqDist_le_pow_iff {x y : SeqSpace 𝒜 θ} {L : ℕ} :
    seqDist θ x y ≤ (θ : ℝ) ^ L ↔ ∀ j < L, x j = y j := by
  /-- If $x = y$ both sides hold. Otherwise $\theta^{n(x,y)} \le \theta^L \iff L \le n(x,y)$
    since $0 < \theta < 1$, and $L \le n(x,y)$ is the prefix-agreement property. -/
  unfold seqDist
  split_ifs with h
  · subst h
    simp [pow_nonneg (theta_pos (θ := θ)).le]
  · rw [pow_le_pow_iff_right_of_lt_one₀ theta_pos theta_lt_one, le_firstDiff_iff]

omit [Fact (θ < 1)] in
@[blueprint "lem:cot-seqdist-nonneg"
  (statement := /-- $d_\theta(x,y) \ge 0$. -/)]
theorem seqDist_nonneg (x y : SeqSpace 𝒜 θ) : 0 ≤ seqDist θ x y := by
  unfold seqDist
  split_ifs
  · exact le_rfl
  · exact pow_nonneg (theta_pos (θ := θ)).le _

@[blueprint "lem:cot-seqdist-le-one"
  (statement := /-- $d_\theta(x,y) \le 1$: the scratchpad space has diameter at most $1$. -/)]
theorem seqDist_le_one (x y : SeqSpace 𝒜 θ) : seqDist θ x y ≤ 1 := by
  /-- The case $L = 0$ of the prefix characterization. -/
  have h := (seqDist_le_pow_iff (x := x) (y := y) (L := 0)).2
    fun j hj => absurd hj (Nat.not_lt_zero _)
  simpa using h

@[blueprint "lem:cot-seqdist-ultra"
  (statement := /-- (Ultrametric inequality.)
    $d_\theta(x,z) \le \max\{d_\theta(x,y), d_\theta(y,z)\}$. -/)]
theorem seqDist_le_max (x y z : SeqSpace 𝒜 θ) :
    seqDist θ x z ≤ max (seqDist θ x y) (seqDist θ y z) := by
  /-- If $x = y$ or $y = z$ this is trivial. Otherwise let $L = \min\{n(x,y), n(y,z)\}$; then
    $x, y$ and $y, z$ agree on the first $L$ symbols, hence so do $x, z$, so
    $d_\theta(x,z) \le \theta^L = \max\{\theta^{n(x,y)}, \theta^{n(y,z)}\}$. -/
  by_cases hxy : x = y
  · subst hxy; exact le_max_right _ _
  by_cases hyz : y = z
  · subst hyz; exact le_max_left _ _
  have key : ∀ L : ℕ, seqDist θ x y ≤ (θ : ℝ) ^ L → seqDist θ y z ≤ (θ : ℝ) ^ L →
      seqDist θ x z ≤ (θ : ℝ) ^ L := by
    intro L h1 h2
    rw [seqDist_le_pow_iff] at h1 h2 ⊢
    intro j hj
    rw [h1 j hj, h2 j hj]
  rw [seqDist_eq_pow hxy, seqDist_eq_pow hyz]
  rcases le_total (firstDiff hxy) (firstDiff hyz) with hle | hle
  · have h2 : (θ : ℝ) ^ firstDiff hyz ≤ (θ : ℝ) ^ firstDiff hxy :=
      pow_le_pow_of_le_one (theta_pos (θ := θ)).le theta_lt_one.le hle
    rw [max_eq_left h2]
    exact key _ (by rw [seqDist_eq_pow hxy]) (by rw [seqDist_eq_pow hyz]; exact h2)
  · have h1 : (θ : ℝ) ^ firstDiff hxy ≤ (θ : ℝ) ^ firstDiff hyz :=
      pow_le_pow_of_le_one (theta_pos (θ := θ)).le theta_lt_one.le hle
    rw [max_eq_right h1]
    exact key _ (by rw [seqDist_eq_pow hxy]; exact h1) (by rw [seqDist_eq_pow hyz])

omit [Fact (θ < 1)] in
@[blueprint "lem:cot-seqdist-eq-zero"
  (statement := /-- $d_\theta(x,y) = 0$ implies $x = y$. -/)]
theorem eq_of_seqDist_eq_zero {x y : SeqSpace 𝒜 θ} (h : seqDist θ x y = 0) : x = y := by
  by_contra hne
  rw [seqDist_eq_pow hne] at h
  exact (pow_pos (theta_pos (θ := θ)) _).ne' h

@[blueprint "def:cot-metric-instance"
  (statement := /-- $(\mathcal A^{\mathbb N}, d_\theta)$ is a metric space (indeed an
    ultrametric space). -/)]
noncomputable instance instMetricSpaceSeqSpace : MetricSpace (SeqSpace 𝒜 θ) where
  dist := seqDist θ
  dist_self x := by simp [seqDist]
  dist_comm := seqDist_comm
  dist_triangle x y z :=
    (seqDist_le_max x y z).trans
      (max_le_add_of_nonneg (seqDist_nonneg x y) (seqDist_nonneg y z))
  eq_of_dist_eq_zero := eq_of_seqDist_eq_zero

@[blueprint "lem:cot-dist-seqspace"
  (statement := /-- On $\mathcal A^{\mathbb N}$ the distance is $d_\theta$. -/)]
theorem dist_seqSpace (x y : SeqSpace 𝒜 θ) : dist x y = seqDist θ x y := rfl

@[blueprint "lem:cot-metric-prefix"
  (statement := /-- Two sequences are within distance $\theta^L$ if and only if they agree in
    the first $L$ symbols: $d_\theta(x,y) \le \theta^L \iff \forall j < L,\ x_j = y_j$. -/)]
theorem dist_le_pow_iff {x y : SeqSpace 𝒜 θ} {L : ℕ} :
    dist x y ≤ (θ : ℝ) ^ L ↔ ∀ j < L, x j = y j :=
  seqDist_le_pow_iff

@[blueprint "lem:cot-dist-le-one"
  (statement := /-- $d_\theta(x,y) \le 1$, i.e. $\mathrm{diam}(\mathcal A^{\mathbb N}) \le 1$. -/)]
theorem dist_seqSpace_le_one (x y : SeqSpace 𝒜 θ) : dist x y ≤ 1 := seqDist_le_one x y

@[blueprint "lem:cot-edist-le-one"
  (statement := /-- $d_\theta(x,y) \le 1$ as an extended distance. -/)]
theorem edist_seqSpace_le_one (x y : SeqSpace 𝒜 θ) : edist x y ≤ 1 := by
  rw [edist_dist]
  exact ENNReal.ofReal_le_one.2 (dist_seqSpace_le_one x y)

@[blueprint "lem:cot-dist-eq-one"
  (statement := /-- If $x_0 \ne y_0$ then $d_\theta(x,y) = 1$. -/)]
theorem dist_eq_one_of_apply_zero_ne {x y : SeqSpace 𝒜 θ} (h : x 0 ≠ y 0) : dist x y = 1 := by
  /-- $x \ne y$ and $n(x,y) = 0$. -/
  have hne : x ≠ y := fun hxy => h (by rw [hxy])
  have h0 : firstDiff hne = 0 := by
    by_contra h0
    exact h (apply_eq_of_lt_firstDiff hne (Nat.pos_of_ne_zero h0))
  rw [dist_seqSpace, seqDist_eq_pow hne, h0, pow_zero]

@[blueprint "lem:cot-pow-le-dist"
  (statement := /-- If $x$ and $y$ do not agree on the first $L$ symbols then
    $d_\theta(x,y) \ge \theta^{L-1}$. -/)]
theorem pow_le_dist_of_not_forall {x y : SeqSpace 𝒜 θ} {L : ℕ}
    (h : ¬ ∀ j < L, x j = y j) : (θ : ℝ) ^ (L - 1) ≤ dist x y := by
  /-- $x \ne y$ and $n(x,y) < L$, so $n(x,y) \le L - 1$ and $\theta^{L-1} \le \theta^{n(x,y)}$. -/
  have hne : x ≠ y := by
    rintro rfl
    exact h fun j _ => rfl
  have hlt : firstDiff hne < L := by
    by_contra hL
    exact h ((le_firstDiff_iff hne).1 (not_lt.1 hL))
  rw [dist_seqSpace, seqDist_eq_pow hne]
  exact pow_le_pow_of_le_one (theta_pos (θ := θ)).le theta_lt_one.le (by omega)

@[blueprint "def:cot-to-seqspace"
  (statement := /-- The identity map $\mathcal A^{\mathbb N} \to (\mathcal A^{\mathbb N}, d_\theta)$
    from the product of the discrete spaces. -/)]
def toSeqSpace (x : ℕ → 𝒜) : SeqSpace 𝒜 θ := x

@[blueprint "lem:cot-compact"
  (statement := /-- For a finite alphabet, $(\mathcal A^{\mathbb N}, d_\theta)$ is compact.
    (The identity from the product of discrete spaces is continuous, since a $d_\theta$-ball is a
    cylinder set.) -/)]
instance instCompactSpaceSeqSpace [Finite 𝒜] : CompactSpace (SeqSpace 𝒜 θ) := by
  /-- Equip $\mathcal A$ with the discrete topology; $\mathcal A^{\mathbb N}$ with the product
    topology is compact (Tychonoff). The identity map to $(\mathcal A^{\mathbb N}, d_\theta)$ is
    continuous: given $\varepsilon > 0$ pick $L$ with $\theta^L < \varepsilon$; the cylinder
    $\{y : y_j = x_j,\ j < L\}$ is a product neighbourhood of $x$ contained in the
    $\varepsilon$-ball. The continuous image of a compact space is compact. -/
  letI : TopologicalSpace 𝒜 := ⊥
  haveI : DiscreteTopology 𝒜 := ⟨rfl⟩
  haveI : CompactSpace 𝒜 := Finite.compactSpace
  have hcont : Continuous (toSeqSpace (𝒜 := 𝒜) (θ := θ)) := by
    rw [continuous_iff_continuousAt]
    intro x
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨L, hL⟩ := exists_pow_lt_of_lt_one hε (theta_lt_one (θ := θ))
    have hcyl : ∀ᶠ y in 𝓝 x, ∀ j ∈ Finset.range L, y j = x j := by
      rw [Filter.eventually_all_finset]
      intro j _
      have hmem : (fun y : ℕ → 𝒜 => y j) ⁻¹' {x j} ∈ 𝓝 x :=
        (continuous_apply j).continuousAt.preimage_mem_nhds
          ((isOpen_discrete _).mem_nhds rfl)
      exact Filter.eventually_of_mem hmem fun y hy => hy
    filter_upwards [hcyl] with y hy
    calc dist (toSeqSpace (θ := θ) y) (toSeqSpace (θ := θ) x) ≤ (θ : ℝ) ^ L :=
          dist_le_pow_iff.2 fun j hj => hy j (Finset.mem_range.2 hj)
      _ < ε := hL
  exact Function.Surjective.compactSpace hcont fun x => ⟨x, rfl⟩

@[blueprint "lem:cot-empdiam-le-one"
  (statement := /-- Since $\mathrm{diam}(\mathcal A^{\mathbb N}) \le 1$ and $d_S \le d_\infty$,
    the empirical diameter of any class of self-maps of $\mathcal A^{\mathbb N}$ is at most
    $1$: $D_k(S) \le 1$. -/)]
theorem empDiam_seqSpace_le_one {n : ℕ} (S : Fin n → SeqSpace 𝒜 θ)
    (A : Set (SeqSpace 𝒜 θ → SeqSpace 𝒜 θ)) : empDiam S A ≤ 1 :=
  /- `lem:empDiam-le-of-bounded` with $D_{\mathcal X} = 1$. -/
  empDiam_le_of_bounded S zero_le_one dist_seqSpace_le_one A

end StateSpace

/-! ### Append-only steps -/

section Append

variable {𝒜 : Type*} (θ : ℝ≥0)

@[blueprint "def:cot-append-step"
  (statement := /-- A write step prepends a symbol: $g_a(x) := (a, x_0, x_1, \dots)$ for
    $a \in \mathcal A$. -/)]
def append (a : 𝒜) : SeqSpace 𝒜 θ → SeqSpace 𝒜 θ := fun x j =>
  match j with
  | 0 => a
  | i + 1 => x i

@[blueprint "def:cot-append-class"
  (statement := /-- The append-only step family $F_{\rm w} := \{g_a : a \in \mathcal A\}$. -/)]
def appendClass : Set (SeqSpace 𝒜 θ → SeqSpace 𝒜 θ) := Set.range (append θ)

@[simp, blueprint "lem:cot-append-apply-zero"
  (statement := /-- $g_a(x)_0 = a$. -/)]
theorem append_apply_zero (a : 𝒜) (x : SeqSpace 𝒜 θ) : append θ a x 0 = a := rfl

@[simp, blueprint "lem:cot-append-apply-succ"
  (statement := /-- $g_a(x)_{i+1} = x_i$. -/)]
theorem append_apply_succ (a : 𝒜) (x : SeqSpace 𝒜 θ) (i : ℕ) : append θ a x (i + 1) = x i := rfl

@[blueprint "lem:cot-append-injective"
  (statement := /-- $a \mapsto g_a$ is injective, so $|F_{\rm w}| = |\mathcal A| = m$. -/)]
theorem append_injective : Function.Injective (append (𝒜 := 𝒜) θ) := by
  intro a b h
  exact congrFun (congrFun h (fun _ => a)) 0

@[blueprint "lem:cot-append-class-finite"
  (statement := /-- $F_{\rm w}$ is finite. -/)]
theorem appendClass_finite [Finite 𝒜] : (appendClass (𝒜 := 𝒜) θ).Finite := Set.finite_range _

@[blueprint "lem:cot-append-class-ncard"
  (statement := /-- $|F_{\rm w}| = m = |\mathcal A|$. -/)]
theorem appendClass_ncard [Fintype 𝒜] : (appendClass (𝒜 := 𝒜) θ).ncard = Fintype.card 𝒜 := by
  rw [appendClass, Set.ncard_range_of_injective (append_injective θ), Nat.card_eq_fintype_card]

variable {θ} [Fact (0 < θ)] [Fact (θ < 1)]

@[blueprint "lem:cot-append-lipschitz"
  (statement := /-- Each write step is $\theta$-Lipschitz:
    $d_\theta(g_a(x), g_a(y)) \le \theta\, d_\theta(x,y)$ (in fact with equality). Hence
    $F_{\rm w}$ is a contractive hidden-layer class with $\mathrm{lip}(g_a) = \theta < 1$. -/)]
theorem lipschitzWith_append (a : 𝒜) : LipschitzWith θ (append θ a) := by
  /-- If $x = y$ there is nothing to prove. Otherwise $g_a(x)$ and $g_a(y)$ agree on the first
    $n(x,y) + 1$ symbols, so
    $d_\theta(g_a(x), g_a(y)) \le \theta^{n(x,y)+1} = \theta\,d_\theta(x,y)$. -/
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  by_cases hxy : x = y
  · subst hxy; simp
  rw [dist_seqSpace x y, seqDist_eq_pow hxy, ← pow_succ']
  refine dist_le_pow_iff.2 fun j hj => ?_
  cases j with
  | zero => rfl
  | succ i =>
    simp only [append_apply_succ]
    exact apply_eq_of_lt_firstDiff hxy (by omega)

@[blueprint "lem:cot-append-nonexpanding"
  (statement := /-- Each write step is non-expanding ($1$-Lipschitz). -/)]
theorem lipschitzWith_one_of_mem_appendClass {g : SeqSpace 𝒜 θ → SeqSpace 𝒜 θ}
    (hg : g ∈ appendClass θ) : LipschitzWith 1 g := by
  obtain ⟨a, rfl⟩ := hg
  exact (lipschitzWith_append a).weaken (Fact.out : θ < 1).le

@[blueprint "lem:cot-append-saturation"
  (statement := /-- (Saturation via P1.) For a finite alphabet and every $\varepsilon > 0$,
    $N^{\mathrm{ext}}(B(k,F_{\rm w}), d_\infty, \varepsilon)
    \le N^{\mathrm{ext}}(\overline{\langle F_{\rm w}\rangle}, d_\infty, \varepsilon) < \infty$
    uniformly in $k$. -/)]
theorem cot_append_saturation [Finite 𝒜] (ε : ℝ≥0) (hε : 0 < ε) (k : ℕ) :
    externalCoveringNumber (X := UnifMaps (SeqSpace 𝒜 θ)) ε (wordBall (appendClass θ) k) ≤
        externalCoveringNumber (X := UnifMaps (SeqSpace 𝒜 θ)) ε
          (closure (X := UnifMaps (SeqSpace 𝒜 θ)) (semigroupClosure (appendClass θ))) ∧
      externalCoveringNumber (X := UnifMaps (SeqSpace 𝒜 θ)) ε
        (closure (X := UnifMaps (SeqSpace 𝒜 θ)) (semigroupClosure (appendClass θ))) ≠ ⊤ :=
  /- `cond:p1-2c` on the compact space $\mathcal A^{\mathbb N}$. -/
  cond_p1_of_nonexpanding (fun _ hg => lipschitzWith_one_of_mem_appendClass hg) ε hε k

omit [Fact (0 < θ)] [Fact (θ < 1)] in
@[blueprint "lem:cot-words-agree"
  (statement := /-- A word of $\ell$ write steps determines the first $\ell$ symbols of its
    output independently of the input: for $w \in F_{\rm w}^{\ell}$ and all $x, y$,
    $w(x)_j = w(y)_j$ for $j < \ell$. -/)]
theorem apply_eq_of_mem_words_appendClass {ℓ : ℕ} {w : SeqSpace 𝒜 θ → SeqSpace 𝒜 θ}
    (hw : w ∈ words (appendClass θ) ℓ) (x y : SeqSpace 𝒜 θ) : ∀ j < ℓ, w x j = w y j := by
  /-- Induction on $\ell$: for $w = g_a \circ w'$, the symbol $0$ is $a$ for both inputs and the
    symbols $1, \dots, \ell$ are the first $\ell - 1$ symbols of $w'(x)$, $w'(y)$. -/
  induction ℓ generalizing w with
  | zero => intro j hj; exact absurd hj (Nat.not_lt_zero _)
  | succ ℓ ih =>
    obtain ⟨g, ⟨a, rfl⟩, w', hw', rfl⟩ := hw
    intro j hj
    cases j with
    | zero => rfl
    | succ i =>
      simp only [Function.comp_apply, append_apply_succ]
      exact ih hw' i (by omega)

@[blueprint "def:cot-length"
  (statement := /-- The resolution length
    $\ell(\varepsilon) := \lceil \log(1/\varepsilon)/\log(1/\theta) \rceil$
    (a natural number; $0$ for $\varepsilon \ge 1$). -/)]
noncomputable def cotLength (θ ε : ℝ≥0) : ℕ :=
  ⌈Real.log (1 / (ε : ℝ)) / Real.log (1 / (θ : ℝ))⌉₊

@[blueprint "lem:cot-log-inv-theta-pos"
  (statement := /-- $\log(1/\theta) > 0$. -/)]
theorem log_one_div_theta_pos : 0 < Real.log (1 / (θ : ℝ)) :=
  Real.log_pos (one_lt_one_div theta_pos theta_lt_one)

@[blueprint "lem:cot-pow-length-le"
  (statement := /-- $\theta^{\ell(\varepsilon)} \le \varepsilon$ for every $\varepsilon > 0$. -/)]
theorem pow_cotLength_le {ε : ℝ≥0} (hε : 0 < ε) : (θ : ℝ) ^ cotLength θ ε ≤ ε := by
  /-- $\ell(\varepsilon) \ge \log(1/\varepsilon)/\log(1/\theta)$, so
    $\log(1/\varepsilon) \le \log((1/\theta)^{\ell(\varepsilon)})$ and
    $1/\varepsilon \le 1/\theta^{\ell(\varepsilon)}$. -/
  have hε' : (0 : ℝ) < ε := hε
  have hb := log_one_div_theta_pos (θ := θ)
  have h1 : Real.log (1 / (ε : ℝ)) / Real.log (1 / (θ : ℝ)) ≤ cotLength θ ε := Nat.le_ceil _
  rw [div_le_iff₀ hb, ← Real.log_pow, Real.log_le_log_iff (one_div_pos.2 hε')
    (pow_pos (one_div_pos.2 theta_pos) _), one_div_pow,
    one_div_le_one_div hε' (pow_pos theta_pos _)] at h1
  exact h1

@[blueprint "lem:cot-length-le"
  (statement := /-- For $0 < \varepsilon \le 1$,
    $\ell(\varepsilon) \le \log(1/\varepsilon)/\log(1/\theta) + 1$. -/)]
theorem cotLength_le {ε : ℝ≥0} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (cotLength θ ε : ℝ) ≤ Real.log (1 / (ε : ℝ)) / Real.log (1 / (θ : ℝ)) + 1 := by
  /-- $\lceil a \rceil < a + 1$ for $a \ge 0$; here $a \ge 0$ since $\varepsilon \le 1$. -/
  have hε' : (0 : ℝ) < ε := hε
  have hε1' : (ε : ℝ) ≤ 1 := by exact_mod_cast hε1
  have ha : 0 ≤ Real.log (1 / (ε : ℝ)) / Real.log (1 / (θ : ℝ)) :=
    div_nonneg (Real.log_nonneg (one_le_one_div hε' hε1')) log_one_div_theta_pos.le
  exact (Nat.ceil_lt_add_one ha).le

@[blueprint "lem:cot-append-cover"
  (statement := /-- (The short words cover the word ball.) For every $\varepsilon > 0$ and $k$,
    the word ball $B(\min\{k, \ell(\varepsilon)\}, F_{\rm w}) \subseteq B(k, F_{\rm w})$ is an
    $\varepsilon$-cover of $B(k,F_{\rm w})$ in $d_\infty$: a word $g_u$ with $|u| > \ell$ is
    within $\theta^{\ell} \le \varepsilon$ of the word $g_{u'}$ formed by its last $\ell$
    letters. -/)]
theorem isCover_wordBall_appendClass {ε : ℝ≥0} (hε : 0 < ε) (k : ℕ) :
    IsCover (X := UnifMaps (SeqSpace 𝒜 θ)) ε (wordBall (appendClass θ) k)
      (wordBall (appendClass θ) (min k (cotLength θ ε))) := by
  /-- Let $f \in F_{\rm w}^l$ with $l \le k$. If $l \le \ell(\varepsilon)$ then $f$ itself lies
    in the cover. Otherwise factor $f = w_2 \circ w_1$ with $w_2 \in F_{\rm w}^{\ell(\varepsilon)}$
    (the last $\ell(\varepsilon)$ letters); $w_2(w_1(x))$ and $w_2(x)$ agree on the first
    $\ell(\varepsilon)$ symbols, so $d_\infty(f, w_2) \le \theta^{\ell(\varepsilon)} \le
    \varepsilon$. -/
  set ℓ := cotLength θ ε with hℓ
  intro f hf
  obtain ⟨l, hlk, hfl⟩ := mem_wordBall_iff.1 hf
  by_cases hlℓ : l ≤ ℓ
  · refine ⟨f, wordBall_mono (le_min hlk hlℓ) (words_subset_wordBall hfl), ?_⟩
    simp
  · rw [not_le] at hlℓ
    obtain ⟨n, rfl⟩ : ∃ n, l = ℓ + n := ⟨l - ℓ, by omega⟩
    obtain ⟨w₂, hw₂, w₁, hw₁, rfl⟩ := exists_comp_of_mem_words_add hfl
    have hℓk : min k ℓ = ℓ := min_eq_right (by omega)
    refine ⟨w₂, by rw [hℓk]; exact words_subset_wordBall hw₂, ?_⟩
    change edist (toUnifMaps (w₂ ∘ w₁)) (toUnifMaps w₂) ≤ ε
    rw [← ENNReal.ofReal_coe_nnreal]
    refine UniformFun.edist_le.2 fun x => ?_
    rw [edist_le_ofReal ε.coe_nonneg]
    calc dist ((w₂ ∘ w₁) x) (w₂ x) ≤ (θ : ℝ) ^ ℓ :=
          dist_le_pow_iff.2 (apply_eq_of_mem_words_appendClass hw₂ (w₁ x) x)
      _ ≤ ε := pow_cotLength_le hε

@[blueprint "lem:cot-append-growth"
  (statement := /-- \textbf{(Saturation for append-only steps.)} Let $|\mathcal A| = m \ge 2$.
    For $\varepsilon > 0$ let $\ell(\varepsilon) := \lceil\log(1/\varepsilon)/\log(1/\theta)\rceil$.
    Then for all $k \ge 0$,
    $$N^{\mathrm{ext}}\bigl(B(k,F_{\rm w}), d_\infty, \varepsilon\bigr)
      \le m^{\min\{k,\ell(\varepsilon)\}+1} .$$ -/)]
theorem cot_append_growth [Fintype 𝒜] (hm : 2 ≤ Fintype.card 𝒜) {ε : ℝ≥0} (hε : 0 < ε)
    (k : ℕ) :
    externalCoveringNumber (X := UnifMaps (SeqSpace 𝒜 θ)) ε (wordBall (appendClass θ) k) ≤
      (Fintype.card 𝒜 : ℕ∞) ^ (min k (cotLength θ ε) + 1) := by
  /-- The cover of `lem:cot-append-cover` has at most
    $\sum_{j \le \min\{k,\ell(\varepsilon)\}} m^j \le m^{\min\{k,\ell(\varepsilon)\}+1}$
    elements (`lem:wordball-card`). -/
  exact (isCover_wordBall_appendClass hε k).externalCoveringNumber_le_encard.trans
    (encard_wordBall_le_pow (appendClass_finite θ) (appendClass_ncard θ) hm)

@[blueprint "lem:cot-append-growth-internal"
  (statement := /-- The same bound for the internal covering number in $d_\infty$ and in $d_S$:
    $N(B(k,F_{\rm w}), d_S, \varepsilon) \le N(B(k,F_{\rm w}), d_\infty, \varepsilon)
    \le m^{\min\{k,\ell(\varepsilon)\}+1}$ (the cover consists of elements of
    $B(k,F_{\rm w})$). -/)]
theorem cot_append_growth_empSpace [Fintype 𝒜] (hm : 2 ≤ Fintype.card 𝒜) {n : ℕ}
    (S : Fin n → SeqSpace 𝒜 θ) {ε : ℝ≥0} (hε : 0 < ε) (k : ℕ) :
    Metric.coveringNumber (X := EmpSpace S) ε (wordBall (appendClass θ) k) ≤
      (Fintype.card 𝒜 : ℕ∞) ^ (min k (cotLength θ ε) + 1) := by
  /-- `lem:covering-empSpace-le-unifMaps-internal`, then the internal cover
    $B(\min\{k,\ell(\varepsilon)\}, F_{\rm w}) \subseteq B(k,F_{\rm w})$. -/
  refine (coveringNumber_empSpace_le S ε _).trans ?_
  refine (IsCover.coveringNumber_le_encard (X := UnifMaps (SeqSpace 𝒜 θ))
    (wordBall_mono (min_le_left _ _)) (isCover_wordBall_appendClass hε k)).trans ?_
  exact encard_wordBall_le_pow (appendClass_finite θ) (appendClass_ncard θ) hm

@[blueprint "lem:cot-append-entropy-pointwise"
  (statement := /-- For $0 < \varepsilon \le 1$ and $m \ge 2$,
    $\sqrt{\log N(B(k,F_{\rm w}), d_S, \varepsilon)}
      \le \sqrt{\log m}\Bigl(\frac{\sqrt{\log(1/\varepsilon)}}{\sqrt{\log(1/\theta)}}
      + \sqrt 2\Bigr)$, using $\ell(\varepsilon) + 1 \le
      \log(1/\varepsilon)/\log(1/\theta) + 2$ and $\sqrt{a+b} \le \sqrt a + \sqrt b$. -/)]
theorem sqrt_metricEntropy_wordBall_appendClass_le [Fintype 𝒜] (hm : 2 ≤ Fintype.card 𝒜)
    {n : ℕ} (S : Fin n → SeqSpace 𝒜 θ) (k : ℕ) {ε : ℝ} (hε : ε ∈ Set.Ioc (0 : ℝ) 1) :
    √(metricEntropy (X := EmpSpace S) ε.toNNReal (wordBall (appendClass θ) k)) ≤
      √(Real.log (Fintype.card 𝒜)) *
        (√(Real.log (1 / ε)) / √(Real.log (1 / (θ : ℝ))) + √2) := by
  /-- $\log N \le (\ell(\varepsilon)+1)\log m \le
    (\log(1/\varepsilon)/\log(1/\theta) + 2)\log m$; take square roots. -/
  set m := Fintype.card 𝒜 with hm_def
  have hε0 : (0 : ℝ) < ε := hε.1
  have hεnn : 0 < ε.toNNReal := Real.toNNReal_pos.2 hε0
  have hε1 : ε.toNNReal ≤ 1 := by
    rw [← Real.toNNReal_one]
    exact Real.toNNReal_le_toNNReal hε.2
  have hcoe : ((ε.toNNReal : ℝ≥0) : ℝ) = ε := Real.coe_toNNReal _ hε0.le
  set ℓ := cotLength θ ε.toNNReal with hℓ
  have hlogm : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  have hb := log_one_div_theta_pos (θ := θ)
  -- the entropy bound
  have h1 : Metric.coveringNumber (X := EmpSpace S) ε.toNNReal (wordBall (appendClass θ) k) ≤
      ((m ^ (ℓ + 1) : ℕ) : ℕ∞) := by
    refine (cot_append_growth_empSpace hm S hεnn k).trans ?_
    rw [Nat.cast_pow]
    exact_mod_cast Nat.pow_le_pow_right (by omega) (by omega)
  have h2 := log_toReal_toENNReal_mono (ENat.coe_ne_top _) h1
  rw [ENat.toENNReal_coe, ENNReal.toReal_natCast, Nat.cast_pow, Real.log_pow] at h2
  have h3 : metricEntropy (X := EmpSpace S) ε.toNNReal (wordBall (appendClass θ) k) ≤
      (Real.log (1 / ε) / Real.log (1 / (θ : ℝ)) + 2) * Real.log m := by
    refine h2.trans ?_
    have hℓle := cotLength_le (θ := θ) hεnn hε1
    rw [hcoe] at hℓle
    push_cast
    nlinarith
  calc √(metricEntropy (X := EmpSpace S) ε.toNNReal (wordBall (appendClass θ) k))
      ≤ √((Real.log (1 / ε) / Real.log (1 / (θ : ℝ)) + 2) * Real.log m) :=
        Real.sqrt_le_sqrt h3
    _ = √(Real.log m) * √(Real.log (1 / ε) / Real.log (1 / (θ : ℝ)) + 2) := by
        rw [mul_comm, Real.sqrt_mul hlogm]
    _ ≤ √(Real.log m) * (√(Real.log (1 / ε) / Real.log (1 / (θ : ℝ))) + √2) :=
        mul_le_mul_of_nonneg_left (sqrt_add_le _ _) (Real.sqrt_nonneg _)
    _ = _ := by rw [Real.sqrt_div' _ hb.le]

@[blueprint "lem:cot-append-profile"
  (statement := /-- \textbf{(Saturated variance profile for append-only steps.)} Let
    $|\mathcal A| = m \ge 2$. For every sample $S$ and every $k \ge 0$,
    $$\mathsf V_k(S) = \int_0^{D_k(S)} \sqrt{\log N(B(k,F_{\rm w}), d_S, \varepsilon)}\,
      d\varepsilon \le \sqrt{\log m}\Bigl(\frac{\sqrt\pi}{2\sqrt{\log(1/\theta)}} + \sqrt2\Bigr)
      =: \mathsf V_\infty .$$
    (Case (i) of `prop:profiles`: the entropy integral does not depend on the depth $k$.) -/)]
theorem cot_append_profile [Fintype 𝒜] (hm : 2 ≤ Fintype.card 𝒜) {n : ℕ}
    (S : Fin n → SeqSpace 𝒜 θ) (k : ℕ) :
    entropyIntegral (Y := EmpSpace S) (empDiam S (wordBall (appendClass θ) k))
        (wordBall (appendClass θ) k) ≤
      √(Real.log (Fintype.card 𝒜)) *
        (√π / (2 * √(Real.log (1 / (θ : ℝ)))) + √2) := by
  /-- Since $D_k(S) \le 1$, dominate the integrand on $(0,1]$ by
    `lem:cot-append-entropy-pointwise` and use
    $\int_0^1 \sqrt{\log(1/\varepsilon)}\,d\varepsilon = \sqrt\pi/2$ (`lem:log-split`). -/
  have hb := log_one_div_theta_pos (θ := θ)
  have hint : IntervalIntegrable (fun ε : ℝ => √(Real.log (1 / ε))) MeasureTheory.volume 0 1 :=
    intervalIntegrable_sqrt_log_div one_pos
  have hg : IntervalIntegrable
      (fun ε : ℝ => √(Real.log (Fintype.card 𝒜)) *
        (√(Real.log (1 / ε)) / √(Real.log (1 / (θ : ℝ))) + √2)) MeasureTheory.volume 0 1 :=
    ((hint.div_const _).add intervalIntegrable_const).const_mul _
  refine (entropyIntegral_le_integral_of_le (empDiam_nonneg S _)
    (empDiam_seqSpace_le_one S _) hg
    fun ε hε => sqrt_metricEntropy_wordBall_appendClass_le hm S k hε).trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hint.div_const _)
    intervalIntegrable_const, intervalIntegral.integral_div, intervalIntegral.integral_const,
    integral_sqrt_log_div one_pos]
  simp only [smul_eq_mul, sub_zero, mul_one]
  have hsq : 0 < √(Real.log (1 / (θ : ℝ))) := Real.sqrt_pos.2 hb
  field_simp

end Append

/-! ### Branching (guarded) steps -/

section Branch

@[blueprint "def:cot-branch-alphabet"
  (statement := /-- The alphabet $\mathcal A = [r] \cup \{\bullet\}$ with $r$ active symbols and
    one padding symbol $\bullet$. -/)]
abbrev BranchAlphabet (r : ℕ) : Type := Fin r ⊕ Unit

variable (θ : ℝ≥0) {r : ℕ}

@[blueprint "def:cot-shift"
  (statement := /-- The shift $\sigma(x) = (x_1, x_2, \dots)$. -/)]
def shift {𝒜 : Type*} : SeqSpace 𝒜 θ → SeqSpace 𝒜 θ := fun x j => x (j + 1)

@[blueprint "def:cot-const-seq"
  (statement := /-- The constant sequence $\bar a = (a, a, \dots)$. -/)]
def constSeq {𝒜 : Type*} (a : 𝒜) : SeqSpace 𝒜 θ := fun _ => a

@[blueprint "def:cot-branch-step"
  (statement := /-- A guarded step $f_a$, $a \in [r]$, reads the current symbol: if it equals
    $a$ the step consumes it, $f_a(x) = \sigma(x)$; otherwise it resets to the constant error
    state $\bar a$. -/)]
def guarded (i : Fin r) : SeqSpace (BranchAlphabet r) θ → SeqSpace (BranchAlphabet r) θ :=
  fun x => if x 0 = Sum.inl i then shift θ x else constSeq θ (Sum.inl i)

@[blueprint "def:cot-branch-class"
  (statement := /-- The branching step family $F_{\rm b} := \{f_a : a \in [r]\}$. -/)]
def branchClass : Set (SeqSpace (BranchAlphabet r) θ → SeqSpace (BranchAlphabet r) θ) :=
  Set.range (guarded θ)

@[blueprint "lem:cot-shift-append"
  (statement := /-- $\sigma(g_a(y)) = y$. -/)]
theorem shift_append {𝒜 : Type*} (a : 𝒜) (y : SeqSpace 𝒜 θ) : shift θ (append θ a y) = y := rfl

@[blueprint "lem:cot-shift-const"
  (statement := /-- $\sigma(\bar a) = \bar a$. -/)]
theorem shift_constSeq {𝒜 : Type*} (a : 𝒜) : shift θ (constSeq θ a) = constSeq θ a := rfl

@[blueprint "lem:cot-guarded-of-ne"
  (statement := /-- If $x_0 \ne a$ then $f_a(x) = \bar a$. -/)]
theorem guarded_of_ne (i : Fin r) {x : SeqSpace (BranchAlphabet r) θ} (h : x 0 ≠ Sum.inl i) :
    guarded θ i x = constSeq θ (Sum.inl i) := by
  unfold guarded; rw [if_neg h]

@[blueprint "lem:cot-guarded-of-eq"
  (statement := /-- If $x_0 = a$ then $f_a(x) = \sigma(x)$. -/)]
theorem guarded_of_eq (i : Fin r) {x : SeqSpace (BranchAlphabet r) θ} (h : x 0 = Sum.inl i) :
    guarded θ i x = shift θ x := by
  unfold guarded; rw [if_pos h]

@[blueprint "lem:cot-guarded-const"
  (statement := /-- $f_a(\bar a) = \bar a$ and $f_a(\bar b) = \bar a$ for $b \ne a$: the
    anchors are mapped to anchors. -/)]
theorem guarded_constSeq (i j : Fin r) :
    guarded θ i (constSeq θ (Sum.inl j)) = constSeq θ (Sum.inl i) := by
  by_cases h : (Sum.inl j : BranchAlphabet r) = Sum.inl i
  · rw [guarded_of_eq θ i h, shift_constSeq, Sum.inl.inj h]
  · exact guarded_of_ne θ i h

@[blueprint "lem:cot-guarded-injective"
  (statement := /-- $a \mapsto f_a$ is injective, so $|F_{\rm b}| = r$. -/)]
theorem guarded_injective : Function.Injective (guarded (r := r) θ) := by
  /-- $f_a(\bar a) = \bar a$ while $f_b(\bar a) = \bar b$. -/
  intro i j h
  have := congrFun (congrFun h (constSeq θ (Sum.inl i))) 0
  rw [guarded_constSeq, guarded_constSeq] at this
  have h0 : (Sum.inl i : BranchAlphabet r) = Sum.inl j := this
  exact Sum.inl.inj h0

@[blueprint "lem:cot-branch-class-ncard"
  (statement := /-- $|F_{\rm b}| = r$. -/)]
theorem branchClass_ncard : (branchClass (r := r) θ).ncard = r := by
  rw [branchClass, Set.ncard_range_of_injective (guarded_injective θ), Nat.card_eq_fintype_card,
    Fintype.card_fin]

variable {θ} [Fact (0 < θ)] [Fact (θ < 1)]

@[blueprint "lem:cot-branch-pingpong"
  (statement := /-- \textbf{(The branching family is a ping–pong family,
    `ex:e2-pingpong-subshift`.)} With chambers $U_a = V_a = \{x : x_0 = a\}$, anchors
    $\bar a$, marker $\bar\bullet$ and $\alpha = 1$, $F_{\rm b}$ satisfies the
    hypotheses of `cond:e2-pingpong` (the chambers are disjoint; they are in fact
    $1$-separated, which the paper's form of E2 requires). Consequently, for $r \ge 2$,
    $N^{\mathrm{ext}}(B(k,F_{\rm b}), d_\infty, \varepsilon) \ge r^k$ for every $k$ and every
    $\varepsilon < 1/2$, and $u \mapsto f_u$ is injective on $[r]^k$. -/)]
theorem cot_branch_pingpong (hr : 2 ≤ r) :
    (∀ k, ∀ ε : ℝ≥0, 2 * ε < 1 →
      (r : ℕ∞) ^ k ≤ externalCoveringNumber (X := UnifMaps (SeqSpace (BranchAlphabet r) θ)) ε
        (wordBall (branchClass θ) k)) ∧
    (∀ k, Set.InjOn (wordOf (guarded θ)) {u : List (Fin r) | u.length = k}) := by
  /-- Verify the four ping–pong conditions: (1) sequences in different chambers differ at
    index $0$, so the chambers are disjoint; (2) $y = f_a(g_a(y))$ with $g_a(y) \in V_a$; (3) the
    reset is the definition of $f_a$ off $U_a$, and anchors go to anchors
    (`lem:cot-guarded-const`); (4) $\bar\bullet_0 = \bullet \ne a = \bar a_0$, so
    $d(\bar\bullet, \bar a) = 1$. -/
  have hedist_one : ∀ x y : SeqSpace (BranchAlphabet r) θ, x 0 ≠ y 0 →
      ((1 : ℝ≥0) : ℝ≥0∞) ≤ edist x y := by
    intro x y hxy
    rw [edist_dist, dist_eq_one_of_apply_zero_ne hxy]
    simp
  have h := cond_e2_pingpong hr (guarded θ)
    (fun i => {x | x 0 = Sum.inl i}) (fun i => {x | x 0 = Sum.inl i}) (fun _ => le_rfl)
    (fun i => constSeq θ (Sum.inl i))
    (constSeq θ (Sum.inr ())) (α := 1) one_pos
    (fun i j hij => Set.disjoint_left.mpr fun x hx hy => by
      change x 0 = Sum.inl i at hx
      change x 0 = Sum.inl j at hy
      exact hij (Sum.inl.inj (hx.symm.trans hy)))
    (fun i y _ => ⟨append θ (Sum.inl i) y, rfl, by
      rw [guarded_of_eq θ i rfl, shift_append]⟩)
    (fun i x hx => guarded_of_ne θ i hx)
    (fun i => by
      rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨i, (guarded_constSeq θ i j).symm⟩)
    (fun i => hedist_one _ _ Sum.inr_ne_inl)
  exact ⟨fun k ε hε => h.1 k ε (by simpa using hε), h.2⟩

@[blueprint "lem:cot-branch-growth"
  (statement := /-- \textbf{(Exponential growth for branching steps.)} For $r \ge 2$, every
    $k \ge 0$ and every $\varepsilon < 1/2$,
    $$r^k \le N^{\mathrm{ext}}\bigl(B(k,F_{\rm b}), d_\infty, \varepsilon\bigr) \le r^{k+1} .$$
    The lower bound is the ping–pong bound `cond:e2-pingpong`; the upper bound holds because
    $F_{\rm b}$ is finite, so $|B(k,F_{\rm b})| \le \sum_{j \le k} r^j \le r^{k+1}$. -/)]
theorem cot_branch_growth (hr : 2 ≤ r) (k : ℕ) {ε : ℝ≥0} (hε : 2 * ε < 1) :
    (r : ℕ∞) ^ k ≤ externalCoveringNumber (X := UnifMaps (SeqSpace (BranchAlphabet r) θ)) ε
        (wordBall (branchClass θ) k) ∧
      externalCoveringNumber (X := UnifMaps (SeqSpace (BranchAlphabet r) θ)) ε
        (wordBall (branchClass θ) k) ≤ (r : ℕ∞) ^ (k + 1) :=
  ⟨(cot_branch_pingpong hr).1 k ε hε,
    (externalCoveringNumber_le_encard_self _).trans
      (encard_wordBall_le_pow (Set.finite_range _) (branchClass_ncard θ) hr)⟩

@[blueprint "lem:cot-branch-profile"
  (statement := /-- For $r \ge 2$, every sample $S$ and every $k$,
    $\mathsf V_k(S) \le \sqrt{(k+1)\log r}$ (case (iii) of `prop:profiles`, with
    $\overline D = \mathrm{diam}(\mathcal A^{\mathbb N}) = 1$). -/)]
theorem cot_branch_profile (hr : 2 ≤ r) {n : ℕ} (S : Fin n → SeqSpace (BranchAlphabet r) θ)
    (k : ℕ) :
    entropyIntegral (Y := EmpSpace S) (empDiam S (wordBall (branchClass θ) k))
        (wordBall (branchClass θ) k) ≤ √((k + 1) * Real.log r) := by
  /-- `prop:profiles-finite` with $|B(k,F_{\rm b})| \le r^{k+1}$ and $D_k(S) \le 1$. -/
  have h := profile_finite (Y := EmpSpace S) (A := fun k => wordBall (branchClass θ) k)
    (D := fun k => empDiam S (wordBall (branchClass θ) k)) (Dbar := 1) (r := r)
    (fun k => empDiam_nonneg S _) (fun k => empDiam_seqSpace_le_one S _)
    (fun k => encard_wordBall_le_pow (Set.finite_range _) (branchClass_ncard θ) hr) k
  simpa using h

end Branch

/-! ### Window one-hot output features -/

section Output

variable {𝒜 : Type*} [Fintype 𝒜] [DecidableEq 𝒜] (θ : ℝ≥0)

@[blueprint "def:cot-window-feature"
  (statement := /-- For $L \ge 1$ the window feature map
    $\Phi_L : \mathcal A^{\mathbb N} \to \mathbb R^{\mathcal A^L}$ is the one-hot encoding of the
    window $(x_0, \dots, x_{L-1})$. -/)]
noncomputable def windowFeature (L : ℕ) (x : SeqSpace 𝒜 θ) : EuclideanSpace ℝ (Fin L → 𝒜) :=
  EuclideanSpace.single (fun j : Fin L => x j) 1

@[blueprint "lem:cot-window-norm"
  (statement := /-- $\|\Phi_L(x)\| = 1$ (in particular $\|\Phi_L\| \le 1$). -/)]
theorem norm_windowFeature (L : ℕ) (x : SeqSpace 𝒜 θ) : ‖windowFeature θ L x‖ = 1 := by
  unfold windowFeature EuclideanSpace.single
  rw [PiLp.norm_single, norm_one]

omit [Fintype 𝒜] in
@[blueprint "lem:cot-window-eq"
  (statement := /-- If $x, y$ agree on the first $L$ symbols then $\Phi_L(x) = \Phi_L(y)$. -/)]
theorem windowFeature_eq_of_forall (L : ℕ) {x y : SeqSpace 𝒜 θ} (h : ∀ j < L, x j = y j) :
    windowFeature θ L x = windowFeature θ L y := by
  unfold windowFeature
  congr 1
  funext j
  exact h j j.2

@[blueprint "lem:cot-onehot-dist"
  (statement := /-- Distinct one-hot vectors are at Euclidean distance $\sqrt2$:
    $\|e_u - e_v\| = \sqrt 2$ for $u \ne v$. -/)]
theorem norm_single_sub_single_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {u v : ι}
    (huv : u ≠ v) :
    ‖(EuclideanSpace.single u (1 : ℝ) : EuclideanSpace ℝ ι) - EuclideanSpace.single v 1‖ = √2 := by
  /-- $\|e_u - e_v\|^2 = \|e_u\|^2 - 2\langle e_u, e_v\rangle + \|e_v\|^2 = 1 - 0 + 1$. -/
  have hsq : ‖(EuclideanSpace.single u (1 : ℝ) : EuclideanSpace ℝ ι) -
      EuclideanSpace.single v 1‖ ^ 2 = 2 := by
    rw [norm_sub_sq_real, EuclideanSpace.inner_single_left]
    unfold EuclideanSpace.single
    rw [PiLp.norm_single, PiLp.norm_single, PiLp.single_apply, if_neg huv]
    norm_num
  rw [← hsq, Real.sqrt_sq (norm_nonneg _)]

variable {θ} [Fact (0 < θ)] [Fact (θ < 1)]

@[blueprint "lem:cot-output"
  (statement := /-- \textbf{(Window output features.)} $\Phi_L$ is
    $\sqrt2\,\theta^{1-L}$-Lipschitz with respect to $d_\theta$, and $\|\Phi_L\| \le 1$.
    (If $d_\theta(x,y) \le \theta^L$ the first $L$ symbols agree and $\Phi_L(x) = \Phi_L(y)$;
    otherwise $d_\theta(x,y) \ge \theta^{L-1}$ and
    $\|\Phi_L(x) - \Phi_L(y)\| = \sqrt2 \le \sqrt2\,\theta^{1-L} d_\theta(x,y)$.) -/)]
theorem lipschitzWith_windowFeature (L : ℕ) :
    LipschitzWith (NNReal.sqrt 2 * θ⁻¹ ^ (L - 1)) (windowFeature (𝒜 := 𝒜) θ L) := by
  /-- Case analysis on whether the windows agree. -/
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hK : ((NNReal.sqrt 2 * θ⁻¹ ^ (L - 1) : ℝ≥0) : ℝ) = √2 * ((θ : ℝ)⁻¹) ^ (L - 1) := by
    push_cast
    rfl
  rw [hK]
  by_cases h : ∀ j < L, x j = y j
  · rw [windowFeature_eq_of_forall θ L h, dist_self]
    positivity
  · have hne : (fun j : Fin L => x j) ≠ (fun j : Fin L => y j) := by
      intro heq
      exact h fun j hj => congrFun heq ⟨j, hj⟩
    rw [dist_eq_norm]
    unfold windowFeature
    rw [norm_single_sub_single_eq hne]
    have hθ := pow_le_dist_of_not_forall (θ := θ) h
    have hpos : 0 < (θ : ℝ) ^ (L - 1) := pow_pos theta_pos _
    calc √2 = √2 * ((θ : ℝ)⁻¹ ^ (L - 1) * (θ : ℝ) ^ (L - 1)) := by
          rw [← mul_pow, inv_mul_cancel₀ theta_pos.ne', one_pow, mul_one]
      _ ≤ √2 * ((θ : ℝ)⁻¹ ^ (L - 1) * dist x y) := by gcongr
      _ = √2 * (θ : ℝ)⁻¹ ^ (L - 1) * dist x y := by ring

@[blueprint "cor:cot-output-sg"
  (statement := /-- Consequently (via `prop:hilbert-sg`) the sub-Gaussian increment condition
    holds for the linear readout class $H_L = \{x \mapsto \langle w, \Phi_L(x)\rangle :
    \|w\| \le 1\}$ and every hidden-layer class on $\mathcal A^{\mathbb N}$, with $A_H = 1$ and
    $L = \sqrt2\,\theta^{1-L}$. -/)]
theorem cot_output_sg {n : ℕ} (S : Fin n → SeqSpace 𝒜 θ) (L : ℕ)
    (𝔉 : Set (SeqSpace 𝒜 θ → SeqSpace 𝒜 θ)) :
    SubGaussianIncrements S (hilbertReadoutClass (windowFeature θ L)) 𝔉 1
      (NNReal.sqrt 2 * θ⁻¹ ^ (L - 1)) :=
  hilbert_sg S (windowFeature θ L) (lipschitzWith_windowFeature L) 𝔉

end Output

/-! ### The append-only scratchpad in the EL regime (`prop:cot-append`) -/

section AppendRegime

open MeasureTheory

variable {𝒜 : Type*} [Fintype 𝒜] {θ : ℝ≥0} [Fact (0 < θ)] [Fact (θ < 1)]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

@[blueprint "def:cot-vinf"
  (statement := /-- The depth-independent entropy integral of `lem:cot-append-profile`:
    $\mathsf V_\infty(m,\theta) := \sqrt{\log m}\Bigl(\frac{\sqrt\pi}{2\sqrt{\log(1/\theta)}}
    + \sqrt2\Bigr)$. -/)]
noncomputable def cotVinf (m : ℕ) (θ : ℝ≥0) : ℝ :=
  √(Real.log m) * (√π / (2 * √(Real.log (1 / (θ : ℝ)))) + √2)

@[blueprint "lem:cot-vinf-nonneg"
  (statement := /-- $\mathsf V_\infty(m,\theta) \ge 0$. -/)]
theorem cotVinf_nonneg (m : ℕ) (θ : ℝ≥0) : 0 ≤ cotVinf m θ := by
  unfold cotVinf
  positivity

@[blueprint "def:cot-target-class"
  (statement := /-- The teacher–student target class of arbitrarily long programs read out
    linearly: $\mathcal C := \overline{H_R(\Phi) \circ \langle F_{\rm w}\rangle}^{\,d_\infty}$,
    the uniform closure of the readouts of all finite compositions of write steps. -/)]
def cotTargetClass (Φ : SeqSpace 𝒜 θ → E) (R : ℝ) : Set (SeqSpace 𝒜 θ → ℝ) :=
  closure (X := SeqSpace 𝒜 θ →ᵤ ℝ)
    (compClass (linearReadouts Φ R) (semigroupClosure (appendClass θ)))

omit [Fintype 𝒜] in
@[blueprint "lem:cot-wordball-continuous"
  (statement := /-- Every element of $B(k, F_{\rm w})$ and of $\langle F_{\rm w}\rangle$ is
    $1$-Lipschitz, hence continuous. -/)]
theorem continuous_of_mem_semigroupClosure_appendClass {f : SeqSpace 𝒜 θ → SeqSpace 𝒜 θ}
    (hf : f ∈ semigroupClosure (appendClass θ)) : Continuous f :=
  (lipschitzWith_one_of_mem_semigroupClosure
    (fun _ hg => lipschitzWith_one_of_mem_appendClass hg) hf).continuous

variable [MeasurableSpace (SeqSpace 𝒜 θ)] [OpensMeasurableSpace (SeqSpace 𝒜 θ)]

omit [Fintype 𝒜] in
@[blueprint "lem:cot-class-measurable"
  (statement := /-- \textbf{(Measurability.)} For a continuous feature map $\Phi$ (with the
    Borel $\sigma$-algebra on $\mathcal A^{\mathbb N}$), every element of
    $\mathcal H_k = H_R(\Phi) \circ B(k, F_{\rm w})$ is measurable. -/)]
theorem cot_class_measurable {Φ : SeqSpace 𝒜 θ → E} (hΦ : Continuous Φ) (R : ℝ) (k : ℕ) :
    ∀ g ∈ hypothesisClass (linearReadouts Φ R) (appendClass θ) k, Measurable g :=
  fun _ hg => measurable_of_mem_compClass_linearReadouts hΦ
    (fun _ hf => continuous_of_mem_semigroupClosure_appendClass (subset_semigroupClosure hf)) hg

omit [Fintype 𝒜] in
@[blueprint "lem:cot-target-measurable"
  (statement := /-- Every element of the target class $\mathcal C$ is measurable (a uniform
    limit of continuous functions). -/)]
theorem cot_target_measurable {Φ : SeqSpace 𝒜 θ → E} (hΦ : Continuous Φ) (R : ℝ) :
    ∀ c ∈ cotTargetClass Φ R, Measurable c :=
  fun _ hc => measurable_of_mem_closure_uniformFun
    (fun _ hg => measurable_of_mem_compClass_linearReadouts hΦ
      (fun _ hf => continuous_of_mem_semigroupClosure_appendClass hf) hg) hc

omit [Fintype 𝒜] [Fact (0 < θ)] [Fact (θ < 1)] [MeasurableSpace (SeqSpace 𝒜 θ)]
  [OpensMeasurableSpace (SeqSpace 𝒜 θ)] in
@[blueprint "lem:cot-target-nonempty"
  (statement := /-- $\mathcal C \ne \emptyset$ (it contains the zero readout) when
    $R \ge 0$. -/)]
theorem cot_target_nonempty (Φ : SeqSpace 𝒜 θ → E) {R : ℝ} (hR : 0 ≤ R) :
    (cotTargetClass Φ R).Nonempty :=
  ⟨_, subset_closure (X := SeqSpace 𝒜 θ →ᵤ ℝ) ⟨_, ⟨0, by simpa using hR, rfl⟩, id,
    subset_semigroupClosure (id_mem_wordBall (k := 0)), rfl⟩⟩

omit [Fintype 𝒜] [Fact (0 < θ)] [Fact (θ < 1)] [MeasurableSpace (SeqSpace 𝒜 θ)]
  [OpensMeasurableSpace (SeqSpace 𝒜 θ)] in
@[blueprint "lem:cot-class-bounded"
  (statement := /-- \textbf{(Pointwise boundedness.)} If $\|\Phi\| \le M_\Phi$ and $R \ge 0$
    then $|g(x)| \le R M_\Phi$ for every $g \in \mathcal H_k$. -/)]
theorem cot_class_bounded {Φ : SeqSpace 𝒜 θ → E} {M : ℝ} (hΦ : ∀ x, ‖Φ x‖ ≤ M) {R : ℝ}
    (hR : 0 ≤ R) (k : ℕ) :
    ∀ x, ∃ C : ℝ, ∀ g ∈ hypothesisClass (linearReadouts Φ R) (appendClass θ) k, |g x| ≤ C :=
  fun x => ⟨R * M, fun _ hg => abs_le_of_mem_compClass_linearReadouts hΦ hR hg x⟩

omit [Fintype 𝒜] [MeasurableSpace (SeqSpace 𝒜 θ)] [OpensMeasurableSpace (SeqSpace 𝒜 θ)] in
@[blueprint "lem:cot-class-separable"
  (statement := /-- \textbf{(Sup-norm separability.)} For a separable feature space, a
    Lipschitz feature map $\Phi$ with $\|\Phi\| \le M_\Phi$ and $R \ge 0$, the class
    $\mathcal H_k = H_R(\Phi) \circ B(k, F_{\rm w})$ is sup-norm separable ($B(k,F_{\rm w})$ is
    finite and the ball of radius $R$ has a countable dense subset). -/)]
theorem cot_class_separable [Finite 𝒜] [TopologicalSpace.SeparableSpace E] {Φ : SeqSpace 𝒜 θ → E}
    {LΦ : ℝ≥0} (hΦ : LipschitzWith LΦ Φ) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x, ‖Φ x‖ ≤ M) {R : ℝ}
    (hR : 0 ≤ R) (k : ℕ) :
    IsSupSeparable (hypothesisClass (linearReadouts Φ R) (appendClass θ) k) :=
  isSupSeparable_compClass_linearReadouts hΦ hM0 hM hR
    (hasCountableUniformDense_of_finite (wordBall_finite (appendClass_finite θ) k))

omit [Fintype 𝒜] [Fact (0 < θ)] [Fact (θ < 1)] [MeasurableSpace (SeqSpace 𝒜 θ)]
  [OpensMeasurableSpace (SeqSpace 𝒜 θ)] in
@[blueprint "lem:cot-readout-rademacher"
  (statement := /-- \textbf{(Rademacher complexity of the readout class, `lem:cot-output`.)}
    If $\|\Phi\| \le M_\Phi$ then $\hat{\mathfrak R}_S(H_R(\Phi)) \le R M_\Phi/\sqrt n$ for every
    sample $S$ (for the window features, $M_\Phi = 1$). -/)]
theorem cot_readout_rademacher {n : ℕ} (S : Fin n → SeqSpace 𝒜 θ) (Φ : SeqSpace 𝒜 θ → E)
    {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M) (hΦ : ∀ x, ‖Φ x‖ ≤ M) :
    empRademacher S (linearReadouts Φ R) ≤ R * M / √n :=
  empRademacher_linearReadouts_le S Φ hR hM hΦ

omit [MeasurableSpace (SeqSpace 𝒜 θ)] [OpensMeasurableSpace (SeqSpace 𝒜 θ)] in
@[blueprint "lem:cot-append-var"
  (statement := /-- \textbf{(Estimation term for append-only steps.)} Let $|\mathcal A| = m \ge 2$,
    $\Phi$ be $L_\Phi$-Lipschitz with $\|\Phi\| \le M_\Phi$ and $R > 0$. Then for every sample
    $S$ of size $n \ge 1$ and every depth $k$,
    $$\hat{\mathfrak R}_S(\mathcal H_k) \le \frac{R M_\Phi}{\sqrt n}
      + \frac{12 \cdot 1 \cdot R L_\Phi}{\sqrt n}\,\mathsf V_\infty(m,\theta)$$
    (`thm:hidden-decomp-depth` with $A\_H = 1$, `lem:cot-append-profile` and
    `lem:cot-readout-rademacher`). -/)]
theorem cot_append_var (hm : 2 ≤ Fintype.card 𝒜) {n : ℕ} (hn : 0 < n)
    (S : Fin n → SeqSpace 𝒜 θ) (Φ : SeqSpace 𝒜 θ → E) {LΦ : ℝ≥0} (hLΦ : 0 < LΦ)
    (hΦ : LipschitzWith LΦ Φ) {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M) (hΦM : ∀ x, ‖Φ x‖ ≤ M)
    (k : ℕ) :
    empRademacher S (hypothesisClass (linearReadouts Φ R) (appendClass θ) k) ≤
      R * M / √n + 12 * 1 * (R * LΦ) / √n * cotVinf (Fintype.card 𝒜) θ := by
  have hcoe : ((R.toNNReal * LΦ : ℝ≥0) : ℝ) = R * LΦ := by
    rw [NNReal.coe_mul, Real.coe_toNNReal _ hR.le]
  have hL : (0 : ℝ) < ((R.toNNReal * LΦ : ℝ≥0) : ℝ) := by
    rw [hcoe]; exact mul_pos hR (by exact_mod_cast hLΦ)
  have h := empRademacher_le_of_entropyIntegral_le S (linearReadouts Φ R) hn (appendClass θ) k
    (AH := 1) one_pos hL
    (fun f _ σ => bddAbove_range_normalizedRademacherSum_of_bound (f ∘ S) (by positivity)
      (fun g hg x => (abs_le_of_mem_linearReadouts hg _).trans
        (mul_le_mul_of_nonneg_left (hΦM _) hR.le)) σ)
    (Set.Finite.totallyBounded (α := EmpSpace S) (wordBall_finite (appendClass_finite θ) k))
    (linearReadouts_sg S Φ hΦ hR _)
    (intervalIntegrable_wordBall_of_finite S (appendClass_finite θ) (appendClass_ncard θ) hm
      zero_le_one dist_seqSpace_le_one k)
    (cot_append_profile hm S k)
  refine h.trans ?_
  rw [hcoe]
  unfold cotVinf
  gcongr
  exact cot_readout_rademacher S Φ hR.le hM hΦM

omit [Fintype 𝒜] in
@[blueprint "lem:cot-append-bias"
  (statement := /-- \textbf{(Bias for append-only steps.)} Let $\Phi$ be $L_\Phi$-Lipschitz and
    $R \ge 0$. Against the teacher–student class
    $\mathcal C = \overline{H_R(\Phi) \circ \langle F_{\rm w}\rangle}^{\,d_\infty}$,
    $$\mathrm{bias}(k) = \varepsilon_{\mathrm{model}}(k) \le \beta_\ell\, R L_\Phi\, \theta^k :$$
    for a teacher $c = h_w \circ g_u \circ g_v$ with $|u| = k$,
    $|c(x) - h_w(g_u(x))| \le R L_\Phi\, d_\theta(g_u(g_v x), g_u x) \le R L_\Phi \theta^k$ since
    $\mathrm{lip}(g_u) = \theta^k$ and $\mathrm{diam} = 1$, and the same bound holds on the uniform
    closure; conclude with `lem:approx-transfer`. -/)]
theorem cot_append_bias {Y : Type*} [MeasurableSpace Y] (P : Measure (SeqSpace 𝒜 θ × Y))
    [IsProbabilityMeasure P] (L : BoundedLipschitzLoss Y) (hℓ : Measurable (Function.uncurry L.ℓ))
    (hβ : 0 ≤ L.β) {Φ : SeqSpace 𝒜 θ → E} {LΦ : ℝ≥0} (hΦ : LipschitzWith LΦ Φ) {R : ℝ}
    (hR : 0 ≤ R) (k : ℕ) :
    modelError L P (hypothesisClass (linearReadouts Φ R) (appendClass θ) k) (cotTargetClass Φ R) ≤
      L.β * (R * LΦ * (θ : ℝ) ^ k) := by
  refine modelError_le_of_approx P L hℓ hβ (cot_class_measurable hΦ.continuous R k)
    (cot_target_measurable hΦ.continuous R) (cot_target_nonempty Φ hR) fun c hc ε hε => ?_
  have := exists_approx_of_mem_closure_compClass_semigroupClosure (H := linearReadouts Φ R)
    (LH := R.toNNReal * LΦ) (fun _ hh => lipschitzWith_of_mem_linearReadouts hΦ hR hh) (c := θ)
    (fun _ hg => by obtain ⟨a, rfl⟩ := hg; exact lipschitzWith_append a) (Dx := 1)
    dist_seqSpace_le_one k hc ε hε
  simpa [NNReal.coe_mul, Real.coe_toNNReal _ hR] using this

@[blueprint "prop:cot-append"
  (statement := /-- \textbf{(Append-only scratchpad, rigorous form.)} Let $|\mathcal A| = m \ge 2$,
    let $\Phi : \mathcal A^{\mathbb N} \to \mathcal H$ be an $L_\Phi$-Lipschitz feature map into
    a separable Hilbert space with $\|\Phi\| \le M_\Phi$ (e.g. the window features $\Phi_L$),
    $R > 0$, $H = H_R(\Phi)$, $F = F_{\rm w}$, and let the target class be
    $\mathcal C = \overline{H \circ \langle F_{\rm w}\rangle}^{\,d_\infty}$. For a measurable
    loss $\ell : \mathbb R \times \mathcal Y \to [0,b]$, $\beta_\ell$-Lipschitz in its first
    argument, $n \ge 1$, $\eta \ge 0$ and $\delta \in (0,1)$: with probability at least
    $1 - \delta$ over $\mathcal D \sim P^{\otimes n}$, every $\eta$-empirical minimizer
    $\hat h \in \mathcal H_k = H \circ B(k, F_{\rm w})$ satisfies
    $$L[\hat h] - \inf_{\mathcal C} L \le \beta_\ell R L_\Phi\,\theta^k + \eta
      + \mathrm{dev}_{\ell,n,\delta}\Bigl(\frac{R M_\Phi}{\sqrt n} + \frac{12 R L_\Phi}{\sqrt n}
        \mathsf V_\infty(m,\theta)\Bigr),$$
    where $\mathrm{dev}_{\ell,n,\delta}(B) = 4\beta_\ell B + 6b\sqrt{2\log(4/\delta)/n}$ is the
    estimation-plus-deviation term of `thm:bv` (`def:bv-dev`). This is the EL regime with
    $\alpha = \log(1/\theta)$ and saturated variance. (The implementation map is the identity,
    $\varepsilon_{\mathrm{imp}} = 0$.) -/)]
theorem prop_cot_append [TopologicalSpace.SeparableSpace E] {Y : Type*} [MeasurableSpace Y]
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
  /- `thm:bv-id-bounds` with the class properties `lem:cot-class-*`, the estimation bound
    `lem:cot-append-var` and the bias bound `lem:cot-append-bias`. -/
  bv_id_of_bounds P L hn hℓ hb hβ (cot_class_measurable hΦ.continuous R k)
    (cot_class_separable hΦ hM hΦM hR.le k) (cot_class_bounded hΦM hR.le k)
    (cot_target_nonempty Φ hR.le) (cot_target_measurable hΦ.continuous R)
    (fun S => cot_append_var hm hn S Φ hLΦ hΦ hR hM hΦM k)
    (cot_append_bias P L hℓ hβ hΦ hR.le k) hη hδ hδ1

omit [MeasurableSpace (SeqSpace 𝒜 θ)] [OpensMeasurableSpace (SeqSpace 𝒜 θ)] in
@[blueprint "lem:cot-append-balance"
  (statement := /-- \textbf{(EL balancing with saturated variance.)} For $n \ge 1$ the depth
    $k^\ast := \lceil \log n / (2\log(1/\theta))\rceil = \frac{\log n}{2\log(1/\theta)} + O(1)$
    satisfies $\theta^{k^\ast} \le n^{-1/2}$, so the bias term matches the saturated variance
    $n^{-1/2}$. -/)]
theorem cot_append_balance {n : ℕ} (hn : 1 ≤ n) :
    (θ : ℝ) ^ ⌈Real.log n / (2 * Real.log (1 / (θ : ℝ)))⌉₊ ≤ 1 / √n :=
  pow_ceil_log_div_le_one_div_sqrt theta_pos theta_lt_one (by exact_mod_cast hn)

@[blueprint "cor:cot-append-depth"
  (statement := /-- \textbf{(Balanced value $O(n^{-1/2})$.)} Under the hypotheses of
    `prop:cot-append`, at the depth $k^\ast = \lceil \log n / (2\log(1/\theta))\rceil$ the bound
    reads
    $$L[\hat h] - \inf_{\mathcal C} L \le
      \frac{\beta_\ell R L_\Phi}{\sqrt n} + \eta
      + \mathrm{dev}_{\ell,n,\delta}\Bigl(\frac{R M_\Phi + 12 R L_\Phi
        \mathsf V_\infty(m,\theta)}{\sqrt n}\Bigr)$$
    with probability at least $1 - \delta$: every term is of order $n^{-1/2}$ (up to the
    $\sqrt{\log(1/\delta)}$ factor of the deviation term), so the balanced value is
    $O(n^{-1/2})$. -/)]
theorem cor_cot_append_depth [TopologicalSpace.SeparableSpace E] {Y : Type*} [MeasurableSpace Y]
    (hm : 2 ≤ Fintype.card 𝒜) {n : ℕ} (hn : 1 ≤ n) (P : Measure (SeqSpace 𝒜 θ × Y))
    [IsProbabilityMeasure P] (L : BoundedLipschitzLoss Y) (hℓ : Measurable (Function.uncurry L.ℓ))
    (hb : 0 < L.b) (hβ : 0 ≤ L.β) (Φ : SeqSpace 𝒜 θ → E) {LΦ : ℝ≥0} (hLΦ : 0 < LΦ)
    (hΦ : LipschitzWith LΦ Φ) {M : ℝ} (hM : 0 ≤ M) (hΦM : ∀ x, ‖Φ x‖ ≤ M) {R : ℝ} (hR : 0 < R)
    {η δ : ℝ} (hη : 0 ≤ η) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ((Measure.pi fun _ : Fin n => P) {D | ¬ ∀ fhat,
        IsEmpMinimizer L D (hypothesisClass (linearReadouts Φ R) (appendClass θ)
          ⌈Real.log n / (2 * Real.log (1 / (θ : ℝ)))⌉₊) η fhat →
        risk L P fhat - sInf (risk L P '' cotTargetClass Φ R) ≤
          L.β * (R * LΦ) / √n + η +
            bvDev L n δ ((R * M + 12 * (R * LΦ) * cotVinf (Fintype.card 𝒜) θ) / √n)}
      ).toReal ≤ δ := by
  /- `prop:cot-append` at $k^\ast$ and `lem:cot-append-balance`. -/
  refine le_trans ?_ (prop_cot_append (n := n) hm (lt_of_lt_of_le Nat.one_pos hn) P L hℓ hb hβ Φ
    hLΦ hΦ hM hΦM hR
    ⌈Real.log n / (2 * Real.log (1 / (θ : ℝ)))⌉₊ hη hδ hδ1)
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun D hD => ?_)
  simp only [Set.mem_setOf_eq] at hD ⊢
  intro hall
  apply hD
  intro fhat hfhat
  have h1 := hall fhat hfhat
  have hθk := cot_append_balance (θ := θ) hn
  have hpos : 0 ≤ L.β * (R * LΦ) := by positivity
  have h2 : L.β * (R * LΦ * (θ : ℝ) ^ ⌈Real.log n / (2 * Real.log (1 / (θ : ℝ)))⌉₊) ≤
      L.β * (R * LΦ) / √n := by
    calc L.β * (R * LΦ * (θ : ℝ) ^ ⌈Real.log n / (2 * Real.log (1 / (θ : ℝ)))⌉₊)
        = L.β * (R * LΦ) * (θ : ℝ) ^ ⌈Real.log n / (2 * Real.log (1 / (θ : ℝ)))⌉₊ := by ring
      _ ≤ L.β * (R * LΦ) * (1 / √n) := mul_le_mul_of_nonneg_left hθk hpos
      _ = L.β * (R * LΦ) / √n := by ring
  have h3 : R * M / √n + 12 * 1 * (R * LΦ) / √n * cotVinf (Fintype.card 𝒜) θ =
      (R * M + 12 * (R * LΦ) * cotVinf (Fintype.card 𝒜) θ) / √n := by ring
  rw [h3] at h1
  linarith

end AppendRegime

end LeanDeepgen
