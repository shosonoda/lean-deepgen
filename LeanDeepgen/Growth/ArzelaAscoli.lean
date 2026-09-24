import Mathlib
import Architect
import LeanDeepgen.Setting.WordBall
import LeanDeepgen.Setting.Metrics
import LeanDeepgen.Setting.Covering
import FoML.ToMathlib.CoveringNumber

/-!
# Compact-domain Arzelà–Ascoli principle for self-maps (paper App. "Compact AA")

Total boundedness of a family `Hs ⊆ 𝒳^𝒳` of self-maps of a (pseudo)metric space `𝒳` for the
uniform distance `d_∞`, i.e. in `UnifMaps X = X →ᵤ X`.

* `thm:maa` (metric modulus criterion): if `𝒳` is totally bounded and `Hs` has a common modulus
  of continuity then `Hs` is totally bounded in `d_∞` (finite net + assignment argument).
* `lem:oaa`: on a compact `𝒳` an equicontinuous family has a common (monotone) modulus.
* `thm:caa`: on a compact `𝒳`, a family of continuous self-maps is totally bounded in `d_∞`
  iff it is equicontinuous; the closure of an equicontinuous family is compact.
* `cor:aa-semigroup-saturation`: if the semigroup `⟨F⟩` is equicontinuous on a compact `𝒳` then
  `N^ext(B(k,F), d_∞, ε) ≤ N^ext(cl ⟨F⟩, d_∞, ε) < ∞` uniformly in `k`.

Finiteness of the covering numbers of a totally bounded set
(`externalCoveringNumber_ne_top_of_totallyBounded`, `coveringNumber_ne_top_of_totallyBounded`) is
Mathlib-generic and lives in `FoML.ToMathlib.CoveringNumber`.
Since the range of the self-maps is the compact space `𝒳` itself, no separate uniform boundedness
hypothesis is needed. The pseudo-metric quotient version `thm:pmaa` of the paper is not
formalized (in Lean, `thm:maa` is already stated for pseudo-metric spaces).
-/

open scoped NNReal ENNReal UniformConvergence Topology
open Metric Filter

open FoML.ToMathlib

namespace LeanDeepgen

section EMetric

variable {X : Type*} [PseudoEMetricSpace X]

@[blueprint "def:unif-maps-complete"
  (statement := /-- If $\mathcal X$ is complete then $(\mathcal X^{\mathcal X}, d_\infty)$ is
    complete (uniform limits of Cauchy sequences). This is Mathlib's instance on
    `X →ᵤ X`. -/)]
noncomputable instance instCompleteSpaceUnifMaps [CompleteSpace X] : CompleteSpace (UnifMaps X) :=
  inferInstanceAs (CompleteSpace (X →ᵤ X))

end EMetric

section Metric

variable {X : Type*} [PseudoMetricSpace X]

@[blueprint "thm:maa"
  (statement := /-- \textbf{(Metric modulus criterion.)} Let $(\mathcal X, d)$ be a totally bounded
    (pseudo)metric space. If $H \subseteq \mathcal X^{\mathcal X}$ has a common modulus of
    continuity, namely there is $\omega : \mathbb R \to \mathbb R$ with $\omega(r) \to 0$ as
    $r \downarrow 0$ (for every $\varepsilon > 0$ there is $r > 0$ with $\omega(t) \le \varepsilon$
    for $0 \le t \le r$) and
    $$d(f(x), f(y)) \le \omega(d(x,y)) \qquad (f \in H,\ x, y \in \mathcal X),$$
    then $H$ is totally bounded in $d_\infty$. -/)]
theorem totallyBounded_unifMaps_of_modulus (hX : TotallyBounded (Set.univ : Set X))
    (ω : ℝ → ℝ) (hω : ∀ ε > 0, ∃ r > 0, ∀ t, 0 ≤ t → t ≤ r → ω t ≤ ε)
    {Hs : Set (X → X)} (hHs : ∀ f ∈ Hs, ∀ x y, dist (f x) (f y) ≤ ω (dist x y)) :
    TotallyBounded (α := UnifMaps X) Hs := by
  /-- Fix $\eta > 0$ (below the prescribed radius). Choose $\rho > 0$ with
    $\omega(t) \le \eta/4$ for $t \le \rho$, a finite $\rho$-net $P$ and a finite $\eta/4$-net $Q$
    of $\mathcal X$. To $f \in H$ assign the map $P \to Q$, $p \mapsto q(f(p))$ with
    $d(f(p), q(f(p))) < \eta/4$. There are finitely many assignments; choose one representative
    $g \in H$ for each occurring assignment. If $f$ and $g$ have the same assignment then for every
    $x$, picking $p \in P$ with $d(x,p) < \rho$,
    $d(f(x), g(x)) \le d(f(x), f(p)) + d(f(p), q(f(p))) + d(q(g(p)), g(p)) + d(g(p), g(x))
    \le \eta$. Thus the representatives form a finite $\eta$-net of $H$ for $d_\infty$. -/
  rw [EMetric.totallyBounded_iff]
  intro ε hε
  obtain ⟨η, hη0, hηε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hε
  have hη : (0 : ℝ) < η := ENNReal.coe_pos.1 hη0
  obtain ⟨ρ, hρ, hωρ⟩ := hω (η / 4) (by positivity)
  obtain ⟨P, hPfin, hPcov⟩ := Metric.totallyBounded_iff.1 hX ρ hρ
  obtain ⟨Q, hQfin, hQcov⟩ := Metric.totallyBounded_iff.1 hX (η / 4) (by positivity)
  have hQ : ∀ z : X, ∃ q ∈ Q, dist z q < η / 4 := fun z => by
    obtain ⟨y, hy, hz⟩ := Set.mem_iUnion₂.1 (hQcov (Set.mem_univ z))
    exact ⟨y, hy, hz⟩
  choose q hqQ hqdist using hQ
  let assign : (X → X) → (P → X) := fun f p => q (f p)
  have hfin : (assign '' Hs).Finite := by
    haveI := hPfin.to_subtype
    refine (Set.Finite.pi (t := fun _ : P => Q) fun _ => hQfin).subset ?_
    rintro _ ⟨f, -, rfl⟩
    rw [Set.mem_univ_pi]
    intro p
    exact hqQ _
  have hrep : ∀ φ ∈ assign '' Hs, ∃ f ∈ Hs, assign f = φ := fun _ hφ => hφ
  choose rep hrepHs hrepEq using hrep
  haveI := hfin.to_subtype
  refine ⟨Set.range (fun φ : assign '' Hs => toUnifMaps (rep φ φ.2)), Set.finite_range _, ?_⟩
  intro f hf
  have hφ : assign f ∈ assign '' Hs := ⟨f, hf, rfl⟩
  refine Set.mem_iUnion₂.2 ⟨_, ⟨⟨assign f, hφ⟩, rfl⟩, ?_⟩
  rw [mem_eball]
  refine lt_of_le_of_lt ?_ hηε
  change edist (toUnifMaps f) (toUnifMaps (rep (assign f) hφ)) ≤ η
  set g := rep (assign f) hφ with hg
  have hgHs : g ∈ Hs := hrepHs _ hφ
  have hgEq : assign g = assign f := hrepEq _ hφ
  rw [← ENNReal.ofReal_coe_nnreal]
  refine UniformFun.edist_le.2 fun x => ?_
  rw [edist_le_ofReal hη.le]
  obtain ⟨p, hpP, hxp⟩ : ∃ p ∈ P, dist x p < ρ := by
    obtain ⟨p, hp, hx⟩ := Set.mem_iUnion₂.1 (hPcov (Set.mem_univ x))
    exact ⟨p, hp, hx⟩
  have h1 : dist (f x) (f p) ≤ η / 4 := (hHs f hf x p).trans (hωρ _ dist_nonneg hxp.le)
  have h2 : dist (f p) (q (f p)) < η / 4 := hqdist _
  have h3 : q (g p) = q (f p) := congrFun hgEq ⟨p, hpP⟩
  have h4 : dist (g p) (q (g p)) < η / 4 := hqdist _
  have h5 : dist (g p) (g x) ≤ η / 4 :=
    (hHs g hgHs p x).trans (hωρ _ dist_nonneg (by rw [dist_comm]; exact hxp.le))
  have h6 : dist (f p) (g p) ≤ dist (f p) (q (f p)) + dist (g p) (q (g p)) := by
    rw [h3, dist_comm (g p)]; exact dist_triangle _ _ _
  have h7 : dist (f x) (g x) ≤ dist (f x) (f p) + dist (f p) (g p) + dist (g p) (g x) :=
    dist_triangle4 _ _ _ _
  change dist (f x) (g x) ≤ η
  linarith

@[blueprint "lem:oaa"
  (statement := /-- \textbf{(Modulus extraction on compact domains.)} Let $(\mathcal X,d)$ be
    compact and $H \subseteq \mathcal X^{\mathcal X}$ equicontinuous. Then $H$ admits a common
    monotone modulus of continuity $\omega$ with $\omega(r) \to 0$ as $r \downarrow 0$ and
    $d(f(x), f(y)) \le \omega(d(x,y))$ for all $f \in H$, $x, y \in \mathcal X$.
    In particular `thm:maa` applies. -/)]
theorem exists_modulus_of_equicontinuous [CompactSpace X] {Hs : Set (X → X)}
    (hHs : Equicontinuous (fun f : Hs => (f : X → X))) :
    ∃ ω : ℝ → ℝ, Monotone ω ∧ (∀ ε > 0, ∃ r > 0, ∀ t, 0 ≤ t → t ≤ r → ω t ≤ ε) ∧
      ∀ f ∈ Hs, ∀ x y, dist (f x) (f y) ≤ ω (dist x y) := by
  /-- Set $\omega(r) := \sup\{d(f(x), f(y)) : f \in H,\ d(x,y) \le r\}$ (bounded by
    $\mathrm{diam}\,\mathcal X$, and $0$ for $r < 0$). It is monotone, and uniform equicontinuity
    (equicontinuity on a compact space) gives $\omega(r) \le \varepsilon$ for $r \le \delta/2$. -/
  have hU := CompactSpace.uniformEquicontinuous_of_equicontinuous hHs
  rw [Metric.uniformEquicontinuous_iff] at hU
  let S : ℝ → Set ℝ := fun r => {d | ∃ f ∈ Hs, ∃ x y, dist x y ≤ r ∧ d = dist (f x) (f y)}
  have hbdd : ∀ r, BddAbove (S r) := fun r => ⟨Metric.diam (Set.univ : Set X), by
    rintro _ ⟨f, -, x, y, -, rfl⟩
    exact Metric.dist_le_diam_of_mem Metric.isBounded_of_compactSpace (Set.mem_univ _)
      (Set.mem_univ _)⟩
  have hnonneg : ∀ r, ∀ d ∈ S r, 0 ≤ d := by
    rintro r _ ⟨f, -, x, y, -, rfl⟩
    exact dist_nonneg
  refine ⟨fun r => sSup (S r), ?_, ?_, ?_⟩
  · intro r s hrs
    rcases (S r).eq_empty_or_nonempty with h | h
    · simp only [h, Real.sSup_empty]
      exact Real.sSup_nonneg (hnonneg s)
    · exact csSup_le_csSup (hbdd s) h
        (fun d ⟨f, hf, x, y, hxy, hd⟩ => ⟨f, hf, x, y, hxy.trans hrs, hd⟩)
  · intro ε hε
    obtain ⟨δ, hδ, hδε⟩ := hU ε hε
    refine ⟨δ / 2, by positivity, fun t _ htδ => ?_⟩
    refine Real.sSup_le ?_ hε.le
    rintro _ ⟨f, hf, x, y, hxy, rfl⟩
    exact (hδε x y (by linarith) ⟨f, hf⟩).le
  · intro f hf x y
    exact le_csSup (hbdd _) ⟨f, hf, x, y, le_rfl, rfl⟩

@[blueprint "thm:caa-of-equicontinuous"
  (statement := /-- (Forward direction of `thm:caa`.) If $\mathcal X$ is compact and
    $H \subseteq \mathcal X^{\mathcal X}$ is equicontinuous, then $H$ is totally bounded in
    $d_\infty$. -/)]
theorem totallyBounded_unifMaps_of_equicontinuous [CompactSpace X] {Hs : Set (X → X)}
    (hHs : Equicontinuous (fun f : Hs => (f : X → X))) :
    TotallyBounded (α := UnifMaps X) Hs := by
  /-- Extract a common modulus (`lem:oaa`) and apply the modulus criterion (`thm:maa`);
    a compact space is totally bounded. -/
  obtain ⟨ω, -, hω, hmod⟩ := exists_modulus_of_equicontinuous hHs
  exact totallyBounded_unifMaps_of_modulus isCompact_univ.totallyBounded ω hω hmod

@[blueprint "thm:caa-of-totallyBounded"
  (statement := /-- (Converse direction of `thm:caa`.) If $H \subseteq C(\mathcal X, \mathcal X)$
    is totally bounded in $d_\infty$ then $H$ is equicontinuous.
    (Continuity of the members of $H$ is needed; compactness of $\mathcal X$ is not.) -/)]
theorem equicontinuous_of_totallyBounded_unifMaps {Hs : Set (X → X)}
    (hcont : ∀ f ∈ Hs, Continuous f) (hHs : TotallyBounded (α := UnifMaps X) Hs) :
    Equicontinuous (fun f : Hs => (f : X → X)) := by
  /-- Fix $x_0$ and $\varepsilon > 0$, and take a finite $\varepsilon/3$-net $t \subseteq H$.
    Each $g \in t$ is continuous at $x_0$, so for $x$ near $x_0$ we have
    $d(g(x_0), g(x)) < \varepsilon/3$ for all $g \in t$ simultaneously. For $f \in H$ choose
    $g \in t$ with $d_\infty(f,g) < \varepsilon/3$; then
    $d(f(x_0), f(x)) \le d(f(x_0), g(x_0)) + d(g(x_0), g(x)) + d(g(x), f(x)) < \varepsilon$. -/
  intro x₀
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  obtain ⟨t, htHs, htfin, hcov⟩ := EMetric.totallyBounded_iff'.1 hHs (ENNReal.ofReal (ε / 3))
    (ENNReal.ofReal_pos.2 (by positivity))
  have h1 : ∀ᶠ x in 𝓝 x₀, ∀ g ∈ t, dist (g x₀) (g x) < ε / 3 := by
    rw [Filter.eventually_all_finite htfin]
    intro g hg
    have hg' := Metric.tendsto_nhds.1 ((hcont g (htHs hg)).continuousAt (x := x₀)) (ε / 3)
      (by positivity)
    exact hg'.mono fun x hx => by rw [dist_comm]; exact hx
  filter_upwards [h1] with x hx
  rintro ⟨f, hf⟩
  obtain ⟨g, hg, hfg⟩ := Set.mem_iUnion₂.1 (hcov hf)
  rw [mem_eball] at hfg
  have hpt : ∀ y, dist (f y) (g y) < ε / 3 := fun y =>
    edist_lt_ofReal.1
      ((UniformFun.edist_eval_le (f := toUnifMaps f) (g := g) (x := y)).trans_lt hfg)
  change dist (f x₀) (f x) < ε
  calc dist (f x₀) (f x) ≤ dist (f x₀) (g x₀) + dist (g x₀) (g x) + dist (g x) (f x) :=
        dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        have := hpt x₀
        have := hpt x
        have := hx g hg
        rw [dist_comm (g x)]
        linarith
    _ = ε := by ring

@[blueprint "thm:caa"
  (statement := /-- \textbf{(Compact Arzelà–Ascoli for self-maps.)} Let $(\mathcal X, d)$ be a
    compact (pseudo)metric space and let $H \subseteq C(\mathcal X, \mathcal X)$. Then $H$ is
    totally bounded in $d_\infty$ if and only if $H$ is equicontinuous. -/)]
theorem totallyBounded_unifMaps_iff_equicontinuous [CompactSpace X] {Hs : Set (X → X)}
    (hcont : ∀ f ∈ Hs, Continuous f) :
    TotallyBounded (α := UnifMaps X) Hs ↔ Equicontinuous (fun f : Hs => (f : X → X)) :=
  ⟨equicontinuous_of_totallyBounded_unifMaps hcont, totallyBounded_unifMaps_of_equicontinuous⟩

@[blueprint "lem:caa-closure-compact"
  (statement := /-- (Consequence of `thm:caa`.) If $\mathcal X$ is compact and
    $H \subseteq \mathcal X^{\mathcal X}$ is equicontinuous, then the closure of $H$ in
    $(\mathcal X^{\mathcal X}, d_\infty)$ is compact. -/)]
theorem isCompact_closure_unifMaps_of_equicontinuous [CompactSpace X] {Hs : Set (X → X)}
    (hHs : Equicontinuous (fun f : Hs => (f : X → X))) :
    IsCompact (closure (X := UnifMaps X) Hs) := by
  /-- $(\mathcal X^{\mathcal X}, d_\infty)$ is complete since $\mathcal X$ is compact (hence
    complete), and the closure of a totally bounded set in a complete space is compact. -/
  exact (totallyBounded_unifMaps_of_equicontinuous hHs).closure.isCompact_of_isClosed
    isClosed_closure

@[blueprint "cor:aa-semigroup-saturation"
  (statement := /-- \textbf{(Saturation for compact equicontinuous semigroups.)} Let
    $(\mathcal X, d)$ be compact and $F \subseteq \mathcal X^{\mathcal X}$. If the generated
    semigroup $\langle F \rangle$ is equicontinuous, then for every $\varepsilon > 0$ and every $k$
    $$N^{\mathrm{ext}}\bigl(B(k,F), d_\infty, \varepsilon\bigr)
      \le N^{\mathrm{ext}}\bigl(\overline{\langle F\rangle}^{d_\infty}, d_\infty, \varepsilon\bigr)
      < \infty .$$
    In particular the covering number of the word ball does not grow with the depth $k$. -/)]
theorem externalCoveringNumber_wordBall_le_closure_semigroupClosure [CompactSpace X]
    {F : Set (X → X)}
    (hF : Equicontinuous (fun f : semigroupClosure F => (f : X → X))) (ε : ℝ≥0) (hε : 0 < ε)
    (k : ℕ) :
    externalCoveringNumber (X := UnifMaps X) ε (wordBall F k) ≤
        externalCoveringNumber (X := UnifMaps X) ε
          (closure (X := UnifMaps X) (semigroupClosure F)) ∧
      externalCoveringNumber (X := UnifMaps X) ε
        (closure (X := UnifMaps X) (semigroupClosure F)) ≠ ⊤ := by
  /-- $B(k,F) \subseteq \langle F \rangle \subseteq \overline{\langle F\rangle}$ and the external
    covering number is monotone in the set; the closure is totally bounded by `thm:caa`, so its
    covering number is finite. -/
  refine ⟨externalCoveringNumber_mono_set
    (subset_semigroupClosure.trans (subset_closure (X := UnifMaps X))), ?_⟩
  exact externalCoveringNumber_ne_top_of_totallyBounded
    (totallyBounded_unifMaps_of_equicontinuous hF).closure hε

@[blueprint "cor:aa-semigroup-saturation-internal"
  (statement := /-- (Internal version of `cor:aa-semigroup-saturation`.) Under the same
    hypotheses, for every $\varepsilon > 0$ and every $k$,
    $N\bigl(B(k,F), d_\infty, \varepsilon\bigr)
      \le N\bigl(\overline{\langle F\rangle}^{d_\infty}, d_\infty, \varepsilon/2\bigr) < \infty$
    (internal covering numbers are not monotone in the set, whence the loss of a factor $2$ in
    the radius). -/)]
theorem coveringNumber_wordBall_le_closure_semigroupClosure [CompactSpace X]
    {F : Set (X → X)}
    (hF : Equicontinuous (fun f : semigroupClosure F => (f : X → X))) (ε : ℝ≥0) (hε : 0 < ε)
    (k : ℕ) :
    coveringNumber (X := UnifMaps X) ε (wordBall F k) ≤
        coveringNumber (X := UnifMaps X) (ε / 2)
          (closure (X := UnifMaps X) (semigroupClosure F)) ∧
      coveringNumber (X := UnifMaps X) (ε / 2)
        (closure (X := UnifMaps X) (semigroupClosure F)) ≠ ⊤ := by
  /-- Mathlib's `coveringNumber\_subset\_le` for the inclusion, and finiteness of the internal
    covering number of a totally bounded set. -/
  refine ⟨coveringNumber_subset_le
    (subset_semigroupClosure.trans (subset_closure (X := UnifMaps X))), ?_⟩
  exact coveringNumber_ne_top_of_totallyBounded
    (totallyBounded_unifMaps_of_equicontinuous hF).closure (by positivity)

end Metric

end LeanDeepgen
