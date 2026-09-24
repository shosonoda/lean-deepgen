import Mathlib
import Architect

/-!
# Metrics on hidden layers

The uniform distance `d_∞(f,g) = sup_x d(f x, g x)` (as an extended real, it may be infinite),
the empirical distance `d_S(f,g) = (n⁻¹ ∑ᵢ d(f xᵢ, g xᵢ)²)^{1/2}` on a sample `S = (x₁,…,xₙ)`,
the empirical norms `‖u‖_S`, `‖u‖_{S,∞}` on real-valued functions, and the empirical diameter
`diam_S(F)`. We prove the key comparison `d_S ≤ d_∞` and the composition (Lipschitz) estimates
for `d_∞`.

Finally, `UnifMaps X` is the type of self-maps of `X` carrying `d_∞` as a pseudo-emetric.
It is Mathlib's `X →ᵤ X` (`UniformFun`, the space of functions with the uniform structure), whose
`PseudoEMetricSpace` instance (`Mathlib.Topology.MetricSpace.UniformConvergence`) has exactly
`edist f g = ⨆ x, edist (f x) (g x) = d_∞(f,g)`.
-/

open scoped ENNReal NNReal UniformConvergence

namespace LeanDeepgen

section EMetric

variable {X : Type*} [PseudoEMetricSpace X]

@[blueprint "def:d-inf"
  (statement := /-- The uniform distance on $\mathcal X^{\mathcal X}$ is
    $d_\infty(f,g) = \sup_{x \in \mathcal X} d(f(x), g(x)) \in [0,\infty]$. -/)]
noncomputable def uniformDist (f g : X → X) : ℝ≥0∞ := ⨆ x, edist (f x) (g x)

@[blueprint "def:d-inf-real"
  (statement := /-- The real-valued uniform distance $d_\infty(f,g)$, with the convention that it
    is $0$ when $d_\infty(f,g) = \infty$. -/)]
noncomputable def uniformDistReal (f g : X → X) : ℝ := (uniformDist f g).toReal

variable {f g a b : X → X}

@[blueprint "lem:edist-le-uniformdist"
  (statement := /-- $d(f(x), g(x)) \le d_\infty(f,g)$ for every $x$. -/)]
theorem edist_le_uniformDist (x : X) : edist (f x) (g x) ≤ uniformDist f g :=
  le_iSup (fun x => edist (f x) (g x)) x

@[blueprint "lem:right-comp-1lip"
  (statement := /-- Right composition is $1$-Lipschitz for $d_\infty$:
    $d_\infty(a \circ f, b \circ f) \le d_\infty(a, b)$. -/)]
theorem uniformDist_comp_right_le : uniformDist (a ∘ f) (b ∘ f) ≤ uniformDist a b :=
  iSup_le fun x => le_iSup (fun y => edist (a y) (b y)) (f x)

@[blueprint "lem:left-comp-lip"
  (statement := /-- Left composition with a $K$-Lipschitz map $f$ is $K$-Lipschitz for $d_\infty$:
    $d_\infty(f \circ a, f \circ b) \le K\, d_\infty(a, b)$. -/)]
theorem uniformDist_comp_left_le {K : ℝ≥0} (hf : LipschitzWith K f) :
    uniformDist (f ∘ a) (f ∘ b) ≤ K * uniformDist a b := by
  /-- Pointwise, $d(f(a(x)), f(b(x))) \le K d(a(x), b(x)) \le K d_\infty(a,b)$. -/
  refine iSup_le fun x => ?_
  calc edist (f (a x)) (f (b x)) ≤ K * edist (a x) (b x) := hf.edist_le_mul _ _
    _ ≤ K * uniformDist a b := by gcongr; exact edist_le_uniformDist x

/-! ### The pseudo-emetric space $(\mathcal X^{\mathcal X}, d_\infty)$

Mathlib already provides the sup-edist on `X →ᵤ X` (`UniformFun X X`). We give it the name
`UnifMaps X`. Since `UnifMaps X` unfolds (by `δ`-reduction) to `X → X`, a set `A : Set (X → X)`
is accepted wherever a `Set (UnifMaps X)` is expected (e.g. `f ∈ A`, `φ '' A`), and a map
`f : UnifMaps X` can be applied to points. However a type ascription `(A : Set (UnifMaps X))` does
*not* change the type Lean infers for `A`, so in `coveringNumber ε A`, `edist f g`, `IsCover ε A C`
etc. one must fix the carrier explicitly: write `coveringNumber (X := UnifMaps X) ε A`,
`IsCover (X := UnifMaps X) ε A C`, and `edist (toUnifMaps f) (toUnifMaps g)` (the reducible
identity `toUnifMaps : (X → X) → UnifMaps X` below). This is the same mechanism as for
`EmpSpace S`. -/

@[blueprint "def:unif-maps"
  (statement := /-- The pseudo-emetric space $(\mathcal X^{\mathcal X}, d_\infty)$ of self-maps
    equipped with the uniform distance (a type synonym of $\mathcal X^{\mathcal X}$; in Lean it is
    Mathlib's `X →ᵤ X`, the function space with the uniform structure). -/)]
def UnifMaps (X : Type*) : Type _ := X →ᵤ X

@[blueprint "def:unif-maps-instance"
  (statement := /-- $d_\infty$ is a pseudo-emetric on $\mathcal X^{\mathcal X}$ (it may take the
    value $\infty$). This is Mathlib's instance on `X →ᵤ X`. -/)]
noncomputable instance instPseudoEMetricSpaceUnifMaps : PseudoEMetricSpace (UnifMaps X) :=
  inferInstanceAs (PseudoEMetricSpace (X →ᵤ X))

@[blueprint "def:to-unif-maps"
  (statement := /-- The (identity) map $\mathcal X^{\mathcal X} \to (\mathcal X^{\mathcal X},
    d_\infty)$ viewing a self-map as a point of the pseudo-emetric space. -/)]
abbrev toUnifMaps (f : X → X) : UnifMaps X := f

omit [PseudoEMetricSpace X] in
@[simp, blueprint "lem:to-unif-maps-apply"
  (statement := /-- Viewing $f$ in $(\mathcal X^{\mathcal X}, d_\infty)$ does not change its
    values. -/)]
theorem toUnifMaps_apply (f : X → X) (x : X) : toUnifMaps f x = f x := rfl

@[blueprint "lem:edist-unif-maps"
  (statement := /-- On $(\mathcal X^{\mathcal X}, d_\infty)$ the extended distance is
    $d_\infty$. -/)]
theorem edist_unifMaps (f g : UnifMaps X) : edist f g = uniformDist f g := rfl

@[blueprint "lem:edist-to-unif-maps"
  (statement := /-- $d_\infty$ is the distance of $(\mathcal X^{\mathcal X}, d_\infty)$:
    $\mathrm{edist}(f, g) = d_\infty(f,g)$ for $f, g \in \mathcal X^{\mathcal X}$. -/)]
theorem edist_toUnifMaps (f g : X → X) : edist (toUnifMaps f) (toUnifMaps g) = uniformDist f g :=
  rfl

@[blueprint "lem:edist-eval-le-unif-maps"
  (statement := /-- $d(f(x), g(x)) \le d_\infty(f,g)$ for $f, g \in (\mathcal X^{\mathcal X},
    d_\infty)$. -/)]
theorem edist_eval_le_unifMaps (f g : UnifMaps X) (x : X) : edist (f x) (g x) ≤ edist f g :=
  edist_le_uniformDist x

end EMetric

variable {X : Type*} [PseudoMetricSpace X]

@[blueprint "def:d-S"
  (statement := /-- For a sample $S = (x_1,\dots,x_n)$ the empirical distance is
    $d_S(f,g) = \bigl(\frac1n \sum_{i=1}^n d(f(x_i), g(x_i))^2\bigr)^{1/2}$. -/)]
noncomputable def empDist {n : ℕ} (S : Fin n → X) (f g : X → X) : ℝ :=
  Real.sqrt ((1 / (n : ℝ)) * ∑ i, dist (f (S i)) (g (S i)) ^ 2)

@[blueprint "def:emp-norm"
  (statement := /-- For real-valued $u, v$ the empirical $L^2$ distance is
    $\|u - v\|_S = \bigl(\frac1n \sum_{i=1}^n |u(x_i) - v(x_i)|^2\bigr)^{1/2}$. -/)]
noncomputable def empNorm {n : ℕ} (S : Fin n → X) (u v : X → ℝ) : ℝ :=
  Real.sqrt ((1 / (n : ℝ)) * ∑ i, |u (S i) - v (S i)| ^ 2)

@[blueprint "def:emp-sup-norm"
  (statement := /-- The empirical sup norm $\|u\|_{S,\infty} = \max_{i \le n} |u(x_i)|$
    (equal to $0$ when $n = 0$). -/)]
noncomputable def empSupNorm {n : ℕ} (S : Fin n → X) (u : X → ℝ) : ℝ := ⨆ i, |u (S i)|

@[blueprint "def:diam-S"
  (statement := /-- The empirical diameter of a class $F$ is
    $\mathrm{diam}_S(F) = \sup_{f, g \in F} d_S(f,g)$. -/)]
noncomputable def empDiam {n : ℕ} (S : Fin n → X) (F : Set (X → X)) : ℝ :=
  sSup (Set.image2 (empDist S) F F)

variable {n : ℕ} {S : Fin n → X} {f g a b : X → X}

@[simp, blueprint "lem:empdist-self"
  (statement := /-- $d_S(f,f) = 0$. -/)]
theorem empDist_self : empDist S f f = 0 := by
  simp [empDist]

@[blueprint "lem:empdist-comm"
  (statement := /-- $d_S(f,g) = d_S(g,f)$. -/)]
theorem empDist_comm : empDist S f g = empDist S g f := by
  simp [empDist, dist_comm]

@[blueprint "lem:empdist-nonneg"
  (statement := /-- $d_S(f,g) \ge 0$. -/)]
theorem empDist_nonneg : 0 ≤ empDist S f g := Real.sqrt_nonneg _

@[blueprint "lem:sqrt-sum-sq-add-le"
  (statement := /-- Minkowski's inequality for the Euclidean norm on $\mathbb R^n$:
    $\bigl(\sum_i (u_i + v_i)^2\bigr)^{1/2} \le \bigl(\sum_i u_i^2\bigr)^{1/2}
    + \bigl(\sum_i v_i^2\bigr)^{1/2}$. -/)]
theorem sqrt_sum_sq_add_le (u v : Fin n → ℝ) :
    Real.sqrt (∑ i, (u i + v i) ^ 2) ≤ Real.sqrt (∑ i, u i ^ 2) + Real.sqrt (∑ i, v i ^ 2) := by
  /-- This is the triangle inequality in the Euclidean space $\ell^2(\{1,\dots,n\})$. -/
  have h := norm_add_le (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 v)
  simpa [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs] using h

@[blueprint "lem:empdist-triangle"
  (statement := /-- The empirical distance satisfies the triangle inequality:
    $d_S(f,h) \le d_S(f,g) + d_S(g,h)$.
    Hence $d_S$ is a pseudometric on $\mathcal X^{\mathcal X}$. -/)]
theorem empDist_triangle (f g h : X → X) : empDist S f h ≤ empDist S f g + empDist S g h := by
  /-- Pointwise $d(f(x_i), h(x_i)) \le d(f(x_i), g(x_i)) + d(g(x_i), h(x_i))$, then apply
    Minkowski's inequality to the vectors of pointwise distances. -/
  have hn : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  simp only [empDist, Real.sqrt_mul hn]
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  calc Real.sqrt (∑ i, dist (f (S i)) (h (S i)) ^ 2)
      ≤ Real.sqrt (∑ i, (dist (f (S i)) (g (S i)) + dist (g (S i)) (h (S i))) ^ 2) := by
        apply Real.sqrt_le_sqrt
        apply Finset.sum_le_sum
        intro i _
        exact pow_le_pow_left₀ dist_nonneg (dist_triangle _ _ _) 2
    _ ≤ _ := sqrt_sum_sq_add_le _ _

@[blueprint "def:emp-space"
  (statement := /-- The pseudometric space $(\mathcal X^{\mathcal X}, d_S)$ of self-maps equipped
    with the empirical distance of the sample $S$
    (a type synonym of $\mathcal X^{\mathcal X}$). -/)]
def EmpSpace {n : ℕ} (_S : Fin n → X) : Type _ := X → X

@[blueprint "def:emp-space-instance"
  (statement := /-- $d_S$ is a pseudometric on $\mathcal X^{\mathcal X}$. -/)]
noncomputable instance instPseudoMetricSpaceEmpSpace (S : Fin n → X) :
    PseudoMetricSpace (EmpSpace S) where
  dist f g := empDist S f g
  dist_self _ := empDist_self
  dist_comm _ _ := empDist_comm
  dist_triangle f g h := empDist_triangle f g h

@[blueprint "lem:dist-emp-space"
  (statement := /-- On $(\mathcal X^{\mathcal X}, d_S)$ the distance is $d_S$. -/)]
theorem dist_empSpace (f g : EmpSpace S) : dist f g = empDist S f g := rfl

@[blueprint "lem:dist-le-uniformdist-toreal"
  (statement := /-- If $d_\infty(f,g) < \infty$ then $d(f(x), g(x)) \le d_\infty(f,g)$
    as real numbers. -/)]
theorem dist_le_uniformDistReal (h : uniformDist f g ≠ ⊤) (x : X) :
    dist (f x) (g x) ≤ uniformDistReal f g := by
  rw [uniformDistReal, ← ENNReal.ofReal_le_iff_le_toReal h, ← edist_dist]
  exact edist_le_uniformDist x

@[blueprint "lem:dS-le-dinf"
  (statement := /-- The empirical distance is dominated by the uniform distance:
    $d_S(f,g) \le d_\infty(f,g)$ for every sample $S$. -/)]
theorem empDist_le_uniformDist : ENNReal.ofReal (empDist S f g) ≤ uniformDist f g := by
  /-- If $d_\infty(f,g) = \infty$ there is nothing to prove. Otherwise each term satisfies
    $d(f(x_i), g(x_i))^2 \le d_\infty(f,g)^2$, so the average is at most $d_\infty(f,g)^2$
    and we take square roots. -/
  by_cases h : uniformDist f g = ⊤
  · rw [h]; exact le_top
  set D := uniformDistReal f g with hD
  have hD0 : 0 ≤ D := ENNReal.toReal_nonneg
  have hsum : ∑ i, dist (f (S i)) (g (S i)) ^ 2 ≤ n * D ^ 2 := by
    calc ∑ i, dist (f (S i)) (g (S i)) ^ 2 ≤ ∑ _i : Fin n, D ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          exact pow_le_pow_left₀ dist_nonneg (dist_le_uniformDistReal h (S i)) 2
      _ = n * D ^ 2 := by simp
  have hle : empDist S f g ≤ D := by
    rw [empDist, Real.sqrt_le_left hD0]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp [sq_nonneg]
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      calc (1 / (n : ℝ)) * ∑ i, dist (f (S i)) (g (S i)) ^ 2 ≤ (1 / (n : ℝ)) * (n * D ^ 2) := by
            gcongr
        _ = D ^ 2 := by field_simp
  calc ENNReal.ofReal (empDist S f g) ≤ ENNReal.ofReal D := ENNReal.ofReal_le_ofReal hle
    _ = uniformDist f g := ENNReal.ofReal_toReal h

end LeanDeepgen
