import Mathlib
import Architect
import FoML
import LeanDeepgen.Setting.WordBall
import LeanDeepgen.Setting.Metrics
import LeanDeepgen.Setting.Covering
import LeanDeepgen.Setting.Hypothesis
import LeanDeepgen.Setting.Loss
import LeanDeepgen.Setting.Rademacher
import LeanDeepgen.Profiles.Defs

/-!
# Assumptions and auxiliary definitions of the main theorems

The definitions needed to *state* the generalization bounds of the paper (Sec. 3, App. B–D),
collected in one module without any of the theorems:

* bias–variance decomposition (`LeanDeepgen.Bounds.BiasVariance`): sup-norm separability
  `IsSupSeparable`, the class `SupIndex 𝓗` (the class `𝓗` indexed by itself inside `X →ᵤ ℝ`) and
  the loss class `lossClass L 𝓗` in FoML's indexed form;
* hidden–output decomposition (`LeanDeepgen.Bounds.HiddenOutput`): the hidden-indexed process
  `outputProcess S H f σ = sup_{h ∈ H} n⁻¹ ∑ᵢ σᵢ h(f(xᵢ))`, the sub-Gaussian increment assumption
  `SubGaussianIncrements` (`ass:sg-increment-main`) and the Hilbert readout class
  `hilbertReadoutClass Φ`;
* Sudakov-type converse (`LeanDeepgen.Bounds.Sudakov`): the readout-realization assumption
  `ReadoutRealization` (`ass:readout-realization-main`);
* deterministic entropy decomposition (`LeanDeepgen.Bounds.EntropyDecomp`): the pseudo-emetric
  space `UnifFun X = X →ᵤ ℝ` with the uniform distance, the assumptions `EntReadout`
  (`ass:ent-readout`) and `EntTransition` (`ass:ent-transition`), and the root entropies
  `entH`, `entF`;
* its sample version (`LeanDeepgen.Bounds.EntropyDecompSample`): the pseudometric space
  `EmpFun S` with the empirical `L²` distance `‖·‖_S` (FoML's `empiricalPMet S`), the reachable
  set `reachSet S F`, the pushed-forward covering number `pushedCoveringNumber`, the
  assumptions `EntReadoutSample`, `EntTransitionSample`, and the root entropies `entHS`, `entFS`;
* the variance term (`LeanDeepgen.Bounds.Variance`): the identity
  `toEmpSpace S : (𝒳^𝒳, d_∞) → (𝒳^𝒳, d_S)` and `varTerm AH L n S F k = 12 A_H L V_k(S) / √n`.

Only definitions, instances and `rfl`/`simp`-level lemmas live here.
-/

open MeasureTheory
open scoped NNReal ENNReal UniformConvergence

namespace LeanDeepgen

/-! ### Bias–variance decomposition: separability and the loss class -/

section BiasVariance

variable {X Y : Type*}

@[blueprint "def:sup-separable"
  (statement := /-- A class $\mathcal H \subseteq \mathbb R^{\mathcal X}$ is (sup-norm) separable
    if it has a countable subset $\mathcal D \subseteq \mathcal H$ which is dense for the uniform
    norm: for every $f \in \mathcal H$ and $\varepsilon > 0$ there is $g \in \mathcal D$ with
    $\sup_x |f(x) - g(x)| \le \varepsilon$. -/)]
def IsSupSeparable (𝓗 : Set (X → ℝ)) : Prop :=
  ∃ Dn : Set (X → ℝ), Dn.Countable ∧ Dn ⊆ 𝓗 ∧
    ∀ f ∈ 𝓗, ∀ ε > (0 : ℝ), ∃ g ∈ Dn, ∀ x, |f x - g x| ≤ ε

/-- The class `𝓗` indexed by itself, viewed inside `X →ᵤ ℝ` (topology of uniform convergence). -/
abbrev SupIndex (𝓗 : Set (X → ℝ)) : Type _ := ↥(UniformFun.toFun ⁻¹' 𝓗 : Set (X →ᵤ ℝ))

/-- The loss class `(x, y) ↦ ℓ(f(x), y)`, `f ∈ 𝓗`, in FoML's indexed form. -/
noncomputable def lossClass (L : BoundedLipschitzLoss Y) (𝓗 : Set (X → ℝ)) :
    SupIndex 𝓗 → X × Y → ℝ :=
  fun h z => L.ℓ (UniformFun.toFun h.1 z.1) z.2

end BiasVariance

/-! ### Hidden–output decomposition: the output process and sub-Gaussian increments -/

section HiddenOutput

variable {X : Type*}

@[blueprint "def:output-process"
  (statement := /-- For a sample $S = (x_1,\dots,x_n)$, an output-layer class $H$ and a hidden
    map $f$, the hidden-indexed process is
    $Z_f(\sigma) = \sup_{h \in H} \frac1n \sum_{i=1}^n \sigma_i h(f(x_i))$,
    $\sigma \in \{\pm1\}^n$. -/)]
noncomputable def outputProcess {n : ℕ} (S : Fin n → X) (H : Set (X → ℝ)) (f : X → X)
    (σ : Signs n) : ℝ :=
  ⨆ h : H, normalizedRademacherSum n (fun h : H => (h : X → ℝ)) (f ∘ S) σ h

variable [PseudoMetricSpace X]

open Classical in
@[blueprint "ass:sg-increment-main"
  (statement := /-- \textbf{Sub-Gaussian output-layer increments.} Let $\mathfrak F$ be a
    hidden-layer class and $A_H, L$ constants. For all $f, g \in \mathfrak F$ and $t > 0$,
    $$\mathbb P_\sigma\bigl(|Z_f - Z_g| > t\bigr) \le
    2 \exp\Bigl(-\frac{n t^2}{2 A_H^2 L^2 d_S(f,g)^2}\Bigr),$$
    where $\mathbb P_\sigma$ is the uniform distribution on $\{\pm1\}^n$; and when
    $d_S(f,g) = 0$ the requirement is $Z_f = Z_g$ (for every $\sigma$), which is the limiting
    interpretation of the display (in Lean the display with $d_S(f,g)=0$ reads
    $\ldots \le 2\exp(0)$, hence the separate conjunct). -/)]
def SubGaussianIncrements {n : ℕ} (S : Fin n → X) (H : Set (X → ℝ)) (𝔉 : Set (X → X))
    (AH L : ℝ) : Prop :=
  (∀ f ∈ 𝔉, ∀ g ∈ 𝔉, empDist S f g = 0 →
    ∀ σ : Signs n, outputProcess S H f σ = outputProcess S H g σ) ∧
  ∀ f ∈ 𝔉, ∀ g ∈ 𝔉, ∀ t : ℝ, 0 < t →
    ((Finset.univ.filter fun σ : Signs n =>
        t < |outputProcess S H f σ - outputProcess S H g σ|).card : ℝ) /
      Fintype.card (Signs n) ≤
    2 * Real.exp (-(n : ℝ) * t ^ 2 / (2 * AH ^ 2 * L ^ 2 * empDist S f g ^ 2))

omit [PseudoMetricSpace X] in
@[blueprint "def:hilbert-readout-class"
  (statement := /-- For a Hilbert space $\mathcal H$ and a feature map $\Phi : \mathcal X \to
    \mathcal H$, the norm-bounded linear output-layer class is
    $H_\Phi = \{x \mapsto \langle w, \Phi(x)\rangle : \|w\| \le 1\}$. -/)]
def hilbertReadoutClass {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Φ : X → E) : Set (X → ℝ) :=
  {h | ∃ w : E, ‖w‖ ≤ 1 ∧ h = fun x => inner ℝ w (Φ x)}

end HiddenOutput

/-! ### Sudakov-type converse: readout realization -/

section Sudakov

variable {X : Type*} [PseudoMetricSpace X]

@[blueprint "ass:readout-realization-main"
  (statement := /-- \textbf{Output-layer realization of hidden geometry.} For a sample $S$, an
    output-layer class $H$, a hidden class $B_k$ and constants $\kappa, R_{\mathrm{out}}$: there is,
    for each $g \in B_k$, an output layer $h_g \in H$ such that the map $\Psi_k(g) = h_g \circ g$
    satisfies $\|\Psi_k(g) - \Psi_k(g')\|_S \ge \kappa\, d_S(g,g')$ for $g, g' \in B_k$ and
    $\|\Psi_k(g)\|_{S,\infty} \le R_{\mathrm{out}}$ for $g \in B_k$. -/)]
def ReadoutRealization {n : ℕ} (S : Fin n → X) (H : Set (X → ℝ)) (Bk : Set (X → X))
    (κ Rout : ℝ) : Prop :=
  ∃ hf : (X → X) → (X → ℝ), (∀ g ∈ Bk, hf g ∈ H) ∧
    (∀ g ∈ Bk, ∀ g' ∈ Bk, κ * empDist S g g' ≤ empNorm S (hf g ∘ g) (hf g' ∘ g')) ∧
    (∀ g ∈ Bk, empSupNorm S (hf g ∘ g) ≤ Rout)

end Sudakov

/-! ### Deterministic entropy decomposition: uniform metric on real-valued functions -/

section UnifFun

@[blueprint "def:unif-fun"
  (statement := /-- The pseudo-emetric space $(\mathbb R^{\mathcal X}, \|\cdot\|_\infty)$ of
    real-valued functions with the uniform distance
    $\|u - v\|_\infty = \sup_x |u(x) - v(x)| \in [0,\infty]$ (a type synonym of
    $\mathbb R^{\mathcal X}$; in Lean Mathlib's `X →ᵤ ℝ`). -/)]
def UnifFun (X : Type*) : Type _ := X →ᵤ ℝ

@[blueprint "def:unif-fun-instance"
  (statement := /-- $\|\cdot\|_\infty$ is a pseudo-emetric on $\mathbb R^{\mathcal X}$. -/)]
noncomputable instance instPseudoEMetricSpaceUnifFun (X : Type*) :
    PseudoEMetricSpace (UnifFun X) :=
  inferInstanceAs (PseudoEMetricSpace (X →ᵤ ℝ))

@[blueprint "lem:edist-unif-fun"
  (statement := /-- On $(\mathbb R^{\mathcal X}, \|\cdot\|_\infty)$ the extended distance is
    $\sup_x \mathrm{edist}(u(x), v(x))$. -/)]
theorem edist_unifFun {X : Type*} (u v : UnifFun X) : edist u v = ⨆ x, edist (u x) (v x) := rfl

end UnifFun

section EntropyDecomp

open Metric

variable {X : Type*} [PseudoMetricSpace X]

@[blueprint "ass:ent-readout"
  (statement := /-- \textbf{Uniform output-layer regularity.} The output-layer class
    $H \subseteq \mathbb R^{\mathcal X}$ has finite uniform covering numbers
    $N(H, \|\cdot\|_\infty, u) < \infty$ for all $u > 0$, and there are constants $B_H, L_H$ with
    $\|h\|_\infty \le B_H$ and $|h(x) - h(x')| \le L_H d(x,x')$ for all $h \in H$. -/)]
structure EntReadout (H : Set (X → ℝ)) (BH : ℝ) (LH : ℝ≥0) : Prop where
  cov : ∀ ε : ℝ≥0, 0 < ε → Metric.externalCoveringNumber (X := UnifFun X) ε H ≠ ⊤
  bdd : ∀ h ∈ H, ∀ x, |h x| ≤ BH
  lip : ∀ h ∈ H, LipschitzWith LH h

@[blueprint "ass:ent-transition"
  (statement := /-- \textbf{Uniform transition covering.} The hidden-layer class
    $F \subseteq \mathcal X^{\mathcal X}$ has finite uniform covering numbers
    $N(F, d_\infty, v) < \infty$ for all $v > 0$. -/)]
def EntTransition (F : Set (X → X)) : Prop :=
  ∀ ε : ℝ≥0, 0 < ε → Metric.externalCoveringNumber (X := UnifMaps X) ε F ≠ ⊤

@[blueprint "def:to-unif-fun"
  (statement := /-- The (identity) map $\mathbb R^{\mathcal X} \to (\mathbb R^{\mathcal X},
    \|\cdot\|_\infty)$ viewing a real-valued function as a point of the pseudo-emetric
    space. -/)]
abbrev toUnifFun (u : X → ℝ) : UnifFun X := u

omit [PseudoMetricSpace X] in
@[blueprint "lem:edist-to-unif-fun"
  (statement := /-- $\mathrm{edist}(u, v) = \sup_x \mathrm{edist}(u(x), v(x))$ in
    $(\mathbb R^{\mathcal X}, \|\cdot\|_\infty)$. -/)]
theorem edist_toUnifFun (u v : X → ℝ) :
    edist (toUnifFun u) (toUnifFun v) = ⨆ x, edist (u x) (v x) := rfl

@[blueprint "def:ent-readout-entropy"
  (statement := /-- The root entropy of the output-layer class at scale $u$:
    $\mathcal E_H(u) = \sqrt{\log N^{\mathrm{ext}}(H, \|\cdot\|_\infty, u)}$ (with
    $u \mapsto \max(u, 0)$ and $\log\infty = \log 0 = 0$ in Lean). -/)]
noncomputable def entH (H : Set (X → ℝ)) (u : ℝ) : ℝ :=
  Real.sqrt (Real.log
    (externalCoveringNumber (X := UnifFun X) (Real.toNNReal u) H : ℝ≥0∞).toReal)

@[blueprint "def:ent-transition-entropy"
  (statement := /-- The root entropy of the hidden class at scale $v$:
    $\mathcal E_F(v) = \sqrt{\log N^{\mathrm{ext}}(F, d_\infty, v)}$. -/)]
noncomputable def entF (F : Set (X → X)) (v : ℝ) : ℝ :=
  Real.sqrt (Real.log
    (externalCoveringNumber (X := UnifMaps X) (Real.toNNReal v) F : ℝ≥0∞).toReal)

end EntropyDecomp

/-! ### Entropy decomposition on the sample: empirical metric on real-valued functions -/

section EmpFun

open Metric

variable {X : Type*} {n : ℕ}

@[blueprint "def:emp-fun"
  (statement := /-- The pseudometric space $(\mathbb R^{\mathcal X}, \|\cdot\|_S)$ of real-valued
    functions equipped with the empirical $L^2$ distance
    $\|u - v\|_S = \bigl(\frac1n \sum_i |u(x_i) - v(x_i)|^2\bigr)^{1/2}$ of the sample $S$
    (a type synonym of $\mathbb R^{\mathcal X}$). -/)]
def EmpFun (_S : Fin n → X) : Type _ := X → ℝ

@[blueprint "def:emp-fun-instance"
  (statement := /-- $\|\cdot\|_S$ is a pseudometric on $\mathbb R^{\mathcal X}$. In Lean this is
    FoML's `empiricalPMet S` (whose distance is FoML's `empiricalDist S`). -/)]
noncomputable instance instPseudoMetricSpaceEmpFun (S : Fin n → X) :
    PseudoMetricSpace (EmpFun S) :=
  empiricalPMet S

@[blueprint "def:to-emp-fun"
  (statement := /-- The (identity) map $\mathbb R^{\mathcal X} \to (\mathbb R^{\mathcal X},
    \|\cdot\|_S)$ viewing a real-valued function as a point of the pseudometric space. -/)]
abbrev toEmpFun (S : Fin n → X) (u : X → ℝ) : EmpFun S := u

@[blueprint "lem:dist-emp-fun-foml"
  (statement := /-- On $(\mathbb R^{\mathcal X}, \|\cdot\|_S)$ the distance is FoML's
    `empiricalDist S`. -/)]
theorem dist_empFun_eq_empiricalDist (S : Fin n → X) (u v : X → ℝ) :
    dist (toEmpFun S u) (toEmpFun S v) = empiricalDist S u v := rfl

@[blueprint "lem:dist-emp-fun"
  (statement := /-- On $(\mathbb R^{\mathcal X}, \|\cdot\|_S)$ the distance is
    $\|u - v\|_S$. -/)]
theorem dist_empFun (S : Fin n → X) (u v : X → ℝ) :
    dist (toEmpFun S u) (toEmpFun S v) = empNorm S u v := by
  rw [dist_empFun_eq_empiricalDist]
  simp [empiricalDist, empiricalNorm, empNorm, sq_abs]

@[blueprint "def:reachable-sample"
  (statement := /-- The set of points reached by the sample through the hidden class:
    $\mathcal R_S(F) = \{f(x_i) : f \in F,\ 1 \le i \le n\} \subseteq \mathcal X$. -/)]
def reachSet (S : Fin n → X) (F : Set (X → X)) : Set X :=
  {x | ∃ f ∈ F, ∃ i, f (S i) = x}

@[blueprint "lem:mem-reachable-sample"
  (statement := /-- $f(x_i) \in \mathcal R_S(F)$ for $f \in F$. -/)]
theorem mem_reachSet {S : Fin n → X} {F : Set (X → X)} {f : X → X} (hf : f ∈ F) (i : Fin n) :
    f (S i) ∈ reachSet S F :=
  ⟨f, hf, i, rfl⟩

@[blueprint "def:pushed-covering-number"
  (statement := /-- The uniform pushed-forward covering number of the output-layer class:
    $N_{S,F}(H, u) = \sup_{f \in F} N^{\mathrm{ext}}(H, \|\cdot\|_{f \circ S}, u)$, the largest
    external covering number of $H$ in the empirical metric of a pushed-forward sample
    $f \circ S = (f(x_1), \dots, f(x_n))$, $f \in F$. (Any uniform bound
    $N^{\mathrm{ext}}(H, \|\cdot\|_{f \circ S}, u) \le \bar N(u)$ for all $f \in F$ dominates
    it.) -/)]
noncomputable def pushedCoveringNumber (S : Fin n → X) (F : Set (X → X)) (H : Set (X → ℝ))
    (ε : ℝ≥0) : ℕ∞ :=
  ⨆ f ∈ F, externalCoveringNumber (X := EmpFun (f ∘ S)) ε H

end EmpFun

section EmpFunSample

open Metric

variable {X : Type*} [PseudoMetricSpace X] {n : ℕ}

@[blueprint "ass:ent-readout-sample"
  (statement := /-- \textbf{Sample output-layer regularity.} For a sample $S$ and a hidden class
    $F$, the output-layer class $H \subseteq \mathbb R^{\mathcal X}$ has finite uniform
    pushed-forward covering numbers $N_{S,F}(H, u) < \infty$ for all $u > 0$, and there are
    constants $B_H$, $L_H$ such that every $h \in H$ satisfies $|h(x)| \le B_H$ and
    $|h(x) - h(x')| \le L_H d(x, x')$ for all $x, x' \in \mathcal R_S(F)$ (boundedness and the
    Lipschitz estimate are only required on the points reached by the sample; compare
    \texttt{ass:ent-readout}, where both hold on all of $\mathcal X$ and $H$ is covered in the
    sup norm). -/)]
structure EntReadoutSample (S : Fin n → X) (F : Set (X → X)) (H : Set (X → ℝ)) (BH : ℝ)
    (LH : ℝ≥0) : Prop where
  cov : ∀ ε : ℝ≥0, 0 < ε → pushedCoveringNumber S F H ε ≠ ⊤
  bdd : ∀ h ∈ H, ∀ x ∈ reachSet S F, |h x| ≤ BH
  lip : ∀ h ∈ H, ∀ x ∈ reachSet S F, ∀ y ∈ reachSet S F, |h x - h y| ≤ LH * dist x y

@[blueprint "ass:ent-transition-sample"
  (statement := /-- \textbf{Sample transition covering.} The hidden-layer class
    $F \subseteq \mathcal X^{\mathcal X}$ has finite covering numbers in the empirical metric:
    $N^{\mathrm{ext}}(F, d_S, v) < \infty$ for all $v > 0$. -/)]
def EntTransitionSample (S : Fin n → X) (F : Set (X → X)) : Prop :=
  ∀ ε : ℝ≥0, 0 < ε → externalCoveringNumber (X := EmpSpace S) ε F ≠ ⊤

@[blueprint "def:ent-readout-entropy-sample"
  (statement := /-- The root entropy of the output-layer class at scale $u$ on the sample:
    $\mathcal E_{H,S}(u) = \sqrt{\log N_{S,F}(H, u)}$ (with $u \mapsto \max(u,0)$ and
    $\log\infty = \log 0 = 0$ in Lean). -/)]
noncomputable def entHS (S : Fin n → X) (F : Set (X → X)) (H : Set (X → ℝ)) (u : ℝ) : ℝ :=
  Real.sqrt (Real.log (pushedCoveringNumber S F H (Real.toNNReal u) : ℝ≥0∞).toReal)

@[blueprint "def:ent-transition-entropy-sample"
  (statement := /-- The root entropy of the hidden class at scale $v$ on the sample:
    $\mathcal E_{F,S}(v) = \sqrt{\log N^{\mathrm{ext}}(F, d_S, v)}$. -/)]
noncomputable def entFS (S : Fin n → X) (F : Set (X → X)) (v : ℝ) : ℝ :=
  Real.sqrt (Real.log
    (externalCoveringNumber (X := EmpSpace S) (Real.toNNReal v) F : ℝ≥0∞).toReal)

end EmpFunSample

/-! ### The variance term -/

section Variance

variable {X : Type*} [PseudoMetricSpace X] {n : ℕ} (S : Fin n → X)

@[blueprint "def:to-emp-space"
  (statement := /-- The identity map $(\mathcal X^{\mathcal X}, d_\infty) \to
    (\mathcal X^{\mathcal X}, d_S)$. -/)]
abbrev toEmpSpace (f : UnifMaps X) : EmpSpace S := f

@[blueprint "def:var"
  (statement := /-- The depth-dependent part of the estimation term is
    $$\mathrm{var}(k,n) := \frac{12 A_H L}{\sqrt n}\,\mathsf V_k(S),\qquad
    \mathsf V_k(S) = \int_0^{D_k(S)} \sqrt{\log N(B(k,F), d_S, \varepsilon)}\,d\varepsilon,$$
    with $D_k(S) = \mathrm{diam}_S B(k,F)$. -/)]
noncomputable def varTerm (AH L : ℝ) (n : ℕ) (S : Fin n → X) (F : Set (X → X)) (k : ℕ) : ℝ :=
  12 * AH * L / Real.sqrt n *
    entropyIntegral (Y := EmpSpace S) (empDiam S (wordBall F k)) (wordBall F k)

end Variance

end LeanDeepgen
