import Mathlib
import Architect
import LeanDeepgen.Setting.WordBall

/-!
# Hypothesis classes

The output-layer class `H ⊆ (X → ℝ)` composed with the depth-`k` hidden class gives the
depth-`k` hypothesis class `ℋ_k = H ∘ B(k,F)`. We also define the implementation error
`ε_imp = sup_{f ∈ ℋ} ‖f - ι f‖_∞` of an implementation map `ι`.
-/

open scoped ENNReal

namespace LeanDeepgen

variable {X : Type*}

@[blueprint "def:comp-class"
  (statement := /-- For $H \subseteq \mathbb R^{\mathcal X}$ and
    $F \subseteq \mathcal X^{\mathcal X}$, $H \circ F = \{h \circ f : h \in H,\ f \in F\}$. -/)]
def compClass (H : Set (X → ℝ)) (F : Set (X → X)) : Set (X → ℝ) :=
  {u | ∃ h ∈ H, ∃ f ∈ F, u = h ∘ f}

@[blueprint "def:hypothesis-class"
  (statement := /-- The depth-$k$ hypothesis class is $\mathcal H_k = H \circ B(k,F)$. -/)]
def hypothesisClass (H : Set (X → ℝ)) (F : Set (X → X)) (k : ℕ) : Set (X → ℝ) :=
  compClass H (wordBall F k)

@[blueprint "def:err-imp"
  (statement := /-- The implementation error of an implementation map $\iota$ on a class
    $\mathcal H$ is
    $\varepsilon_{\mathrm{imp}} = \sup_{f \in \mathcal H} \|f - \iota f\|_\infty$. -/)]
noncomputable def implError (ι : (X → ℝ) → (X → ℝ)) (𝓗 : Set (X → ℝ)) : ℝ≥0∞ :=
  ⨆ f ∈ 𝓗, ⨆ x, ENNReal.ofReal |f x - ι f x|

variable {H : Set (X → ℝ)} {F F' : Set (X → X)}

@[blueprint "lem:comp-class-mono"
  (statement := /-- If $F \subseteq F'$ then $H \circ F \subseteq H \circ F'$. -/)]
theorem compClass_mono_right (h : F ⊆ F') : compClass H F ⊆ compClass H F' := by
  rintro u ⟨h', hh', f, hf, rfl⟩
  exact ⟨h', hh', f, h hf, rfl⟩

@[blueprint "lem:comp-class-singleton-id"
  (statement := /-- $H \circ \{\mathrm{id}\} = H$. -/)]
theorem compClass_singleton_id : compClass H {id} = H := by
  ext u
  simp [compClass]

@[blueprint "lem:hypothesis-class-zero"
  (statement := /-- $\mathcal H_0 = H \circ \{\mathrm{id}\} = H$. -/)]
theorem hypothesisClass_zero : hypothesisClass H F 0 = H := by
  ext u
  simp [hypothesisClass, compClass]

@[blueprint "lem:hypothesis-class-mono"
  (statement := /-- The hypothesis classes are increasing in depth:
    $\mathcal H_k \subseteq \mathcal H_{k+1}$. -/)]
theorem hypothesisClass_mono : Monotone (hypothesisClass H F) :=
  fun _ _ hkl => compClass_mono_right (wordBall_mono hkl)

end LeanDeepgen
