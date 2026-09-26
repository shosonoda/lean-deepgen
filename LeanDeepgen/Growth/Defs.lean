import Mathlib
import Architect
import LeanDeepgen.Setting.WordBall
import LeanDeepgen.Setting.Metrics
import LeanDeepgen.Setting.Covering

/-!
# Growth of the hidden class with depth: definitions

The objects needed to *state* the growth conditions of the paper (App. F), without the
theorems about them:

* `wordOf f u = f_{i_k} ∘ ⋯ ∘ f_{i_1}` for a finite family `f : Fin r → X → X` and a word
  `u : List (Fin r)` (E1, E1', E2; theorems in `LeanDeepgen.Growth.Exponential`);
* `geomSum Λ m = S_m(Λ) = ∑_{i<m} Λ^i`, the geometric sum of the layerwise Lipschitz constant
  (the covering envelope `prop:envelope`; `LeanDeepgen.Growth.Envelope`);
* `evalProbes P f = (f (p_j))_j`, the evaluation map at finitely many probes
  (`LeanDeepgen.Growth.Lemmas`);
* `orbitMap α g = α g` for a monoid homomorphism `α : G →* Function.End X` (P2;
  `LeanDeepgen.Growth.Polynomial`);
* `memoryLength c L K ε = L + ⌈log_{1/c}(2 diam K / ε)⌉`, the memory length of P1'
  (`LeanDeepgen.Growth.Saturation`);
* the memory-preserving expansion of E3 (`LeanDeepgen.Growth.MemoryExpansion`): the state
  space `MemState E = ℕ → E` with the bounded sup metric
  `edist x y = ⨆ j, min 1 (edist (x j) (y j))`, the reset `reset x = 0`, the expander
  `expand lam x = (lam • x_j)_j`, the writers `write u x = (u, x_0, x_1, …)`, the generator
  set `memGen G lam = {reset, expand lam} ∪ write '' G`, the words
  `memWord lam k u = expand lam ∘ write (u (k-1)) ∘ ⋯ ∘ expand lam ∘ write (u 0) ∘ reset` and
  `memWords G lam k = {memWord lam k u : u ∈ G^k}`.

Only definitions, instances and `rfl`/`simp`-level lemmas live here.
-/

open scoped NNReal ENNReal
open Metric

namespace LeanDeepgen

/-! ### Words in a finite family of generators (E1, E1', E2) -/

section Words

variable {X : Type*} {r : ℕ}

@[blueprint "def:word-of"
  (statement := /-- For a finite family $f = (f_1, \dots, f_r)$ of self-maps and a word
    $u = (i_1, \dots, i_k) \in [r]^k$, the associated map is
    $f_u = f_{i_k} \circ \cdots \circ f_{i_1}$ (the first letter acts first);
    $f_{\emptyset} = \mathrm{id}$. In Lean: `wordOf f [] = id` and
    `wordOf f (i :: u) = wordOf f u ∘ f i`. -/)]
def wordOf (f : Fin r → X → X) : List (Fin r) → X → X
  | [] => id
  | i :: u => wordOf f u ∘ f i

@[simp, blueprint "lem:wordof-nil"
  (statement := /-- $f_\emptyset = \mathrm{id}$. -/)]
theorem wordOf_nil (f : Fin r → X → X) : wordOf f [] = id := rfl

@[simp, blueprint "lem:wordof-cons"
  (statement := /-- $f_{(i, u)} = f_u \circ f_i$. -/)]
theorem wordOf_cons (f : Fin r → X → X) (i : Fin r) (u : List (Fin r)) :
    wordOf f (i :: u) = wordOf f u ∘ f i := rfl

@[blueprint "lem:wordof-cons-apply"
  (statement := /-- $f_{(i,u)}(x) = f_u(f_i(x))$. -/)]
theorem wordOf_cons_apply (f : Fin r → X → X) (i : Fin r) (u : List (Fin r)) (x : X) :
    wordOf f (i :: u) x = wordOf f u (f i x) := rfl

end Words

/-! ### The geometric sum of the layerwise Lipschitz constant (covering envelope) -/

section GeomSum

@[blueprint "def:envelope-geom-sum"
  (statement := /-- For a layerwise Lipschitz constant $\Lambda \ge 0$ and $m \ge 0$, the
    geometric sum $S_m(\Lambda) := \sum_{i=0}^{m-1} \Lambda^i$ (so $S_0 = 0$, $S_1 = 1$) of
    `prop:implementation`(b); it is the amplification factor of the covering envelope
    `prop:envelope`. -/)]
def geomSum (Λ : ℝ≥0) (m : ℕ) : ℝ≥0 := ∑ i ∈ Finset.range m, Λ ^ i

@[simp, blueprint "lem:envelope-geom-sum-zero"
  (statement := /-- $S_0(\Lambda) = 0$. -/)]
theorem geomSum_zero (Λ : ℝ≥0) : geomSum Λ 0 = 0 := by simp [geomSum]

@[simp, blueprint "lem:envelope-geom-sum-one"
  (statement := /-- $S_1(\Lambda) = 1$. -/)]
theorem geomSum_one (Λ : ℝ≥0) : geomSum Λ 1 = 1 := by simp [geomSum]

@[blueprint "lem:envelope-geom-sum-coe"
  (statement := /-- As a real number, $S_m(\Lambda) = \sum_{i<m} \Lambda^i$. -/)]
theorem coe_geomSum (Λ : ℝ≥0) (m : ℕ) :
    ((geomSum Λ m : ℝ≥0) : ℝ) = ∑ i ∈ Finset.range m, (Λ : ℝ) ^ i := by
  simp [geomSum]

end GeomSum

/-! ### Evaluation at probes -/

section Probes

variable {X : Type*}

@[blueprint "def:eval-probes"
  (statement := /-- For probes $P = (p_j)_{j \in J}$ ($J$ finite) the evaluation map is
    $\mathrm{ev}_P : (\mathcal X^{\mathcal X}, d_\infty) \to (\mathcal X^J, d_{\max})$,
    $\mathrm{ev}_P(f) = (f(p_j))_{j \in J}$, where $\mathcal X^J$ carries the sup-metric. -/)]
def evalProbes {ι : Type*} (P : ι → X) (f : UnifMaps X) : ι → X := fun j => f (P j)

end Probes

/-! ### Orbit maps of a group action (P2) -/

section Action

variable {X : Type*} {G : Type*} [Group G]

@[blueprint "def:p2-orbit-map"
  (statement := /-- For a monoid homomorphism $\alpha : H \to \mathcal X^{\mathcal X}$
    (i.e. $\alpha(gh) = \alpha(g) \circ \alpha(h)$ and $\alpha(e) = \mathrm{id}$), the orbit map
    is $g \mapsto \alpha(g) \in \mathcal X^{\mathcal X}$. -/)]
def orbitMap (α : G →* Function.End X) (g : G) : X → X := α g

@[simp, blueprint "lem:p2-orbit-map-one"
  (statement := /-- $\alpha(e) = \mathrm{id}$. -/)]
theorem orbitMap_one (α : G →* Function.End X) : orbitMap α 1 = id := by
  simp only [orbitMap, map_one]; rfl

@[simp, blueprint "lem:p2-orbit-map-mul"
  (statement := /-- $\alpha(gh) = \alpha(g) \circ \alpha(h)$. -/)]
theorem orbitMap_mul (α : G →* Function.End X) (g h : G) :
    orbitMap α (g * h) = orbitMap α g ∘ orbitMap α h := by
  simp only [orbitMap, map_mul]; rfl

end Action

/-! ### The memory length of P1' -/

section MemoryLength

variable {X : Type*} [PseudoMetricSpace X]

@[blueprint "def:p1ucont-memory-length"
  (statement := /-- The memory length of P1':
    $m(\varepsilon) := L + \bigl\lceil \log_{1/c}\bigl(2\,\mathrm{diam}(K)/\varepsilon\bigr)
    \bigr\rceil$ (a natural number; the ceiling of a non-positive real is $0$). -/)]
noncomputable def memoryLength (c : ℝ≥0) (L : ℕ) (K : Set X) (ε : ℝ≥0) : ℕ :=
  L + ⌈Real.logb (1 / (c : ℝ)) (2 * Metric.diam K / (ε : ℝ))⌉₊

end MemoryLength

/-! ### Memory-preserving expansion (E3): the state space and its bounded sup metric -/

@[blueprint "def:e3-state-space"
  (statement := /-- The memory state space $X = E^{\mathbb N}$ (the paper's $\ell_\infty(E)$;
    we allow all sequences since the bounded metric below is finite anyway). -/)]
def MemState (E : Type*) : Type _ := ℕ → E

section MemState

variable {E : Type*} [NormedAddCommGroup E]

@[blueprint "lem:e3-state-nonempty"
  (statement := /-- $X = E^{\mathbb N}$ is nonempty (it contains $0$). -/)]
instance instNonemptyMemState : Nonempty (MemState E) := ⟨fun _ => 0⟩

@[blueprint "lem:e3-min-one-triangle"
  (statement := /-- If $a \le b + c$ in $[0,\infty]$ then
    $\min\{1,a\} \le \min\{1,b\} + \min\{1,c\}$. -/)]
theorem min_one_le_add_min_one {a b c : ℝ≥0∞} (h : a ≤ b + c) :
    min 1 a ≤ min 1 b + min 1 c := by
  /-- If $b, c \le 1$ this is $a \le b + c$; otherwise the right side is at least $1$. -/
  rcases le_or_gt b 1 with hb | hb
  · rcases le_or_gt c 1 with hc | hc
    · rw [min_eq_right hb, min_eq_right hc]; exact (min_le_right _ _).trans h
    · rw [min_eq_left hc.le]; exact (min_le_left _ _).trans le_add_self
  · rw [min_eq_left hb.le]; exact (min_le_left _ _).trans le_self_add

@[blueprint "def:e3-state-metric"
  (statement := /-- The bounded sup metric on $X = E^{\mathbb N}$:
    $d_X(x,y) = \sup_{j} \min\{1, \|x_j - y_j\|_E\}$. It is a pseudo-emetric (indeed a metric
    with values in $[0,1]$). -/)]
noncomputable instance instPseudoEMetricSpaceMemState : PseudoEMetricSpace (MemState E) where
  edist x y := ⨆ j, min 1 (edist (x j) (y j))
  edist_self x := by simp
  edist_comm x y := by simp only [edist_comm]
  edist_triangle x y z := by
    refine iSup_le fun j => ?_
    calc min 1 (edist (x j) (z j))
        ≤ min 1 (edist (x j) (y j)) + min 1 (edist (y j) (z j)) :=
          min_one_le_add_min_one (edist_triangle _ _ _)
      _ ≤ (⨆ j, min 1 (edist (x j) (y j))) + ⨆ j, min 1 (edist (y j) (z j)) :=
          add_le_add (le_iSup (fun j => min 1 (edist (x j) (y j))) j)
            (le_iSup (fun j => min 1 (edist (y j) (z j))) j)

@[blueprint "lem:e3-edist-state"
  (statement := /-- $d_X(x,y) = \sup_j \min\{1, \|x_j - y_j\|_E\}$. -/)]
theorem edist_memState (x y : MemState E) : edist x y = ⨆ j, min 1 (edist (x j) (y j)) := rfl

@[blueprint "lem:e3-edist-state-le-one"
  (statement := /-- $d_X(x,y) \le 1$. -/)]
theorem edist_memState_le_one (x y : MemState E) : edist x y ≤ 1 :=
  iSup_le fun _ => min_le_left _ _

/-! ### Reset, expander, writers -/

@[blueprint "def:e3-reset"
  (statement := /-- The reset map $r(x) = 0$. -/)]
def reset : MemState E → MemState E := fun _ _ => 0

@[blueprint "def:e3-write"
  (statement := /-- The writer $g_u(x_0, x_1, \dots) = (u, x_0, x_1, \dots)$. -/)]
def write (u : E) : MemState E → MemState E := fun x j =>
  match j with
  | 0 => u
  | i + 1 => x i

@[simp, blueprint "lem:e3-reset-apply"
  (statement := /-- $r(x)_j = 0$. -/)]
theorem reset_apply (x : MemState E) (j : ℕ) : reset x j = 0 := rfl

omit [NormedAddCommGroup E] in
@[simp, blueprint "lem:e3-write-apply-zero"
  (statement := /-- $g_u(x)_0 = u$. -/)]
theorem write_apply_zero (u : E) (x : MemState E) : write u x 0 = u := rfl

omit [NormedAddCommGroup E] in
@[simp, blueprint "lem:e3-write-apply-succ"
  (statement := /-- $g_u(x)_{i+1} = x_i$. -/)]
theorem write_apply_succ (u : E) (x : MemState E) (i : ℕ) : write u x (i + 1) = x i := rfl

variable [NormedSpace ℝ E]

@[blueprint "def:e3-expand"
  (statement := /-- The expander $A(x_0, x_1, \dots) = (\lambda x_0, \lambda x_1, \dots)$. -/)]
def expand (lam : ℝ≥0) : MemState E → MemState E := fun x j => (lam : ℝ) • x j

@[simp, blueprint "lem:e3-expand-apply"
  (statement := /-- $A(x)_j = \lambda x_j$. -/)]
theorem expand_apply (lam : ℝ≥0) (x : MemState E) (j : ℕ) :
    expand lam x j = (lam : ℝ) • x j := rfl

@[blueprint "def:e3-generators"
  (statement := /-- The hidden-layer class $F = \{r, A\} \cup \{g_u : u \in G\}$. -/)]
def memGen (G : Set E) (lam : ℝ≥0) : Set (MemState E → MemState E) :=
  {reset, expand lam} ∪ write '' G

/-! ### Words -/

@[blueprint "def:e3-word"
  (statement := /-- For $u = (u_0, \dots, u_{k-1}) \in E^k$ the word
    $w_u = A \circ g_{u_{k-1}} \circ A \circ g_{u_{k-2}} \circ \cdots \circ A \circ g_{u_0}
    \circ r$ (so $u_0$ is written first and $u_{k-1}$ last). In Lean it is defined by recursion
    on $k$: $w_{()} = r$ and $w_{(u, a)} = A \circ g_a \circ w_u$. -/)]
def memWord (lam : ℝ≥0) : (k : ℕ) → (Fin k → E) → MemState E → MemState E
  | 0, _ => reset
  | k + 1, u => expand lam ∘ write (u (Fin.last k)) ∘ memWord lam k (Fin.init u)

@[simp, blueprint "lem:e3-word-zero"
  (statement := /-- $w_{()} = r$. -/)]
theorem memWord_zero (lam : ℝ≥0) (u : Fin 0 → E) : memWord lam 0 u = reset := rfl

@[simp, blueprint "lem:e3-word-succ"
  (statement := /-- $w_u = A \circ g_{u_k} \circ w_{u|_{k}}$ for $u \in E^{k+1}$. -/)]
theorem memWord_succ (lam : ℝ≥0) (k : ℕ) (u : Fin (k + 1) → E) :
    memWord lam (k + 1) u = expand lam ∘ write (u (Fin.last k)) ∘ memWord lam k (Fin.init u) := rfl

@[blueprint "def:e3-words"
  (statement := /-- $W_k = \{w_u : u \in G^k\}$. -/)]
def memWords (G : Set E) (lam : ℝ≥0) (k : ℕ) : Set (MemState E → MemState E) :=
  memWord lam k '' Set.univ.pi fun _ : Fin k => G

end MemState

end LeanDeepgen
