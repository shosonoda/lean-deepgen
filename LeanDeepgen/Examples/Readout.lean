import Mathlib
import Architect
import LeanDeepgen.Setting.WordBall
import LeanDeepgen.Setting.Metrics
import LeanDeepgen.Bounds.Sudakov

/-!
# Output-layer separation criteria for the Sudakov lower bound (paper App. Sudakov, §"When does
a linear output layer satisfy the lower-Lipschitz assumption")

Sufficient conditions on a linear Hilbert-space output layer
`H_{R_H}(Φ) = {x ↦ ⟪w, Φ x⟫ : ‖w‖ ≤ R_H}` (`linearReadouts Φ RH`) for the readout-realization
assumption `ass:readout-realization-main` (`ReadoutRealization`) of the conditional Sudakov bound.

* `prop:global_scalar_observable`: a single vector `u` whose scalar observable
  `x ↦ ⟪u, Φ x⟫` is `κ`-co-Lipschitz on the reachable sample set gives `ReadoutRealization` with
  the constant choice `h_g = ⟪u, Φ ·⟫` and `R_out = R_H R_Φ`.
* `prop:linear-interpolation`: if for each map `f_j` the evaluation operator
  `w ↦ (⟪w, Φ(f_j(x_i))⟫)_i` has a right inverse of norm `≤ Λ_j`, then any family of codes
  `u^{(j)} ∈ ℝ^n` is realized exactly by output layers `h_j ∈ H_{R_H}(Φ)` as soon as
  `R_H ≥ Λ_j ‖u^{(j)}‖_2`; separated bounded codes give separated, bounded `h_j ∘ f_j`.
  `cor:linear-interpolation-realization` turns this into `ReadoutRealization` for
  `B_k = {f_1, …, f_M}`.
* `cor:rkhs-readout`: the right-inverse hypothesis follows from a lower bound `λ_min > 0` on the
  Gram matrices `G_j = (⟪Φ(f_j(x_i)), Φ(f_j(x_{i'}))⟫)_{i,i'}`, with `Λ_j = λ_min^{-1/2}`
  (`lem:gram-right-inverse`); `cor:finite-dim-feature` is the special case
  `𝓗 = ℝ^m = EuclideanSpace ℝ (Fin m)`.

The right-inverse hypothesis of `prop:linear-interpolation` is stated abstractly, as the
existence, for every target vector `c ∈ ℝ^n`, of `w` with `‖w‖ ≤ Λ_j ‖c‖_2` and
`⟪w, Φ(f_j(x_i))⟫ = c_i` for all `i` (with `‖c‖_2 = (∑ c_i²)^{1/2}` written out). The paper's
assumption that `z_{j,1}, …, z_{j,n}` are distinct is implied by (and only needed for) the
surjectivity of the evaluation operator, so it does not appear separately.
-/

open scoped NNReal ENNReal

namespace LeanDeepgen

variable {X : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

@[blueprint "def:linear-readouts"
  (statement := /-- For a real Hilbert space $\mathcal H$, a feature map $\Phi : \mathcal X \to
    \mathcal H$ and a radius $R_H \ge 0$, the norm-bounded linear output-layer class is
    $$H_{R_H}(\Phi) = \{h_w(x) = \langle w, \Phi(x)\rangle_{\mathcal H} : \|w\|_{\mathcal H}
    \le R_H\}.$$ -/)]
def linearReadouts (Φ : X → E) (RH : ℝ) : Set (X → ℝ) :=
  {h | ∃ w : E, ‖w‖ ≤ RH ∧ h = fun x => inner ℝ (w) (Φ x)}

@[blueprint "def:reachable-sample-set"
  (statement := /-- The reachable sample set of a hidden class $B_k$ on the sample
    $S = (x_1, \dots, x_n)$ is $U_{k,S} = \{f(x_i) : f \in B_k,\ i \in [n]\}$. -/)]
def reachableSet {n : ℕ} (S : Fin n → X) (Bk : Set (X → X)) : Set X :=
  {x | ∃ f ∈ Bk, ∃ i, x = f (S i)}

/-! ### Global scalar observable -/

@[blueprint "prop:global_scalar_observable"
  (statement := /-- \textbf{(Global scalar observable.)} Fix a sample $S = (x_i)_{i=1}^n$, a hidden
    class $B_k$ and $U_{k,S} = \{f(x_i) : f \in B_k, i \in [n]\}$. Let $\Phi : \mathcal X \to
    \mathcal H$ and assume there are $u \in \mathcal H$ with $\|u\| \le R_H$ and constants
    $\kappa, R_\Phi > 0$ such that
    $$|\langle u, \Phi(x) - \Phi(y)\rangle| \ge \kappa\, d(x,y) \quad (x, y \in U_{k,S}), \qquad
    \sup_{x \in \mathcal X} \|\Phi(x)\| \le R_\Phi .$$
    Then the readout-realization assumption holds for $H_{R_H}(\Phi)$ on $B_k$ with constants
    $\kappa$ and $R_{\mathrm{out}} = R_H R_\Phi$, with the single choice $h_f = h_u =
    \langle u, \Phi(\cdot)\rangle$ for all $f \in B_k$:
    $\|h_u \circ f - h_u \circ g\|_S \ge \kappa\, d_S(f,g)$ and
    $\|h_u \circ f\|_{S,\infty} \le R_H R_\Phi$ for $f, g \in B_k$. -/)]
theorem global_scalar_observable [PseudoMetricSpace X] {n : ℕ} (S : Fin n → X)
    (Bk : Set (X → X)) (Φ : X → E)
    {RH RΦ κ : ℝ} (u : E) (hu : ‖u‖ ≤ RH) (hκ : 0 < κ) (hRΦ : 0 < RΦ)
    (hcolip : ∀ x ∈ reachableSet S Bk, ∀ y ∈ reachableSet S Bk,
      κ * dist x y ≤ |inner ℝ (u) (Φ x - Φ y)|)
    (hbdd : ∀ x, ‖Φ x‖ ≤ RΦ) :
    ReadoutRealization S (linearReadouts Φ RH) Bk κ (RH * RΦ) := by
  /-- Termwise, $\kappa^2 d(f(x_i), g(x_i))^2 \le |\langle u, \Phi(f(x_i)) - \Phi(g(x_i))
    \rangle|^2$ by co-Lipschitzness on $U_{k,S}$; average and take square roots. The bound
    $|\langle u, \Phi(f(x))\rangle| \le \|u\| \|\Phi(f(x))\| \le R_H R_\Phi$ is
    Cauchy--Schwarz. -/
  refine ⟨fun _ => fun x => inner ℝ (u) (Φ x), fun g _ => ⟨u, hu, rfl⟩, fun g hg g' hg' => ?_,
    fun g hg => ?_⟩
  · unfold empDist empNorm
    simp only [Function.comp_apply]
    rw [show κ = Real.sqrt (κ ^ 2) from (Real.sqrt_sq hκ.le).symm, ← Real.sqrt_mul (sq_nonneg κ)]
    apply Real.sqrt_le_sqrt
    rw [mul_left_comm, Finset.mul_sum]
    gcongr with i _
    rw [← mul_pow, ← inner_sub_right]
    exact pow_le_pow_left₀ (by positivity)
      (hcolip _ ⟨g, hg, i, rfl⟩ _ ⟨g', hg', i, rfl⟩) 2
  · unfold empSupNorm
    have hRH : 0 ≤ RH := (norm_nonneg u).trans hu
    refine Real.iSup_le (fun i => ?_) (by positivity)
    exact (abs_real_inner_le_norm u _).trans (mul_le_mul hu (hbdd _) (norm_nonneg _) hRH)

/-! ### Map-dependent finite-set interpolation -/

@[blueprint "prop:linear-interpolation"
  (statement := /-- \textbf{(Map-dependent finite-set interpolation criterion for linear heads.)}
    Fix $f_1, \dots, f_M \in B_k$ and a sample $S = (x_i)_{i=1}^n$, and let $\Phi : \mathcal X \to
    \mathcal H$. Assume that for each $j$ the evaluation operator $T_j : w \mapsto (\langle w,
    \Phi(f_j(x_i))\rangle)_{i \in [n]}$ admits a right inverse of norm $\le \Lambda_j$: for every
    $c \in \mathbb R^n$ there is $w \in \mathcal H$ with $\|w\| \le \Lambda_j \|c\|_2$ and
    $\langle w, \Phi(f_j(x_i))\rangle = c_i$ for all $i$. Then for every family of code vectors
    $u^{(1)}, \dots, u^{(M)} \in \mathbb R^n$ with $\Lambda_j \|u^{(j)}\|_2 \le R_H$ there are
    output layers $h_j \in H_{R_H}(\Phi)$ with $h_j(f_j(x_i)) = u^{(j)}_i$. Consequently, if
    $\bigl(\frac1n \sum_i |u^{(j)}_i - u^{(\ell)}_i|^2\bigr)^{1/2} \ge \rho$ for $j \ne \ell$ then
    $\|h_j \circ f_j - h_\ell \circ f_\ell\|_S \ge \rho$ for $j \ne \ell$, and if
    $\max_{j,i} |u^{(j)}_i| \le R_{\mathrm{out}}$ (with $R_{\mathrm{out}} \ge 0$) then
    $\|h_j \circ f_j\|_{S,\infty} \le R_{\mathrm{out}}$. -/)]
theorem linear_interpolation {n M : ℕ} (S : Fin n → X) (f : Fin M → X → X) (Φ : X → E)
    (Λ : Fin M → ℝ)
    (hinv : ∀ j, ∀ c : Fin n → ℝ, ∃ w : E, ‖w‖ ≤ Λ j * Real.sqrt (∑ i, c i ^ 2) ∧
      ∀ i, inner ℝ (w) (Φ (f j (S i))) = c i)
    (cd : Fin M → Fin n → ℝ) {ρ Rout RH : ℝ}
    (hsep : ∀ j l, j ≠ l → ρ ≤ Real.sqrt ((1 / (n : ℝ)) * ∑ i, (cd j i - cd l i) ^ 2))
    (hbdd : ∀ j i, |cd j i| ≤ Rout) (hRout : 0 ≤ Rout)
    (hRH : ∀ j, Λ j * Real.sqrt (∑ i, cd j i ^ 2) ≤ RH) :
    ∃ h : Fin M → (X → ℝ), (∀ j, h j ∈ linearReadouts Φ RH) ∧
      (∀ j i, h j (f j (S i)) = cd j i) ∧
      (∀ j l, j ≠ l → ρ ≤ empNorm S (h j ∘ f j) (h l ∘ f l)) ∧
      (∀ j, empSupNorm S (h j ∘ f j) ≤ Rout) := by
  /-- Set $w_j := R_j u^{(j)}$ and $h_j := \langle w_j, \Phi(\cdot)\rangle$; then
    $h_j(f_j(x_i)) = u^{(j)}_i$ and $\|w_j\| \le \Lambda_j \|u^{(j)}\|_2 \le R_H$. The separation
    and boundedness claims follow by evaluating on the sample. -/
  choose w hw hwc using fun j => hinv j (cd j)
  refine ⟨fun j x => inner ℝ (w j) (Φ x), fun j => ⟨w j, (hw j).trans (hRH j), rfl⟩,
    fun j i => hwc j i, fun j l hjl => ?_, fun j => ?_⟩
  · unfold empNorm
    simp only [Function.comp_apply, hwc, sq_abs]
    exact hsep j l hjl
  · unfold empSupNorm
    refine Real.iSup_le (fun i => ?_) hRout
    simp only [Function.comp_apply, hwc]
    exact hbdd j i

@[blueprint "lem:code-norm-le"
  (statement := /-- If $|u_i| \le R_{\mathrm{out}}$ for all $i \in [n]$ then
    $\|u\|_2 \le \sqrt n\, R_{\mathrm{out}}$. -/)]
theorem sqrt_sum_sq_le_of_abs_le {n : ℕ} (c : Fin n → ℝ) {Rout : ℝ} (hRout : 0 ≤ Rout)
    (hbdd : ∀ i, |c i| ≤ Rout) :
    Real.sqrt (∑ i, c i ^ 2) ≤ Real.sqrt n * Rout := by
  rw [← Real.sqrt_sq hRout, ← Real.sqrt_mul (Nat.cast_nonneg n)]
  apply Real.sqrt_le_sqrt
  calc ∑ i, c i ^ 2 ≤ ∑ _i : Fin n, Rout ^ 2 :=
        Finset.sum_le_sum fun i _ => by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hbdd i) 2
    _ = n * Rout ^ 2 := by simp

@[blueprint "cor:linear-interpolation-bounded"
  (statement := /-- (Bounded codes.) In `prop:linear-interpolation`, for
    $R_{\mathrm{out}}$-bounded codes it suffices to take
    $R_H \ge \sqrt n\, R_{\mathrm{out}} \max_j \Lambda_j$ (with $\Lambda_j \ge 0$), which is
    independent of the number $M$ of maps. -/)]
theorem linear_interpolation_of_bounded {n M : ℕ} (S : Fin n → X) (f : Fin M → X → X) (Φ : X → E)
    (Λ : Fin M → ℝ) (hΛ : ∀ j, 0 ≤ Λ j)
    (hinv : ∀ j, ∀ c : Fin n → ℝ, ∃ w : E, ‖w‖ ≤ Λ j * Real.sqrt (∑ i, c i ^ 2) ∧
      ∀ i, inner ℝ (w) (Φ (f j (S i))) = c i)
    (cd : Fin M → Fin n → ℝ) {ρ Rout RH : ℝ}
    (hsep : ∀ j l, j ≠ l → ρ ≤ Real.sqrt ((1 / (n : ℝ)) * ∑ i, (cd j i - cd l i) ^ 2))
    (hbdd : ∀ j i, |cd j i| ≤ Rout) (hRout : 0 ≤ Rout)
    (hRH : ∀ j, Λ j * Real.sqrt n * Rout ≤ RH) :
    ∃ h : Fin M → (X → ℝ), (∀ j, h j ∈ linearReadouts Φ RH) ∧
      (∀ j i, h j (f j (S i)) = cd j i) ∧
      (∀ j l, j ≠ l → ρ ≤ empNorm S (h j ∘ f j) (h l ∘ f l)) ∧
      (∀ j, empSupNorm S (h j ∘ f j) ≤ Rout) := by
  /-- `lem:code-norm-le` gives $\Lambda_j \|u^{(j)}\|_2 \le \Lambda_j \sqrt n R_{\mathrm{out}}
    \le R_H$; apply `prop:linear-interpolation`. -/
  refine linear_interpolation S f Φ Λ hinv cd hsep hbdd hRout fun j => ?_
  calc Λ j * Real.sqrt (∑ i, cd j i ^ 2) ≤ Λ j * (Real.sqrt n * Rout) :=
        mul_le_mul_of_nonneg_left (sqrt_sum_sq_le_of_abs_le (cd j) hRout (hbdd j)) (hΛ j)
    _ = Λ j * Real.sqrt n * Rout := by ring
    _ ≤ RH := hRH j

@[blueprint "cor:linear-interpolation-realization"
  (statement := /-- (Readout realization from interpolation.) Under the hypotheses of
    `prop:linear-interpolation`, if moreover $\kappa\, d_S(f_j, f_\ell) \le \rho$ for all
    $j \ne \ell$, then the readout-realization assumption holds for $H_{R_H}(\Phi)$ on
    $B_k = \{f_1, \dots, f_M\}$ with constants $\kappa$ and $R_{\mathrm{out}}$. -/)]
theorem readoutRealization_of_linear_interpolation [PseudoMetricSpace X] {n M : ℕ}
    (S : Fin n → X)
    (f : Fin M → X → X) (Φ : X → E) (Λ : Fin M → ℝ)
    (hinv : ∀ j, ∀ c : Fin n → ℝ, ∃ w : E, ‖w‖ ≤ Λ j * Real.sqrt (∑ i, c i ^ 2) ∧
      ∀ i, inner ℝ (w) (Φ (f j (S i))) = c i)
    (cd : Fin M → Fin n → ℝ) {ρ Rout RH κ : ℝ}
    (hsep : ∀ j l, j ≠ l → ρ ≤ Real.sqrt ((1 / (n : ℝ)) * ∑ i, (cd j i - cd l i) ^ 2))
    (hbdd : ∀ j i, |cd j i| ≤ Rout) (hRout : 0 ≤ Rout)
    (hRH : ∀ j, Λ j * Real.sqrt (∑ i, cd j i ^ 2) ≤ RH)
    (hκ : ∀ j l, j ≠ l → κ * empDist S (f j) (f l) ≤ ρ) :
    ReadoutRealization S (linearReadouts Φ RH) (Set.range f) κ Rout := by
  /-- Take the $h_j$ of `prop:linear-interpolation` and set $h_{f_j} := h_j$ (choosing an index
    $j$ for each element of the range). For $f_j \ne f_\ell$ one has $j \ne \ell$, so
    $\kappa\, d_S(f_j, f_\ell) \le \rho \le \|h_j \circ f_j - h_\ell \circ f_\ell\|_S$; for
    $f_j = f_\ell$ the left-hand side vanishes. -/
  obtain ⟨h, hmem, -, hsep', hbdd'⟩ :=
    linear_interpolation S f Φ Λ hinv cd hsep hbdd hRout hRH
  have key : ∀ g : X → X, ∃ hg : X → ℝ, g ∈ Set.range f → ∃ j, f j = g ∧ hg = h j := by
    intro g
    by_cases hg : g ∈ Set.range f
    · obtain ⟨j, rfl⟩ := hg
      exact ⟨h j, fun _ => ⟨j, rfl, rfl⟩⟩
    · exact ⟨fun _ => 0, fun h' => absurd h' hg⟩
  choose hf hhf using key
  refine ⟨hf, fun g hg => ?_, fun g hg g' hg' => ?_, fun g hg => ?_⟩
  · obtain ⟨j, rfl, hj⟩ := hhf g hg
    rw [hj]; exact hmem j
  · obtain ⟨j, rfl, hj⟩ := hhf g hg
    obtain ⟨l, rfl, hl⟩ := hhf g' hg'
    rw [hj, hl]
    by_cases hjl : j = l
    · subst hjl
      simp only [empDist_self, mul_zero]
      exact Real.sqrt_nonneg _
    · exact (hκ j l hjl).trans (hsep' j l hjl)
  · obtain ⟨j, rfl, hj⟩ := hhf g hg
    rw [hj]; exact hbdd' j

/-! ### Gram-matrix (RKHS) criterion -/

@[blueprint "lem:gram-right-inverse"
  (statement := /-- (Right inverse from a well-conditioned Gram matrix.) Let $\varphi_1, \dots,
    \varphi_n \in \mathcal H$ and suppose the Gram matrix $G = (\langle \varphi_i, \varphi_{i'}
    \rangle)_{i,i'}$ satisfies $c^\top G c \ge \lambda_{\min} \|c\|_2^2$ for all $c \in
    \mathbb R^n$, with $\lambda_{\min} > 0$. Then for every $c \in \mathbb R^n$ there is
    $w \in \mathcal H$ with $\langle w, \varphi_i\rangle = c_i$ for all $i$ and
    $\|w\| \le \lambda_{\min}^{-1/2} \|c\|_2$. -/)]
theorem exists_inner_eq_of_gram {n : ℕ} (φ : Fin n → E) {lmin : ℝ} (hl : 0 < lmin)
    (hG : ∀ c : Fin n → ℝ, lmin * ∑ i, c i ^ 2 ≤ ∑ i, ∑ i', c i * c i' * inner ℝ (φ i) (φ i'))
    (c : Fin n → ℝ) :
    ∃ w : E, ‖w‖ ≤ (Real.sqrt lmin)⁻¹ * Real.sqrt (∑ i, c i ^ 2) ∧
      ∀ i, inner ℝ w (φ i) = c i := by
  /-- $G$ is injective (if $Ga = 0$ then $\lambda_{\min}\|a\|^2 \le a^\top G a = 0$), hence
    surjective: pick $a$ with $Ga = c$ and set $w = \sum_i a_i \varphi_i$. Then
    $\langle w, \varphi_i\rangle = (Ga)_i = c_i$ and $p := \|w\|^2 = a^\top G a = a^\top c$.
    From $\lambda_{\min} \|a\|^2 \le p$ and $p^2 \le \|a\|^2 \|c\|^2$ (Cauchy--Schwarz) we get
    $\lambda_{\min} p \le \|c\|^2$, i.e. $\|w\| \le \lambda_{\min}^{-1/2} \|c\|_2$. -/
  classical
  set G : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i i' => inner ℝ (φ i) (φ i') with hGdef
  have hquad : ∀ a b : Fin n → ℝ,
      ∑ i, a i * (G.mulVec b) i = ∑ i, ∑ i', a i * b i' * inner ℝ (φ i) (φ i') := by
    intro a b
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, hGdef, Matrix.of_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => by ring
  have hinj : Function.Injective G.mulVec := by
    intro a b hab
    have h0 : G.mulVec (a - b) = 0 := by rw [Matrix.mulVec_sub, hab, sub_self]
    have h1 := hG (a - b)
    rw [← hquad, h0] at h1
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h1
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ (a - b) i ^ 2 := fun i _ => sq_nonneg _
    have hs := Finset.sum_nonneg hnn
    have hsum : ∑ i, (a - b) i ^ 2 = 0 := le_antisymm (by nlinarith) hs
    rw [Finset.sum_eq_zero_iff_of_nonneg hnn] at hsum
    funext i
    have := hsum i (Finset.mem_univ i)
    rw [pow_eq_zero_iff two_ne_zero, Pi.sub_apply, sub_eq_zero] at this
    exact this
  obtain ⟨a, ha⟩ :=
    (Matrix.mulVec_surjective_iff_isUnit.mpr (Matrix.mulVec_injective_iff_isUnit.mp hinj)) c
  have heval : ∀ i, inner ℝ (∑ i', a i' • φ i') (φ i) = c i := by
    intro i
    have hi := congrFun ha i
    simp only [Matrix.mulVec, dotProduct, hGdef, Matrix.of_apply] at hi
    rw [sum_inner, ← hi]
    simp only [real_inner_smul_left]
    exact Finset.sum_congr rfl fun i' _ => by rw [real_inner_comm, mul_comm]
  refine ⟨∑ i, a i • φ i, ?_, heval⟩
  set p : ℝ := ∑ i, a i * c i with hp
  have hw : ‖∑ i, a i • φ i‖ ^ 2 = p := by
    rw [← real_inner_self_eq_norm_sq, inner_sum]
    simp only [real_inner_smul_right, heval]
    exact hp.symm
  have hp0 : 0 ≤ p := hw ▸ sq_nonneg _
  set A : ℝ := ∑ i, a i ^ 2 with hA
  set C : ℝ := ∑ i, c i ^ 2 with hC
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hp1 : lmin * A ≤ p := by
    have := hG a
    rw [← hquad, ha] at this
    exact this
  have hp2 : p ^ 2 ≤ A * C := Finset.sum_mul_sq_le_sq_mul_sq _ a c
  have hkey : lmin * p ≤ C := by
    rcases hp0.eq_or_lt with hp' | hp'
    · rw [← hp', mul_zero]; exact hC0
    · have h3 : lmin * p * p ≤ C * p := by
        calc lmin * p * p = lmin * p ^ 2 := by ring
          _ ≤ lmin * (A * C) := by gcongr
          _ = (lmin * A) * C := by ring
          _ ≤ p * C := by gcongr
          _ = C * p := by ring
      exact le_of_mul_le_mul_right h3 hp'
  calc ‖∑ i, a i • φ i‖ = Real.sqrt p := by rw [← hw, Real.sqrt_sq (norm_nonneg _)]
    _ ≤ Real.sqrt (C / lmin) := Real.sqrt_le_sqrt ((le_div_iff₀ hl).2 (by linarith))
    _ = (Real.sqrt lmin)⁻¹ * Real.sqrt C := by
        rw [Real.sqrt_div' _ hl.le, div_eq_inv_mul]

@[blueprint "cor:rkhs-readout"
  (statement := /-- \textbf{(RKHS / kernel output layer.)} Let $\Phi : \mathcal X \to \mathcal H$
    be a feature map (e.g. the canonical feature map of a positive definite kernel $K$, so that
    $\langle \Phi(a), \Phi(a')\rangle = K(a, a')$) and fix $f_1, \dots, f_M$ and a sample $S$.
    Suppose that for each $j$ the Gram matrix $G_j = (\langle \Phi(f_j(x_i)), \Phi(f_j(x_{i'}))
    \rangle)_{i,i'}$ satisfies $c^\top G_j c \ge \lambda_{\min,j} \|c\|_2^2$ with
    $\lambda_{\min,j} > 0$. Then `prop:linear-interpolation` applies with
    $\Lambda_j = \lambda_{\min,j}^{-1/2}$: for all codes $u^{(j)}$ with
    $\lambda_{\min,j}^{-1/2} \|u^{(j)}\|_2 \le R_H$, $\rho$-separated and
    $R_{\mathrm{out}}$-bounded, there are $h_j \in H_{R_H}(\Phi)$ with $h_j(f_j(x_i)) =
    u^{(j)}_i$, $\|h_j \circ f_j - h_\ell \circ f_\ell\|_S \ge \rho$ ($j \ne \ell$) and
    $\|h_j \circ f_j\|_{S,\infty} \le R_{\mathrm{out}}$. -/)]
theorem rkhs_readout {n M : ℕ} (S : Fin n → X) (f : Fin M → X → X) (Φ : X → E)
    (lmin : Fin M → ℝ) (hl : ∀ j, 0 < lmin j)
    (hG : ∀ j, ∀ c : Fin n → ℝ, lmin j * ∑ i, c i ^ 2 ≤
      ∑ i, ∑ i', c i * c i' * inner ℝ (Φ (f j (S i))) (Φ (f j (S i'))))
    (cd : Fin M → Fin n → ℝ) {ρ Rout RH : ℝ}
    (hsep : ∀ j l, j ≠ l → ρ ≤ Real.sqrt ((1 / (n : ℝ)) * ∑ i, (cd j i - cd l i) ^ 2))
    (hbdd : ∀ j i, |cd j i| ≤ Rout) (hRout : 0 ≤ Rout)
    (hRH : ∀ j, (Real.sqrt (lmin j))⁻¹ * Real.sqrt (∑ i, cd j i ^ 2) ≤ RH) :
    ∃ h : Fin M → (X → ℝ), (∀ j, h j ∈ linearReadouts Φ RH) ∧
      (∀ j i, h j (f j (S i)) = cd j i) ∧
      (∀ j l, j ≠ l → ρ ≤ empNorm S (h j ∘ f j) (h l ∘ f l)) ∧
      (∀ j, empSupNorm S (h j ∘ f j) ≤ Rout) := by
  /-- `lem:gram-right-inverse` applied to $\varphi_i = \Phi(f_j(x_i))$ gives the right-inverse
    hypothesis of `prop:linear-interpolation` with $\Lambda_j = \lambda_{\min,j}^{-1/2}$. -/
  exact linear_interpolation S f Φ (fun j => (Real.sqrt (lmin j))⁻¹)
    (fun j c => exists_inner_eq_of_gram (fun i => Φ (f j (S i))) (hl j) (hG j) c)
    cd hsep hbdd hRout hRH

@[blueprint "cor:finite-dim-feature"
  (statement := /-- \textbf{(Finite-dimensional feature map.)} Let $\mathcal H = \mathbb R^m$ and
    $\Phi : \mathcal X \to \mathbb R^m$. If for each $j$ the feature matrix
    $\Phi_j = (\Phi(f_j(x_i)))_{i \in [n]} \in \mathbb R^{m \times n}$ has full column rank,
    quantified as $\sigma_{\min}(\Phi_j)^2 = \lambda_{\min}(\Phi_j^\top \Phi_j) \ge
    \lambda_{\min,j} > 0$, i.e. $c^\top \Phi_j^\top \Phi_j c \ge \lambda_{\min,j} \|c\|_2^2$,
    then `prop:linear-interpolation` applies with $\Lambda_j = \lambda_{\min,j}^{-1/2} =
    \sigma_{\min}(\Phi_j)^{-1}$. (This is `cor:rkhs-readout` for
    $\mathcal H = \mathbb R^m$, since $\Phi_j^\top \Phi_j$ is the Gram matrix.) -/)]
theorem finite_dim_feature {m n M : ℕ} (S : Fin n → X) (f : Fin M → X → X)
    (Φ : X → EuclideanSpace ℝ (Fin m)) (lmin : Fin M → ℝ) (hl : ∀ j, 0 < lmin j)
    (hG : ∀ j, ∀ c : Fin n → ℝ, lmin j * ∑ i, c i ^ 2 ≤
      ∑ i, ∑ i', c i * c i' * inner ℝ (Φ (f j (S i))) (Φ (f j (S i'))))
    (cd : Fin M → Fin n → ℝ) {ρ Rout RH : ℝ}
    (hsep : ∀ j l, j ≠ l → ρ ≤ Real.sqrt ((1 / (n : ℝ)) * ∑ i, (cd j i - cd l i) ^ 2))
    (hbdd : ∀ j i, |cd j i| ≤ Rout) (hRout : 0 ≤ Rout)
    (hRH : ∀ j, (Real.sqrt (lmin j))⁻¹ * Real.sqrt (∑ i, cd j i ^ 2) ≤ RH) :
    ∃ h : Fin M → (X → ℝ), (∀ j, h j ∈ linearReadouts Φ RH) ∧
      (∀ j i, h j (f j (S i)) = cd j i) ∧
      (∀ j l, j ≠ l → ρ ≤ empNorm S (h j ∘ f j) (h l ∘ f l)) ∧
      (∀ j, empSupNorm S (h j ∘ f j) ≤ Rout) := by
  /-- Specialization of `cor:rkhs-readout` to $\mathcal H = \mathbb R^m$. -/
  exact rkhs_readout S f Φ lmin hl hG cd hsep hbdd hRout hRH

end LeanDeepgen
