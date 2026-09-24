import Mathlib
import Architect
import LeanDeepgen.Setting.WordBall
import LeanDeepgen.Setting.Metrics
import LeanDeepgen.Setting.Covering
import LeanDeepgen.Growth.Defs

/-!
# Memory-preserving expansion: condition E3 (paper App. F, `cond:e3`)

State space `MemState E = ℕ → E` (the paper's `ℓ_∞(E)`; we use all sequences, since the bounded
sup metric `d(x,y) = sup_j min{1, ‖x_j - y_j‖}` makes sense without a boundedness restriction)
with the bounded sup metric, realised as a `PseudoEMetricSpace` with
`edist x y = ⨆ j, min 1 (edist (x j) (y j))` (values in `[0,1] ⊆ ℝ≥0∞`; using `ℝ≥0∞` avoids all
`BddAbove` bookkeeping for the supremum).

Maps: the reset `r x = 0`, the expander `A x = (λ x_j)_j` and the writers `g_u x = (u, x_0, x_1, …)`
for `u ∈ G`; `F = {r, A} ∪ {g_u : u ∈ G}`.

Words: `memWord lam k u = A ∘ g_{u_{k-1}} ∘ A ∘ ⋯ ∘ A ∘ g_{u_0} ∘ r` for `u : Fin k → E`
(defined by recursion on `k`, peeling off the *last* letter `u (Fin.last k)`, which acts last),
so that `memWord lam k u x = (λ u_{k-1}, λ² u_{k-2}, …, λ^k u_0, 0, 0, …)`, i.e. coordinate
`j < k` holds `λ^(j+1) • u (Fin.rev j)` with `Fin.rev j = k - 1 - j`. This is the paper's
`w_u` with `u_i` (1-based) written as `u (i-1)` (0-based). `memWords G lam k = {w_u : u ∈ G^k}`.

The state space, its metric, the maps `reset`, `expand`, `write`, the generator set `memGen`
and the words `memWord`, `memWords` are defined in `LeanDeepgen.Growth.Defs`.

Main results: `w_u ∈ B(2k+1, F)`, the explicit formula (i), the distance formula (ii),
the product covering/packing bounds (iii), monotonicity to `B(2k+1,F)`, and the two
corollaries (super-exponential and double-exponential growth of `log N(W_k, ε)`).
-/

open scoped NNReal ENNReal
open Metric

open FoML.ToMathlib

namespace LeanDeepgen

section MemState

variable {E : Type*} [NormedAddCommGroup E]

variable [NormedSpace ℝ E]

variable {G : Set E} {lam : ℝ≥0} {k : ℕ}

@[blueprint "lem:e3-w-mem"
  (statement := /-- $w_u \in B(2k+1, F)$ for every $u \in G^k$. -/)]
theorem memWord_mem_wordBall {u : Fin k → E} (hu : ∀ i, u i ∈ G) :
    memWord lam k u ∈ wordBall (memGen G lam) (2 * k + 1) := by
  /-- Induction on $k$: $r \in F \subseteq B(1,F)$, and $A, g_{u_k} \in F$ add two letters. -/
  induction k with
  | zero =>
    have hr : reset ∈ memGen G lam := Set.mem_union_left _ (Set.mem_insert _ _)
    simpa using mem_wordBall_succ_of_mem_of_mem hr (id_mem_wordBall (F := memGen G lam) (k := 0))
  | succ k ih =>
    have hA : expand lam ∈ memGen G lam :=
      Set.mem_union_left _ (Set.mem_insert_of_mem _ rfl)
    have hg : write (u (Fin.last k)) ∈ memGen G lam :=
      Set.mem_union_right _ ⟨u (Fin.last k), hu _, rfl⟩
    have h2 : 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 := by ring
    rw [memWord_succ, h2]
    exact mem_wordBall_succ_of_mem_of_mem hA
      (mem_wordBall_succ_of_mem_of_mem hg (ih fun i => hu _))

@[blueprint "lem:e3-words-subset-wordball"
  (statement := /-- $W_k \subseteq B(2k+1, F)$. -/)]
theorem memWords_subset_wordBall : memWords G lam k ⊆ wordBall (memGen G lam) (2 * k + 1) := by
  rintro _ ⟨u, hu, rfl⟩
  exact memWord_mem_wordBall fun i => hu i (Set.mem_univ _)

@[blueprint "cond:e3-i"
  (statement := /-- \textbf{(E3 (i).)} For every $x \in X$,
    $w_u(x) = (\lambda u_{k-1}, \lambda^2 u_{k-2}, \dots, \lambda^k u_0, 0, 0, \dots)$:
    coordinate $j < k$ of $w_u(x)$ is $\lambda^{j+1} u_{k-1-j}$ and the coordinates $j \ge k$
    vanish. In particular $w_u$ is a constant map. -/)]
theorem memWord_apply (lam : ℝ≥0) (k : ℕ) (u : Fin k → E) (x : MemState E) (j : ℕ) :
    memWord lam k u x j =
      if h : j < k then ((lam : ℝ) ^ (j + 1)) • u (Fin.rev ⟨j, h⟩) else 0 := by
  /-- Induction on $k$. For $k+1$: coordinate $0$ of $A(g_a(y))$ is $\lambda a$ with
    $a = u_k$, and coordinate $j+1$ is $\lambda y_j$ where $y = w_{u|_k}(x)$; apply the induction
    hypothesis to $y$. -/
  induction k generalizing j with
  | zero => simp
  | succ k ih =>
    rw [memWord_succ]
    cases j with
    | zero =>
      simp only [Function.comp_apply, expand_apply, write_apply_zero, Nat.zero_lt_succ,
        dite_true, zero_add, pow_one]
      congr 2
    | succ j =>
      simp only [Function.comp_apply, expand_apply, write_apply_succ, ih, Nat.succ_lt_succ_iff]
      by_cases h : j < k
      · simp only [h, dite_true, smul_smul, Fin.init]
        rw [← pow_succ']
        congr 2
        ext
        simp
      · simp [h]

@[blueprint "lem:e3-word-const"
  (statement := /-- $w_u$ is constant: $w_u(x) = w_u(y)$ for all $x, y$. -/)]
theorem memWord_apply_eq (lam : ℝ≥0) (k : ℕ) (u : Fin k → E) (x y : MemState E) :
    memWord lam k u x = memWord lam k u y := by
  funext j
  rw [memWord_apply, memWord_apply]

@[blueprint "lem:e3-word-injective"
  (statement := /-- For $\lambda \ne 0$ the map $u \mapsto w_u$ is injective on $E^k$. -/)]
theorem memWord_injective (hlam : lam ≠ 0) : Function.Injective (memWord (E := E) lam k) := by
  /-- Coordinate $k-1-i$ of $w_u(0)$ is $\lambda^{k-i} u_i$, and $\lambda^{k-i} \ne 0$. -/
  intro u v huv
  funext i
  have h := congrFun (congrFun huv (fun _ => 0)) (Fin.rev i)
  rw [memWord_apply, memWord_apply, dif_pos (Fin.rev i).isLt, dif_pos (Fin.rev i).isLt] at h
  simp only [Fin.eta, Fin.rev_rev] at h
  have hpow : ((lam : ℝ) ^ ((Fin.rev i : ℕ) + 1)) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast hlam)
  exact smul_right_injective E hpow h

@[blueprint "lem:e3-isup-nat-fin"
  (statement := /-- If $f : \mathbb N \to [0,\infty]$ vanishes on $j \ge k$ then
    $\sup_{j \in \mathbb N} f(j) = \max_{j < k} f(j)$. -/)]
theorem iSup_nat_eq_iSup_fin (f : ℕ → ℝ≥0∞) (hf : ∀ j, k ≤ j → f j = 0) :
    ⨆ j, f j = ⨆ j : Fin k, f j := by
  apply le_antisymm
  · refine iSup_le fun j => ?_
    by_cases h : j < k
    · exact le_iSup (fun i : Fin k => f i) ⟨j, h⟩
    · rw [hf j (not_lt.mp h)]; exact zero_le
  · exact iSup_le fun i => le_iSup f i

@[blueprint "cond:e3-ii"
  (statement := /-- \textbf{(E3 (ii).)} For $u, v \in E^k$,
    $d_\infty(w_u, w_v) = \max_{0 \le j < k} \min\{1, \lambda^{j+1} \|u_{k-1-j} - v_{k-1-j}\|_E\}$
    (the paper's $\max_{1 \le j \le k} \min\{1, \lambda^{k-j+1}\|u_j - v_j\|\}$ after
    reindexing). -/)]
theorem uniformDist_memWord (lam : ℝ≥0) (k : ℕ) (u v : Fin k → E) :
    uniformDist (memWord lam k u) (memWord lam k v) =
      ⨆ j : Fin k, min 1 (((lam ^ ((j : ℕ) + 1) : ℝ≥0) : ℝ≥0∞) *
        edist (u (Fin.rev j)) (v (Fin.rev j))) := by
  /-- Both maps are constant, so $d_\infty(w_u,w_v) = d_X(w_u(0), w_v(0))$; the coordinates
    $j \ge k$ of both vanish and coordinate $j < k$ contributes
    $\min\{1, \|\lambda^{j+1}(u_{k-1-j} - v_{k-1-j})\|\}$. -/
  have hconst : ∀ x, edist (memWord lam k u x) (memWord lam k v x) =
      edist (memWord lam k u (fun _ => 0)) (memWord lam k v (fun _ => 0)) := fun x => by
    rw [memWord_apply_eq lam k u x, memWord_apply_eq lam k v x]
  unfold uniformDist
  simp_rw [hconst, iSup_const, edist_memState]
  rw [iSup_nat_eq_iSup_fin (k := k)]
  · refine iSup_congr fun j => ?_
    rw [memWord_apply, memWord_apply, dif_pos j.isLt, dif_pos j.isLt, edist_smul₀,
      ENNReal.smul_def, smul_eq_mul, nnnorm_pow, NNReal.nnnorm_eq]
  · intro j hj
    rw [memWord_apply, memWord_apply, dif_neg (not_lt.mpr hj), dif_neg (not_lt.mpr hj),
      edist_self]
    simp

@[blueprint "lem:e3-edist-word-unifmaps"
  (statement := /-- The same identity for the extended distance of
    $(\mathcal X^{\mathcal X}, d_\infty)$. -/)]
theorem edist_memWord (lam : ℝ≥0) (k : ℕ) (u v : Fin k → E) :
    edist (toUnifMaps (memWord lam k u)) (toUnifMaps (memWord lam k v)) =
      ⨆ j : Fin k, min 1 (((lam ^ ((j : ℕ) + 1) : ℝ≥0) : ℝ≥0∞) *
        edist (u (Fin.rev j)) (v (Fin.rev j))) :=
  uniformDist_memWord lam k u v

end MemState

/-! ### Product covering and packing bounds (E3 (iii)) -/

section Covering

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {G : Set E} {lam : ℝ≥0} {k : ℕ}

@[blueprint "cond:e3-iii-upper"
  (statement := /-- \textbf{(E3 (iii), upper bound.)} For every $\varepsilon \ge 0$ (and
    $\lambda \ne 0$),
    $$N^{\mathrm{ext}}(W_k, d_\infty, \varepsilon)
      \le \prod_{j=0}^{k-1} N^{\mathrm{ext}}(G, \|\cdot\|_E, \varepsilon/\lambda^{j+1}).$$ -/)]
theorem externalCoveringNumber_memWords_le (hlam : lam ≠ 0) (ε : ℝ≥0) :
    externalCoveringNumber (X := UnifMaps (MemState E)) ε (memWords G lam k) ≤
      ∏ j : Fin k, externalCoveringNumber (ε / lam ^ ((j : ℕ) + 1)) G := by
  /-- Take minimal $\varepsilon/\lambda^{j+1}$-covers $C_j$ of $G$. For $u \in G^k$ choose
    $c_i \in C_{k-1-i}$ with $\|u_i - c_i\| \le \varepsilon/\lambda^{k-i}$; then by (ii)
    $d_\infty(w_u, w_c) \le \max_j \lambda^{j+1} \|u_{k-1-j} - c_{k-1-j}\| \le \varepsilon$.
    So $w(\prod_i C_{k-1-i})$ is an $\varepsilon$-cover of $W_k$ of cardinality
    $\le \prod_j |C_j|$. -/
  choose C hC hCe using fun j : Fin k =>
    exists_isCover_encard_eq_externalCoveringNumber (ε / lam ^ ((j : ℕ) + 1)) G
  have hcover : IsCover (X := UnifMaps (MemState E)) ε (memWords G lam k)
      (memWord lam k '' Set.univ.pi fun i => C (Fin.rev i)) := by
    rintro _ ⟨u, hu, rfl⟩
    choose c hc hcu using fun i : Fin k => hC (Fin.rev i) (hu i (Set.mem_univ _))
    refine ⟨memWord lam k c, ⟨c, fun i _ => hc i, rfl⟩, ?_⟩
    change uniformDist (memWord lam k u) (memWord lam k c) ≤ ε
    rw [uniformDist_memWord]
    refine iSup_le fun j => (min_le_right _ _).trans ?_
    have hpow : lam ^ ((j : ℕ) + 1) ≠ 0 := pow_ne_zero _ hlam
    calc ((lam ^ ((j : ℕ) + 1) : ℝ≥0) : ℝ≥0∞) * edist (u (Fin.rev j)) (c (Fin.rev j))
        ≤ ((lam ^ ((j : ℕ) + 1) : ℝ≥0) : ℝ≥0∞) *
            ((ε / lam ^ ((Fin.rev (Fin.rev j) : ℕ) + 1) : ℝ≥0) : ℝ≥0∞) := by
          gcongr
          exact hcu (Fin.rev j)
      _ = ε := by
          rw [Fin.rev_rev, ← ENNReal.coe_mul, mul_comm, div_mul_cancel₀ _ hpow]
  calc externalCoveringNumber (X := UnifMaps (MemState E)) ε (memWords G lam k)
      ≤ (memWord lam k '' Set.univ.pi fun i => C (Fin.rev i) :
          Set (UnifMaps (MemState E))).encard :=
        hcover.externalCoveringNumber_le_encard
    _ ≤ (Set.univ.pi fun i => C (Fin.rev i)).encard := Set.encard_image_le _ _
    _ = ∏ i : Fin k, (C (Fin.rev i)).encard := Set.encard_pi_eq_prod_encard
    _ = ∏ j : Fin k, (C j).encard := Equiv.prod_comp Fin.revPerm fun j => (C j).encard
    _ = ∏ j : Fin k, externalCoveringNumber (ε / lam ^ ((j : ℕ) + 1)) G :=
        Finset.prod_congr rfl fun j _ => hCe j

@[blueprint "lem:e3-prod-packing-family"
  (statement := /-- (Product packing.) Let $2\varepsilon < 1$, $\lambda \ne 0$, and let
    $P_j \subseteq G$ be $2\varepsilon/\lambda^{j+1}$-separated ($0 \le j < k$). Then
    $\prod_j |P_j| \le M(W_k, d_\infty, 2\varepsilon)$. -/)]
theorem prod_encard_le_packingNumber_memWords (hlam : lam ≠ 0) {ε : ℝ≥0} (hε : 2 * ε < 1)
    (P : Fin k → Set E) (hPG : ∀ j, P j ⊆ G)
    (hP : ∀ j : Fin k, IsSeparated ((2 * ε / lam ^ ((j : ℕ) + 1) : ℝ≥0) : ℝ≥0∞) (P j)) :
    ∏ j : Fin k, (P j).encard ≤
      packingNumber (X := UnifMaps (MemState E)) (2 * ε) (memWords G lam k) := by
  /-- The set $w(\prod_i P_{k-1-i}) \subseteq W_k$ is $2\varepsilon$-separated: if $u \ne v$
    then $u_i \ne v_i$ for some $i$, and with $j = k-1-i$ the $j$-th term of (ii) is
    $\min\{1, \lambda^{j+1}\|u_i - v_i\|\} > \min\{1, 2\varepsilon\} = 2\varepsilon$.
    Since $w$ is injective its cardinality is $\prod_i |P_{k-1-i}| = \prod_j |P_j|$. -/
  set D := Set.univ.pi fun i : Fin k => P (Fin.rev i) with hD
  have hsub : (memWord lam k '' D : Set (UnifMaps (MemState E))) ⊆ memWords G lam k := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨u, fun i _ => hPG _ (hu i (Set.mem_univ _)), rfl⟩
  have hsep : IsSeparated ((2 * ε : ℝ≥0) : ℝ≥0∞)
      (memWord lam k '' D : Set (UnifMaps (MemState E))) := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ hne
    have huv : u ≠ v := fun h => hne (by rw [h])
    obtain ⟨i, hi⟩ : ∃ i, u i ≠ v i := by
      by_contra h
      push Not at h
      exact huv (funext h)
    have hsepi := hP (Fin.rev i) (hu i (Set.mem_univ _)) (hv i (Set.mem_univ _)) hi
    change ((2 * ε : ℝ≥0) : ℝ≥0∞) < uniformDist (memWord lam k u) (memWord lam k v)
    rw [uniformDist_memWord]
    refine lt_of_lt_of_le ?_ (le_iSup (fun j : Fin k => min 1
      (((lam ^ ((j : ℕ) + 1) : ℝ≥0) : ℝ≥0∞) * edist (u (Fin.rev j)) (v (Fin.rev j))))
      (Fin.rev i))
    rw [Fin.rev_rev]
    refine lt_min (by exact_mod_cast hε) ?_
    have hpow : lam ^ ((Fin.rev i : ℕ) + 1) ≠ 0 := pow_ne_zero _ hlam
    calc ((2 * ε : ℝ≥0) : ℝ≥0∞)
        = ((lam ^ ((Fin.rev i : ℕ) + 1) : ℝ≥0) : ℝ≥0∞) *
            ((2 * ε / lam ^ ((Fin.rev i : ℕ) + 1) : ℝ≥0) : ℝ≥0∞) := by
          rw [← ENNReal.coe_mul, ← mul_div_assoc, mul_div_cancel_left₀ _ hpow]
      _ < ((lam ^ ((Fin.rev i : ℕ) + 1) : ℝ≥0) : ℝ≥0∞) * edist (u i) (v i) :=
          ENNReal.mul_lt_mul_right (by exact_mod_cast hpow) ENNReal.coe_ne_top hsepi
  have hinj : Set.InjOn (memWord lam k) D := (memWord_injective hlam).injOn
  calc ∏ j : Fin k, (P j).encard
      = ∏ i : Fin k, (P (Fin.rev i)).encard :=
        (Equiv.prod_comp Fin.revPerm fun j => (P j).encard).symm
    _ = D.encard := Set.encard_pi_eq_prod_encard.symm
    _ = (memWord lam k '' D : Set (UnifMaps (MemState E))).encard := hinj.encard_image.symm
    _ ≤ packingNumber (X := UnifMaps (MemState E)) (2 * ε) (memWords G lam k) :=
        hsep.encard_le_packingNumber hsub

@[blueprint "lem:enat-prod-isup"
  (statement := /-- In $\mathbb N \cup \{\infty\}$, a finite product of suprema over nonempty
    index types is the supremum of the products:
    $\prod_{i \in s} \sup_{a \in A_i} g_i(a)
    = \sup_{x \in \prod_i A_i} \prod_{i \in s} g_i(x_i)$. -/)]
theorem ENat.prod_iSup_eq_iSup_prod {ι : Type*} {α : ι → Type*} [∀ i, Nonempty (α i)]
    (s : Finset ι) (g : ∀ i, α i → ℕ∞) :
    ∏ i ∈ s, ⨆ a, g i a = ⨆ x : (∀ i, α i), ∏ i ∈ s, g i (x i) := by
  /-- Induction on $s$, distributing multiplication over suprema
    (`ENat.mul\_iSup`, `ENat.iSup\_mul`) and identifying pairs $(a, x)$ with the update
    $x[i := a]$. -/
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, ih, ENat.iSup_mul]
    simp_rw [ENat.mul_iSup]
    apply le_antisymm
    · refine iSup_le fun a => iSup_le fun x => ?_
      refine le_iSup_of_le (Function.update x i a) ?_
      rw [Finset.prod_insert hi, Function.update_self]
      refine le_of_eq (congrArg _ ?_)
      exact Finset.prod_congr rfl fun j hj => by
        rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)]
    · refine iSup_le fun x => ?_
      rw [Finset.prod_insert hi]
      exact le_iSup₂_of_le (x i) x le_rfl

@[blueprint "cond:e3-iii-lower"
  (statement := /-- \textbf{(E3 (iii), lower bound.)} For every $0 \le \varepsilon < 1/2$ (and
    $\lambda \ne 0$),
    $$\prod_{j=0}^{k-1} M(G, \|\cdot\|_E, 2\varepsilon/\lambda^{j+1})
      \le N^{\mathrm{ext}}(W_k, d_\infty, \varepsilon).$$ -/)]
theorem prod_packingNumber_le_externalCoveringNumber_memWords (hlam : lam ≠ 0) {ε : ℝ≥0}
    (hε : ε < 1 / 2) :
    ∏ j : Fin k, packingNumber (2 * ε / lam ^ ((j : ℕ) + 1)) G ≤
      externalCoveringNumber (X := UnifMaps (MemState E)) ε (memWords G lam k) := by
  /-- Each packing number is a supremum over separated subsets of $G$; by
    `lem:enat-prod-isup` the product is the supremum over families $(P_j)_j$ of
    $\prod_j |P_j|$, which is bounded by $M(W_k, 2\varepsilon) \le N^{\mathrm{ext}}(W_k,
    \varepsilon)$ by `lem:e3-prod-packing-family` and `lem:packing-covering`. -/
  have h2ε : 2 * ε < 1 := by
    calc 2 * ε < 2 * (1 / 2) := by gcongr
      _ = 1 := by norm_num
  let α : Fin k → Type _ := fun j =>
    {P : Set E // P ⊆ G ∧ IsSeparated ((2 * ε / lam ^ ((j : ℕ) + 1) : ℝ≥0) : ℝ≥0∞) P}
  haveI : ∀ j, Nonempty (α j) := fun j => ⟨⟨∅, Set.empty_subset _, IsSeparated.empty⟩⟩
  have hpk : ∀ j : Fin k, packingNumber (2 * ε / lam ^ ((j : ℕ) + 1)) G =
      ⨆ P : α j, (P : Set E).encard := by
    intro j
    simp_rw [packingNumber, α, iSup_subtype, iSup_and]
  simp_rw [hpk]
  rw [ENat.prod_iSup_eq_iSup_prod]
  refine iSup_le fun x => ?_
  refine (prod_encard_le_packingNumber_memWords hlam h2ε (fun j => (x j).1)
    (fun j => (x j).2.1) (fun j => (x j).2.2)).trans ?_
  exact packingNumber_two_mul_le_externalCoveringNumber ε _

@[blueprint "lem:e3-covering-le-wordball"
  (statement := /-- $N^{\mathrm{ext}}(W_k, d_\infty, \varepsilon) \le
    N^{\mathrm{ext}}(B(2k+1,F), d_\infty, \varepsilon)$ (monotonicity of the external covering
    number under $W_k \subseteq B(2k+1,F)$). -/)]
theorem externalCoveringNumber_memWords_le_wordBall (ε : ℝ≥0) :
    externalCoveringNumber (X := UnifMaps (MemState E)) ε (memWords G lam k) ≤
      externalCoveringNumber (X := UnifMaps (MemState E)) ε
        (wordBall (memGen G lam) (2 * k + 1)) :=
  externalCoveringNumber_mono_set memWords_subset_wordBall

@[blueprint "cond:e3"
  (statement := /-- \textbf{(E3: memory-preserving expansion grows super- or double-exponentially.)}
    Let $E$ be a normed space, $G \subseteq E$, $\lambda > 1$, $X = E^{\mathbb N}$ with the
    bounded sup metric, $F = \{r, A\} \cup \{g_u : u \in G\}$ and $W_k = \{w_u : u \in G^k\}
    \subseteq B(2k+1, F)$. Then (i) each $w_u$ is the constant map with value
    $(\lambda u_{k-1}, \dots, \lambda^k u_0, 0, \dots)$ (`cond:e3-i`), (ii)
    $d_\infty(w_u, w_v) = \max_{j<k} \min\{1, \lambda^{j+1}\|u_{k-1-j} - v_{k-1-j}\|\}$
    (`cond:e3-ii`), and (iii) for every $0 < \varepsilon < 1/2$,
    $$\prod_{j<k} M\Bigl(G, \tfrac{2\varepsilon}{\lambda^{j+1}}\Bigr)
      \le N^{\mathrm{ext}}(W_k, d_\infty, \varepsilon)
      \le \prod_{j<k} N^{\mathrm{ext}}\Bigl(G, \tfrac{\varepsilon}{\lambda^{j+1}}\Bigr).$$
    Consequently $N^{\mathrm{ext}}(B(2k+1,F), d_\infty, \varepsilon) \ge
    N^{\mathrm{ext}}(W_k, d_\infty, \varepsilon)$. -/)]
theorem cond_e3 (hlam : 1 < lam) {ε : ℝ≥0} (_hε : 0 < ε) (hε1 : ε < 1 / 2) :
    (∏ j : Fin k, packingNumber (2 * ε / lam ^ ((j : ℕ) + 1)) G ≤
        externalCoveringNumber (X := UnifMaps (MemState E)) ε (memWords G lam k) ∧
      externalCoveringNumber (X := UnifMaps (MemState E)) ε (memWords G lam k) ≤
        ∏ j : Fin k, externalCoveringNumber (ε / lam ^ ((j : ℕ) + 1)) G) ∧
    externalCoveringNumber (X := UnifMaps (MemState E)) ε (memWords G lam k) ≤
      externalCoveringNumber (X := UnifMaps (MemState E)) ε
        (wordBall (memGen G lam) (2 * k + 1)) :=
  have hlam0 : lam ≠ 0 := (zero_lt_one.trans hlam).ne'
  ⟨⟨prod_packingNumber_le_externalCoveringNumber_memWords hlam0 hε1,
    externalCoveringNumber_memWords_le hlam0 ε⟩,
    externalCoveringNumber_memWords_le_wordBall ε⟩

end Covering

/-! ### Metric entropy: the sum forms of (iii) -/

section Entropy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {G : Set E} {lam : ℝ≥0} {k : ℕ}

@[blueprint "lem:e3-log-prod"
  (statement := /-- For finite nonzero $n_i \in \mathbb N \cup \{\infty\}$,
    $\log \prod_i n_i = \sum_i \log n_i$ (with the coercion to $[0,\infty]$ and `toReal`). -/)]
theorem log_toReal_prod {ι : Type*} (s : Finset ι) (n : ι → ℕ∞) (hn : ∀ i ∈ s, n i ≠ ⊤)
    (h0 : ∀ i ∈ s, n i ≠ 0) :
    Real.log ((∏ i ∈ s, n i : ℕ∞) : ℝ≥0∞).toReal = ∑ i ∈ s, Real.log (n i : ℝ≥0∞).toReal := by
  have h : ((∏ i ∈ s, n i : ℕ∞) : ℝ≥0∞) = ∏ i ∈ s, (n i : ℝ≥0∞) :=
    map_prod ENat.toENNRealRingHom n s
  rw [h, ENNReal.toReal_prod, Real.log_prod]
  intro i hi
  exact ENNReal.toReal_ne_zero.mpr ⟨by simpa using h0 i hi, by simpa using hn i hi⟩

@[blueprint "lem:e3-log-covering-le-sum"
  (statement := /-- If $G \ne \emptyset$ and all $N^{\mathrm{ext}}(G, \varepsilon/\lambda^{j+1})$
    are finite, then
    $\log N^{\mathrm{ext}}(W_k, \varepsilon) \le \sum_{j<k} \log N^{\mathrm{ext}}(G,
    \varepsilon/\lambda^{j+1})$. -/)]
theorem log_externalCoveringNumber_memWords_le (hlam : lam ≠ 0) (hG : G.Nonempty) {ε : ℝ≥0}
    (hfin : ∀ j : Fin k, externalCoveringNumber (ε / lam ^ ((j : ℕ) + 1)) G ≠ ⊤) :
    Real.log (externalCoveringNumber (X := UnifMaps (MemState E)) ε (memWords G lam k) :
        ℝ≥0∞).toReal ≤
      ∑ j : Fin k, Real.log (externalCoveringNumber (ε / lam ^ ((j : ℕ) + 1)) G : ℝ≥0∞).toReal := by
  /-- Take logarithms in `cond:e3-iii-upper`; all quantities are finite and positive since $G$
    (hence $W_k$) is nonempty. -/
  have hne : ∀ j : Fin k, externalCoveringNumber (ε / lam ^ ((j : ℕ) + 1)) G ≠ 0 := fun j =>
    (externalCoveringNumber_pos_iff.mpr hG).ne'
  have hprod : (∏ j : Fin k, externalCoveringNumber (ε / lam ^ ((j : ℕ) + 1)) G) ≠ ⊤ :=
    ENat.prod_ne_top fun j _ => hfin j
  have hW : (memWords G lam k : Set (UnifMaps (MemState E))).Nonempty :=
    ⟨memWord lam k fun _ => hG.some, ⟨fun _ => hG.some, fun _ _ => hG.some_mem, rfl⟩⟩
  have hNtop : externalCoveringNumber (X := UnifMaps (MemState E)) ε (memWords G lam k) ≠ ⊤ :=
    ne_top_of_le_ne_top hprod (externalCoveringNumber_memWords_le hlam ε)
  have hNpos : 0 < (externalCoveringNumber (X := UnifMaps (MemState E)) ε (memWords G lam k) :
      ℝ≥0∞).toReal := by
    apply ENNReal.toReal_pos
    · simpa using (externalCoveringNumber_pos_iff (X := UnifMaps (MemState E)) (ε := ε)
        (A := memWords G lam k) |>.mpr hW).ne'
    · simpa using hNtop
  rw [← log_toReal_prod _ _ (fun j _ => hfin j) (fun j _ => hne j)]
  apply Real.log_le_log hNpos
  apply ENNReal.toReal_mono (by simpa using hprod)
  exact ENat.toENNReal_mono (externalCoveringNumber_memWords_le hlam ε)

@[blueprint "lem:e3-sum-log-packing-le"
  (statement := /-- If $G \ne \emptyset$, $\varepsilon < 1/2$, all
    $M(G, 2\varepsilon/\lambda^{j+1})$ and $N^{\mathrm{ext}}(W_k, \varepsilon)$ are finite, then
    $\sum_{j<k} \log M(G, 2\varepsilon/\lambda^{j+1}) \le
    \log N^{\mathrm{ext}}(W_k, \varepsilon)$. -/)]
theorem sum_log_packingNumber_le_log_externalCoveringNumber_memWords (hlam : lam ≠ 0)
    (hG : G.Nonempty) {ε : ℝ≥0} (hε : ε < 1 / 2)
    (hfin : ∀ j : Fin k, packingNumber (2 * ε / lam ^ ((j : ℕ) + 1)) G ≠ ⊤)
    (hNfin : externalCoveringNumber (X := UnifMaps (MemState E)) ε (memWords G lam k) ≠ ⊤) :
    ∑ j : Fin k, Real.log (packingNumber (2 * ε / lam ^ ((j : ℕ) + 1)) G : ℝ≥0∞).toReal ≤
      Real.log (externalCoveringNumber (X := UnifMaps (MemState E)) ε (memWords G lam k) :
        ℝ≥0∞).toReal := by
  /-- Take logarithms in `cond:e3-iii-lower`. -/
  have hne : ∀ j : Fin k, packingNumber (2 * ε / lam ^ ((j : ℕ) + 1)) G ≠ 0 := fun j =>
    (packingNumber_pos_iff.mpr hG).ne'
  rw [← log_toReal_prod _ _ (fun j _ => hfin j) (fun j _ => hne j)]
  apply Real.log_le_log
  · apply ENNReal.toReal_pos
    · simpa using Finset.prod_ne_zero_iff.mpr fun j _ => hne j
    · simpa using ENat.prod_ne_top fun j _ => hfin j
  · apply ENNReal.toReal_mono (by simpa using hNfin)
    exact ENat.toENNReal_mono
      (prod_packingNumber_le_externalCoveringNumber_memWords hlam hε)

@[blueprint "lem:e3-sum-log-radius"
  (statement := /-- $\sum_{j<k} \log\bigl(\lambda^{j+1}/a\bigr)
    = \frac{k(k+1)}{2}\log\lambda - k \log a$ for $a, \lambda > 0$. -/)]
theorem sum_log_one_div_radius {lam a : ℝ} (hlam : 0 < lam) (ha : 0 < a) (k : ℕ) :
    ∑ j : Fin k, Real.log (1 / (a / lam ^ ((j : ℕ) + 1))) =
      ((k : ℝ) * (k + 1) / 2) * Real.log lam - k * Real.log a := by
  /-- Induction on $k$ using $\log(\lambda^{j+1}/a) = (j+1)\log\lambda - \log a$. -/
  rw [Fin.sum_univ_eq_sum_range (fun j => Real.log (1 / (a / lam ^ (j + 1)))) k]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, one_div_div, Real.log_div (pow_ne_zero _ hlam.ne') ha.ne',
      Real.log_pow]
    push_cast
    ring

@[blueprint "lem:e3-radius-lt"
  (statement := /-- If $0 \le a < \lambda\delta_0$ and $\lambda > 1$ then
    $a/\lambda^{j+1} < \delta_0$ for every $j$. -/)]
theorem div_pow_lt_of_lt_mul {lam a δ₀ : ℝ} (hlam : 1 < lam) (ha : 0 ≤ a) (h : a < lam * δ₀)
    (j : ℕ) : a / lam ^ (j + 1) < δ₀ := by
  have hlam0 : 0 < lam := zero_lt_one.trans hlam
  calc a / lam ^ (j + 1) ≤ a / lam :=
        div_le_div_of_nonneg_left ha hlam0 (le_self_pow₀ hlam.le (Nat.succ_ne_zero j))
    _ < δ₀ := by rw [div_lt_iff₀ hlam0]; linarith

omit [NormedSpace ℝ E] in
@[blueprint "lem:e3-nonempty-of-entropy"
  (statement := /-- If $c_- \log(1/\delta) \le \log M(G, \delta)$ for all small $\delta > 0$
    with $c_- > 0$, then $G \ne \emptyset$. -/)]
theorem nonempty_of_log_packing_lower {cLow δ₀ : ℝ} (hcLow : 0 < cLow) (hδ₀ : 0 < δ₀)
    (hlow : ∀ δ : ℝ≥0, 0 < δ → (δ : ℝ) < δ₀ →
      cLow * Real.log (1 / (δ : ℝ)) ≤ Real.log (packingNumber δ G : ℝ≥0∞).toReal) :
    G.Nonempty := by
  /-- Otherwise $M(G, \delta) = 0$ and $\log 0 = 0 < c_- \log(1/\delta)$ for
    $\delta = \min\{\delta_0/2, 1/2\}$. -/
  by_contra hemp
  rw [Set.not_nonempty_iff_eq_empty] at hemp
  have hm : (0 : ℝ) < min (δ₀ / 2) (1 / 2) := lt_min (by positivity) (by norm_num)
  set δ : ℝ≥0 := Real.toNNReal (min (δ₀ / 2) (1 / 2)) with hδ
  have hδcoe : (δ : ℝ) = min (δ₀ / 2) (1 / 2) := Real.coe_toNNReal _ hm.le
  have h := hlow δ (by rw [← NNReal.coe_pos, hδcoe]; exact hm)
    (by rw [hδcoe]; exact (min_le_left _ _).trans_lt (by linarith))
  rw [hemp, packingNumber_empty] at h
  simp only [ENat.toENNReal_zero, ENNReal.toReal_zero, Real.log_zero] at h
  have hpos : 0 < cLow * Real.log (1 / (δ : ℝ)) := by
    apply mul_pos hcLow
    apply Real.log_pos
    rw [hδcoe]
    exact one_lt_one_div hm ((min_le_right _ _).trans_lt (by norm_num))
  linarith

@[blueprint "lem:e3-log-memwords-le-sum"
  (statement := /-- (Upper bound in sum form.) Suppose $N^{\mathrm{ext}}(G,\delta) < \infty$
    for all $\delta > 0$, $G \ne \emptyset$, and $\log N^{\mathrm{ext}}(G, \delta) \le
    \varphi(\delta)$ for $0 < \delta < \delta_0$. If $0 < \varepsilon < \lambda\delta_0$ then
    $\log N^{\mathrm{ext}}(W_k, \varepsilon) \le \sum_{j<k} \varphi(\varepsilon/\lambda^{j+1})$
    for every $k$. -/)]
theorem log_externalCoveringNumber_memWords_le_sum (hlam : 1 < lam)
    (hfin : ∀ δ : ℝ≥0, 0 < δ → externalCoveringNumber δ G ≠ ⊤) (hG : G.Nonempty)
    {δ₀ : ℝ} {φ : ℝ → ℝ}
    (hup : ∀ δ : ℝ≥0, 0 < δ → (δ : ℝ) < δ₀ →
      Real.log (externalCoveringNumber δ G : ℝ≥0∞).toReal ≤ φ δ)
    {ε : ℝ≥0} (hε : 0 < ε) (hεδ : (ε : ℝ) < lam * δ₀) (k : ℕ) :
    Real.log (externalCoveringNumber (X := UnifMaps (MemState E)) ε (memWords G lam k) :
        ℝ≥0∞).toReal ≤ ∑ j : Fin k, φ ((ε : ℝ) / (lam : ℝ) ^ ((j : ℕ) + 1)) := by
  /-- All radii $\varepsilon/\lambda^{j+1} \le \varepsilon/\lambda < \delta_0$, so
    `lem:e3-log-covering-le-sum` and the hypothesis apply termwise. -/
  have hlam0 : lam ≠ 0 := (zero_lt_one.trans hlam).ne'
  have hlamR : (1 : ℝ) < lam := by exact_mod_cast hlam
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  have hcoe : ∀ j : ℕ, ((ε / lam ^ (j + 1) : ℝ≥0) : ℝ) = (ε : ℝ) / (lam : ℝ) ^ (j + 1) :=
    fun j => by rw [NNReal.coe_div, NNReal.coe_pow]
  have hrad : ∀ j : ℕ, 0 < ε / lam ^ (j + 1) ∧ ((ε / lam ^ (j + 1) : ℝ≥0) : ℝ) < δ₀ :=
    fun j => ⟨by positivity, by rw [hcoe]; exact div_pow_lt_of_lt_mul hlamR hεR.le hεδ j⟩
  refine (log_externalCoveringNumber_memWords_le hlam0 hG fun j =>
    hfin _ (hrad j).1).trans ?_
  refine Finset.sum_le_sum fun j _ => ?_
  rw [← hcoe]
  exact hup _ (hrad j).1 (hrad j).2

@[blueprint "lem:e3-memwords-covering-ne-top"
  (statement := /-- If $N^{\mathrm{ext}}(G,\delta) < \infty$ for all $\delta > 0$ then
    $N^{\mathrm{ext}}(W_k, \varepsilon) < \infty$ for all $\varepsilon > 0$. -/)]
theorem externalCoveringNumber_memWords_ne_top (hlam : 1 < lam)
    (hfin : ∀ δ : ℝ≥0, 0 < δ → externalCoveringNumber δ G ≠ ⊤) {ε : ℝ≥0} (hε : 0 < ε) :
    externalCoveringNumber (X := UnifMaps (MemState E)) ε (memWords G lam k) ≠ ⊤ :=
  ne_top_of_le_ne_top (ENat.prod_ne_top fun (j : Fin k) _ => hfin _ (by positivity))
    (externalCoveringNumber_memWords_le (zero_lt_one.trans hlam).ne' ε)

@[blueprint "lem:e3-sum-le-log-memwords"
  (statement := /-- (Lower bound in sum form.) Suppose $N^{\mathrm{ext}}(G,\delta) < \infty$
    for all $\delta > 0$, $G \ne \emptyset$, and $\varphi(\delta) \le \log M(G, \delta)$ for
    $0 < \delta < \delta_0$. If $0 < \varepsilon < 1/2$ and $2\varepsilon < \lambda\delta_0$ then
    $\sum_{j<k} \varphi(2\varepsilon/\lambda^{j+1}) \le \log N^{\mathrm{ext}}(W_k, \varepsilon)$
    for every $k$. -/)]
theorem sum_le_log_externalCoveringNumber_memWords (hlam : 1 < lam)
    (hfin : ∀ δ : ℝ≥0, 0 < δ → externalCoveringNumber δ G ≠ ⊤) (hG : G.Nonempty)
    {δ₀ : ℝ} {φ : ℝ → ℝ}
    (hlow : ∀ δ : ℝ≥0, 0 < δ → (δ : ℝ) < δ₀ →
      φ δ ≤ Real.log (packingNumber δ G : ℝ≥0∞).toReal)
    {ε : ℝ≥0} (hε : 0 < ε) (hε1 : ε < 1 / 2) (hεδ : 2 * (ε : ℝ) < lam * δ₀) (k : ℕ) :
    ∑ j : Fin k, φ (2 * (ε : ℝ) / (lam : ℝ) ^ ((j : ℕ) + 1)) ≤
      Real.log (externalCoveringNumber (X := UnifMaps (MemState E)) ε (memWords G lam k) :
        ℝ≥0∞).toReal := by
  /-- All radii $2\varepsilon/\lambda^{j+1} \le 2\varepsilon/\lambda < \delta_0$; the packing
    numbers are finite since $M(G, 2\delta) \le N^{\mathrm{ext}}(G, \delta)$; apply
    `lem:e3-sum-log-packing-le` and the hypothesis termwise. -/
  have hlam0 : lam ≠ 0 := (zero_lt_one.trans hlam).ne'
  have hlamR : (1 : ℝ) < lam := by exact_mod_cast hlam
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  have hcoe2 : ∀ j : ℕ, ((2 * ε / lam ^ (j + 1) : ℝ≥0) : ℝ) =
      2 * (ε : ℝ) / (lam : ℝ) ^ (j + 1) :=
    fun j => by rw [NNReal.coe_div, NNReal.coe_pow, NNReal.coe_mul, NNReal.coe_ofNat]
  have hrad : ∀ j : ℕ, 0 < 2 * ε / lam ^ (j + 1) ∧
      ((2 * ε / lam ^ (j + 1) : ℝ≥0) : ℝ) < δ₀ :=
    fun j => ⟨by positivity, by
      rw [hcoe2]; exact div_pow_lt_of_lt_mul hlamR (by positivity) hεδ j⟩
  refine le_trans ?_ (sum_log_packingNumber_le_log_externalCoveringNumber_memWords hlam0 hG hε1
    (fun j => ?_) (externalCoveringNumber_memWords_ne_top hlam hfin hε))
  · refine Finset.sum_le_sum fun j _ => ?_
    rw [← hcoe2]
    exact hlow _ (hrad j).1 (hrad j).2
  · refine ne_top_of_le_ne_top (hfin (ε / lam ^ ((j : ℕ) + 1)) (by positivity)) ?_
    rw [mul_div_assoc]
    exact packingNumber_two_mul_le_externalCoveringNumber _ _

@[blueprint "cor:superexp"
  (statement := /-- \textbf{(Super-exponential regime.)} Assume there are $c_-, c_+, \delta_0 > 0$
    with $c_- \log(1/\delta) \le \log M(G, \delta)$ and
    $\log N^{\mathrm{ext}}(G, \delta) \le c_+ \log(1/\delta)$ for all $0 < \delta < \delta_0$,
    and that $N^{\mathrm{ext}}(G, \delta) < \infty$ for all $\delta > 0$ (automatic for compact
    $G$). Then for every fixed $\varepsilon$ with $0 < \varepsilon < 1/2$ and
    $\varepsilon < \lambda\delta_0/2$ there are $C_1, C_2 > 0$ and $k_0$ such that
    $C_1 k^2 \le \log N^{\mathrm{ext}}(W_k, d_\infty, \varepsilon) \le C_2 k^2$ for all
    $k \ge k_0$. (The smallness condition $\varepsilon < \lambda\delta_0/2$ makes every radius
    $2\varepsilon/\lambda^{j+1} \le 2\varepsilon/\lambda$ fall below $\delta_0$; it cannot be
    replaced by "large $k$" since the $j = 0$ radius does not shrink with $k$.) -/)]
theorem cor_superexp (hlam : 1 < lam)
    (hfin : ∀ δ : ℝ≥0, 0 < δ → externalCoveringNumber δ G ≠ ⊤)
    {cLow cUp δ₀ : ℝ} (hcLow : 0 < cLow) (hcUp : 0 < cUp) (hδ₀ : 0 < δ₀)
    (hlow : ∀ δ : ℝ≥0, 0 < δ → (δ : ℝ) < δ₀ →
      cLow * Real.log (1 / (δ : ℝ)) ≤ Real.log (packingNumber δ G : ℝ≥0∞).toReal)
    (hup : ∀ δ : ℝ≥0, 0 < δ → (δ : ℝ) < δ₀ →
      Real.log (externalCoveringNumber δ G : ℝ≥0∞).toReal ≤ cUp * Real.log (1 / (δ : ℝ)))
    {ε : ℝ≥0} (hε : 0 < ε) (hε1 : ε < 1 / 2) (hεδ : (ε : ℝ) < lam * δ₀ / 2) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      C₁ * (k : ℝ) ^ 2 ≤
        Real.log (externalCoveringNumber (X := UnifMaps (MemState E)) ε (memWords G lam k) :
          ℝ≥0∞).toReal ∧
      Real.log (externalCoveringNumber (X := UnifMaps (MemState E)) ε (memWords G lam k) :
          ℝ≥0∞).toReal ≤ C₂ * (k : ℝ) ^ 2 := by
  /-- By the sum forms of (iii) and the entropy hypotheses,
    $$c_- \sum_{j<k} \log\frac{\lambda^{j+1}}{2\varepsilon}
      \le \log N^{\mathrm{ext}}(W_k, \varepsilon)
      \le c_+ \sum_{j<k} \log\frac{\lambda^{j+1}}{\varepsilon},$$
    and $\sum_{j<k} \log(\lambda^{j+1}/a) = \frac{k(k+1)}{2}\log\lambda + k\log(1/a)$.
    For $k \ge 1$ and $a \le 1$ this is between $\frac{\log\lambda}{2} k^2$ and
    $(\log\lambda + \log(1/a)) k^2$; take $C_1 = c_- \log\lambda / 2$,
    $C_2 = c_+(\log\lambda - \log\varepsilon)$, $k_0 = 1$. -/
  have hlamR : (1 : ℝ) < lam := by exact_mod_cast hlam
  have hlamR0 : (0 : ℝ) < lam := zero_lt_one.trans hlamR
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  have hε1R : (ε : ℝ) < 1 / 2 := by exact_mod_cast hε1
  have hG : G.Nonempty := nonempty_of_log_packing_lower hcLow hδ₀ hlow
  have hlog_lam : 0 < Real.log lam := Real.log_pos hlamR
  have hlog_ε : Real.log ε < 0 := Real.log_neg hεR (by linarith)
  have hlog_2ε : Real.log (2 * ε) < 0 := Real.log_neg (by positivity) (by linarith)
  refine ⟨cLow * Real.log lam / 2, cUp * (Real.log lam - Real.log ε), by positivity,
    mul_pos hcUp (by linarith), 1, fun k hk => ?_⟩
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := by linarith
  have hkk : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hk2 : (k : ℝ) * (k + 1) / 2 ≤ (k : ℝ) ^ 2 := by nlinarith
  have hup' := log_externalCoveringNumber_memWords_le_sum hlam hfin hG
    (φ := fun δ => cUp * Real.log (1 / δ)) hup hε (by linarith) k
  have hlow' := sum_le_log_externalCoveringNumber_memWords hlam hfin hG
    (φ := fun δ => cLow * Real.log (1 / δ)) hlow hε hε1 (by linarith) k
  simp only [← Finset.mul_sum] at hup' hlow'
  rw [sum_log_one_div_radius hlamR0 hεR] at hup'
  rw [sum_log_one_div_radius hlamR0 (by positivity)] at hlow'
  constructor
  · refine le_trans ?_ hlow'
    have h1 : 0 ≤ cLow * Real.log lam * k := by positivity
    have h2 : 0 ≤ cLow * k * (-Real.log (2 * ε)) := by
      apply mul_nonneg (by positivity); linarith
    nlinarith
  · refine hup'.trans ?_
    have h1 : 0 ≤ cUp * Real.log lam * ((k : ℝ) ^ 2 - k * (k + 1) / 2) := by
      apply mul_nonneg (by positivity); linarith
    have h2 : 0 ≤ cUp * (-Real.log ε) * ((k : ℝ) ^ 2 - k) := by
      apply mul_nonneg (mul_nonneg hcUp.le (by linarith)); linarith
    nlinarith

@[blueprint "lem:e3-sum-rpow-radius"
  (statement := /-- $\sum_{j<k} (a/\lambda^{j+1})^{-p} = a^{-p} \sum_{j<k} (\lambda^p)^{j+1}$
    for $a, \lambda > 0$. -/)]
theorem sum_rpow_neg_radius {lam a p : ℝ} (hlam : 0 < lam) (ha : 0 < a) (k : ℕ) :
    ∑ j : Fin k, (a / lam ^ ((j : ℕ) + 1)) ^ (-p) =
      a ^ (-p) * ∑ j ∈ Finset.range k, (lam ^ p) ^ (j + 1) := by
  /-- Termwise: $(a/\lambda^{j+1})^{-p} = (\lambda^{j+1})^p / a^p = a^{-p} (\lambda^p)^{j+1}$. -/
  rw [Fin.sum_univ_eq_sum_range (fun j => (a / lam ^ (j + 1)) ^ (-p)) k, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hl : (0 : ℝ) ≤ lam ^ (j + 1) := by positivity
  rw [Real.div_rpow ha.le hl, Real.rpow_neg ha.le, Real.rpow_neg hl,
    ← Real.rpow_natCast_mul hlam.le, mul_comm (((j + 1 : ℕ) : ℝ)) p,
    Real.rpow_mul_natCast hlam.le, div_inv_eq_mul]

@[blueprint "lem:e3-geom-sum-bounds"
  (statement := /-- For $q > 1$ and $k \ge 1$:
    $q^k \le \sum_{j<k} q^{j+1} \le \frac{q}{q-1} q^k$. -/)]
theorem geom_sum_succ_bounds {q : ℝ} (hq : 1 < q) {k : ℕ} (hk : 1 ≤ k) :
    q ^ k ≤ ∑ j ∈ Finset.range k, q ^ (j + 1) ∧
      ∑ j ∈ Finset.range k, q ^ (j + 1) ≤ q / (q - 1) * q ^ k := by
  /-- The lower bound is the last term; the upper bound is the geometric sum formula
    $q(q^k - 1)/(q-1)$. -/
  have hq0 : 0 < q := by linarith
  have hq1 : 0 < q - 1 := by linarith
  constructor
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [Finset.sum_range_succ]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun j _ => by positivity)
  · have h : ∑ j ∈ Finset.range k, q ^ (j + 1) = q * ((q ^ k - 1) / (q - 1)) := by
      rw [← geom_sum_eq hq.ne', Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h]
    calc q * ((q ^ k - 1) / (q - 1)) = q / (q - 1) * (q ^ k - 1) := by ring
      _ ≤ q / (q - 1) * q ^ k :=
          mul_le_mul_of_nonneg_left (by linarith) (div_pos hq0 hq1).le

omit [NormedSpace ℝ E] in
@[blueprint "lem:e3-nonempty-of-entropy-rpow"
  (statement := /-- If $c_- \delta^{-p} \le \log M(G, \delta)$ for all small $\delta > 0$
    with $c_- > 0$, then $G \ne \emptyset$. -/)]
theorem nonempty_of_rpow_packing_lower {cLow δ₀ p : ℝ} (hcLow : 0 < cLow) (hδ₀ : 0 < δ₀)
    (hlow : ∀ δ : ℝ≥0, 0 < δ → (δ : ℝ) < δ₀ →
      cLow * (δ : ℝ) ^ (-p) ≤ Real.log (packingNumber δ G : ℝ≥0∞).toReal) :
    G.Nonempty := by
  /-- Otherwise $M(G, \delta) = 0$ and $\log 0 = 0 < c_- \delta^{-p}$ for $\delta = \delta_0/2$. -/
  by_contra hemp
  rw [Set.not_nonempty_iff_eq_empty] at hemp
  have hm : (0 : ℝ) < δ₀ / 2 := by positivity
  set δ : ℝ≥0 := Real.toNNReal (δ₀ / 2) with hδ
  have hδcoe : (δ : ℝ) = δ₀ / 2 := Real.coe_toNNReal _ hm.le
  have h := hlow δ (by rw [← NNReal.coe_pos, hδcoe]; exact hm) (by rw [hδcoe]; linarith)
  rw [hemp, packingNumber_empty] at h
  simp only [ENat.toENNReal_zero, ENNReal.toReal_zero, Real.log_zero] at h
  have hpos : 0 < cLow * (δ : ℝ) ^ (-p) := mul_pos hcLow (Real.rpow_pos_of_pos (by
    rw [hδcoe]; exact hm) _)
  linarith

@[blueprint "cor:doubleexp"
  (statement := /-- \textbf{(Double-exponential regime.)} Assume there are
    $p, c_-, c_+, \delta_0 > 0$ with $c_- \delta^{-p} \le \log M(G, \delta)$ and
    $\log N^{\mathrm{ext}}(G, \delta) \le c_+ \delta^{-p}$ for all $0 < \delta < \delta_0$,
    and that $N^{\mathrm{ext}}(G, \delta) < \infty$ for all $\delta > 0$. Then for every fixed
    $\varepsilon$ with $0 < \varepsilon < 1/2$ and $\varepsilon < \lambda\delta_0/2$ there are
    $C_1, C_2 > 0$ and $k_0$ such that
    $C_1 \lambda^{pk} \le \log N^{\mathrm{ext}}(W_k, d_\infty, \varepsilon) \le C_2 \lambda^{pk}$
    for all $k \ge k_0$. -/)]
theorem cor_doubleexp (hlam : 1 < lam)
    (hfin : ∀ δ : ℝ≥0, 0 < δ → externalCoveringNumber δ G ≠ ⊤)
    {p cLow cUp δ₀ : ℝ} (hp : 0 < p) (hcLow : 0 < cLow) (hcUp : 0 < cUp) (hδ₀ : 0 < δ₀)
    (hlow : ∀ δ : ℝ≥0, 0 < δ → (δ : ℝ) < δ₀ →
      cLow * (δ : ℝ) ^ (-p) ≤ Real.log (packingNumber δ G : ℝ≥0∞).toReal)
    (hup : ∀ δ : ℝ≥0, 0 < δ → (δ : ℝ) < δ₀ →
      Real.log (externalCoveringNumber δ G : ℝ≥0∞).toReal ≤ cUp * (δ : ℝ) ^ (-p))
    {ε : ℝ≥0} (hε : 0 < ε) (hε1 : ε < 1 / 2) (hεδ : (ε : ℝ) < lam * δ₀ / 2) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      C₁ * (lam : ℝ) ^ (p * k) ≤
        Real.log (externalCoveringNumber (X := UnifMaps (MemState E)) ε (memWords G lam k) :
          ℝ≥0∞).toReal ∧
      Real.log (externalCoveringNumber (X := UnifMaps (MemState E)) ε (memWords G lam k) :
          ℝ≥0∞).toReal ≤ C₂ * (lam : ℝ) ^ (p * k) := by
  /-- By the sum forms of (iii), with $q = \lambda^p > 1$,
    $$c_- (2\varepsilon)^{-p} \sum_{j<k} q^{j+1}
      \le \log N^{\mathrm{ext}}(W_k, \varepsilon)
      \le c_+ \varepsilon^{-p} \sum_{j<k} q^{j+1},$$
    and $q^k \le \sum_{j<k} q^{j+1} \le \frac{q}{q-1} q^k$ for $k \ge 1$; take
    $C_1 = c_-(2\varepsilon)^{-p}$, $C_2 = c_+ \varepsilon^{-p} q/(q-1)$, $k_0 = 1$. -/
  have hlamR : (1 : ℝ) < lam := by exact_mod_cast hlam
  have hlamR0 : (0 : ℝ) < lam := zero_lt_one.trans hlamR
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  have hG : G.Nonempty := nonempty_of_rpow_packing_lower hcLow hδ₀ hlow
  have hq1 : 1 < (lam : ℝ) ^ p := Real.one_lt_rpow hlamR hp
  have hqk : ∀ k : ℕ, (lam : ℝ) ^ (p * k) = ((lam : ℝ) ^ p) ^ k := fun k =>
    Real.rpow_mul_natCast hlamR0.le p k
  refine ⟨cLow * (2 * ε : ℝ) ^ (-p), cUp * (ε : ℝ) ^ (-p) * ((lam : ℝ) ^ p / ((lam : ℝ) ^ p - 1)),
    by positivity, mul_pos (by positivity) (div_pos (by linarith) (by linarith)), 1,
    fun k hk => ?_⟩
  have hup' := log_externalCoveringNumber_memWords_le_sum hlam hfin hG
    (φ := fun δ => cUp * δ ^ (-p)) hup hε (by linarith) k
  have hlow' := sum_le_log_externalCoveringNumber_memWords hlam hfin hG
    (φ := fun δ => cLow * δ ^ (-p)) hlow hε hε1 (by linarith) k
  simp only [← Finset.mul_sum] at hup' hlow'
  rw [sum_rpow_neg_radius hlamR0 hεR] at hup'
  rw [sum_rpow_neg_radius hlamR0 (by positivity)] at hlow'
  obtain ⟨hg1, hg2⟩ := geom_sum_succ_bounds hq1 hk
  constructor
  · refine le_trans ?_ hlow'
    rw [hqk]
    calc cLow * (2 * (ε : ℝ)) ^ (-p) * ((lam : ℝ) ^ p) ^ k
        = cLow * ((2 * (ε : ℝ)) ^ (-p) * ((lam : ℝ) ^ p) ^ k) := by ring
      _ ≤ cLow * ((2 * (ε : ℝ)) ^ (-p) * ∑ j ∈ Finset.range k, ((lam : ℝ) ^ p) ^ (j + 1)) := by
          gcongr
  · refine hup'.trans ?_
    rw [hqk]
    calc cUp * ((ε : ℝ) ^ (-p) * ∑ j ∈ Finset.range k, ((lam : ℝ) ^ p) ^ (j + 1))
        ≤ cUp * ((ε : ℝ) ^ (-p) * ((lam : ℝ) ^ p / ((lam : ℝ) ^ p - 1) * ((lam : ℝ) ^ p) ^ k)) := by
          gcongr
      _ = cUp * (ε : ℝ) ^ (-p) * ((lam : ℝ) ^ p / ((lam : ℝ) ^ p - 1)) * ((lam : ℝ) ^ p) ^ k := by
          ring

end Entropy

end LeanDeepgen
