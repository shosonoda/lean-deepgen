import Mathlib
import Architect
import LeanDeepgen.Tradeoff.Defs

/-!
# Depth bias–variance trade-offs: the four regimes

Paper Sec. 5 (`sec:optdepth`), Table `tab:tradeoff` and App. J (`sec:proof.tradeoff`).

We treat the depth `k` as a positive real and study the bound
`gen(k, n) = bias(k) + var(k, n)` for the two bias laws
`biasExp α k = e^{-α k}`, `biasPoly β k = k^{-β}` and the two variance profiles
`varLog n k = √(log k / n)`, `varPoly γ n k = √(k^γ / n)` (all defined, together with the
balancing depths `kPP`, `kEP`, `kEL`, `kPL` and the balanced rates `rateEP`, `rateEL`, `ratePL`,
in `LeanDeepgen.Tradeoff.Defs`).

* `lem:balancing` — the balancing principle: if `bias` is nonincreasing and `var(·, n)` is
  nondecreasing then `gen(k, n) ≥ max(bias k, var n k)`, and any depth `k₀` with
  `bias k₀ = var n k₀` is optimal up to the factor `2`.
* `thm:tradeoff-pp` — PP regime, exact: at `k = n^{1/(2β+γ)}` the bound equals
  `2 n^{-β/(2β+γ)}`, and no depth does better than `n^{-β/(2β+γ)}`.
* `thm:tradeoff-ep`, `thm:tradeoff-el`, `thm:tradeoff-pl` — EP, EL, PL regimes: with the
  balancing depths of Table `tab:tradeoff` (leading terms), the bound is `Θ` of the
  displayed balanced rate (`Asymptotics.IsTheta` along `Filter.atTop`).
* `rem:tradeoff-ordering` — EP is no worse than PL for `γ ≤ 1`, and PL no worse than EP for
  `γ ≥ 1`.

Mathlib has no Lambert `W` function, so the PL balancing depth is stated directly in the
closed form `k = (2βn / log(2βn))^{1/(2β)}` obtained from `W(x) ∼ log x`, and the balancing
equation `k^{2β} log k ≍ n` is recorded as the exact identity
`k^{2β} log k = n (1 - log L / L)`, `L = log(2βn)` (`lem:tradeoff-pl-balance`), together
with `k^{2β} log k / n → 1`.
-/

open Filter Asymptotics
open scoped Topology

namespace LeanDeepgen.Tradeoff

/-! ### Monotonicity of the four families -/

@[blueprint "lem:bias-exp-antitone"
  (statement := /-- For $\alpha > 0$, $k \mapsto e^{-\alpha k}$ is nonincreasing. -/)]
theorem biasExp_antitone {α : ℝ} (hα : 0 < α) : Antitone (biasExp α) := by
  /-- $\exp$ is monotone and $k \mapsto -\alpha k$ is nonincreasing. -/
  intro a b hab
  exact Real.exp_le_exp.2 (by nlinarith)

@[blueprint "lem:bias-poly-antitoneOn"
  (statement := /-- For $\beta > 0$, $k \mapsto k^{-\beta}$ is nonincreasing on $(0,\infty)$. -/)]
theorem biasPoly_antitoneOn {β : ℝ} (hβ : 0 < β) : AntitoneOn (biasPoly β) (Set.Ioi 0) := by
  /-- Power with a nonpositive exponent is antitone on the positive reals. -/
  intro a ha _ _ hab
  exact Real.rpow_le_rpow_of_nonpos ha hab (by linarith)

@[blueprint "lem:var-log-monotoneOn"
  (statement := /-- For $n \ge 0$, $k \mapsto \sqrt{\log k / n}$ is nondecreasing on
    $(0,\infty)$. -/)]
theorem varLog_monotoneOn {n : ℝ} (hn : 0 ≤ n) : MonotoneOn (varLog n) (Set.Ioi 0) := by
  /-- $\log$ is monotone on $(0,\infty)$; divide by $n \ge 0$ and take square roots. -/
  intro a ha _ _ hab
  exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (Real.log_le_log ha hab) hn)

@[blueprint "lem:var-poly-monotoneOn"
  (statement := /-- For $\gamma \ge 0$ and $n \ge 0$, $k \mapsto \sqrt{k^{\gamma}/n}$ is
    nondecreasing on $(0,\infty)$. -/)]
theorem varPoly_monotoneOn {γ n : ℝ} (hγ : 0 ≤ γ) (hn : 0 ≤ n) :
    MonotoneOn (varPoly γ n) (Set.Ioi 0) := by
  /-- $k \mapsto k^\gamma$ is monotone for $\gamma \ge 0$; divide by $n$ and take roots. -/
  intro a ha _ _ hab
  exact Real.sqrt_le_sqrt
    (div_le_div_of_nonneg_right (Real.rpow_le_rpow (le_of_lt ha) hab hγ) hn)

/-! ### The balancing principle -/

@[blueprint "lem:balancing-max"
  (statement := /-- If $\bias \ge 0$ and $\var(\cdot,n) \ge 0$ on a set $S$ of depths, then
    $\gen(k,n) \ge \max\{\bias(k), \var(k,n)\}$ for every $k \in S$. -/)]
theorem max_le_genBound {bias : ℝ → ℝ} {var : ℝ → ℝ → ℝ} {n : ℝ} {S : Set ℝ}
    (hb : ∀ k ∈ S, 0 ≤ bias k) (hv : ∀ k ∈ S, 0 ≤ var n k) {k : ℝ} (hk : k ∈ S) :
    max (bias k) (var n k) ≤ genBound bias var n k := by
  /-- Each summand is bounded by the sum because the other one is nonnegative. -/
  unfold genBound
  exact max_le (le_add_of_nonneg_right (hv k hk)) (le_add_of_nonneg_left (hb k hk))

@[blueprint "lem:balancing"
  (statement := /-- \textbf{Balancing principle.}  Let $S \subseteq \mathbb R$ be a set of
    depths on which $\bias \ge 0$ is nonincreasing and $\var(\cdot,n) \ge 0$ is nondecreasing.
    If $k_0 \in S$ balances the two terms, $\bias(k_0) = \var(k_0,n)$, then
    $\gen(k,n) \ge \bias(k_0)$ for every $k \in S$, while
    $\gen(k_0,n) = 2\bias(k_0)$; hence $k_0$ minimizes the bound over $S$ up to the
    factor $2$. -/)]
theorem balancing {bias : ℝ → ℝ} {var : ℝ → ℝ → ℝ} {n : ℝ} {S : Set ℝ}
    (hb : ∀ k ∈ S, 0 ≤ bias k) (hv : ∀ k ∈ S, 0 ≤ var n k)
    (hanti : AntitoneOn bias S) (hmono : MonotoneOn (var n) S)
    {k₀ : ℝ} (hk₀ : k₀ ∈ S) (hbal : bias k₀ = var n k₀) :
    (∀ k ∈ S, bias k₀ ≤ genBound bias var n k) ∧ genBound bias var n k₀ = 2 * bias k₀ := by
  /-- Case split on $k \le k_0$ or $k \ge k_0$: in the first case
    $\bias(k) \ge \bias(k_0)$ and $\var(k,n) \ge 0$; in the second
    $\var(k,n) \ge \var(k_0,n) = \bias(k_0)$ and $\bias(k) \ge 0$.
    The identity at $k_0$ is the balance equation. -/
  refine ⟨fun k hk => ?_, ?_⟩
  · unfold genBound
    rcases le_total k k₀ with hkk | hkk
    · have := hanti hk hk₀ hkk
      linarith [hv k hk]
    · have := hmono hk₀ hk hkk
      linarith [hb k hk]
  · unfold genBound
    rw [← hbal]; ring

/-! ### PP: polynomial bias, polynomial variance -/

@[blueprint "lem:bias-poly-kpp"
  (statement := /-- For $\beta,\gamma > 0$ and $n > 0$,
    $\bias(\kopt) = \kopt^{-\beta} = n^{-\beta/(2\beta+\gamma)}$. -/)]
theorem biasPoly_kPP {β γ n : ℝ} (hβ : 0 < β) (hγ : 0 < γ) (hn : 0 < n) :
    biasPoly β (kPP β γ n) = n ^ (-β / (2 * β + γ)) := by
  /-- $(n^{1/(2\beta+\gamma)})^{-\beta} = n^{-\beta/(2\beta+\gamma)}$ by the power rule. -/
  unfold biasPoly kPP
  rw [← Real.rpow_mul hn.le]
  congr 1
  have : (2 * β + γ) ≠ 0 := by positivity
  field_simp

@[blueprint "lem:var-poly-kpp"
  (statement := /-- For $\beta,\gamma > 0$ and $n > 0$,
    $\var(\kopt,n) = \sqrt{\kopt^{\gamma}/n} = n^{-\beta/(2\beta+\gamma)}$. -/)]
theorem varPoly_kPP {β γ n : ℝ} (hβ : 0 < β) (hγ : 0 < γ) (hn : 0 < n) :
    varPoly γ n (kPP β γ n) = n ^ (-β / (2 * β + γ)) := by
  /-- $\kopt^\gamma / n = n^{\gamma/(2\beta+\gamma) - 1} = n^{-2\beta/(2\beta+\gamma)}$,
    and the square root halves the exponent. -/
  unfold varPoly kPP
  rw [← Real.rpow_mul hn.le, ← Real.rpow_sub_one hn.ne', Real.sqrt_eq_rpow,
    ← Real.rpow_mul hn.le]
  congr 1
  have : (2 * β + γ) ≠ 0 := by positivity
  field_simp
  ring

@[blueprint "thm:tradeoff-pp"
  (statement := /-- \textbf{PP regime} (\cref{tab:tradeoff}).  Let $\beta,\gamma > 0$ and
    $n > 0$.  At the balancing depth $\kopt = n^{1/(2\beta+\gamma)}$,
    $\gen(\kopt,n) = \kopt^{-\beta} + \sqrt{\kopt^{\gamma}/n} = 2\,n^{-\beta/(2\beta+\gamma)}$,
    and for every depth $k > 0$,
    $\gen(k,n) = k^{-\beta} + \sqrt{k^{\gamma}/n} \ge n^{-\beta/(2\beta+\gamma)}$.
    Thus $\kopt$ is optimal up to the factor $2$ and
    $\gen(\kopt,n) \asymp n^{-\beta/(2\beta+\gamma)}$. -/)]
theorem tradeoff_PP {β γ n : ℝ} (hβ : 0 < β) (hγ : 0 < γ) (hn : 0 < n) :
    genBound (biasPoly β) (varPoly γ) n (kPP β γ n) = 2 * n ^ (-β / (2 * β + γ)) ∧
    ∀ k > 0, n ^ (-β / (2 * β + γ)) ≤ genBound (biasPoly β) (varPoly γ) n k := by
  /-- Both terms equal $n^{-\beta/(2\beta+\gamma)}$ at $\kopt$
    (\cref{lem:bias-poly-kpp}, \cref{lem:var-poly-kpp}), so the balancing principle
    \cref{lem:balancing} on $S = (0,\infty)$ gives both claims. -/
  have hk₀ : kPP β γ n ∈ Set.Ioi (0 : ℝ) := Real.rpow_pos_of_pos hn _
  have hbal : biasPoly β (kPP β γ n) = varPoly γ n (kPP β γ n) := by
    rw [biasPoly_kPP hβ hγ hn, varPoly_kPP hβ hγ hn]
  have h := balancing (bias := biasPoly β) (var := varPoly γ) (n := n) (S := Set.Ioi 0)
    (fun k hk => Real.rpow_nonneg (le_of_lt hk) _) (fun _ _ => Real.sqrt_nonneg _)
    (biasPoly_antitoneOn hβ) (varPoly_monotoneOn hγ.le hn.le) hk₀ hbal
  refine ⟨?_, fun k hk => ?_⟩
  · rw [h.2, biasPoly_kPP hβ hγ hn]
  · rw [← biasPoly_kPP hβ hγ hn]
    exact h.1 k hk

/-! ### Auxiliary facts -/

@[blueprint "lem:eventually-log-le-mul"
  (statement := /-- For every $c > 0$, $\log x \le c\,x$ for all sufficiently large $x$. -/)]
theorem eventually_log_le_mul {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, Real.log x ≤ c * x := by
  /-- $\log x = o(x)$ (Mathlib: `Real.isLittleO\_log\_id\_atTop`). -/
  filter_upwards [Real.isLittleO_log_id_atTop.def hc, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  rw [id, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx0] at hx
  exact (le_abs_self _).trans hx

@[blueprint "lem:eventually-log-log-le-mul"
  (statement := /-- For every $c > 0$, $\log\log n \le c \log n$ for all sufficiently large
    $n$. -/)]
theorem eventually_log_log_le_mul {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℝ in atTop, Real.log (Real.log n) ≤ c * Real.log n := by
  /-- Compose \cref{lem:eventually-log-le-mul} with $\log n \to \infty$. -/
  exact Real.tendsto_log_atTop.eventually (eventually_log_le_mul hc)

@[blueprint "lem:log-lt-self-of-pos"
  (statement := /-- $\log x < x$ for $x > 0$. -/)]
theorem log_lt_self_of_pos {x : ℝ} (hx : 0 < x) : Real.log x < x := by
  /-- $\log x \le x - 1 < x$. -/
  linarith [Real.log_le_sub_one_of_pos hx]

@[blueprint "lem:rpow-neg-half-mul-rpow"
  (statement := /-- For $n > 0$ and $L \ge 0$,
    $n^{-1/2} L^{\gamma/2} = \sqrt{L^{\gamma}/n}$. -/)]
theorem rpow_neg_half_mul_rpow_half {n L γ : ℝ} (hn : 0 < n) (hL : 0 ≤ L) :
    n ^ (-(1 : ℝ) / 2) * L ^ (γ / 2) = √(L ^ γ / n) := by
  /-- $\sqrt{L^\gamma/n} = \sqrt{L^\gamma}/\sqrt n = L^{\gamma/2} n^{-1/2}$. -/
  rw [Real.sqrt_div (Real.rpow_nonneg hL _), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hL, show (-(1 : ℝ) / 2) = -(1 / 2) by ring, Real.rpow_neg hn.le,
    show γ * (1 / 2) = γ / 2 by ring]
  ring

@[blueprint "lem:sqrt-mul-div"
  (statement := /-- For $c \ge 0$, $\sqrt{c\,x/n} = \sqrt c\,\sqrt{x/n}$. -/)]
theorem sqrt_mul_div {c x n : ℝ} (hc : 0 ≤ c) : √(c * x / n) = √c * √(x / n) := by
  /-- Multiplicativity of the square root. -/
  rw [mul_div_assoc, Real.sqrt_mul hc]

/-! ### EP: exponential bias, polynomial variance -/

@[blueprint "lem:rate-ep-nonneg"
  (statement := /-- $n^{-1/2}(\log n)^{\gamma/2} \ge 0$ for $n \ge 1$. -/)]
theorem rateEP_nonneg {γ n : ℝ} (hn : 1 ≤ n) : 0 ≤ rateEP γ n := by
  /-- Product of two nonnegative powers. -/
  exact mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (Real.log_nonneg hn) _)

@[blueprint "lem:bias-exp-kep"
  (statement := /-- For $\alpha > 0$ and $n > 1$,
    $e^{-\alpha \kopt} = n^{-1/2}(\log n)^{\gamma/2}$ exactly. -/)]
theorem biasExp_kEP {α γ n : ℝ} (hα : 0 < α) (hn : 1 < n) :
    biasExp α (kEP α γ n) = rateEP γ n := by
  /-- $-\alpha\kopt = -\tfrac12 \log n + \tfrac\gamma2 \log\log n$; exponentiate. -/
  unfold biasExp kEP rateEP
  rw [Real.rpow_def_of_pos (by linarith), Real.rpow_def_of_pos (Real.log_pos hn), ← Real.exp_add]
  congr 1
  field_simp
  ring

@[blueprint "lem:kep-le"
  (statement := /-- For $\alpha, \gamma > 0$ and $\log n \ge 1$, $\kopt \le \log n/(2\alpha)$. -/)]
theorem kEP_le {α γ n : ℝ} (hα : 0 < α) (hγ : 0 < γ) (hn : 1 ≤ Real.log n) :
    kEP α γ n ≤ Real.log n / (2 * α) := by
  /-- $\gamma \log\log n \ge 0$ when $\log n \ge 1$. -/
  unfold kEP
  apply div_le_div_of_nonneg_right _ (by positivity)
  have := Real.log_nonneg hn
  nlinarith

@[blueprint "lem:var-poly-kep-le"
  (statement := /-- For $\alpha,\gamma > 0$, $n > 1$, $\log n \ge 1$ and
    $\gamma \log\log n \le \log n$:
    $\sqrt{\kopt^{\gamma}/n} \le \sqrt{(2\alpha)^{-\gamma}}\; n^{-1/2}(\log n)^{\gamma/2}$. -/)]
theorem varPoly_kEP_le {α γ n : ℝ} (hα : 0 < α) (hγ : 0 < γ) (hn : 1 < n)
    (hlog : 1 ≤ Real.log n) (hll : γ * Real.log (Real.log n) ≤ Real.log n) :
    varPoly γ n (kEP α γ n) ≤ √((2 * α) ^ (-γ)) * rateEP γ n := by
  /-- $0 \le \kopt \le \log n/(2\alpha)$, so
    $\kopt^\gamma \le (2\alpha)^{-\gamma} (\log n)^\gamma$; divide by $n$ and take roots. -/
  have hn0 : 0 < n := by linarith
  have hL : 0 ≤ Real.log n := by linarith
  have hk0 : 0 ≤ kEP α γ n := by
    unfold kEP
    apply div_nonneg _ (by positivity)
    linarith
  have hpow : kEP α γ n ^ γ ≤ (2 * α) ^ (-γ) * Real.log n ^ γ := by
    calc kEP α γ n ^ γ ≤ (Real.log n / (2 * α)) ^ γ :=
          Real.rpow_le_rpow hk0 (kEP_le hα hγ hlog) hγ.le
      _ = (2 * α) ^ (-γ) * Real.log n ^ γ := by
          rw [Real.div_rpow hL (by positivity), Real.rpow_neg (by positivity), div_eq_inv_mul]
  unfold varPoly rateEP
  rw [rpow_neg_half_mul_rpow_half hn0 hL, ← sqrt_mul_div (Real.rpow_nonneg (by positivity) _)]
  exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hpow hn0.le)

@[blueprint "lem:eventually-ep"
  (statement := /-- For $\alpha,\gamma > 0$, eventually in $n$:
    $n^{-1/2}(\log n)^{\gamma/2} \le \gen(\kopt,n)
      \le \bigl(1 + \sqrt{(2\alpha)^{-\gamma}}\bigr)\, n^{-1/2}(\log n)^{\gamma/2}$. -/)]
theorem eventually_EP_bounds {α γ : ℝ} (hα : 0 < α) (hγ : 0 < γ) :
    ∀ᶠ n : ℝ in atTop,
      rateEP γ n ≤ genBound (biasExp α) (varPoly γ) n (kEP α γ n) ∧
      genBound (biasExp α) (varPoly γ) n (kEP α γ n) ≤ (1 + √((2 * α) ^ (-γ))) * rateEP γ n := by
  /-- The bias term equals the rate exactly (\cref{lem:bias-exp-kep}) and the variance term is
    at most $\sqrt{(2\alpha)^{-\gamma}}$ times the rate (\cref{lem:var-poly-kep-le}); the side
    conditions hold for large $n$ by \cref{lem:eventually-log-log-le-mul}. -/
  filter_upwards [eventually_gt_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_log_log_le_mul (inv_pos.2 hγ)] with n hn hlog hll
  have hll' : γ * Real.log (Real.log n) ≤ Real.log n := by
    have := mul_le_mul_of_nonneg_left hll hγ.le
    rwa [← mul_assoc, mul_inv_cancel₀ hγ.ne', one_mul] at this
  have hb := biasExp_kEP (γ := γ) hα hn
  have hv := varPoly_kEP_le hα hγ hn hlog hll'
  unfold genBound
  constructor
  · rw [hb]; exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
  · rw [hb]; linarith

@[blueprint "lem:isTheta-of-eventually-bounds"
  (statement := /-- If $0 \le g$ eventually, $c > 0$, and $g \le f \le c\,g$ eventually, then
    $f = \Theta(g)$. -/)]
theorem isTheta_of_eventually_bounds {f g : ℝ → ℝ} {c : ℝ}
    (hg : ∀ᶠ n in atTop, 0 ≤ g n) (h : ∀ᶠ n in atTop, g n ≤ f n ∧ f n ≤ c * g n) :
    f =Θ[atTop] g := by
  /-- Both $O$-directions, with constants $c$ and $1$. -/
  constructor
  · refine IsBigO.of_bound c ?_
    filter_upwards [hg, h] with n hg hn
    rw [Real.norm_of_nonneg (hg.trans hn.1), Real.norm_of_nonneg hg]
    exact hn.2
  · refine IsBigO.of_bound 1 ?_
    filter_upwards [hg, h] with n hg hn
    rw [Real.norm_of_nonneg (hg.trans hn.1), Real.norm_of_nonneg hg, one_mul]
    exact hn.1

@[blueprint "thm:tradeoff-ep"
  (statement := /-- \textbf{EP regime} (\cref{tab:tradeoff}).  Let $\alpha,\gamma > 0$ and
    $\kopt(n) = \frac{1}{2\alpha}(\log n - \gamma\log\log n)$.  Then
    $\gen(\kopt,n) = e^{-\alpha\kopt} + \sqrt{\kopt^{\gamma}/n}
      \asymp n^{-1/2}(\log n)^{\gamma/2}$ as $n \to \infty$
    (more precisely, between $1$ and $1 + (2\alpha)^{-\gamma/2}$ times the rate). -/)]
theorem tradeoff_EP {α γ : ℝ} (hα : 0 < α) (hγ : 0 < γ) :
    (fun n => genBound (biasExp α) (varPoly γ) n (kEP α γ n)) =Θ[atTop]
      (fun n => n ^ (-(1 : ℝ) / 2) * Real.log n ^ (γ / 2)) := by
  /-- Apply \cref{lem:isTheta-of-eventually-bounds} to the two-sided bound
    \cref{lem:eventually-ep}. -/
  exact isTheta_of_eventually_bounds (g := rateEP γ)
    ((eventually_ge_atTop 1).mono fun n hn => rateEP_nonneg hn) (eventually_EP_bounds hα hγ)

@[blueprint "cor:tradeoff-ep-bigO"
  (statement := /-- EP regime, upper bound: $\gen(\kopt,n) = O(n^{-1/2}(\log n)^{\gamma/2})$. -/)]
theorem tradeoff_EP_isBigO {α γ : ℝ} (hα : 0 < α) (hγ : 0 < γ) :
    (fun n => genBound (biasExp α) (varPoly γ) n (kEP α γ n)) =O[atTop]
      (fun n => n ^ (-(1 : ℝ) / 2) * Real.log n ^ (γ / 2)) := by
  /-- The $O$-half of \cref{thm:tradeoff-ep}. -/
  exact (tradeoff_EP hα hγ).1

/-! ### EL: exponential bias, logarithmic variance -/

@[blueprint "lem:bias-exp-kel"
  (statement := /-- For $\alpha > 0$ and $n > e$,
    $e^{-\alpha\kopt} = \sqrt{\log\log n/n}$ exactly. -/)]
theorem biasExp_kEL {α n : ℝ} (hα : 0 < α) (hn : Real.exp 1 < n) :
    biasExp α (kEL α n) = rateEL n := by
  /-- $-\alpha\kopt = -\tfrac12\log n + \tfrac12\log\log\log n$; exponentiate and rewrite
    $n^{-1/2}(\log\log n)^{1/2} = \sqrt{\log\log n/n}$. -/
  have hn0 : 0 < n := (Real.exp_pos 1).trans hn
  have hL : 1 < Real.log n := by
    have := Real.log_lt_log (Real.exp_pos 1) hn
    rwa [Real.log_exp] at this
  have hM : 0 < Real.log (Real.log n) := Real.log_pos hL
  have hconv := rpow_neg_half_mul_rpow_half (γ := 1) hn0 hM.le
  rw [Real.rpow_one] at hconv
  unfold biasExp kEL rateEL
  rw [← hconv, Real.rpow_def_of_pos hn0, Real.rpow_def_of_pos hM, ← Real.exp_add]
  congr 1
  field_simp
  ring

@[blueprint "lem:kel-bounds"
  (statement := /-- For $\alpha > 0$ and $\log n \ge e$: $0 < \kopt \le \log n/(2\alpha)$
    and $\log \kopt \le \log\log n + |\log(2\alpha)|$. -/)]
theorem kEL_bounds {α n : ℝ} (hα : 0 < α) (hn : Real.exp 1 ≤ Real.log n) :
    0 < kEL α n ∧ kEL α n ≤ Real.log n / (2 * α) ∧
      Real.log (kEL α n) ≤ Real.log (Real.log n) + |Real.log (2 * α)| := by
  /-- $\log\log\log n \ge 0$ gives the upper bound; $\log\log\log n < \log\log n < \log n$
    gives positivity; then $\log\kopt \le \log(\log n/(2\alpha)) = \log\log n - \log(2\alpha)$. -/
  have hL : 0 < Real.log n := (Real.exp_pos 1).trans_le hn
  have hM : 1 ≤ Real.log (Real.log n) := by
    have := Real.log_le_log (Real.exp_pos 1) hn
    rwa [Real.log_exp] at this
  have hP : 0 ≤ Real.log (Real.log (Real.log n)) := Real.log_nonneg hM
  have h1 : Real.log (Real.log (Real.log n)) < Real.log n :=
    (log_lt_self_of_pos (by linarith)).trans (log_lt_self_of_pos hL)
  have hk : 0 < kEL α n := by
    unfold kEL
    apply div_pos _ (by positivity)
    linarith
  have hle : kEL α n ≤ Real.log n / (2 * α) := by
    unfold kEL
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  refine ⟨hk, hle, ?_⟩
  calc Real.log (kEL α n) ≤ Real.log (Real.log n / (2 * α)) := Real.log_le_log hk hle
    _ = Real.log (Real.log n) - Real.log (2 * α) := Real.log_div hL.ne' (by positivity)
    _ ≤ Real.log (Real.log n) + |Real.log (2 * α)| := by linarith [neg_abs_le (Real.log (2 * α))]

@[blueprint "lem:var-log-kel-le"
  (statement := /-- For $\alpha > 0$ and $\log n \ge e$:
    $\sqrt{\log\kopt/n} \le \sqrt{1 + |\log(2\alpha)|}\,\sqrt{\log\log n/n}$. -/)]
theorem varLog_kEL_le {α n : ℝ} (hα : 0 < α) (hn0 : 0 < n) (hn : Real.exp 1 ≤ Real.log n) :
    varLog n (kEL α n) ≤ √(1 + |Real.log (2 * α)|) * rateEL n := by
  /-- $\log\kopt \le \log\log n + |\log 2\alpha| \le (1 + |\log 2\alpha|)\log\log n$ because
    $\log\log n \ge 1$ (\cref{lem:kel-bounds}). -/
  have hM : 1 ≤ Real.log (Real.log n) := by
    have := Real.log_le_log (Real.exp_pos 1) hn
    rwa [Real.log_exp] at this
  have h := (kEL_bounds hα hn).2.2
  have h' : Real.log (kEL α n) ≤ (1 + |Real.log (2 * α)|) * Real.log (Real.log n) := by
    nlinarith [abs_nonneg (Real.log (2 * α))]
  unfold varLog rateEL
  rw [← sqrt_mul_div (by positivity)]
  exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right h' hn0.le)

@[blueprint "lem:eventually-el"
  (statement := /-- For $\alpha > 0$, eventually in $n$:
    $\sqrt{\log\log n/n} \le \gen(\kopt,n)
      \le \bigl(1 + \sqrt{1 + |\log(2\alpha)|}\bigr)\sqrt{\log\log n/n}$. -/)]
theorem eventually_EL_bounds {α : ℝ} (hα : 0 < α) :
    ∀ᶠ n : ℝ in atTop,
      rateEL n ≤ genBound (biasExp α) varLog n (kEL α n) ∧
      genBound (biasExp α) varLog n (kEL α n) ≤ (1 + √(1 + |Real.log (2 * α)|)) * rateEL n := by
  /-- Bias equals the rate (\cref{lem:bias-exp-kel}); variance is at most
    $\sqrt{1 + |\log 2\alpha|}$ times the rate (\cref{lem:var-log-kel-le}). -/
  filter_upwards [eventually_gt_atTop (Real.exp 1),
    Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 1)] with n hn hlog
  have hn0 : 0 < n := (Real.exp_pos 1).trans hn
  have hb := biasExp_kEL hα hn
  have hv := varLog_kEL_le hα hn0 hlog
  unfold genBound
  constructor
  · rw [hb]; exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
  · rw [hb]; linarith

@[blueprint "thm:tradeoff-el"
  (statement := /-- \textbf{EL regime} (\cref{tab:tradeoff}).  Let $\alpha > 0$ and
    $\kopt(n) = \frac{1}{2\alpha}(\log n - \log\log\log n)$.  Then
    $\gen(\kopt,n) = e^{-\alpha\kopt} + \sqrt{\log\kopt/n} \asymp \sqrt{\log\log n/n}$
    as $n \to \infty$. -/)]
theorem tradeoff_EL {α : ℝ} (hα : 0 < α) :
    (fun n => genBound (biasExp α) varLog n (kEL α n)) =Θ[atTop]
      (fun n => √(Real.log (Real.log n) / n)) := by
  /-- Apply \cref{lem:isTheta-of-eventually-bounds} to \cref{lem:eventually-el}. -/
  exact isTheta_of_eventually_bounds (g := rateEL)
    (Eventually.of_forall fun n => Real.sqrt_nonneg _) (eventually_EL_bounds hα)

@[blueprint "cor:tradeoff-el-bigO"
  (statement := /-- EL regime, upper bound: $\gen(\kopt,n) = O(\sqrt{\log\log n/n})$. -/)]
theorem tradeoff_EL_isBigO {α : ℝ} (hα : 0 < α) :
    (fun n => genBound (biasExp α) varLog n (kEL α n)) =O[atTop]
      (fun n => √(Real.log (Real.log n) / n)) := by
  /-- The $O$-half of \cref{thm:tradeoff-el}. -/
  exact (tradeoff_EL hα).1

/-! ### PL: polynomial bias, logarithmic variance -/

@[blueprint "lem:bias-poly-kpl"
  (statement := /-- For $\beta > 0$, $n > 0$ and $L = \log(2\beta n) > 0$:
    $\kopt^{-\beta} = \sqrt{L/(2\beta n)}$. -/)]
theorem biasPoly_kPL {β n : ℝ} (hβ : 0 < β) (hn : 0 < n) (hL : 0 < Real.log (2 * β * n)) :
    biasPoly β (kPL β n) = √(Real.log (2 * β * n) / (2 * β * n)) := by
  /-- $\kopt^{-\beta} = (2\beta n/L)^{-1/2} = (L/(2\beta n))^{1/2}$. -/
  have hm : 0 < 2 * β * n := by positivity
  have hq : 0 ≤ 2 * β * n / Real.log (2 * β * n) := (div_pos hm hL).le
  unfold biasPoly kPL
  rw [← Real.rpow_mul hq, show 1 / (2 * β) * (-β) = -(1 / 2) by field_simp,
    Real.rpow_neg hq, ← Real.inv_rpow hq, inv_div, Real.sqrt_eq_rpow]

@[blueprint "lem:log-kpl"
  (statement := /-- For $\beta > 0$, $n > 0$ and $L = \log(2\beta n) > 0$:
    $\log\kopt = (L - \log L)/(2\beta)$. -/)]
theorem log_kPL {β n : ℝ} (hβ : 0 < β) (hn : 0 < n) (hL : 0 < Real.log (2 * β * n)) :
    Real.log (kPL β n) =
      (Real.log (2 * β * n) - Real.log (Real.log (2 * β * n))) / (2 * β) := by
  /-- $\log$ of a power and of a quotient. -/
  have hm : 0 < 2 * β * n := by positivity
  unfold kPL
  rw [Real.log_rpow (div_pos hm hL), Real.log_div hm.ne' hL.ne']
  ring

@[blueprint "lem:tradeoff-pl-balance"
  (statement := /-- The PL balancing equation $k^{2\beta}\log k \asymp n$ holds exactly up to
    the factor $1 - \log L/L$: for $\beta > 0$, $n > 0$ and $L = \log(2\beta n) > 0$,
    $\kopt^{2\beta}\log\kopt = n\,(1 - \log L/L)$. -/)]
theorem kPL_balance {β n : ℝ} (hβ : 0 < β) (hn : 0 < n) (hL : 0 < Real.log (2 * β * n)) :
    kPL β n ^ (2 * β) * Real.log (kPL β n) =
      n * (1 - Real.log (Real.log (2 * β * n)) / Real.log (2 * β * n)) := by
  /-- $\kopt^{2\beta} = 2\beta n/L$ and $\log\kopt = (L - \log L)/(2\beta)$
    (\cref{lem:log-kpl}); multiply out. -/
  have hm : 0 < 2 * β * n := by positivity
  have hq : 0 ≤ 2 * β * n / Real.log (2 * β * n) := (div_pos hm hL).le
  rw [log_kPL hβ hn hL]
  unfold kPL
  rw [← Real.rpow_mul hq, show 1 / (2 * β) * (2 * β) = 1 by field_simp, Real.rpow_one]
  field_simp

@[blueprint "lem:tradeoff-pl-balance-tendsto"
  (statement := /-- $\kopt^{2\beta}\log\kopt / n \to 1$ as $n \to \infty$, i.e.
    $\kopt^{2\beta}\log\kopt \sim n$. -/)]
theorem kPL_balance_tendsto {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun n => kPL β n ^ (2 * β) * Real.log (kPL β n) / n) atTop (𝓝 1) := by
  /-- By \cref{lem:tradeoff-pl-balance} the ratio is $1 - \log L/L$ with
    $L = \log(2\beta n) \to \infty$, and $\log L / L \to 0$. -/
  have hLt : Tendsto (fun n : ℝ => Real.log (2 * β * n)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_id.const_mul_atTop (by positivity))
  have h0 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simpa only [pow_one, one_mul, add_zero] using this
  have h1 : Tendsto (fun n : ℝ => 1 - Real.log (Real.log (2 * β * n)) / Real.log (2 * β * n))
      atTop (𝓝 1) := by
    have := (h0.comp hLt).const_sub 1
    simpa only [sub_zero, Function.comp_def] using this
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ), hLt.eventually_gt_atTop 0] with n hn hL
  rw [kPL_balance hβ hn hL, mul_div_cancel_left₀ _ hn.ne']

@[blueprint "lem:var-log-kpl-le"
  (statement := /-- For $\beta > 0$, $n > 0$ and $L = \log(2\beta n) \ge 1$:
    $\sqrt{\log\kopt/n} \le \sqrt{L/(2\beta n)}$. -/)]
theorem varLog_kPL_le {β n : ℝ} (hβ : 0 < β) (hn : 0 < n) (hL : 1 ≤ Real.log (2 * β * n)) :
    varLog n (kPL β n) ≤ √(Real.log (2 * β * n) / (2 * β * n)) := by
  /-- $\log\kopt = (L - \log L)/(2\beta) \le L/(2\beta)$ since $\log L \ge 0$. -/
  have hL0 : 0 < Real.log (2 * β * n) := by linarith
  unfold varLog
  rw [log_kPL hβ hn hL0]
  apply Real.sqrt_le_sqrt
  have hlogL := Real.log_nonneg hL
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos hβ hn, mul_nonneg hlogL (by positivity : (0:ℝ) ≤ 2 * β * n)]

@[blueprint "lem:log-two-beta-n-bounds"
  (statement := /-- For $\beta > 0$ and $\log n \ge \max\{1, 2|\log 2\beta|\}$:
    $\tfrac12\log n \le \log(2\beta n) \le (1 + |\log 2\beta|)\log n$. -/)]
theorem log_two_beta_mul_bounds {β n : ℝ} (hβ : 0 < β) (hn : 0 < n) (h1 : 1 ≤ Real.log n)
    (h2 : 2 * |Real.log (2 * β)| ≤ Real.log n) :
    Real.log n / 2 ≤ Real.log (2 * β * n) ∧
      Real.log (2 * β * n) ≤ (1 + |Real.log (2 * β)|) * Real.log n := by
  /-- $\log(2\beta n) = \log 2\beta + \log n$ and $-|c| \le c \le |c| \le |c|\log n$. -/
  rw [Real.log_mul (by positivity) hn.ne']
  have := le_abs_self (Real.log (2 * β))
  have := neg_abs_le (Real.log (2 * β))
  constructor
  · linarith
  · nlinarith [abs_nonneg (Real.log (2 * β))]

@[blueprint "lem:eventually-pl"
  (statement := /-- For $\beta > 0$, eventually in $n$:
    $\sqrt{1/(4\beta)}\sqrt{\log n/n} \le \gen(\kopt,n)
      \le 2\sqrt{(1 + |\log 2\beta|)/(2\beta)}\,\sqrt{\log n/n}$. -/)]
theorem eventually_PL_bounds {β : ℝ} (hβ : 0 < β) :
    ∀ᶠ n : ℝ in atTop,
      √(1 / (4 * β)) * ratePL n ≤ genBound (biasPoly β) varLog n (kPL β n) ∧
      genBound (biasPoly β) varLog n (kPL β n) ≤
        2 * √((1 + |Real.log (2 * β)|) / (2 * β)) * ratePL n := by
  /-- Both terms are at most $\sqrt{L/(2\beta n)}$ with $L = \log(2\beta n)$
    (\cref{lem:bias-poly-kpl}, \cref{lem:var-log-kpl-le}), the bias term equals it, and
    $\tfrac12\log n \le L \le (1 + |\log 2\beta|)\log n$
    (\cref{lem:log-two-beta-n-bounds}). -/
  filter_upwards [eventually_gt_atTop (0 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Real.tendsto_log_atTop.eventually_ge_atTop (2 * |Real.log (2 * β)|),
    (Real.tendsto_log_atTop.comp (tendsto_id.const_mul_atTop (by positivity : (0:ℝ) < 2 * β)))
      |>.eventually_ge_atTop 1] with n hn h1 h2 hL
  simp only [Function.comp_def, id] at hL
  have hL0 : 0 < Real.log (2 * β * n) := by linarith
  obtain ⟨hlo, hhi⟩ := log_two_beta_mul_bounds hβ hn h1 h2
  have hb := biasPoly_kPL hβ hn hL0
  have hv := varLog_kPL_le hβ hn hL
  have hm : 0 < 2 * β * n := by positivity
  have hup : √(Real.log (2 * β * n) / (2 * β * n)) ≤
      √((1 + |Real.log (2 * β)|) / (2 * β)) * ratePL n := by
    unfold ratePL
    rw [← sqrt_mul_div (by positivity)]
    apply Real.sqrt_le_sqrt
    rw [div_le_div_iff₀ hm hn]
    have : (1 + |Real.log (2 * β)|) / (2 * β) * Real.log n * (2 * β * n) =
        (1 + |Real.log (2 * β)|) * Real.log n * n := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right hhi hn.le
  have hlow : √(1 / (4 * β)) * ratePL n ≤ √(Real.log (2 * β * n) / (2 * β * n)) := by
    unfold ratePL
    rw [← sqrt_mul_div (by positivity)]
    apply Real.sqrt_le_sqrt
    rw [div_le_div_iff₀ hn hm]
    have : 1 / (4 * β) * Real.log n * (2 * β * n) = Real.log n / 2 * n := by field_simp; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hlo hn.le
  unfold genBound
  rw [hb]
  constructor
  · exact hlow.trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  · linarith

@[blueprint "thm:tradeoff-pl"
  (statement := /-- \textbf{PL regime} (\cref{tab:tradeoff}).  Let $\beta > 0$ and
    $\kopt(n) = \bigl(2\beta n/\log(2\beta n)\bigr)^{1/(2\beta)}$.  Then
    $\gen(\kopt,n) = \kopt^{-\beta} + \sqrt{\log\kopt/n} \asymp \sqrt{\log n/n}$
    as $n \to \infty$. -/)]
theorem tradeoff_PL {β : ℝ} (hβ : 0 < β) :
    (fun n => genBound (biasPoly β) varLog n (kPL β n)) =Θ[atTop]
      (fun n => √(Real.log n / n)) := by
  /-- Rescale the lower bound of \cref{lem:eventually-pl} by $\sqrt{1/(4\beta)}^{-1}$ and apply
    \cref{lem:isTheta-of-eventually-bounds} to the function $\sqrt{1/(4\beta)}\,\sqrt{\log n/n}$,
    which is $\Theta(\sqrt{\log n/n})$. -/
  have hc : 0 < √(1 / (4 * β)) := Real.sqrt_pos.2 (by positivity)
  have h1 : (fun n => genBound (biasPoly β) varLog n (kPL β n)) =Θ[atTop]
      (fun n => √(1 / (4 * β)) * ratePL n) := by
    refine isTheta_of_eventually_bounds
      (c := 2 * √((1 + |Real.log (2 * β)|) / (2 * β)) / √(1 / (4 * β)))
      (Eventually.of_forall fun n => mul_nonneg hc.le (Real.sqrt_nonneg _)) ?_
    filter_upwards [eventually_PL_bounds hβ] with n hn
    refine ⟨hn.1, hn.2.trans (le_of_eq ?_)⟩
    field_simp
  have h2 : (fun n => √(1 / (4 * β)) * ratePL n) =Θ[atTop] ratePL :=
    (isTheta_const_mul_left hc.ne').2 (isTheta_refl _ _)
  exact h1.trans h2

@[blueprint "cor:tradeoff-pl-bigO"
  (statement := /-- PL regime, upper bound: $\gen(\kopt,n) = O(\sqrt{\log n/n})$. -/)]
theorem tradeoff_PL_isBigO {β : ℝ} (hβ : 0 < β) :
    (fun n => genBound (biasPoly β) varLog n (kPL β n)) =O[atTop]
      (fun n => √(Real.log n / n)) := by
  /-- The $O$-half of \cref{thm:tradeoff-pl}. -/
  exact (tradeoff_PL hβ).1

/-! ### Ordering of EP and PL -/

@[blueprint "lem:rate-pl-eq"
  (statement := /-- For $n > 1$, $\sqrt{\log n/n} = n^{-1/2}(\log n)^{1/2}$. -/)]
theorem ratePL_eq {n : ℝ} (hn : 1 < n) :
    √(Real.log n / n) = n ^ (-(1 : ℝ) / 2) * Real.log n ^ ((1 : ℝ) / 2) := by
  /-- \cref{lem:rpow-neg-half-mul-rpow} with $\gamma = 1$. -/
  have := rpow_neg_half_mul_rpow_half (γ := 1) (by linarith : (0:ℝ) < n)
    (Real.log_nonneg hn.le)
  rw [Real.rpow_one] at this
  exact this.symm

@[blueprint "rem:tradeoff-ordering-le"
  (statement := /-- \textbf{Ordering note}, first half.  If $\gamma \le 1$ then the EP rate is no
    worse than the PL rate: $n^{-1/2}(\log n)^{\gamma/2} = O(\sqrt{\log n/n})$. -/)]
theorem rateEP_isBigO_ratePL {γ : ℝ} (hγ : γ ≤ 1) :
    (fun n => n ^ (-(1 : ℝ) / 2) * Real.log n ^ (γ / 2)) =O[atTop]
      (fun n => √(Real.log n / n)) := by
  /-- For $\log n \ge 1$, $(\log n)^{\gamma/2} \le (\log n)^{1/2}$. -/
  refine IsBigO.of_bound' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with n hn hL
  rw [ratePL_eq hn]
  change ‖rateEP γ n‖ ≤ ‖rateEP 1 n‖
  rw [Real.norm_of_nonneg (rateEP_nonneg hn.le), Real.norm_of_nonneg (rateEP_nonneg hn.le)]
  unfold rateEP
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL (by linarith))
    (Real.rpow_nonneg (by linarith) _)

@[blueprint "rem:tradeoff-ordering-ge"
  (statement := /-- \textbf{Ordering note}, second half.  If $\gamma \ge 1$ then the PL rate is no
    worse than the EP rate: $\sqrt{\log n/n} = O(n^{-1/2}(\log n)^{\gamma/2})$. -/)]
theorem ratePL_isBigO_rateEP {γ : ℝ} (hγ : 1 ≤ γ) :
    (fun n => √(Real.log n / n)) =O[atTop]
      (fun n => n ^ (-(1 : ℝ) / 2) * Real.log n ^ (γ / 2)) := by
  /-- For $\log n \ge 1$, $(\log n)^{1/2} \le (\log n)^{\gamma/2}$. -/
  refine IsBigO.of_bound' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with n hn hL
  rw [ratePL_eq hn]
  change ‖rateEP 1 n‖ ≤ ‖rateEP γ n‖
  rw [Real.norm_of_nonneg (rateEP_nonneg hn.le), Real.norm_of_nonneg (rateEP_nonneg hn.le)]
  unfold rateEP
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL (by linarith))
    (Real.rpow_nonneg (by linarith) _)

@[blueprint "rem:tradeoff-ordering"
  (statement := /-- \textbf{Ordering note} (\cref{sec:proof.tradeoff}).  The EP and PL balanced
    rates are not uniformly ordered: EP $\lesssim$ PL when $\gamma \le 1$, and PL $\lesssim$ EP
    when $\gamma \ge 1$; for $\gamma = 1$ they coincide up to constants. -/)]
theorem tradeoff_ordering (γ : ℝ) :
    (γ ≤ 1 → (fun n => n ^ (-(1 : ℝ) / 2) * Real.log n ^ (γ / 2)) =O[atTop]
      (fun n => √(Real.log n / n))) ∧
    (1 ≤ γ → (fun n => √(Real.log n / n)) =O[atTop]
      (fun n => n ^ (-(1 : ℝ) / 2) * Real.log n ^ (γ / 2))) := by
  /-- \cref{rem:tradeoff-ordering-le} and \cref{rem:tradeoff-ordering-ge}. -/
  exact ⟨rateEP_isBigO_ratePL, ratePL_isBigO_rateEP⟩

end LeanDeepgen.Tradeoff
