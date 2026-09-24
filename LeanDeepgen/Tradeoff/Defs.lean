import Mathlib
import Architect

/-!
# Depth bias–variance trade-offs: definitions

The bias laws, variance profiles, the generalization bound `gen(k, n) = bias(k) + var(k, n)`,
and the balancing depths and balanced rates of the four regimes of Table `tab:tradeoff`
(paper Sec. 5, App. J).  The depth `k` is treated as a positive real.

* bias laws `biasExp α k = e^{-α k}`, `biasPoly β k = k^{-β}`;
* variance profiles `varLog n k = √(log k / n)`, `varPoly γ n k = √(k^γ / n)`;
* balancing depths `kPP`, `kEP`, `kEL`, `kPL` and balanced rates `rateEP`, `rateEL`, `ratePL`.

Mathlib has no Lambert `W` function, so the PL balancing depth is stated directly in the
closed form `k = (2βn / log(2βn))^{1/(2β)}` obtained from `W(x) ∼ log x`.

The theorems (balancing principle, the four regimes, their ordering) are in
`LeanDeepgen.Tradeoff.Regimes`.
-/

namespace LeanDeepgen.Tradeoff

/-! ### The bias laws and variance profiles -/

@[blueprint "def:bias-exp"
  (statement := /-- Exponentially decaying approximation error:
    $\bias(k) = e^{-\alpha k}$, $\alpha > 0$. -/)]
noncomputable def biasExp (α k : ℝ) : ℝ := Real.exp (-α * k)

@[blueprint "def:bias-poly"
  (statement := /-- Polynomially decaying approximation error:
    $\bias(k) = k^{-\beta}$, $\beta > 0$. -/)]
noncomputable def biasPoly (β k : ℝ) : ℝ := k ^ (-β)

@[blueprint "def:var-log"
  (statement := /-- Root-logarithmic estimation profile:
    $\var(k,n) = \sqrt{\log k / n}$ (\cref{prop:profiles}(i)–(ii)). -/)]
noncomputable def varLog (n k : ℝ) : ℝ := √(Real.log k / n)

@[blueprint "def:var-poly"
  (statement := /-- Root-polynomial estimation profile:
    $\var(k,n) = \sqrt{k^{\gamma} / n}$, $\gamma > 0$ (\cref{prop:profiles}(iii)–(iv)). -/)]
noncomputable def varPoly (γ n k : ℝ) : ℝ := √(k ^ γ / n)

@[blueprint "def:gen-bound"
  (statement := /-- The depth-dependent part of the excess-risk bound of \cref{thm:bv}:
    $\gen(k,n) = \bias(k) + \var(k,n)$. -/)]
noncomputable def genBound (bias : ℝ → ℝ) (var : ℝ → ℝ → ℝ) (n k : ℝ) : ℝ :=
  bias k + var n k

/-! ### Balancing depths and balanced rates -/

@[blueprint "def:k-pp"
  (statement := /-- PP balancing depth $\kopt = n^{1/(2\beta+\gamma)}$. -/)]
noncomputable def kPP (β γ n : ℝ) : ℝ := n ^ (1 / (2 * β + γ))

@[blueprint "def:k-ep"
  (statement := /-- EP balancing depth (leading terms):
    $\kopt = \frac{1}{2\alpha}(\log n - \gamma \log\log n)$. -/)]
noncomputable def kEP (α γ n : ℝ) : ℝ := (Real.log n - γ * Real.log (Real.log n)) / (2 * α)

@[blueprint "def:rate-ep"
  (statement := /-- EP balanced rate $n^{-1/2}(\log n)^{\gamma/2}$. -/)]
noncomputable def rateEP (γ n : ℝ) : ℝ := n ^ (-(1 : ℝ) / 2) * Real.log n ^ (γ / 2)

@[blueprint "def:k-el"
  (statement := /-- EL balancing depth (leading terms):
    $\kopt = \frac{1}{2\alpha}(\log n - \log\log\log n)$. -/)]
noncomputable def kEL (α n : ℝ) : ℝ :=
  (Real.log n - Real.log (Real.log (Real.log n))) / (2 * α)

@[blueprint "def:rate-el"
  (statement := /-- EL balanced rate $\sqrt{\log\log n / n}$. -/)]
noncomputable def rateEL (n : ℝ) : ℝ := √(Real.log (Real.log n) / n)

@[blueprint "def:k-pl"
  (statement := /-- PL balancing depth
    $\kopt = \bigl(2\beta n/\log(2\beta n)\bigr)^{1/(2\beta)}$, the leading term of
    $\exp\bigl(W(2\beta n)/(2\beta)\bigr)$ (Lambert $W$, $W(x) \sim \log x$). -/)]
noncomputable def kPL (β n : ℝ) : ℝ := (2 * β * n / Real.log (2 * β * n)) ^ (1 / (2 * β))

@[blueprint "def:rate-pl"
  (statement := /-- PL balanced rate $\sqrt{\log n/n}$. -/)]
noncomputable def ratePL (n : ℝ) : ℝ := √(Real.log n / n)

end LeanDeepgen.Tradeoff
