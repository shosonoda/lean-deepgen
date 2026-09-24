# ICLR 原稿に反映すべき修正 (ToDraft.md)

作成日: 2026-09-24．Lean 形式化（[SUMMARY.md](SUMMARY.md)，[PROGRESS.md](PROGRESS.md)）で判明した，原稿 `main-iclr2027.tex` + `06iclr2027/` 側の修正候補．
「必須」= 現在の記述では定理が偽または未定義，「推奨」= 仮定の明示・定数の明示・記述の整合，「任意」= 強化・簡略化の提案．

## Sec. 2–3（設定・主定理）

| # | 箇所 | 種別 | 内容 |
|---|---|---|---|
| D1 | `thm:bv`, `thm:bv-general` | 推奨 | 損失 `ℓ` の可測性，`b > 0`，および仮説クラスの各点有界性（`∀x ∃M ∀f∈ℋ, |f(x)| ≤ M`，または `R̂_S(ℋ) < ∞`）を仮定に明記．sup が非有界だと右辺が無意味になる |
| D2 | `thm:bv-general` (gap) | 任意 | gap 不等式 `L[h] − L̂[h] ≤ …` は η-経験最小化元だけでなく **全ての `f ∈ ℋ`（`h = ι f`）で成立**（証明がそのまま与える）．そう述べた方が強い |
| D3 | `thm:bv` の定数 `C` | 推奨 | 形式化では Rademacher 項は原稿どおり `4β_ℓ R̂_S`（gap `2β_ℓ`），偏差項は明示定数 `6b√(2 log(4/δ)/n)`（gap `3b√(2 log(4/δ)/n)`；`log(4/δ)` は `±ℓ` 各 2 事象の union bound）．「universal constant `C`」のままでもよいが，`log(4/δ)` 型で書けば Lean と一致する |
| D4 | `ass:sg-increment-main` | 推奨 | `d_S(f,g) = 0` の場合の解釈（`Z_f = Z_g` a.s.）は既に記載あり．加えて「各 `Z_f` の sup が有限」を仮定に含める（`H` が標本上で有界なら自動） |
| D5 | `thm:hidden-decomp` | 必須 | 右辺の Dudley 積分が **可積分（有限）** であることを仮定に含めるか，「右辺が `+∞` のとき自明」と明記．Lean の Bochner 積分は非可積分で 0 になるため，仮定なしの literal な写しは偽（反例: `ℓ²` 上の定数写像族で `√log N(ε) ≳ 1/ε`） |
| D6 | `thm:rad.decomp.ent.ent` | 必須 | 同上（可積分性）．さらに被覆数の規約（内部/外部，開球/閉球）で積分のスケールが定数倍変わる（Lean: `x/4, x/(4L_H)` on `[0, B_H/2]`）．「絶対定数のスケール変更を除いて」と断るか，規約を固定して書き直す |
| D7 | `thm:sudakov-type` | 必須 | `R̂_S(ℋ_k) < ∞`（各符号パターンで sup が有界）を仮定に追加．反例: `H = C(X)` 全体だと左辺の sup が発散し不等式が意味を持たない（Lean では 0 になり偽） |
| D8 | `thm:sudakov-type` | 推奨 | packing number が `∞` のときの `sup_ε` の扱い（`log ∞ = ∞` で右辺の min は第 2 項）を一言 |
| D9 | `prop:hilbert-sg` | 任意 | `A_H = 1` は Hilbert 空間値 Rademacher 和の tail `P(‖Σσ_i v_i‖ > t) ≤ 2 exp(−t²/(2Σ‖v_i‖²))`（Pinelis 型）で確認済み．完備性は不要（任意の実内積空間で成立）と書ける．引用 (Pinelis 1994) を付けると親切 |
| D10 | `prop:finite-lipschitz-sg` | 任意 | `A_H = (1 + log m/log 2)^{1/2}` の代数（`min{1, 2m e^{−x}} ≤ 2 e^{−x/A_H²}`）は全ての実 `x` で成立することを確認済み．`m = 0`, `L = 0`, `d_S = 0` の退化ケースも含めて成立 |

## Sec. 4 / App. F（増大度条件）

| # | 箇所 | 種別 | 内容 |
|---|---|---|---|
| D11 | `cond:p1` | 推奨 | 結論の `N(G, ε) < ∞` に加え，(1) の precompact 仮定のみの場合は `X` のコンパクト性が不要．`thm:caa` の逆向き（全有界 ⇒ 等連続）は `H ⊆ C(X,X)` の連続性を明示的に使う |
| D12 | `cond:p1-ucont` (P1') | 必須 | (i) 右辺の有限性には各 `N(F^ℓ, ε) < ∞`（例: `F` が `d_∞` 全有界）が必要で，現状仮定されていない．`ℕ ∪ {∞}` 値として述べるか仮定を追加．(ii) 結論は実は **全ての `k`** で成立（`k ≥ m(ε)` は不要）．(iii) 「compact absorbing set」は有界で十分（タイトルと本文の不整合）．(iv) `A` のコンパクト性は未使用（非空・不変で十分）．(v) `c = 0` の `log_{1/c}` は別扱い（`0 < c` を仮定） |
| D13 | `cond:p2-nilp` (P2) | 推奨 | `k ≥ 1` は不要（`k = 0` でも成立）．定数は `C = C_H max(1, R_S L_α)^D` と明示可能．球のエントロピー仮定 `N(B_H(e,R), δ) ≤ C_H(1+R/δ)^D` は有限性を含意する形で述べる |
| D14 | `cond:e1-free-iso` (E1) | 任意 | 仮定 (1)（語長ごとの単射性 = 自由性）は (2) の一様分離から従うので削除可能 |
| D15 | `cond:e1p-theoremC` (E1') | 必須 | `r` が未定義（`F = {f_1,…,f_r}`, `r ≥ 2` を明記）．等長性と `d_∞` の有限性は下界の証明に不要（E1 と同じ証明） |
| D16 | `cond:e2-pingpong` (E2) | 任意 | 証明は (1) の `Δ` の値を使わず，チャンバーの互いに素性（`Δ > 0`）のみ使う．`V_i ≠ ∅` は (2) から従う |
| D17 | `cond:e3` / `cor:superexp` / `cor:doubleexp` | 必須 | 「十分小さい `ε`」を定量化: `ε < λδ₀/2` かつ `ε < 1/2`（`j = k` の項の半径 `ε/λ` が `k` に依存しないため，`k` を大きくしても `δ_0` 未満にはならない）．`N(W_k) ≤ N(B(2k+1,F))` は被覆数の部分集合単調性（外部被覆数）を使うことを注記 |
| D18 | `cor:superexp` / `cor:doubleexp` | 任意 | 定数を明示可能: superexp `C₁ = c₋ log λ/2`, `C₂ = c₊(log λ − log ε)`, `k₀ = 1`；doubleexp `C₁ = c₋(2ε)^{−p}`, `C₂ = c₊ ε^{−p} q/(q−1)`, `q = λ^p`．`G` のコンパクト性は不要（エントロピー仮定と `N(δ,G) < ∞` のみ）；`G ≠ ∅` は packing 下界から従う |
| D19 | `thm:caa` 系 | 任意 | `thm:pmaa`（擬距離商）は `thm:maa` を擬距離空間で述べれば不要 |

## Sec. 4.2 / Sec. 5（プロファイル・トレードオフ）

| # | 箇所 | 種別 | 内容 |
|---|---|---|---|
| D20 | `prop:profiles` (ii),(iv) | 推奨 | `C₀ ≥ 1`, `D ≥ 0`, `D̄ > 0` を明記（`log C₀ ≥ 0` が必要）．(iii) は `ψ ≥ 0`, `α ≥ 0` 不要 |
| D21 | `tab:profiles` の `d_S ≤ d_∞` 転送 | 推奨 | 内部被覆数は部分集合単調でないため `N(A, d_S, ε) ≤ N^{ext}(A, d_∞, ε/2)` を経由する．結果として P2 の定数に `2^D` が付く（「定数を除いて」で吸収可） |
| D22 | `tab:tradeoff` | 任意 | EL/EP/PL の各 rate は両側 `Θ` で成立し，定数も明示可能（EP: `1 + (2α)^{−γ/2}`，EL: `1 + √(1+|log 2α|)`）．PL の深さは Lambert W なしで `k* = (2βn/log(2βn))^{1/(2β)}` と書け，`k^{2β} log k / n → 1` |
| D23 | balancing principle | 任意 | 「`bias(k*) = var(k*, n)` なら全ての `k` で `gen(k,n) ≥ bias(k*)`，かつ `gen(k*,n) = 2 bias(k*)`」（因子 2 で最適）を補題として述べると PP の最適性が厳密になる |

## 付録の例

| # | 箇所 | 種別 | 内容 |
|---|---|---|---|
| D24 | `prop:implementation` (a) | 推奨 | 有限実装クラスのサイズは `= N(ℋ_k, ε/2)` ではなく `≤ N(ℋ_k, ε/2)`（内部被覆）．`K` のコンパクト性は不要（`ℋ_k` の sup-norm 全有界性と `𝒜` の稠密性のみ） |
| D25 | `prop:implementation` (b) | 任意 | `δ ≥ 0`, `Λ ≥ 0` の明記．表現長 `m ≤ k` の場合の和の単調性に `Λ ≥ 0` を使う |
| D26 | `lem:cot-branch-growth` | 必須 | `Σ_{j≤k} r^j ≤ r^{k+1}` には `r ≥ 2` が必要 |
| D27 | `lem:cot-append-growth` | 任意 | 被覆数の上界は `ε ∈ (0,1]` に限らず全ての `ε > 0` で成立 |
| D28 | `lem:fp-contraction` | 推奨 | `(1 − hμ)`-Lipschitz の証明は強単調性に加え co-coercivity `⟨s x − s y, x − y⟩ ≤ −(μΛ/(μ+Λ))‖x−y‖² − (1/(μ+Λ))‖s x − s y‖²`（強凹＋smooth から従う；Nesterov Thm 2.1.12 相当）を使う．`μ ≤ Λ`, `0 < h ≤ 2/(μ+Λ)` を明記．射影 `Π_K` の性質（像が `K`，`K` 上恒等，1-Lipschitz）を明記 |
| D29 | `lem:ode-saturation` | 任意 | 時刻スタンプの整合性 `τ_i = Σ_{j<i} h_j` は飽和の証明に不要（それを外した上位クラスでも `e^{Λ_s T}`-Lipschitz） |
| D30 | `prop:linear-interpolation` | 任意 | 「`z_{j,i}` が相異なる」仮定は右逆写像の存在仮定に含まれるので削除可能 |
| D31 | `prop:global_scalar_observable` | 推奨 | `R_Φ > 0`（`n = 0` の退化を避ける） |
| D32 | `cor:matching`, `cor:sudakov-rates` (ii) | 推奨 | `k ≥ 1`（`log k ≥ 0`）を明記 |
| D33 | `prop:cot-append`, `prop:ode-fixedpoint`, `prop:ode-horizon` | 任意 | 現状 `≲` の非形式的記述．Lean 側で厳密版（明示定数，`k* = ⌈log n/(2 log(1/θ))⌉` 型の明示深さ）を整備中；確定後に本文へ反映可 |

## 記法・規約

| # | 内容 |
|---|---|
| D34 | 被覆数の規約を一箇所で固定する（形式化: 閉球，半径 `ε`；上界は外部被覆数，下界は内部被覆数 / packing）．内部被覆数は部分集合単調でないことを注意書きに |
| D35 | `B(0,F) = {id}` により `id ∈ ⟨F⟩`（モノイド）である旨を App. F の冒頭で明記（`cor:aa-semigroup-saturation` 等で使用） |
| D36 | `d_∞` は `[0, ∞]` 値として扱えば非コンパクト域の注意書き（Sec. 2「Notation」）は簡略化できる |

## 採用した緩和・強化（PLAN.md §5 の W4–W28；2026-09-24 採用）

Lean 側は以下の一般形で述べる（原稿にも反映する場合の文案）．

| W | 対象 | 原稿への反映案 |
|---|---|---|
| W4 | `thm:hidden-decomp` | 「有限確率空間上の任意の sub-Gaussian 増分過程」に対する Dudley 型定理（定数 12）として述べ，Rademacher 過程 `Z_f` は系にする |
| W5 | `thm:hidden-decomp` | anchor は `F` の任意の点 `f₀` でよく，右辺第 1 項は `R̂_S(H∘f₀)`；`id ∈ F` の場合が原稿の形 |
| W6 | `prop:hilbert-sg` | 「Hilbert 空間」→「実内積空間」（完備性不要）；tail 定数 2 は最良（Pinelis） |
| W7 | `thm:sudakov-type` | `B_k = B(k,F)` → 任意の部分集合 `B ⊆ C(X,X)`（word ball の構造は不使用）；有界クラス版も系として |
| W8 | `thm:rad.decomp.ent.ent` | 標本版（`thm:rad.decomp.ent.ent-sample`）: `H` は到達標本集合 `{f(X_i)}` 上でのみ有界・`L_H`-Lipschitz，被覆数は `H` を各押し出し標本 `f∘S` の経験ノルムで（`f ∈ F` 一様），`F` を `d_S` で取る．結論は `12/√n ∫_0^{B_H/2} (√log N_{S,F}(H, x/4) + √log N(F, d_S, x/(8L_H))) dx`（`F` 側の被覆中心が `F` 内に必要なため内部被覆数経由で係数 2）．sup-norm 版はこの系 |
| W9 | `thm:caa` | 逆向き（全有界 ⇒ 等連続）はコンパクト性不要（連続性のみ）；順向きは `X` 全有界（擬距離）で十分 |
| W10 | `cond:p1` (1) | precompact 仮定のみならコンパクト性不要 |
| W11 | `cond:p1-ucont` | 全ての `k` で成立；`A` は非空・不変のみ；`K` は有界のみ |
| W12 | `cond:p2-nilp` | `k ≥ 0`；結論に直径評価 `D_k(S) ≤ 2 L_α R_S k` を含める |
| W13 | `cond:e1-free-iso` | 自由性 (1) を削除（(2) から従う） |
| W14 | `cond:e1p-theoremC` | 等長性・`d_∞` 有限性・自由性を削除（同長分離のみ） |
| W15 | `cond:e2-pingpong` | (1) を「チャンバーが互いに素」に；`V_i ≠ ∅` は (2) から従う |
| W16 | `cond:e3` 系 | `G` のコンパクト性を削除；`cor:superexp/doubleexp` は `N(δ,G) < ∞`，`ε < λδ₀/2`，`ε < 1/2` を明示 |
| W17 | `cond:e3` (iii) 上界 | `λ ≠ 0`，任意の `ε` で成立 |
| W18 | `prop:profiles` (iii) | `ψ`, `α` の符号条件不要 |
| W19 | `prop:profiles` (i) | `D̄ ≥ 0` |
| W20 | `prop:profiles`「有限 `F`」 | 距離構造不要 |
| W21 | `tab:tradeoff` | EL/EP/PL は両側 `Θ`・定数明示；PP は厳密等式＋全 `k` 下界 |
| W22 | balancing principle | 補題化（`bias(k₀) = var(k₀)` ⇒ `∀k, gen(k) ≥ bias(k₀)`，`gen(k₀) = 2 bias(k₀)`） |
| W23 | `prop:implementation` (a) | `X` 任意；`ℋ_k` sup-norm 全有界と `𝒜` の `ℋ_k` 上稠密性のみ |
| W24 | `prop:implementation` (b) | 連続性不要（既記） |
| W25 | `lem:cot-append-growth` | 全ての `ε > 0` |
| W26 | `lem:ode-saturation` | 時刻整合なしの上位クラスでも飽和 |
| W27 | `prop:linear-interpolation` | `z_{j,i}` 相異なる仮定を削除 |
| W28 | `lem:cot-output` | 窓版 `Φ_L` のみ形式化（`Φ_∞` は未） |

## 反映状況（2026-09-25，ブランチ lean-fixes）

原稿リポジトリ `draft-metric-deep` のブランチ `lean-fixes`（`main` から分岐，4 コミット: Sec. 2–3 hypotheses / growth conditions / profiles and trade-offs / appendix examples）に反映．`latexmk -pdf main-iclr2027.tex` はエラー・未定義参照なし（全 56 ページ，`main` は 54；References は p.13 から，`main` と同じ）．Lean 形式化への言及は Reproducibility statement（`06iclr2027/statements.tex`）に 1 箇所，「companion Lean formalization (URL withheld for anonymity)」として記載．引用 `Pinelis1994`，`Nesterov2004` を `06iclr2027/extra.bib` に追加．

| # | 状況 | ファイル | 備考 |
|---|---|---|---|
| D1 | 反映 | 03bounds.tex, supp-gerror.tex | 可測性，`b>0`，各点有界性（sup-norm 可分も明記）を仮定に追加 |
| D2 | 反映 | 03bounds.tex, supp-gerror.tex | gap 不等式は全ての `f∈ℋ`（`ĥ=ιf`）で成立と明記 |
| D3 | 反映 | 03bounds.tex（脚注）, supp-gerror.tex | 「universal `C`」は維持し，`6b√(2log(4/δ)/n)`（gap: `3b√(2log(4/δ)/n)`）を明示 |
| D4 | 反映 | 03bounds.tex, supp-radent.tex | `Z_f` の有限性を仮定に追加 |
| D5 | 反映 | 03bounds.tex, supp-radent.tex | 積分が発散すれば自明と明記 |
| D6 | 反映 | supp-entent.tex | 可積分性を仮定；外部閉球被覆の規約で `x/4, x/(4L_H)` on `[0,B_H/2]` に書き直し（証明も内部/外部の因子 2 を含めて更新） |
| D7 | 反映 | 03bounds.tex, supp-sudakov.tex | `R̂_S(ℋ_k)<∞`（各符号パターンで有界）を仮定に追加 |
| D8 | 反映 | 03bounds.tex, supp-sudakov.tex | `M=∞` のとき min は第 2 項 |
| D9 | 反映 | supp-radent.tex | 実内積空間（完備性不要），Pinelis (1994) を引用 |
| D10 | 反映 | supp-radent.tex | 全ての実 `x` で成立と注記 |
| D11 | 反映 | supp-growth.tex, supp-cpt-ft.tex | (1) のみならコンパクト性不要；逆向きは連続性のみ使用と注記 |
| D12 | 反映 | supp-growth.tex, 04growth.tex, table-profiles.tex | `ℕ∪{∞}` 値と有限性条件，全ての `k`，bounded absorbing set，`A` は非空・不変，`0<c` |
| D13 | 反映 | supp-growth.tex | `k≥0`，`C=C_H max(1,R_S L_α)^D`，`C_H≥1`，直径評価を結論に含めた |
| D14 | 反映 | supp-growth.tex | 自由性 (1) を削除（結論に「(2) から従う」を注記） |
| D15 | 反映 | supp-growth.tex | `F={f_1,…,f_r}`, `r≥2` を明記；等長性・`d_∞` 有限性・自由性を削除 |
| D16 | 反映 | supp-growth.tex | (1) を「チャンバー互いに素」に；`V_i≠∅` は (2) から；`Δ` は例の注記のみ |
| D17 | 反映 | supp-condE3.tex | `ε<1/2` かつ `ε<λδ₀/2` を明示（証明を書き直し）；部分集合単調性（外部被覆数）を注記 |
| D18 | 反映 | supp-condE3.tex | 定数 `C₁,C₂` 明示，`k₀=1`；`G` 任意部分集合，`N(G,δ)<∞` を仮定 |
| D19 | 反映 | supp-cpt-ft.tex | `thm:maa` を擬距離空間で述べ，`thm:pmaa` はその直接の帰結と注記（環境は残置） |
| D20 | 反映 | 04growth.tex | `C₀≥1`, `D≥0`, `D̄>0`（(ii)），`D₁>0` を明記 |
| D21 | 反映 | supp-profiles.tex, 04growth.tex | 内部被覆数への転送 `N^{int}(A,d_S,ε)≤N(A,d_∞,ε/2)`（`2^D C₀`）を注記 |
| D22 | 反映 | supp-tradeoff.tex | PL 深さを Lambert W なしで（`k*^{2β}log k* = n(1−log L/L)`）；両側 Θ と定数を注記 |
| D23 | 反映 | supp-tradeoff.tex, 05tradeoff.tex | `lem:balancing` を追加，本文で 1 文参照 |
| D24 | 反映 | app-examples.tex, supp-implementation.tex | `≤ N(ℋ_k,ε/2)`（内部被覆），`K` のコンパクト性不要 |
| D25 | 反映 | app-examples.tex, supp-implementation.tex | `δ,Λ≥0` を明記，和の単調性に `Λ≥0` |
| D26 | 反映 | app-cot.tex, 04growth.tex, supp-profiles.tex | `r≥2` を明記（`prop:profiles` (iii) の有限 `F` も同様に修正） |
| D27 | 反映 | app-cot.tex | 全ての `ε>0`（`ℓ(ε):=max{0,⌈…⌉}`） |
| D28 | 反映 | app-ode.tex | 強単調性＋co-coercivity（Nesterov 2004, Thm 2.1.12）で証明を書き直し；`0<μ≤Λ_s`，`Π_K` の性質を明記 |
| D29 | 反映 | app-ode.tex | 時刻整合は不要と注記 |
| D30 | 反映 | supp-sudakov.tex | 相異なる仮定を削除（右逆写像の存在に含まれる；`A_j` 添字を `[n]` 添字に変更） |
| D31 | 既記 | supp-sudakov.tex | 原稿は既に `κ,R_Φ>0` を仮定（変更なし） |
| D32 | 反映 | 03bounds.tex, supp-sudakov.tex | `k≥1` を明記 |
| D33 | 見送り | — | Lean 側の厳密版確定後に反映 |
| D34 | 反映 | 02setting.tex, supp-growth.tex | 規約（閉球・外部；内部は非単調，`N≤N^{int}≤N(ε/2)`）を明記 |
| D35 | 反映 | supp-growth.tex | `id∈⟨F⟩`（モノイド）を明記 |
| D36 | 反映 | 02setting.tex | `d_∞` を `[0,∞]` 値として注意書きを簡略化 |
| W4 | 部分 | supp-radent.tex | 定理は Rademacher 過程のまま；証明中に一般の sub-Gaussian 過程（有限確率空間，定数 12，任意 anchor）で成立する旨を注記 |
| W5 | 反映 | 03bounds.tex, supp-radent.tex | anchor `f₀∈F` 任意，第 1 項 `R̂_S(H∘f₀)`；`id∈F` の場合が原稿の形 |
| W6 | 反映 | supp-radent.tex | 実内積空間；tail 定数 2 は最良（Pinelis） |
| W7 | 反映 | 03bounds.tex, supp-sudakov.tex | 任意の部分集合 `B` で成立と明記（記号 `B_k` は維持） |
| W8 | 部分 | supp-entent.tex | 標本版は remark（`x/4, x/(8L_H)` on `[0,B_H/2]`）として追加；sup-norm 版が主定理のまま |
| W9 | 反映 | supp-cpt-ft.tex | 両方向の必要仮定を注記 |
| W10 | 反映 | supp-growth.tex | D11 と同じ |
| W11 | 反映 | supp-growth.tex | D12 と同じ |
| W12 | 反映 | supp-growth.tex | D13 と同じ |
| W13 | 反映 | supp-growth.tex | D14 と同じ |
| W14 | 反映 | supp-growth.tex | D15 と同じ |
| W15 | 反映 | supp-growth.tex | D16 と同じ |
| W16 | 反映 | supp-condE3.tex | D17/D18 と同じ |
| W17 | 反映 | supp-condE3.tex | (iii) 上界を全ての `ε>0` で（`λ>1` は設定で固定） |
| W18 | 変更なし | 04growth.tex | (iii) に `ψ,α` の符号条件は元々なし |
| W19 | 反映 | 04growth.tex | `D̄≥0` |
| W20 | 変更なし | 04growth.tex | 有限 `F` の主張は距離構造を使っていない |
| W21 | 反映 | supp-tradeoff.tex | 両側 Θ・定数を注記；PP は `lem:balancing` で厳密 |
| W22 | 反映 | supp-tradeoff.tex, 05tradeoff.tex | `lem:balancing` |
| W23 | 反映 | app-examples.tex, supp-implementation.tex | `X` 任意，全有界＋`ℋ_k` 上稠密性のみ |
| W24 | 既記 | supp-implementation.tex | 連続性不要は既に記載（変更なし） |
| W25 | 反映 | app-cot.tex | 全ての `ε>0` |
| W26 | 反映 | app-ode.tex | 時刻整合なしでも飽和 |
| W27 | 反映 | supp-sudakov.tex | `z_{j,i}` 相異なる仮定を削除 |
| W28 | 見送り | — | 原稿は `Φ_∞` 版を維持（Lean 未形式化のため原稿側は変更なし） |
