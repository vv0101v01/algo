# moon-algebra 🌙 — 有限域上的抽象代數・代數幾何・概形計算庫

以 **MoonBit**（moon 0.1.20261012）寫成的代數結構庫：由 `Ring`/`Field` 特質起步，
沿 `num → linalg → root → finite → modules → geometry → scheme → verify` 依賴鏈
構築 **投射模・循環模・層・凝聚層・剩餘理想・半單/單純/半素理想・坐標環・落特環・
仿射代數簇・概形・局部環・冪等元・正則局部環** 等結構——全部計算留喺**編譯時/零成本抽象**，
成個套件可以當作**依賴**俾你其他 project 用。

---

## 1. 快速接入（作為依賴）

```bash
# 模組內其他 package 直接 import（本 repo 內互相依賴嘅寫法）：
#   import { "moon-algebra"          @poly,    # Ring/Field/Poly/Buchberger/PolyIdeal
#            "moon-algebra/num"       @num,     # IntMod、mod_pos、冪次
#            "moon-algebra/linalg"    @linalg,  # 矩陣 rref/nullspace/solve、向量空間
#            "moon-algebra/finite"    @finite,  # 有限商環 R/I、radical、局部化、冪等元
#            "moon-algebra/modules"   @modules, # 投射/循環/凝聚模、子模枚舉
#            "moon-algebra/geometry"  @geometry,# 仿射簇、坐標環、CRT
#            "moon-algebra/scheme"    @scheme,  # Spec、Zariski 拓撲、結構層、黏合
#            "moon-algebra/hott"      @hott,    # 同倫類型論：Equiv/transport/HIT/衍生定理
#            "moon-algebra/port"      @port,    # 移植流水線：簽名抽取→型別映射→骨架+報告
#            "moon-algebra/verify"    ———       # 形式化證明（moon prove）
```

零成本：所有 trait 實現、特化、有限枚舉都喺編譯期決定；`@num.IntMod`、
`Poly`、`FinAlg` 等皆係 `struct`/`trait` 直譯，運行時無 dictionary boxing。

## 2. 驗證三件套（命題要求）

| 類型 | 位置 | 數量 |
|------|------|------|
| 斷言測試 ✓ | 各 package `*_wbtest.mbt` / `*_test.mbt` | **98** |
| 屬性測試 ✓ | `@quickcheck.check`（root 5・finite 4・modules 3・geometry 1・scheme 2・hott 4・port 3・num/linalg） | 含於 98 |
| 形式化證明 ✓ | `verify/`（`options("proof-enabled": true)` + `.mbtp` 謂詞/引理） | **8 goals 全綠** |

```bash
moon check          # 0 errors / 0 warnings
moon test           # 98/98
./prove.sh          # moon prove → "1 of 1 packages proved, 8 goals proved"
                    # 內部：MOON_PROVE_PRELUDE_OVERRIDE=prelude/ + --why3-config why3-user.conf
```

形式化證明要求 `why3`、`z3`、`cvc5` 三者喺 PATH。證明流水線：
`arith.mbt` 合約 → `moonc-prove` 生成 V.C. → Why3 → Z3 快攻 + `split_vc` + cvc5 收尾。

---

## 3. 定義與算式（Definitions & Formulas）

### 3.1 環・落特環（`ring.mbt`, `moon.mod` warnings 配置）

**定義（環）**：`(R, +, ·)` 為交換環若 `+` 成 Abel 群、`·` 結合且分配於 `+`：
∀a,b,c∈R：`a(b+c) = ab+ac`、`ab = ba`、∃0, ∀a: `a+0=a`。

- `trait Ring` — 公理化 `add/mul/sub/neg/zero/one/is_eq`。
- `struct IntMod[p]` — `ℤ/pℤ`，`a ⊗ b = (a·b) mod p`（`@num.mod_pos` 保代表元 ∈ [0,p)）。
- `trait Field : Ring` — 每非零元可逆：∀a≠0 ∃a⁻¹: `a·a⁻¹ = 1`。

**定義（落特環 / Noetherian）**：理想升鏈穩定——∀ `I₁ ⊆ I₂ ⊆ ⋯` ∃n, Iₙ = Iₙ₊₁ = ⋯。
有限維商環 `R = 𝔽_p[x]/(f)` 自動落特（`zero_dim_quotient` 以 `standard_monomials`
封頂 `p^d ≤ 100000`，dim 上限 64）。

### 3.2 剩餘理想・半素理想・單純/半單（`ideal.mbt`, `finite/ideals.mbt`, `finite/radical.mbt`）

- **剩餘理想（商）**：`R/I` 類 `(a+I)`，`(a+I)(b+I) = ab+I`；`zero_dim_quotient(alg, I)`。
- **根理想（半素）**：`√I = { r ∈ R : rⁿ ∈ I, 某 n ≥ 1 }`；`I` 半素 ⟺ `I = √I`。
  `radical.mbt: radical_basis`、`@finite.nilradical(R) = √(0)`。
- **極大理想**：`I ⋛ R` 極大 ⟺ `R/I` 為域。`@finite.prime_ideals`（有限交換環素=極大）。
- **單純理想/模**：除 0 同自身外無理想；**半單** ⟺ 每個子模都有補（`FinModule::complement_exists`
  — 測試驗證 `semisimple ⟸⟺ 全部 complement_exists`）。
- **冪等元**：`e² = e`；本原冪等元 `e` 不能寫成兩個正交非零冪等元之和。
  `@finite.primitive_idempotents` — `1 = e₁+⋯+eₖ`（正交分解）、`corner(e) = eRe`。
- **芯 socle（新）**：`soc(R) = Ann(J(R))`（`socle(alg)`）——交換 Artin 環中
  `soc(R) ≅ ⊕_i 𝔽_p`（各域分量的單純模直和）；`soc ≠ 0 ⟺ R` 有單純直和項。
- **單純理想判定（新）**：`is_simple_ideal(I)`（理想格中極小非零元）、
  `simple_ideals(alg)`（`{0} ⊊ J ⊊ I` 不存在；有限交換環中單純理想 ≅ 𝔽_p 作為模）。
- **半單 / Wedderburn–Artin（新，定理即程序）**：交換 Artin 環上四者等價：
  `(1) J(R)=0 ⟺ (2) R ≅ ∏ᵢ Fᵢ（有限域直積）⟺ (3) R 模半單 ⟺ (4) 每模投射`。
  `is_semisimple_ring`（J=0 判定）、`wedderburn_fields`（冪等元分塊 + 單塊回退）、
  `is_field_alg`（窮舉可逆）、`is_wedderburn_product`（半單 ∧ 每塊為域 ∧ `Σ dim Fᵢ = dim R`）。

### 3.3 模：投射・循環・層模・凝聚・連續（`modules/`）

- **循環模**：`M = R·x ≅ R/ann(x)`；`FinModule::cyclic(x)`、`annihilator`（由生成集 + 零向量張成求出）。
- **投射模**：`P` 投射 ⟺ `Hom(P, −)` 正合 ⟺ 存在 Q 使 `P ⊕ Q` 自由；
  等價判準（有限情形）：`is_projective(M) ⟺ ∃N, M ⊕ N ≅ Rⁿ`（`hom_space` 求 Hom 維數，
  `is_free/is_projective/is_split_extension`）。
- **凝聚層/凝聚模**：有限表現——`M ≅ coker(Rᵐ → Rⁿ)`（`FinModule::relations` 給出關係格的基）；
  `is_coherent` 驗證有限生成 + 有限關係表現。層版：坐標環層 `O_V` 係凝聚（有限型 `𝔽_p[x₁..xₙ]/I`）。
- **層模**：概形 `X` 上 O_X-模層 `ℱ`：開集 U ↦ 模 `ℱ(U)` + 限制 `ℱ(U) → ℱ(V)` 合函子性；
  我哋喺 `scheme/` 用 stalk `ℱ_x`（局部化）同黏合公理測試體現（`stalks` 測試：∏|𝒪_x| = |R| 即 CRT）。
- **連續模（逆向系統，新）**：`InvSystem{sizes, bonds}`、`limit_threads`（相容線程
  `x_t = bond_t(x_{t+1})`）；**有限塔定理**：投影 `lim → X_{n−1}` 恆雙射（`|lim| = |頂層|`）；
  無限塔（p-adic 完備化 `lim R/Iⁿ`）為其極限——`projection_surjective`/`bond_injective`
  驗證 Mittag-Leffler 性質（全鍵滿射 ⟺ 全投影滿射）。
- **對偶模（新）**：`dual_dim(M) = dim_k Hom_R(M, R)`（`hom_space(M, R)`）；
  **定理**：自由模自對偶 `Hom(Rⁿ, R) ≅ Rⁿ ⇒ dual_dim = n·dim_k R`；
  循環模對偶 `Hom(R/I, R) ≅ Ann(I)`（映射 `φ ↦ φ(1)` 互逆）⇒ `dual_dim = dim_k Ann(I)`
  （`ideal_kdim(annihilator_ideal(I))`，性質測試隨機驗證）——雙對偶於自由/循環層面成立。
- **扭率子模（新）**：`tor(M) = { x : Ann(x) ≠ 0 }`（`torsion_elements`）；
  **定理**：`tor(M)` 為子模、`M/tor(M)` 扭率自由；`free₁ 扭率自由 ⟺ R 無零因子`
  （有限整環 = 域；有冪等元 e 時 `(1−e)·e = 0` 見證非自由扭率）。
- **模層局部化（新）**：`mod_localize_size(M, g)` = `|M_g|`，計算模型
  `M_g = (M × ℕ)/~`，生成元 `(x,k) ~ (g·x,k+1)`（有限圖連通分量 / 集合商 HIT）；
  **定理**：`g=1 ⇒ M_1 ≅ M`（層恆等公理）、`g=0 ⇒ M_0 = 0`、
  `gᵏx = 0 ⇒ [x] = 0`（g-扭率消沒）——`mod_localize_class_of` 給類標記供限制/粘合取用。
- **層公理（沿用+新片段）**：`restriction`、`sheaf_gluing_bijective`（粘合唯一）+
  上面模局部化的 `M_1 ≅ M`、粘合相容性的類標記基礎。

### 3.4 坐標・函數環・仿射代數簇（`geometry/`）

- **坐標**：variety 上點嘅值 `eval: 𝔽_pⁿ ∋ x ↦ (f(x))_f`。
- **仿射代數簇**：`V(S) = { x ∈ 𝔽_pⁿ : f(x)=0, ∀f∈S }`（`variety(gens, bound)`、
  `affine_points(p,n,bound)`，守衛 `p^n ≤ bound`）。
- **函數環（坐標環）**：`O(V) = 𝔽_p[x₁..xₙ]/I(V)`、`I(V) = ∩_{x∈V} m_x`（`vanishing_ideal`）。
  `coordinate_ring` 用 `standard_monomials`（`1` 放 index 0 對齊 `zero_dim_quotient`）。
- **定理（F_p-Nullstellensatz，測試驗證）**：`I(V(I)) = √I` — 例：`I(V(x²,y²)) = (x,y)`，
  即 `x ∈ I(V)` 但 `x ∉ (x²,y²)`（`assert_false(x_poly ∈ gens)`）。
- **定理（CRT / eval 同態，測試驗證）**：`eval_matrix`（點×基）滿秩 ⟺
  `O(V) ≅ ∏_{x∈V} 𝔽_p`；`eval` 係環同態（`eval(a·b) = eval(a)·eval(b)` 逐點成立）。
  例：`𝔽₃` 圓 `x²+y²=1` → 4 點、`dim O(V) = 4`、rank 4；直線 `x=y` + 全平面 `dim = 9`。
- **形式導數（新）**：`Poly::derivative(k)`：`∂(c·x^e)/∂x_k = c·e_k·x^{e−ε_k}`
  （特徵 p 下 `p | e_k` 消失——**Frobenius 定理** `∂(x^p) = 0`，測試驗證）；
  **萊布尼茲** `∂(fg) = ∂f·g + f·∂g`（隨機二元多項式 quickcheck 逐點驗證）、`∂` 為 `𝔽_p`-線性。
- **雅可比與光滑（新，定理即程序）**：`jacobian_matrix(gens, pt) = (∂f_i/∂x_j)(pt)`；
  `smooth_at(gens, pt, dim_v)` ⟺ `pt ∈ V ∧ dim T_pt(V) = nvars − rank J = dim_v`
  （**光滑 ⟺ 正則**：切空間維數 = 幾何維數 = 嵌入維數）；
  `singular_points(gens, bound, dim_v)` = 切空間維數虧損點。
  測試：`𝔽₃` 圓全部光滑（奇異集空）；尖點 `y²−x³` 於原點唯一奇異。

### 3.5 概形・層・局部環・正則局部環（`scheme/`）

- **定義（概形）**：`Spec R = { 素理想 P }` + 由 `D(f) = { P : f ∉ P` } 生成嘅
  Zariski 開集 + 對每開集 U 配函子性層 `O(U)`。
  - `spec(alg)` 枚舉素理想（有限環：`prime_ideals`）；
  - `Spec::is_le(P,Q)` = 包含 `P ⊆ Q`（包含序，代碼真值）；
  - `basic_open(f)`、`opens()`（OR-閉包枚舉，`≤ 2^|Spec|`，31-bit cap）。
- **定理（Zariski 拓撲，測試）**：`∅, Spec ∈ τ`、`|τ| ≤ 2^|Spec|`；
  布爾環 `𝔽₃×𝔽₃`：`|Spec| = 2`、`|τ| = 4`、冪等元 `e = [2,2]` 拆環 `R ≅ Re × R(1−e)`。
- **層公理（限制）**：`restriction(alg, g, h) : O(D(h)) → O(D(g))`，`a/gʲ ↦ a·ι^{-j}`
  （ι = g 在 R_h 可逆）；`D(h) ⊆ D(g)` 先決（否則 `None`）；
  測試：單位元 `h=1` 時係環同態、`D(e) → D(1)`（e≠1 素元）為 `None`。
- **定理（黏合 / Stacks Project，測試）**：`D(h) ⊆ D(f) ∪ D(g)` 時以 `D(hf), D(hg)` 重覆蓋，
  重疊 `D(h²fg)` 上相容嘅截面 ↔ `O(D(h))` 元素**一一對應**
  （`sheaf_gluing_bijective`：`agree_count == |O(D(h))|`，例 9 ↔ 9）。
- **局部環**：`(R, 𝔪)`，`𝔪` 唯一極大理想 ⟺ `R \ 𝔪` 全體可逆。
  `localize_at_element(f)`、`localize_at(P)` — `R_f`；stalk `𝒪_{Spec R, P} = R_P`。
  測試：stalk 皆 `𝔽₃` 域、∏| stalk | = |R|（有限 CRT）。
- **正則局部環**：`m/m²` 作為 k-向量空間（嵌入維數）= dim R；
  測則中以 `k = 1`（正則 ⇔ 嵌入維1 對曲線）同 cusp conductor 對照。
- **冪等元**：`e²=e ⇒ R = eR × (1−e)R`（測試：idempotent 分裂 + `covers_basic`）。
- **Krull 維數（新）**：`Spec::dimension` = 素理想嚴格包含鏈最長度
  （按 `|P|` 拓撲序最長路 DP；空 Spec 回 `−1`）；**定理（Artin）**：有限環
  `dim = 0`（素=極大）——與 `@finite.krull_dim`（理想鏈）交叉驗證相等。
- **不可約分支（新）**：`Spec::irreducible_components` = `⊑`-極小素理想；
  **定理**：分支數 = 準素分解項數；環既約 ⟺ 極小素理想互異覆蓋 `(0)`。
  測試：`𝔽₂[x,y]/(x²,xy,y²)`、`𝔽₃×𝔽₃`、`𝔽₄` 維數 0、分支 = 全部素理想。

### 3.6 同倫類型論層（`hott/` — 深層定義・定理・公理）

**定義（等價）**：`A ≃ B :≡ Σ(f : A→B) isEquiv(f)`；qinv 形：`∃g, f∘g ~ id_B ∧ g∘f ~ id_A`。
程序：`struct Equiv{fwd, bwd}` + 律檢查 `sect_ok`（`bwd∘fwd = id_A`）、`retr_ok`（`fwd∘bwd = id_B`）、
`is_equiv_finite`（有限全域精確）；半伴隨 `HalfAdj{fwd,bwd,η}` + `qinv_to_halfadj ⇄ halfadj_to_qinv`
（qinv ↔ half-adjoint 轉換定理的可計算片段）。

**衍生定理（derivers，定理即程序）**：
- 對稱 `equiv_symm : A ≃ B → B ≃ A`、傳遞 `equiv_trans`、單位 `id_equiv`（群胚結構）；
- 命題演算逐點定理：反證 `contrapose`（`p⟹q ⟺ ¬q⟹¬p`）、蘊涵傳遞、
  雙重否定（布林可判定 `¬¬p ⟺ p`）、De Morgan `¬(p∧q) ⟺ ¬p∨¬q`、`iff` 對稱
  （`contrapose_holds` 等函子 + 隨機遮罩 quickcheck 全域驗證）。
- **transport**：`transport_pred(e, P, a) = P(fwd(a))`（沿等價搬運性質）；
  `ua_beta_holds` = univalence β 規則的可計算投影。

**公理（README 記載，程序層僅用其可計算片段）**：
- **FunExt**：`(∀x, f x = g x) → f = g`；有限載體可驗投影 `funext_finite`（逐點相等 ⟺ 擴展相等）。
- **Univalence (UA)**：`(A = B) ≃ Equiv(A, B)`——`ua(e) := e`；β 由 `ua_beta` 測試。
- **Excluded Middle / Id・J**：`p + ¬p`、`Id(a,b)` 由 `refl` 生成、J 消去
  `J : P(refl) → ∏p:P`；可判定型別上 `Id ≃ Eq`（UIP/K 於集合層成立——
  `int_refl_unique` 見證）。

**HIT 與截斷層級**：
- **S¹**：`{base} + loop`，路徑 = 繞數 `n ∈ ℤ`；路徑複合 `+`、逆 `−`（`s1_groupoid_laws` 驗
  結合/單位/逆）；**定理 π₁(S¹) ≅ ℤ**：`pi1_s1_equiv`（`fwd = loop, bwd = 繞數`，雙向律精確驗證）。
- **集合商 HIT**：`cls : R → Q`、路徑公理 `cls a = cls b ⟺ a−b ∈ I`（`quotient_path`）；
  消去定理 `f̄ ∘ cls = f` ⟺ `f` 在 I-陪集常值（`quotient_rec_ok` 精確判定）。
- **截斷塔** `Contr ⊂ Prop ⊂ Set ⊂ Groupoid ⊂ ⋯`：`is_n` 遞歸定義
  （`isProp` = 路徑空間皆可居；`isSet` = 路徑間道路唯一）；
  見證：`is_prop_elems`（−1 層判定）、`s1_is_set = false`（S¹ 有 `loop⁰ ≠ loop¹` ⇒ 1-型非 0-型）、
  `int_refl_unique`（Int 層 UIP）。

**範疇/伴隨（Hom 形式等價，有限精確）**：
- 乘積伴隨：`Hom(X, Y×Z) ≅ Hom(X,Y) × Hom(X,Z)`（`curry_equiv_holds` 驗雙向 roundtrip）；
- 餘積伴隨：`Hom(Y⊔Z, X) ≅ Hom(Y,X) × Hom(Z,X)`（`coprod_hom_equiv_holds`）；
- `enumerate_functions` = 有限函子空間枚舉（`ny^nx` 封頂 10⁵）。

**既有定理的 HoTT 重寫（`rewrite.mbt`）**：
- **CRT 等價**：`ℤ/n ≅ ∏ ℤ/pᵏ`，`fwd = 取剩餘、bwd = 逐對合併（invmod）`；
  `crt_equiv_holds(n)` 全域 roundtrip 證據（n ≤ 4096 精確）。
- **零化子加法律**：`Ann(I+J) = Ann(I) ∩ Ann(J)`（`ann_sum_law` 判定即證據，
  隨機主理想 quickcheck 驗證）。

### 3.7 移植流水線（`port/` — 其他語言 → MoonBit，核心功能底層）

**定義（pipeline）**：`migrate(src, lang) : MigrationReport` =
逐行簽名抽取（`def/async def`、參數/回傳/行號）→ 型別映射 `map_type(lang, ·)`
→ MoonBit 骨架（`generate_skeleton`：TODO + `abort` 待 AI 填入）+ JSON 報告（`report_json`）。
- **型別映射**：Python `int→Int`、`list[T]→Array[T]`、`Optional[T]→Option[T]`、
  `dict[K,V]→Map[K,V]`、`T | None → Option[T]`；Rust `i32→Int`、`Vec<T>→Array[T]`、
  `&str→String`、`Option<T>→Option[T]`；未知型 → `None`（記入 `unmapped`，骨架以 `Json` 佔位）。
- **定理（映射保持外形）**：`map(lang,T)=Some(u) ⇒ u` 非空合法外形；
  複合型成立 ⟺ 內層成立（結構歸納，property test 驗）。
- **定理（抽取充分性）**：括號同行配對嘅 `def` 恆產出唯一 `FuncSig`（`lineno` 精確、
  行號嚴格不減——property test）；`migrate` 滿足 `mapped ≤ total`、
  `skeleton` 片段數 = `total`、測試函式/`assert` 行獨立搬運（`extract_test_names`、`count_asserts`）。
- 設計邊界：**只做底層演算法與資料結構，不實作 CLI**——上層 AI/CLI 驅動骨架填充與重構。

---

## 4. 形式化證明（`verify/` — 定理清單）

| # | 定理 | 陳述 | 載體 |
|---|------|------|------|
| T1 | 取模代表元 | `p > 0 ⇒ 0 ≤ mod_pos(a,p) < p ∧ a = ((a−r)/p)·p + r` | `mod_pos` 合約 |
| T2 | 帶餘除法 | `p > 0 ⇒ ∃! (q,r): a = q·p + r ∧ 0 ≤ r < p` | `euclid_divmod → Euclid{q,r}` 合約 |
| T3 | 2ⁿ ≥ 1 | `n ≥ 0 ⇒ pow2_rec(n) ≥ 1`（`proof_decrease: n` 終止） | `pow2_rec` 合約 |
| T4 | 快速冪值域 | `p>0 ∧ exp ≥ 0 ⇒ 0 ≤ pow_mod(b,e,p) < p`（`proof_decrease: exp`） | `pow_mod` 合約 |

**設計原則（實測結論）**：定理＝函數合約（`proof_require`/`proof_ensure`/`proof_decrease`），
定義點 V.C. 睇得見自己嘅函數體——呢個係唯一可靠嘅證明來源；後定義函數可引用先者合約。
`#proof_pure` 函數喺 V.C. 中係抽象符號，故唔用佢承載定理。

**自訂證明 prelude**（`prelude/moonbit_builtin_prelude.mlw`，經 `MOON_PROVE_PRELUDE_OVERRIDE`）：
把 stdlib `Computer*` 公理組換成最小截斷除法理論 + `Div_exact`/`Mod_exact`
一步命中規則（`div(y·x, y) = x`、`mod(y·x, y) = 0`），配合 `why3-user.conf`
策略（Z3 快攻 → `split_vc` → Z3 → cvc5），令 8 條 V.C. 全數 discharge。

---

## 5. 測試一覽（98 tests + 8 形式化證明 goals）

- **num** 8：`mod_pos` 值域、冪、CRT 基元。
- **linalg** 8：rref/rank/nullspace/solve、子空間枚舉。
- **root** 18：Ring/Field 公理、多項式、Buchberger、理想成員；導數值/Frobenius/萊布尼茲 quickcheck。
- **finite** 12：商環公理、radical、localisation、冪等元分解；socle/單純/半單/Wedderburn。
- **modules** 13：循環/自由/投射、商模、凝聚、`hom_space` quickcheck×3；對偶維數、扭率、逆極限、模局部化。
- **geometry** 6：圓4點、CRT 滿秩、Nullstellensatz、eval 同態 quickcheck；光滑/奇異/雅可比。
- **scheme** 8：Zariski 拓撲、冪等分裂、限制/黏合、stalk=CRT、quickcheck×2；Spec 維數/分支。
- **hott** 15：等價/半伴隨、transport+UA-β、命題 derivers、FunExt 片段、π₁(S¹)≅ℤ、商 HIT、
  截斷層、CRT 等價、Ann 加法律、伴隨 Hom-等價 + quickcheck×4 + impl/半伴隨往返。
- **port** 10：Python/Rust 型別表、簽名/測試抽取、骨架流水線、JSON 報告 + quickcheck×3。
- **共享測試工具** `testutil/`：`det_rand`/`prop_ring`/`prop_elem`/`is_zero_vec`（原本分散
  4 個測試檔嘅重複定義已收斂到此套件）。
- 形式化證明獨立：`./prove.sh` → 8 goals（T1–T4，見 §4）。

## 6. 模組依賴鏈

```
num ─→ linalg ─→ root(ring/poly/groebner/ideal) ─→ finite ─→ modules ─→ geometry ─→ scheme
                    │                              │          │                      │
                    └──────────────────────────────┴──────────┴──→ hott（Equiv/HIT/derivers）
                    └──────────────────────────────┴──────────┴──→ port（移植流水線，零依賴除外）
                                                                      └────────→ verify (moon prove)
```

## 7. 參考

- MoonBit 驗證：docs.moonbitlang.com/en/stable/language/verification.html
  （`options("proof-enabled")`、`.mbtp` predicate/lemma、`proof_require/ensure/decrease`）
- quickcheck：mooncakes `core/quickcheck`（`check(prop, count?, seed?)`）
- EGA/Stacks Project：Spec、結構層、黏合公理（gluing lemma）
- Atiyah–MacDonald：坐標環、Nullstellensatz、局部化
- Lam, *Serre's Conjecture* / **投射模**；Hungerford 有限半單模判準
- HoTT Book：Equiv、univalence、HIT、截斷層；Rijke *Introduction to HoTT*（π₁(S¹)）
- Wedderburn–Artin、Atiyah–MacDonald Ch.1–3（socle、Ann、局部化）

License: Apache-2.0　|　toolchain: moon 0.1.20261012, moonc-prove + why3 1.8 + z3 4.13.3 + cvc5 1.1.2
