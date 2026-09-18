> **⚠ 2026-09-18 更新:`CurveModel` 的存在性已被证明。**
> 本报告写于 `exists_curveModel_zmod` 尚未有实例时。实例现在有了:
> `Erdos960.Nodal.curveModel`,建在奇异三次曲线 `Z(X² + Y²) = X³` 上,见 `Erdos960/Nodal.lean`。

# 曲线侧报告 —— `Erdos960/Curve.lean`

**日期**:2026-09-18
**本步验收口径**:`Erdos960/Curve.lean` 自身零 `sorry`,`lake build` 退出 0。

> 本文件逐条落盘,边证边写。最终验收命令的真实输出见 §5。

---

## 1. 与 `GATE0.md` 推荐路线的偏差(以及为什么是收紧,不是放松)

闸门 0 批准的路线 (0) 把**两条**论文引理降级为假设:

- Lemma 2.2(`E(ℝ)` 含 `7m` 阶循环子群)
- Lemma 2.3(无四点共线)

**本步发现 Lemma 2.3 根本不必假设 —— 它是共线判据的推论。**

设 `w, x, y, z` 四点两两不同且共线。取子三元组 `{w,x,y}` 与 `{w,x,z}`,两者都共线,
于是判据给出 `w + x + y = 0` 且 `w + x + z = 0`,`add_left_cancel` 立得 `y = z`,矛盾。
全程只用群论,一点几何都没用到。

⇒ `CurveModel` 结构从“`emb` + 单射 + `collinear_iff` + `no_four_collinear`”
**减为**“`emb` + 单射 + `collinear_iff`”,`no_four_collinear` 变成
`CurveModel.no_four_collinear` 定理。**假设集严格变小**,这是相对 `GATE0.md` 的偏差,
方向是收紧。

### 第二处偏差:`exists_curveModel_zmod` 不再是带 `sorry` 的 `theorem`

原 `Curve.lean:153` 是

```lean
theorem exists_curveModel_zmod (m : ℕ) (hm : 0 < m) :
    ∃ M : CurveModel (ZMod (7 * m)), True := by sorry
```

它**没有任何下游消费者**(`Main.lean:47` 的 `erdos960` 把曲线模型作为显式假设
`hcurve` 接收,不调用这条)。一条无人使用、永不打算证的 `sorry` 定理,唯一作用是
让文件的 sorry 计数不为零,同时给人“有一条定理在那里”的错觉。

已替换为**不带证明义务**的命题定义:

```lean
def CurveModelAssumption (m : ℕ) : Prop := Nonempty (CurveModel (ZMod (7 * m)))
```

这**不是** `axiom`(`#print axioms` 抓不到、也不该抓到 —— 因为它根本没有被断言为真)。
缺口仍然完整暴露:`erdos960` 的结论只在给定该假设时成立。诚实性不降反升。

### 本步没有走的路(以及为什么)

本步 prompt 第 4 条要求“在 `AddCircle (1:ℝ)` 侧取 `zmultiples ((1:ℝ)/(7*m))` 再**传回**
`E(ℝ)`”。**这条走不通,理由是闸门 0 已经查证过的**:

Mathlib 的 `WeierstrassCurve.Affine.Point` **连 `TopologicalSpace` 实例都没有**
(`GATE0.md` G0-1,对整个 Mathlib 的检索零命中)。“传回”的含义就是
`E(ℝ) ≅ ℝ/ℤ`,要证它必须先给 `Point` 装拓扑、证明它是拓扑群、再证紧连通一维交换李群
分类定理 —— 这正是用户点名要避开的“现造整个理论”。

闸门 0 的结论原文:“**传回不存在,因为不需要传回**”——
把 `7m` 阶循环子群作为**假设**而非结论,`ℝ/ℤ` 整个消失。本步遵循该结论。
`AddCircle` 侧的见证仍然保留(`addCircle_hasCyclicSubgroup`),作用是**反空转**:
证明 `HasCyclicSubgroupOfOrder` 这个接口是可满足的,不是空假设。

---

## 2. 证明结构(`Curve.lean` 的声明清单)

文件 482 行,31 个对外声明,零 `sorry`。

### 2.1 循环子群接口(论文 Lemma 2.2 的**结论**)

| 声明 | 内容 |
|---|---|
| `HasCyclicSubgroupOfOrder G M` | `∃ g : G, addOrderOf g = M` |
| `zmod_hasCyclicSubgroup` | 反空转见证 #1:`ZMod (7m)` 满足之 |
| `addCircle_hasCyclicSubgroup` | 反空转见证 #2:`AddCircle (1:ℝ)` 满足之 |

两个见证互不相干,证明接口不绑死在任何一侧 —— 这是闸门 0 的要求。

### 2.2 `CurveModel`:**只剩一个**非结构性字段

```lean
structure CurveModel (G : Type*) [AddCommGroup G] where
  emb           : G → ℝ × ℝ
  emb_injective : Function.Injective emb
  collinear_iff : ∀ x y z : G, x ≠ y → y ≠ z → x ≠ z →
    (Collinear ℝ ({emb x, emb y, emb z} : Set (ℝ × ℝ)) ↔ x + y + z = 0)
```

`no_four_collinear` 原本是第四个字段,本步降为定理(见 §1)。

### 2.3 群侧小引理

`third x y := -(x + y)`;`sum_third : x + y + third x y = 0`;
`third_eq_iff : x + y + z = 0 ↔ third x y = z`(把判据的右边换成“`z` 就是第三点”)。

### 2.4 主链路(本步工作量所在)

| 声明 | 内容 | 关键步骤 |
|---|---|---|
| `CurveModel.mem_line_iff` | `emb z ∈ line[ℝ, emb x, emb y] ↔ third x y = z`(三点两两不同) | 判据的“点在直线上”形态。← 方向用 `collinear_insert_of_mem_affineSpan_pair` 得三元组共线再套判据;→ 方向用 `Collinear.mem_affineSpan_of_mem_of_ne` |
| **`CurveModel.no_four_collinear`** | **论文 Lemma 2.3**,由假设升级为定理 | 取子三元组 `{w,x,y}`、`{w,x,z}` 各套一次判据,`add_left_cancel` |
| `collinear_coe_of_isLine` | 直线的载体集合共线 | `AffineSubspace.direction_eq_vectorSpan` + `direction_affineSpan` + `collinear_pair` |
| **`CurveModel.ordinaryLine_iff`** | **Prop 2.4 的归约,几何 ⇄ 群论主桥** | 先建辅助 `hmem`:`ℓ_xy` 上的 `A`-点恰是 `x`、`y`、以及可能的 `third x y` 的像。→ 方向:若三者互异且都在 `S` 里则 `ncard ≥ 3 ≠ 2`;← 方向:点集恰为 `{emb x, emb y}`,`Set.ncard_pair` |
| `CurveModel.noKCollinear_pts` | Lemma 2.3 ⇒ `NoKCollinear`(`k ≥ 4`) | 反设 `ncard > 3`,`Set.three_lt_ncard` 取四点,拉回原像,套 `no_four_collinear` |

`ordinaryLine_iff` 的右边 `third x y ∉ S ∨ third x y = x ∨ third x y = y`
与 `Combinatorial.ordAdj` 的析取式**逐字相同**(`Combinatorial.lean:180-182`,
`ordAdj S x y := x ≠ y ∧ (-(x+y) ∉ S ∨ -(x+y) = x ∨ -(x+y) = y)`),
第 5 步的 `Bridge.edgeCount_eq_ord` 可以直接消费。

### 2.5 剩余假设

`CurveModelAssumption m := Nonempty (CurveModel (ZMod (7 * m)))` —— 见 §1。

---

## 3. 用到的 Mathlib 声明全名(全部经 `lake build` 真实 elaboration)

**仿射几何 / 共线**

- `Collinear`(`Mathlib/LinearAlgebra/AffineSpace/FiniteDimensional.lean:459`)
- `Collinear.subset`(同上 `:480`)
- `Collinear.mem_affineSpan_of_mem_of_ne`(同上 `:629`)
- `collinear_pair`(同上 `:559`)
- `collinear_insert_of_mem_affineSpan_pair`(同上 `:665`)
- `left_mem_affineSpan_pair` / `right_mem_affineSpan_pair`
  (`Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Defs.lean:1077` / `:1081`)
- `AffineSubspace.direction_eq_vectorSpan`(同上 `:263`)
- `direction_affineSpan`(同上 `:515`)

**基数**

- `Set.ncard_pair`(`Mathlib/Data/Set/Card.lean:744`)
- `Set.ncard_eq_three`(同上 `:1375`)
- `Set.ncard_le_ncard`(同上 `:655`)
- `Set.three_lt_ncard`(同上 `:1344`)
- `Finset.card_image_of_injective`、`Finset.card_le_card`(`Mathlib/Data/Finset/Card.lean:66`)
- `Multiset.toFinset_card_le`(同上 `:192`)

**群论 / `ZMod` / `AddCircle`**

- `ZMod.addOrderOf_one`、`AddCircle.addOrderOf_period_div`、`add_left_cancel`

**椭圆曲线**

- `WeierstrassCurve`(`Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:77`)
- `WeierstrassCurve.Δ`(同上 `:132`)、`b₂`/`b₄`/`b₆`/`b₈`(`:101`–`:113`)
- `WeierstrassCurve.Affine.equation_iff`
- `WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero`
  (`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean:243`)

**多项式**

- `Polynomial.card_roots'`(`Mathlib/Algebra/Polynomial/Roots.lean:80`)
- `Polynomial.mem_roots`(同上 `:110`)
- `coeff_add` / `coeff_C_mul` / `coeff_X_pow` / `coeff_C` / `coeff_X`、`compute_degree` 策略

---

## 4. 具体曲线 `y² = x³ − x + 1` 侧做到了哪里(`Concrete` 命名空间)

主定理**用不到**这一节。它的作用是把永久缺口**精确定位**:证明“除了 Lemma 2.2,
其余都不是 Mathlib 的障碍”。

| 声明 | 内容 |
|---|---|
| `E` | `a₁ = a₂ = a₃ = 0`、`a₄ = −1`、`a₆ = 1` 的 `WeierstrassCurve ℝ` |
| `E_Δ` | `E.Δ = -368` |
| `E_Δ_eq_sixteen_mul_paper` | `E.Δ = 16 * (−4a₄³ − 27a₆²)` |
| `paper_discriminant` | `−4a₄³ − 27a₆² = −23`(论文写的那个数) |
| `E_Δ_ne_zero` | `E.Δ ≠ 0` |
| `E_nonsingular` | 曲线上每点非奇异 ⇒ `Point.instAddCommGroup` 可用 |
| `E_equation_iff` | `Equation x y ↔ y² = x³ − x + 1` |
| `lineCubic` + `lineCubic_eval` | 直线代入曲线得到的三次式,及**展开正确性的机器核对** |
| `lineCubic_natDegree_le` / `_coeff_three` / `_coeff_two` / `_ne_zero` | 次数 ≤ 3 且非零多项式 |
| **`card_le_three_of_line`** | **论文 Lemma 2.3 对具体曲线**:任何仿射直线与 `E(ℝ)` 至多交 3 点 |

### ⚠ 判别式的符号约定换算(论文 `−23` vs Mathlib `−368`)

论文把 `y² = x³ + a₄x + a₆` 的判别式写作 `−4a₄³ − 27a₆²`,代入得
`−4(−1)³ − 27·1² = 4 − 27 = −23`。

Mathlib 的 `WeierstrassCurve.Δ` 用的是 LMFDB 归一化。对 `a₁ = a₂ = a₃ = 0`:

```
b₂ = a₁² + 4a₂        = 0
b₄ = 2a₄ + a₁a₃       = −2
b₆ = a₃² + 4a₆        = 4
b₈ = … − a₄²          = −1
Δ  = −b₂²b₈ − 8b₄³ − 27b₆² + 9b₂b₄b₆
   = 0 − 8(−8) − 27(16) + 0 = 64 − 432 = −368
```

即 `Δ_mathlib = −368 = 16 × (−23) = 16 × Δ_paper`。**两者同时为零**,所以论文的
“`−23 ≠ 0` ⇒ 光滑”与 Lean 里的 `E_Δ_ne_zero` 是同一件事。换算本身也被机器核对了
(`E_Δ_eq_sixteen_mul_paper`),不靠注释里的口算。

### Lemma 2.3 为什么走代数而不是 Bézout

论文用 Bézout 定理。Mathlib **没有交叉重数理论**,现造是数月级工程。
代数路线:把直线参数化为 `t ↦ (p₁ + t d₁, p₂ + t d₂)`,代入 `y² − (x³ − x + 1)` 得
关于 `t` 的三次式 `lineCubic`;曲线点 ⟺ `t` 是它的根;该多项式非零(`d₁ ≠ 0` 时
`X³` 系数为 `−d₁³`,竖直线 `d₁ = 0` 时 `X²` 系数为 `d₂²`)且次数 ≤ 3,
于是根数 ≤ 3(`Polynomial.card_roots'`)。这正是本步 prompt 第 3 条推荐的路线。

---

## 5. 验收命令真实输出

### 5.1 `lake build` + sorry 检查

```
$ lake build 2>&1 | tail -3
warning: Erdos960/Main.lean:45:8: declaration uses `sorry`
warning: Erdos960/Main.lean:110:8: declaration uses `sorry`
Build completed successfully (8930 jobs).

$ grep -rn -F "sorry" Erdos960/Curve.lean || echo "NO-SORRY-IN-CURVE"
NO-SORRY-IN-CURVE

$ grep -c -F "declaration uses 'sorry'" build.log   # 全工程(第 5 步的 10 条)
10

$ grep -F "Curve.lean" build.log | grep -F "sorry" || echo "NO-SORRY-WARNING-FOR-CURVE"
NO-SORRY-WARNING-FOR-CURVE
```

**本步验收口径(`Curve.lean` 自身零 sorry)达成**:源码无 `sorry` 字样,
build 日志中没有任何一条 `Curve.lean` 的 `sorry` 警告。
全工程剩余 10 条全部在 `Defs.lean`(6)、`Bridge.lean`(1)、`Main.lean`(3),归第 5 步。

### 5.2 `#print axioms`(`Axioms.lean`,31 个声明逐条)

```
$ lean Axioms.lean
lean exit: 0

$ grep -c -E "sorryAx" axioms.log
0

$ grep -c "depends on axioms" axioms.log
31

$ grep -vE "\[propext(, Classical\.choice, Quot\.sound)?\]$" axioms.log || echo "(none)"
(none)
```

逐条输出(`axioms.log` 全文):

```
'Erdos960.HasCyclicSubgroupOfOrder' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.zmod_hasCyclicSubgroup' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.addCircle_hasCyclicSubgroup' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.CurveModel' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.third' depends on axioms: [propext]
'Erdos960.sum_third' depends on axioms: [propext]
'Erdos960.third_eq_iff' depends on axioms: [propext]
'Erdos960.CurveModel.pts' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.CurveModel.card_pts' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.CurveModel.emb_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.CurveModel.mem_pts' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.CurveModel.mem_line_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.CurveModel.no_four_collinear' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.collinear_coe_of_isLine' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.CurveModel.ordinaryLine_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.CurveModel.noKCollinear_pts' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.CurveModelAssumption' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.Concrete.E' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.Concrete.E_Δ' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.Concrete.E_Δ_eq_sixteen_mul_paper' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.Concrete.paper_discriminant' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.Concrete.E_Δ_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.Concrete.E_nonsingular' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.Concrete.E_equation_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.Concrete.lineCubic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.Concrete.lineCubic_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.Concrete.lineCubic_natDegree_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.Concrete.lineCubic_coeff_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.Concrete.lineCubic_coeff_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.Concrete.lineCubic_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.Concrete.card_le_three_of_line' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**31/31 全部只依赖 `propext` / `Classical.choice` / `Quot.sound`,零 `sorryAx`,
零自定义 `axiom`。**(`third` 等三条更强,只用到 `propext`。)

---

## 6. 诚实声明(必须随交付一起出现)

本步**没有**证明论文 Theorem 2.1 的完整机器验证,也没有证明
`E : y² = x³ − x + 1` 的实点群含 `7m` 阶循环子群(论文 Lemma 2.2)。

- 已证:共线判据 ⇒ 无四点共线(Lemma 2.3),几何 ⇄ 群论主桥,
  以及具体曲线的判别式非零与“直线至多交 3 点”。
- 仍假设:`CurveModelAssumption` —— 存在阶为 `7m` 的交换群,单射进平面,
  且共线性由群律刻画。它以**显式假设**形式进入 `erdos960` 的签名,不是 `axiom`,
  不是 `sorry`,`#print axioms` 干净。代价是主定理为**条件定理**。

相比闸门 0 批准的路线,假设集**减少了一条**(Lemma 2.3 已成定理)。
