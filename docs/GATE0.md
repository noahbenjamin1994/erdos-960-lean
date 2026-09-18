# 闸门 0 报告 —— Erdős 960(Theorem 2.1)的 Lean 4 形式化可行性

**日期**:2026-09-17
**目标定理**:arXiv 2604.06609 Theorem 2.1 —— 固定 `r ≥ 3`、`k ≥ 4`、`n ≥ 72`,
则 `F_{r,k}(n) ≥ n²/12 − 10n/3`。
**本步范围**:只验缺口,不写主证明。

---

## VERDICT: PROCEED

三项缺口全部落在“现成”或“可绕开”,**没有任何一项需要现造整个理论**。
最关键的风险点(G0-1 的“传回”)已被证伪 —— 它根本不需要传回,详见下文。

---

## 环境(已固定并实测通过)

| 项 | 值 |
|---|---|
| Lean toolchain | `leanprover/lean4:v4.34.0` |
| Mathlib tag | `v4.34.0`(稳定发布 tag) |
| Mathlib commit | `5ed2965256430c3649e86755f9576b54eca72435` |
| 冷启动实测耗时 | 约 7 分钟(elan + clone + `cache get` + `build`) |
| `.lake` 体积 | 6.7 GB |
| 探针文件 | `.work/erdos-960-lean/lean/Erdos960/Gate0.lean`,**`lake build` 退出 0** |

完整复现命令见 `.work/erdos-960-lean/lean/SETUP.md`。

**探针的证据强度**:`Gate0.lean` 里每一条 `#check` 都是对 Mathlib 的真实 elaboration ——
声明名或类型签名写错,`lake build` 就会失败。文件当前**只有 1 处 `sorry`**(第 274 行),
且那一处是**故意**用来标记“Mathlib 没有这条”的,不是没证出来。
构建输出:`Build completed successfully (8924 jobs)`。

---

## G0-1 `E(ℝ)` 连通 ⇒ 同构于圆群

### 判定:**可绕开**(原始形式为“需现造”,但整条路线不需要它)

### 摸底结论(负面,但已确认)

对 `Mathlib/AlgebraicGeometry/EllipticCurve/` 全目录检索
`TopologicalSpace`、`IsTopologicalAddGroup`、`ContinuousAdd`、`IsConnected`、
`Connected`、`LieGroup`、`Circle` —— **零命中**。
进一步对**整个 Mathlib** 检索 `WeierstrassCurve.*TopologicalSpace` 等模式 —— **零命中**。

> **Mathlib 里 `WeierstrassCurve.Affine.Point` 连拓扑空间实例都没有**,更谈不上李群。
> 它是一个 `inductive`,群结构经 coordinate ring 的理想类群纯代数地建立
> (`toClass_injective` + `AddCommGroup` 实例)。

同时确认 `Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean` 里的 ℘ 函数
**与曲线点群没有任何连接**:该文件检索 `Point`、`WeierstrassCurve`、`AddEquiv`、`≃+`
全部零命中。即 **Mathlib 没有单值化(uniformization)`ℂ/Λ ≅ E(ℂ)`**。

⇒ 按论文 Lemma 2.2 的字面路线(连通 ⇒ 李群同构于圆)在 Mathlib 上**是需现造整个理论**:
要先给 `Point` 装拓扑、证明它是拓扑群、证实紧连通一维交换李群同构于圆。
**这条路必须放弃**,用户批准的绕开是对的。

### 🔴 真风险点的结论:**“传回”不存在,因为不需要传回**

闸门指令担心的是:绕到 `ℝ/ℤ` 侧取 `⟨1/7m⟩` 之后,**把它传回 `E(ℝ)`** 这一步本身
是不是又要现造 `E(ℝ) ≅ ℝ/ℤ`。**答案是不需要,而且理由比预期强。**

Mathlib 有(`Gate0.lean:119`,已 `#check` 通过):

```
zmodAddEquivOfGenerator :
  {G : Type*} → [AddGroup G] → {g : G} → (∀ x, x ∈ AddSubgroup.zmultiples g) →
  {n : ℕ} → Nat.card G = n → (ZMod n ≃+ G)
```

这是**纯群论**的:任何由单个元素生成、阶为 `n` 的加法群都 `≃+ ZMod n`,
不涉及拓扑、分析或 `AddCircle`。配套 simp 引理
`zmodAddEquivOfGenerator_apply_one`(`Gate0.lean:121`)、
`zmodAddCyclicAddEquiv`(`Gate0.lean:120`)同样现成。

**于是圆群在最终开发里根本不必出现。** 论文用“`E(ℝ) ≅ ℝ/ℤ`”只是为了论证
“存在 `7m` 阶循环子群”这一个结论;一旦把它作为**假设**而不是**结论**,
`ℝ/ℤ` 就整个消失了,`ZMod (7m)` 的同构直接由上面这条给出。

探针里已把这个接口写成可编译的定义并给出**两个**互不相干的见证
(`Gate0.lean:131–145`,全部无 `sorry`):

- `HasCyclicSubgroupOfOrder G M := ∃ g : G, addOrderOf g = M`(`Gate0.lean:131`)
- `zmod_hasCyclicSubgroup`:`ZMod (7*m)` 满足之,生成元取 `1`(`Gate0.lean:135`)
- `addCircle_hasCyclicSubgroup`:`AddCircle (1:ℝ)` 也满足之(`Gate0.lean:142`)

**有两个见证是关键**:它证明待形式化的定理不绑死在任何一侧。

### 论文作者本人已授权这一参数化

论文第 150–151 行逐字:

> while we use a specific elliptic curve below for concreteness, **any (non-degenerate)
> elliptic curve suffices** (even in the case of a two-component curve, one just works
> within the component containing the identity).

⇒ 把曲线参数化掉**不是我们偷工**,是原作者明说的构造弹性。

### 三条替代路线的成本评估(按闸门要求逐条给出)

| 路线 | 需要的新理论(不在 Mathlib 里) | 评价 |
|---|---|---|
| **(0) 参数化 + `ZMod` 侧(推荐)** | **零新理论**。`zmodAddEquivOfGenerator` 直接给出 `ZMod (7m)`;共线性改为定义式(见 G0-3)。 | ✅ **推荐**。唯一不需要现造任何东西的路线。 |
| (i) 除法多项式 / `n`-torsion 在 `E(ℝ)` 内造 `7m` 阶元 | `DivisionPolynomial/{Basic,Degree}.lean` **只有多项式 `Ψₙ`、`preΨ`、次数引理,没有任何“`Ψₙ` 的根 ↔ `n`-torsion 点”的定理**(检索 `torsion`/`addOrderOf`/`Nat.card.*Point` 在该目录零命中)。要自己证 `E(ℝ)[n] ≅ (ℤ/n)²` 或至少实数域上的 `ℤ/n`,再证 `7m` 阶元存在。 | ❌ 大工程,数月级 |
| (ii) 装拓扑证 `E(ℝ) ≅ ℝ/ℤ` | 给 `Point` 装拓扑 + 拓扑群 + 紧连通一维交换李群分类。Mathlib 零基础。 | ❌ 最大,不可行 |

### 代价与诚实声明(必须写进 README)

路线 (0) 的代价是:**最终定理不会字面提到 `y² = x³ − x + 1`**。
形式化的是“设 `G` 为含 `7m` 阶循环子群的交换群,且其点集满足无四点共线的几何约束,则……”。
把具体曲线 `E : y² = x³ − x + 1` 实例化进去**仍然缺 Lemma 2.2**(即该曲线的实点群确实含
`7m` 阶循环子群)—— 这一条我们不证,作为**显式假设**留在定理陈述里。

这是一个**真实的范围缩减,不得含糊**:我们交付的是“给定该群论假设,论文第 2 节的组合论证
成立”的机器验证,而不是 Theorem 2.1 的完整机器验证。
这一点必须在 README、论文和任何 credit 主张中**明写**。

---

## G0-2 循环子群存在性可绕开

### 判定:**完全现成**

用到的声明全名与类型签名(全部 `#check` 通过):

| 声明 | 类型签名(要点) | 探针行号 |
|---|---|---|
| `AddCircle` | `{𝕜} → [AddCommGroup 𝕜] → 𝕜 → Type` | `Gate0.lean:84` |
| `AddCircle.addOrderOf_period_div` | `0 < n → addOrderOf ((p / n : 𝕜) : AddCircle p) = n` | `Gate0.lean:85` |
| `AddCircle.addOrderOf_div_of_gcd_eq_one` | `0 < n → m.gcd n = 1 → addOrderOf (↑(↑m / ↑n * p)) = n` | `Gate0.lean:86` |
| `AddSubgroup.zmultiples` | `{G} → [AddGroup G] → G → AddSubgroup G` | `Gate0.lean:87` |
| `Nat.card_zmultiples` | 循环子群的基数 = 元素的阶 | `Gate0.lean:88` |
| `ZMod.card` | `Nat.card (ZMod n) = n`(需 `NeZero n`) | `Gate0.lean:162` |
| `ZMod.castHom` | `n ∣ m → (ZMod m →+* ZMod n)` | `Gate0.lean:164` |
| `ZMod.addOrderOf_one` | `addOrderOf (1 : ZMod n) = n` | `Gate0.lean:165` |
| `zmodAddEquivOfGenerator` | `ZMod n ≃+ G`(见 G0-1) | `Gate0.lean:119` |

**已完整证明的探针(无 `sorry`)**:

- `circle_has_element_of_order`(`Gate0.lean:96`):`addOrderOf ((1/M : ℝ) : AddCircle 1) = M`,
  证明是**单条 Mathlib 引理**。
- `circle_has_cyclic_subgroup_of_order`(`Gate0.lean:103`):Lemma 2.2 的结论部分,直接得。
- `card_zmod_seven_mul`(`Gate0.lean:168`):`Nat.card (ZMod (7*m)) = 7*m`。
- `resid`(`Gate0.lean:174`):`ZMod (7*m) →+* ZMod 7`,即“模 7 剩余类”。
- `Hsub`(`Gate0.lean:178`):`H = ker(resid)`,即论文的 `C₀ = H = ⟨7g⟩`。

**组合核心也已 `decide` 通过**(这几条是 Prop 2.4 二部性的全部内容):

- `multipliers_send_U_to_V`(`Gate0.lean:187`):三个乘子 `−1`、`−2`、`3` 把
  `U = {1,2,4}` 全部送进 `V = {3,5,6}`。
- `neg_two_mul_three`(`Gate0.lean:196`):`(−2) * 3 = 1` in `ZMod 7` ——
  这条解释了为什么第三个关系是 `j ≡ 3i` 而不是 `j ≡ −2i` 的重复。
- `U_union_V` / `U_disjoint_V`(`Gate0.lean:199`、`204`):`U ⊔ V` 恰是非零剩余类。

> 三条都是 `by decide`。`ZMod 7` 上的穷举在 Lean 里是免费的,
> **Prop 2.4 的二部性论证几乎不需要人写证明**。

---

## G0-3 共线 ⟺ 群和为零

### 判定:**Mathlib 无现成引理;但按定义式改写即可绕开(不需现造理论)**

### 摸底结论(负面,已确认)

对 `Mathlib/AlgebraicGeometry/EllipticCurve/` 全目录检索 `Collinear` —— **零命中**。

> Mathlib **没有**把椭圆曲线群律与 `Collinear` 连起来的任何引理。
> 群律是用 `addX` / `addY` / `slope` 公式**定义**的,结合律经 coordinate ring 的
> 理想类群证明;几何陈述“过两点的直线交曲线于第三点”从未与
> `Mathlib.LinearAlgebra.AffineSpace.Collinear` 对接。

### Mathlib 确实给了什么(全部 `#check` 通过,`Gate0.lean:231–249`)

| 声明 | 类型签名(要点) |
|---|---|
| `WeierstrassCurve.Affine.Point` | `inductive`:`zero` 或 `some x y (h : Nonsingular x y)` |
| `WeierstrassCurve.Affine.Point.instAddCommGroup` | **`AddCommGroup W.Point`,对 `F` 为 field 时可用** |
| `Point.add` | `W.Point → W.Point → W.Point`,需 `[Field F] [DecidableEq F]` |
| `Point.add_some` | `¬(x₁ = x₂ ∧ y₁ = negY x₂ y₂) → some + some = some (addX …) (addY …)` |
| `Point.add_of_Y_eq` | `x₁ = x₂ → y₁ = negY x₂ y₂ → some + some = 0` |
| `Point.neg_some` | `-some x y h = some x (negY x y) _` |
| `Affine.slope` | `F → F → F → F → F`(`x₁ x₂ y₁ y₂`),含切线与竖直线分支 |
| `Affine.addX` | `ℓ² + a₁ℓ − a₂ − x₁ − x₂` |
| `Affine.addY` | `negY (addX …) (negAddY …)` |
| `Affine.addPolynomial_slope` | **最接近共线判据的一条**(见下) |
| `Collinear` | `(k) → Set P → Prop`,来自仿射几何,与曲线无关 |

**`Point.instAddCommGroup` 对 `ℝ` 上的曲线确实可用** —— 已确认:实例对任意
`[Field F] [DecidableEq F]` 成立,`ℝ` 二者皆满足(`DecidableEq ℝ` 由 `Classical` 提供)。
⚠ 注意 `Point.add` **需要 `[DecidableEq F]`**,`ℝ` 上是 noncomputable 的,
写代码时要记得 `open Classical` 或显式 `letI`。

### 最接近的一条,以及它差在哪

```
WeierstrassCurve.Affine.addPolynomial_slope :
  W.Equation x₁ y₁ → W.Equation x₂ y₂ → ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂) →
  W.addPolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂) =
    -((X - C x₁) * (X - C x₂) * (X - C (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂))))
```

这**正是**“把斜率为 `ℓ` 的直线代入曲线方程后,三次式恰好分解成这三个 `x` 坐标”——
即“直线与曲线交于这三点、计重数”。但它是关于**多项式分解**的陈述,
不是关于 `Collinear` 的。桥接到 `Collinear ℝ {p, q, r}` 是需要我们自己做的活。

缺失的那条已写成**well-typed 的目标**放在 `Gate0.lean:266`(带 `sorry`,这是全文件唯一一处):

```
Collinear ℝ ({![x₁,y₁], ![x₂,y₂], ![x₃,y₃]} : Set (Fin 2 → ℝ))
  ↔ (Point.some _ _ h₁ + Point.some _ _ h₂ + Point.some _ _ h₃ = 0)
```

它能通过类型检查,说明接口对得上;但 Mathlib 不提供它。

### 绕开方式:把“第三点”改为定义而非推论

论文只在**一个方向**使用该判据:给定 `x, y`,**定义** `z` 为“直线的第三个交点”,
然后用 `x + y + z = O`。如果我们直接**定义** `z := −(x + y)`,那么 `x + y + z = O`
就是 `neg_add_cancel`,**完全免费**。这是合法的,因为 Mathlib 的群律本来就是
按弦切构造定义的 —— `add_some` 的结论里 `addX`/`addY` 就是第三交点取负。

探针 `third_point_sums_to_zero`(`Gate0.lean:284`)已证明该式,`by simp` 一行,无 `sorry`。

于是**几何内容整体迁移到 Lemma 2.3**(任何仿射直线至多含 3 个曲线点)。
而 Lemma 2.3 在参数化路线下**也变成假设**:我们把“无四点共线”作为构型的
组合性质直接假设,不去证 Bézout。

⚠ **这是路线 (0) 的第二处范围缩减**,与 G0-1 的那处同等重要,必须同样明写。

---

## G0-4(自加)最终数值论证是否闭合

这一项不在原闸门清单里,但它决定能不能真的收尾。**全部已证,无 `sorry`**:

| 探针 | 内容 | 行号 |
|---|---|---|
| `key_identity` | `3m² − 3ms = (6m+s)²/12 − (2s/3)(6m+s) + 7s²/12`,`by ring` | `Gate0.lean:303` |
| `final_bound` | `0 ≤ s ≤ 5` ⇒ `3m² − 3ms ≥ n²/12 − (10/3)n`,`by nlinarith` | `Gate0.lean:310` |
| `m_ge_twelve` | `n = 6m+s`、`s ≤ 5`、`n ≥ 72` ⇒ `m ≥ 12`,`by omega` | `Gate0.lean:317` |

⇒ **产生 `1/12` 和 `10/3` 这两个常数的那段代数,在 Lean 里是三行。**
`n ≥ 72 ⟺ m ≥ 12` 也由 `omega` 一行解决。第 2 节最末端的算术**没有风险**。

论文那步代数我也独立核对过:`3m(m−s) = (n−s)(n−7s)/12 = n²/12 − (2s/3)n + 7s²/12`,
与论文一致,放大只丢掉非负项 `7s²/12`。详见 `paper-section2.md`。

---

## 给第 2–4 步的模块切分建议

按“曲线侧 / 组合侧”切开,**接口是一个群论假设,不是一条曲线**。

### `Erdos960/Defs.lean` —— 定义与接口

- `ord(A)`、ordinary-line graph `G_A` 的组合化定义。
  **建议不要用 `ℝ²` 的真直线**,而是用抽象的“第三点函数”`third : G → G → G`,
  `third x y = −(x+y)`。ordinary 判据变成纯群论的
  `ordinary A x y ↔ third x y ∉ A ∨ third x y = x ∨ third x y = y`。
- `F_{r,k}(n)` 的定义,**务必带上 `−1` 的退化约定**(见 `paper-section2.md`)。
  建议返回 `ℤ` 而非 `ℕ`,否则 `−1` 无处安放。
- 接口 `HasCyclicSubgroupOfOrder`(探针已给,`Gate0.lean:131`)。

### `Erdos960/ZModCombinatorics.lean` —— 组合侧(工作量主体,风险最低)

全部在 `ZMod (7*m)` 上,不涉及任何几何:

- 陪集分解 `C = C₀ ⊔ … ⊔ C₆`,用 `resid`(探针已给)的纤维。
- Prop 2.4 的二部性:核心三条 `decide` 探针已通过(`Gate0.lean:187/196/199/204`),
  剩下的是把它们提升到陪集层面。
- Prop 2.4 的计数 `ord(A₀) ≥ 3m²`:三个对偶陪集对各 `m²` 条。
  建议用 `Finset.card_nbij` 之类做双射,不要硬算。
- Prop 2.5 的 `T_s` 分析:`s = 0..5` 六种情形,**`T_s` 里最多 5 个点,
  建议对 `s` 做 `interval_cases` 后逐个 `decide`/`fin_cases`**,
  不要试图找统一论证 —— 论文自己也是“a direct computation”。
- Prop 2.5 (3) 的“每个补点恰毁 `3m` 条边”:对固定 `t`,`x ↦ −t−x` 是
  `C_i → C_{−i}` 的双射,用 `Equiv` 构造。

### `Erdos960/Main.lean` —— 收尾

- `key_identity` / `final_bound` / `m_ge_twelve` 三条已证(`Gate0.lean:303–320`),直接搬。
- 主定理陈述带上两条显式假设(见下)。

### 接口长什么样(建议的主定理签名)

```
theorem erdos960_main
    (G : Type*) [AddCommGroup G]
    (r k n m s : ℕ)
    (hr : 3 ≤ r) (hk : 4 ≤ k) (hn : 72 ≤ n)
    (hns : n = 6 * m + s) (hs : s ≤ 5)
    (hcyc : HasCyclicSubgroupOfOrder G (7 * m))        -- ← 代替 Lemma 2.2
    (hgeom : NoFourCollinear G)                        -- ← 代替 Lemma 2.3
    : (n : ℤ)^2 / 12 - 10 * n / 3 ≤ F r k n
```

两条假设正是我们**不证**的部分,它们把“曲线”整个封装掉了。

---

## 已完成到哪一步 / 未完成什么

**已完成**:

- 论文正文获取(源可达,无降级),第 2 节逐字摘抄落盘为
  `.work/erdos-960-lean/gate0/paper-section2.md`,含全部常数、`−1` 退化约定、
  `n ≥ 72` 的来源(`m ≥ 12` 使 `T_5` 五点互异非零)、`−10n/3` 的来源(补点毁边 `3ms`)、
  以及 `n` 不被 6 整除时的确切补点规则 `T_0..T_5`。
- Lean 4 + Mathlib v4.34.0 环境固定并实测 `lake build` 退出 0。
- 三项(+1 项自加)闸门探针全部**真实编译通过**,唯一 `sorry` 是故意标记缺口的那条。

**未完成(留给后续步骤,均为预期内)**:

- 主证明一行未写 —— 本步明确禁止。
- G0-3 的 `Collinear ⟺ 群和为零` 未证(按路线 (0) 不需要证,改为定义式)。

**没有任何一项需要暂停重规划。**

---

## 遗留风险(按严重度排序,供后续步骤注意)

1. **范围缩减必须全程明写(最重要,非技术风险)。**
   路线 (0) 有两处把论文的引理降级为假设:Lemma 2.2(`hcyc`)与 Lemma 2.3(`hgeom`)。
   最终交付**不是** Theorem 2.1 的完整机器验证。README、论文和 credit 主张中
   必须显式声明,否则是对成果的虚假陈述。
2. **`F_{r,k}(n)` 的 `−1` 约定容易写错。** 定义域要用 `ℤ`;`sSup`/`Finset.max` 在空集上的
   默认值与论文的 `−1` 不一致,必须手工处理空集分支。
3. **`DecidableEq ℝ` 是 noncomputable 的。** `Point.add` 需要它;
   写曲线侧代码时若忘了 `Classical`,会撞上 `failed to synthesize` 而非逻辑错误。
4. **Prop 2.5 的 `T_s` 逐情形验算是体力活。** 六种情形、每种要验“边恰好是这几条”,
   `decide` 在 `ZMod m` 上对一般 `m` **不可用**(`m` 是变量)。
   需要的是“`T_s ⊂ H` 内部的 ordinary 关系只依赖 `h` 的整数系数”这一观察,
   再对系数做有限验算。这是第 3 步的主要工作量,建议单独排一步。

---

## 结论行

**VERDICT: PROCEED**
