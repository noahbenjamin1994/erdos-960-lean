# 陈述忠实性报告 —— Erdős 960 Theorem 2.1

第 2 步唯一真正的验收项。三部分:反空转检查、逐条对照、形式化取舍说明。
事实源只有 `.work/erdos-960-lean/gate0/paper-section2.md`(论文第 2 节逐字摘抄)。

环境:Lean 4.34.0 + Mathlib v4.34.0(`5ed2965…`)。
`lake build` **退出 0**,8929 jobs,零 error,除 31 条 `sorry` 外**零 warning**。

---

## 一、反空转检查

形式化最容易出的错是陈述被悄悄变弱或变空。逐项排查:

### 1.1 主陈述的假设不矛盾

`erdos960` 的数值假设是 `3 ≤ r`、`4 ≤ k`、`72 ≤ n`。取 `r = 3`、`k = 4`、`n = 72` 全部成立
(`Main.lean` 的 `example : 3 ≤ 3 ∧ 4 ≤ 4 ∧ 72 ≤ 72`,`by norm_num`,已编译)。
不存在“假设互斥导致定理空真”的情况。

`hcurve` 是唯一的非数值假设。它**可满足**:论文第 2 节证明了真实椭圆曲线
`y² = x³ − x + 1` 满足它(Lemma 2.2 给循环子群,§2.2.1 的弦切构造给共线判据)。
⚠ 本轮更新:Lemma 2.3(无四点共线)**已不在假设内**,它是共线判据的推论,
见下方取舍 (1) 与 `CURVE-REPORT.md`。
另外接口 `HasCyclicSubgroupOfOrder` 本身在 Lean 里有**两个已证见证**
(`zmod_hasCyclicSubgroup`、`addCircle_hasCyclicSubgroup`,均无 `sorry`),
说明它不是一个无人满足的空条件。

### 1.2 结论不平凡 —— `m = 12`、`n = 72` 的数值实例

`#eval` 实测(`lake env lean`,退出 0,输出逐条核对):

| 表达式 | `#eval` 结果 | 说明 |
|---|---|---|
| `(72*72 : ℚ)/12 - 10*72/3` | **`192`** | 论文界在 `n = 72` 处的值 |
| `(73*73 : ℚ)/12 - 10*73/3` | **`803/4`**(= 200.75) | `n = 73` 处 |
| `3*12*12 - 3*12*0` | **`432`** | 构造在 `m=12, s=0` 给出的 `ord(A)` |
| `3*12*12 - 3*12*1` | **`396`** | 构造在 `m=12, s=1` |
| `decide ((0:ℚ) < 72²/12 - 10·72/3)` | **`true`** | 界**为正** |
| `decide (72²/12 - 10·72/3 ≤ 432)` | **`true`** | 构造确实清过界 |

**界是正数(192 > 0),所以结论不是白给的。** 这一点很关键:`F` 的取值域是 `ℤ`,
退化值是 `−1`,若界落在 `≤ −1` 则任何 `F` 都自动满足、定理变空。
`Main.lean` 里 `bound_pos_at_72` 把这条钉死(`by norm_num`,已编译)。

**与论文对得上**:论文 §2.3 说 `n = 6m + s`、`s = 0` 时 `ord(A) ≥ 3m² = n²/12`。
`n = 72` ⇒ `m = 12` ⇒ `3·144 = 432`,而 `n²/12 = 5184/12 = 432`。✔ 完全一致。
再减 `10n/3 = 240` 得 `192`,即论文界比构造实际给出的 `432` 宽松 `240` —— 这个差正是
§2.3 为了统一处理 `s = 0..5` 而丢掉的 `(10/3 − 2s/3)n + 7s²/12`,在 `s = 0` 时等于 `10n/3 = 240`。✔

`n = 73`(`m = 12`、`s = 1`)第二个实例:构造给 `396`,界要 `200.75`,`396 > 200.75`。✔
这个实例**让 `−3ms` 项真正起作用**(`s = 1 ≠ 0`),比 `n = 72` 覆盖面更广。

### 1.3 每条关键引理的非平凡性

| 引理 | 会不会平凡/空转 | 排查结论 |
|---|---|---|
| `ord_A₀_ge : 3m² ≤ edgeCount A₀` | 若 `edgeCount` 定义错成恒大数则空转 | `edgeCount` 定义为 `offDiag.filter(ordAdj) / 2`,上界受 `|A₀|² ` 限制;`3m²` 相对 `|A₀| = 6m` 是 `Θ(|A₀|²)`,是真约束 |
| `card_T : |T s| = s` | `s = 0` 时平凡,`s ≥ 1` 时非平凡 | 论文逐字要求 `m ≥ 12` 才成立,假设已带上;这是 `n ≥ 72` 的唯一来源 |
| `multipliers_send_U_to_V` | 可能 `U`/`V` 写错导致恒真 | **已 `#eval` 实测**:三个乘子作用在 `{1,2,4}` 上分别得 `{6,5,3}`、`{5,3,6}`、`{3,6,5}`,都**恰好**是 `V = {3,5,6}`,不多不少。非平凡且与论文一致 ✔ |
| `neg_two_mul_three` | — | `#eval ((-2 : ZMod 7) * 3)` = **`1`** ✔ 论文据此说第三条关系是 `j ≡ 3i` 而非 `−2i` 的重复 |
| `Aset_bipartite` | 若 `P`/`Q` 允许取 `∅` 则可能退化 | 结论要求 `Aset ⊆ P ∪ Q` **且**每条边跨 `P`/`Q`,`Aset` 非空时强制 `P`、`Q` 非平凡 |
| `le_F` | 若 `F` 定义恒为大数则空转 | `F` 由 `sSup` 定义、`ordValues_bddAbove` 已证有界(`≤ n.choose 2`),不会是 `⊤` |

### 1.4 `F` 没有被定义成恒真的东西

风险:`sSup` 在 `ℕ` 上对空集返回 `0`,若不手工处理空集分支,`F` 会在退化情形给 `0` 而非论文的 `−1`,
且“`F ≥ 正数`”在空集分支会变成假命题(反而不是空转,是**错误**)。
本形式化用 `if (ordValues r k n).Nonempty then ↑(sSup …) else -1` 显式分支,
两侧都与论文一致。`F_ne_neg_one_of_admissible` 记录了“构造排除退化分支”这一义务。

---

## 二、逐条对照:定义 ↔ 论文原文

| Lean 定义 | 位置 | 论文原文(逐字) | 是否忠实 |
|---|---|---|---|
| `IsLine L := ∃ p q, p ≠ q ∧ L = line[ℝ,p,q]` | `Defs.lean:34` | §2.1“lines `ℓ`”(未进一步说明) | ✔ 标准读法,排除空集与单点 |
| `ptsOn A L := ↑A ∩ ↑L` | `Defs.lean:38` | §2.1 `ℓ ∩ A` | ✔ |
| `ordinaryLine A L := IsLine L ∧ (ptsOn A L).ncard = 2` | `Defs.lean:57` | §2.1“the number of lines `ℓ` with **`\|ℓ ∩ A\| = 2`**” | ✔ **恰好** 2,不是 `≤ 2` 或 `≥ 2` |
| `ord A := (ordinaryLines A).ncard` | `Defs.lean:72` | §2.1 `ord(A)` | ✔ 取值 `ℕ`,符合工单 |
| `ordGraph A` | `Defs.lean:86` | §2.1“`V(G_A) = A`,`{p,q} ∈ E(G_A) ⟺ \|ℓ_pq ∩ A\| = 2`” | ✔ 顶点类型是 `↥A`(子类型),邻接即 `ordinaryLine A line[p,q]` |
| `card_edgeFinset_ordGraph` | `Defs.lean:99` | §2.1“so that **`e(G_A) = ord(A)`**” | ✔ 工单点名要求的陈述,已给出 |
| `NoKCollinear A k := ∀ L, IsLine L → (ptsOn A L).ncard ≤ k - 1` | `Defs.lean:119` | §2.1“**`\|ℓ ∩ A\| ≤ k − 1`** for every line `ℓ`” | ✔ `k - 1` 是 `ℕ` 截断减法,但 `k ≥ 4` 下无差别 |
| `Admissible r k A := NoKCollinear A k ∧ (ordGraph A).CliqueFree r` | `Defs.lean:133` | §2.1 两个约束;论文注明所求 `r` 点子集“is precisely a `K_r` in `G_A`” | ✔ 见 §三取舍 (3) |
| `F r k n` | `Defs.lean:150` | §2.1 `F_{r,k}(n) := max ord(A)`;**“If no such configuration exists, set `F_{r,k}(n) = −1`”** | ✔ 退化约定显式实现,codomain `ℤ` |
| `HasCyclicSubgroupOfOrder G M := ∃ g, addOrderOf g = M` | `Curve.lean:47` | Lemma 2.2 结论“contains a cyclic subgroup of order `M`” | ✔ |
| `CurveModel.collinear_iff` | `Curve.lean:83` | §2.2.1“three points `x, y, z ∈ E` are collinear, counted with multiplicity, **iff `x + y + z = O`**” | ✔ 见 §三取舍 (5) |
| `CurveModel.no_four_collinear` | `Curve.lean:173` | Lemma 2.3“every finite subset of `E(ℝ)\{O}` has **no four collinear points**” | ✔ **已升级为定理**(不再是 `CurveModel` 的字段),由 `collinear_iff` 推出 |
| `Concrete.card_le_three_of_line` | `Curve.lean:466` | Lemma 2.3 对具体曲线:任何仿射直线与 `E(ℝ)` 至多交 3 点 | ✔ 已证(代数路线,非 Bézout) |
| `Concrete.E_Δ_ne_zero` | `Curve.lean:376` | Lemma 2.2 光滑性半边“判别式 `−23 ≠ 0`” | ✔ 已证;Mathlib 的 `Δ = −368 = 16 × (−23)`,换算亦经机器核对 |
| `third x y := -(x + y)` | `Curve.lean:106` | §2.2.2“`z` 是 `ℓ_xy` 与 `E` 的第三个交点,`x + y + z = O`” | ✔ 见 §三取舍 (5) |
| `resid m` | `Combinatorial.lean:31` | §2.2.2“`C_i = ig + H`,`i ∈ ℤ/7ℤ`” | ✔ `ZMod.castHom`,`C_i` 是其纤维 |
| `C m i` / `H m` | `Combinatorial.lean:37,42` | §2.2.2“`C = C_0 ⊔ … ⊔ C_6`,`C_0 = H = ⟨7g⟩`,`\|H\| = m`” | ✔ |
| `A₀ := {x \| resid x ≠ 0}` | `Combinatorial.lean:62` | §2.2.2“**`A_0 = C \ H`** = `C_1 ⊔ … ⊔ C_6`,`\|A_0\| = 6m`” | ✔ 即“删掉模 7 余 0 的那一类” |
| `U = {1,2,4}`、`V = {3,5,6}` | `Combinatorial.lean:87,88` | §2.2.2 逐字同值 | ✔ 已 `#eval` 验三乘子 `U → V` |
| `hgen := (7 : ℕ)` | `Combinatorial.lean:159` | §2.2.3“fix a generator `h` of `H`” | ✔ `H = ⟨7g⟩`,`ZMod` 侧生成元即 `7` |
| `T s` | `Combinatorial.lean:177` | §2.2.3 逐字 `T_0 = ∅`、`T_1 = {h}`、`T_2 = {h,2h}`、`T_3 = {h,2h,−3h}`、`T_4 = {h,2h,−3h,3h}`、`T_5 = {h,2h,−3h,3h,−4h}` | ✔ 实现为列表 `[h, 2h, −3h, 3h, −4h]` 取前 `s` 项,**六种情形逐一复现** |
| `Aset s := A₀ ∪ T s` | `Combinatorial.lean:190` | §2.2.3“`A = A_0 ∪ T_s`,`\|A\| = 6m + s = n`” | ✔ |
| `erdos960` | `Main.lean:45` | **Theorem 2.1**“Fix integers `r ≥ 3` and `k ≥ 4` and `n ≥ 72`. Then `F_{r,k}(n) ≥ n²/12 − (10/3)·n`” | ✔ 见下 |

### 主定理陈述并排

论文:

> **Theorem 2.1.** Fix integers `r ≥ 3` and `k ≥ 4` and `n ≥ 72`. Then
> `F_{r,k}(n) ≥ n²/12 − (10/3)·n`.

Lean(`Main.lean:45`):

```lean
theorem erdos960
    (r k n : ℕ) (hr : 3 ≤ r) (hk : 4 ≤ k) (hn : 72 ≤ n)
    (hcurve : ∀ m : ℕ, 0 < m → Nonempty (CurveModel (ZMod (7 * m)))) :
    (n : ℝ) ^ 2 / 12 - 10 * (n : ℝ) / 3 ≤ (F r k n : ℝ)
```

逐项核对:`r ≥ 3` ✔、`k ≥ 4` ✔、`n ≥ 72` ✔、`n²/12` ✔、`10n/3` ✔、不等号方向 ✔
(论文 `F ≥ 界`,Lean `界 ≤ F`,同义)。多出的 `hcurve` 是范围缩减,见 §三取舍 (1)。

---

## 三、有意的形式化取舍

每条都写明**理由**与**代价**。

### (1) 🔴 Lemma 2.2 降级为假设 —— 真实的范围缩减

`hcurve` 断言 `ZMod (7m)` 上存在 `CurveModel`,把论文 Lemma 2.2
(`E(ℝ)` 连通 ⇒ 含 `7m` 阶循环子群)连同 §2.2.1 的共线判据**假设掉**。

✅ **本轮收紧:Lemma 2.3 已从假设中移除。** 原先 `CurveModel` 有一个
`no_four_collinear` 字段;现已证明它是 `collinear_iff` 的推论 ——
若 `w,x,y,z` 四点两两不同且共线,子三元组 `{w,x,y}`、`{w,x,z}` 各套一次判据得
`w+x+y = 0 = w+x+z`,`add_left_cancel` 给出 `y = z`,矛盾。全程纯群论,不用几何。
因此下文关于 Lemma 2.3 的“假设掉”只适用于本轮之前的版本。

**理由**:闸门 0 实测 —— Mathlib 对 `WeierstrassCurve.Affine.Point` **连 `TopologicalSpace` 实例都没有**
(检索 `TopologicalSpace`/`IsConnected`/`LieGroup`/`Circle` 全目录零命中),也**没有**把群律与 `Collinear`
连起来的任何引理(`Collinear` 在椭圆曲线目录零命中)。两条都属于“现造整个理论”,
是用户明确要求**暂停而非硬上**的情形。

**代价(必须明写)**:交付的**不是** Theorem 2.1 的完整机器验证,而是
“给定曲线侧的群论+几何假设,论文 §2.2.2–§2.3 的论证成立”的机器验证。
论文作者授权了“参数化掉具体曲线”(§2.2 逐字:"any (non-degenerate) elliptic curve suffices"),
但**没有**授权省掉 Lemma 2.2 —— 那是我们的取舍,已在 `Curve.lean` 文件头、
`SORRY-LEDGER.md`、`CURVE-REPORT.md` 和 `README.md` 四处标注。

**该假设的形态**:`CurveModelAssumption m := Nonempty (CurveModel (ZMod (7*m)))`,
一个**不被断言为真**的 `def ... : Prop`。它既不是 `axiom` 也不是 `sorry`;
`erdos960` 把它作为显式参数接收,所以全工程 `#print axioms` 干净
(只有 `propext` / `Classical.choice` / `Quot.sound`)。代价是主定理为**条件定理**。

### (2) 用 `Finset` 而非 `Set` 表示点集

**理由**:工单指定;且 `A` 本就是有限 `n` 点集,`Finset` 让 `A.card = n` 直接可写,
计数引理(`Finset.card_nbij` 等)可用。`ord` 的取值按工单为 `ℕ`。

**代价**:`ordinaryLines` 仍是 `Set (AffineSubspace …)`(直线的全体不可枚举),
`ord` 用 `Set.ncard`。`ncard` 对无限集返回 `0`,所以必须另证 `ordinaryLines_finite`
才能保证 `ord` 有意义 —— 这条已作为义务登记在台账(`Defs.lean:68`),不是遗漏。

### (3) 用 `SimpleGraph.CliqueFree r` 表达“无 `r` 点全 ordinary 子集”

**理由**:论文自己做了这个翻译,§2.1 逐字:所求的 `r` 点子集“is precisely a `K_r` in `G_A`”。
用 Mathlib 的 `CliqueFree` 可直接接上 `Colorable.cliqueFree` 等现成引理。

**代价**:`ordGraph A` 的顶点类型是子类型 `↥A` 而非 `A` 本身,`Fintype (edgeSet)` 需
`Fintype.ofFinite`(noncomputable)。纯技术负担,不影响语义。

### (4) 界写在 `ℝ` 上,`F` 落在 `ℤ` 上

**理由**:`n²/12` 与 `10n/3` 一般不是整数(`n = 73` 时为 `803/4`),写在 `ℕ`/`ℤ` 上会被截断除法
悄悄改变含义 —— 这正是“陈述被悄悄变弱”的典型。`F` 落在 `ℤ` 是因为论文的退化值 `−1`
在 `ℕ` 里无处安放(闸门 0 风险点 2)。

**代价**:主定理里出现 `(F r k n : ℝ)` 的 cast。已用 `n = 73` 的数值实例
(`bound_at_73_lt_construction`)确认 cast 后不等式仍是想要的那条。

### (5) 第三点取为**定义** `third x y := −(x+y)`,而非从共线判据推出

**理由**:论文只在一个方向使用共线判据 —— 给定 `x, y`,把 `z` **定义**为第三个交点,再用
`x + y + z = O`。直接定义 `z := −(x+y)` 后该式是 `neg_add_cancel`,免费。
这是合法的:Mathlib 的群律本就按弦切构造定义。

**代价**:几何内容整体迁移到 `CurveModel.ordinaryLine_iff`(`Curve.lean:206`)——
即“`ℓ_xy` 对 `S` ordinary ⟺ 第三点不是 `S` 的另一点”。**该引理现已证明**;
它其实不需要 `no_four_collinear`,只需 `collinear_iff` 本身:线上的 `A`-点要么是 `x`、
要么是 `y`、要么满足 `x+y+z = 0` 即 `z = third x y`,三种可能已穷尽。
`CurveModel` 的 `collinear_iff` 字段仍保留了论文判据的**完整双向**形式,没有偷偷只留弱方向。

### (6) `collinear_iff` 限制在两两不同的三点上

**理由**:论文说“counted with multiplicity”。三点互异时重数概念为空,等价关系就是朴素的
`Collinear ℝ {x,y,z}`;点重合时“计重数共线”需要切线条件,形式化代价大且论文的计数论证
只用互异情形(Prop 2.4 取“不同 `x, y ∈ A_0`”)。

**代价**:形式化的判据比论文原句窄。这一点在 `Curve.lean` 字段注释里写明。
因为它是 `CurveModel` 的**假设**字段(我们要求模型提供的性质),变窄意味着**假设更弱**、
定理更强,不是把定理变弱 —— 方向是安全的。

### (7) `edgeCount` 用有序对折半而非 `Sym2`

**理由**:`offDiag.filter(…).card / 2` 在 `ZMod` 上便于用双射引理做计数(Prop 2.4/2.5 的
`m²` 与 `3m` 都是配对论证)。

**代价**:自然数除法。需要另证“被 filter 的集合基数是偶数”才能保证 `/2` 无截断,
这隐含在 `ordAdj` 的对称性中,属第 3 步义务(`edgeCount_eq_ord`,`Combinatorial.lean:119`)。

---

## 四、结论

- 主陈述 `erdos960` 与论文 Theorem 2.1 **逐项对得上**(常数 `1/12`、`10/3`,阈值 `r ≥ 3`、
  `k ≥ 4`、`n ≥ 72`,不等号方向)。
- 数值实例 `n = 72` 给界 `192 > 0`、构造给 `432`;`n = 73` 给界 `200.75`、构造给 `396`。
  两者都与论文 §2.3 的代数对得上,且界为正 ⇒ **结论非平凡**。
- 定义链 21 项逐条对照完毕,7 处形式化取舍全部写明理由与代价。
- **唯一的实质性缩减是 (1)**:Lemma 2.2(连同共线判据)降级为假设 `hcurve`。
  它不是疏漏,是闸门 0 判定“Mathlib 需现造整个理论”后的既定路线,
  且**必须**在 README 与任何 formalizer credit 主张中同等显著地声明。
  **Lemma 2.3 已不在此列** —— 它现在是定理 `CurveModel.no_four_collinear`,
  且对具体曲线另有独立的代数证明 `Concrete.card_le_three_of_line`。
