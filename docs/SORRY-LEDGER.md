# SORRY 台账 —— Erdős 960 形式化

**状态:台账已清零。库内 `sorry` 数 = 0。**

```
$ rm -rf .lake/build && lake build          # 39.4 s, 8930 jobs
Build completed successfully (8930 jobs).
$ grep -c -F "declaration uses 'sorry'" build.log
0
$ grep -c -F "sorryAx" axioms.log            # 123 条 #print axioms
0
```

完整、未经编辑的验收输出在 `ACCEPTANCE.md`。本文件保留下来作为**核销记录**:
13 条义务从哪来、被哪一步证掉、以及**哪一条没有被证掉而是变成了显式假设**。

> 计数口径:`lake build` 的 `declaration uses 'sorry'` 警告,逐条核对行号与声明名。
> 历史轨迹:第 2 步 **22** → 第 3 步 **13** → 第 4 步 **10** → 第 5 步 **0**。

---

## 分类汇总(终态)

| 归属 | 条数 | 状态 |
|---|---|---|
| 第 3 步(组合侧,`ZMod (7m)` 上的初等数论) | ~~19~~ → **0** | ✅ 已核销 |
| 第 4 步之曲线侧(`Curve.lean`) | ~~3~~ → **0** | ✅ 已核销 |
| 第 5 步(`Defs.lean` 定义链) | ~~6~~ → **0** | ✅ **本步核销** |
| 第 5 步(`Bridge.lean` 几何 ⇄ 群论桥) | ~~1~~ → **0** | ✅ **本步核销** |
| 第 5 步(`Main.lean` 收尾与主定理) | ~~3~~ → **0** | ✅ **本步核销** |
| **永久缺口(不由任何步骤核销)** | **0 条 `sorry`,1 条显式假设** | 见下 |

---

## 🔴 永久缺口:`CurveModelAssumption`(论文 Lemma 2.2 + 共线判据)

它**不是 `sorry`**,也**不是 `axiom`**,而是一条不带证明义务的命题定义:

```lean
def CurveModelAssumption (m : ℕ) : Prop := Nonempty (CurveModel (ZMod (7 * m)))
```

主定理把它当**显式假设**接收(`Main.lean` 的 `hcurve`),因此:

- `#print axioms Erdos960.erdos960` 只输出 `[propext, Classical.choice, Quot.sound]` ——
  没有偷偷把它断言为真;
- 代价是 `erdos960` 是一条**条件定理**,假设写在签名里,读者一眼可见。

**第 5 步不得、也没有把它算作“已核销”。** README 与 `statement-fidelity.md` 均明写:
交付的是**条件**形式化,不是 Theorem 2.1 的完整机器验证。缺口的具体内容是
“某个 `7m` 阶交换群嵌入平面、且共线性由群律支配”—— 即论文 Lemma 2.2(需要
`E(ℝ) ≅ ℝ/ℤ`,Mathlib 对 `WeierstrassCurve.Affine.Point` 连 `TopologicalSpace`
实例都没有)加上共线判据(Mathlib 无 `Collinear` ⇄ 群律的任何引理)。判定细节见 `GATE0.md`
的 G0-1 / G0-3。

### 缺口比闸门 0 设想的更小:Lemma 2.3 是定理,不是假设

`GATE0.md` 路线 (0) 把 Lemma 2.3 也列为要假设的东西。**它不是。**
`CurveModel.no_four_collinear` 由共线判据单独推出,全程纯群论:
若 `w,x,y,z` 四点两两不同且共线,则 `{w,x,y}` 与 `{w,x,z}` 都共线,判据给出
`w+x+y = 0 = w+x+z`,`add_left_cancel` 得 `y = z`,矛盾。

⇒ 永久缺口从“Lemma 2.2 **+** Lemma 2.3”收缩为“**仅** Lemma 2.2(+ 共线判据)”。
这是相对闸门 0 的偏差,方向是**收紧假设集**。

---

## ✅ 第 5 步核销记录

### `Defs.lean` —— 定义链的基本性质(6 条,全部核销)

| 原位置 | 声明 | 对应论文 | 怎么证的 |
|---|---|---|---|
| `Defs.lean:68` | `ordinaryLines_finite` | §2.1 `ord(A)` 有定义所需 | `ptsOn_injOn` + `Set.Finite.of_finite_image` + `Finite.finite_subsets` |
| `Defs.lean:76` | `ord_le_choose` | 同上;`F` 的上确界有界性依赖它 | `ptsOn_injOn` 打到 `A.powersetCard 2`,`Finset.card_powersetCard` |
| `Defs.lean:101` | `card_edgeFinset_ordGraph` | §2.1 逐字 "so that `e(G_A) = ord(A)`" | `Finset.card_nbij`,双射 `lineOfEdge = Sym2.lift (line[·,·])` |
| `Defs.lean:110` | `cliqueFree_of_isBipartite` | §2.3“二部 ⇒ 无三角 ⇒ 无 `K_r`” | 一行:`IsBipartite` 即 `Colorable 2`,接 `Colorable.cliqueFree` |
| `Defs.lean:157` | `F_eq_of_nonempty` | §2.1 `F` 是 max | `Nat.sSup_mem` + `ordValues_bddAbove` |
| `Defs.lean:163` | `le_F` | §2.3“`A` 合法 ⇒ `F ≥ ord(A)`” | `le_csSup` + `ordValues_bddAbove` |

共同的技术核心是一条新引理 **`IsLine.eq_line_of_mem`**:一条直线等于其上任意两个不同点的
仿射张成(`Collinear.affineSpan_eq_of_ne` + `AffineSubspace.affineSpan_coe`)。由它得到
**`ptsOn_injOn`**(`L ↦ ℓ ∩ A` 在 ordinary 直线上单射),前两条义务都是它的推论。

新增的无 `sorry` 辅助:`ptsOn_subset`、`mem_ordinaryLines`、`ptsOn_eq_pair_of_mem`、
`ordinaryLine.exists_pair`、`ordGraph_adj_iff`、`lineOfEdge`、`lineOfEdge_mk`、
`ptsOn_line_eq_pair_of_adj`、`edge_eq_of_line_eq`、`F_eq_sSup`、`F_eq_neg_one`。

**一处文件边界移动(不是核销)**:`collinear_coe_of_isLine` 从 `Curve.lean` 上移到
`Defs.lean`(`Defs.lean` 自己要用它,而 `Curve.lean` import `Defs.lean`)。
**陈述与证明一字未改**,名字也没变(原声明本就写作 `_root_.Erdos960.collinear_coe_of_isLine`,
现在直接在 `Erdos960` 命名空间里,全名相同),下游零影响。

### `Bridge.lean` —— 几何 ⇄ 群论桥(1 条,核销)

| 原位置 | 声明 | 对应论文 | 怎么证的 |
|---|---|---|---|
| `Bridge.lean:29` | `edgeCount_eq_ord` | 把群侧 `edgeCount` 接到几何 `ord` | 经**有序对**中间量 `ordPairs` 两次 `Finset.card_nbij` |

链条:`edgeCount S = |ordAdj 有序对| / 2 = |ordPairs (M.pts S)| / 2 = 2·e(G_A) / 2 = ord (M.pts S)`。

**`/2` 是精确的**,因为 `ordPairs` 是**有序**计数:每条 ordinary 直线恰好贡献它的两个排序。
台账第 3 步曾把“被 filter 的集合基数是偶数”列为隐含义务(`statement-fidelity.md` §3(7)
的代价一栏),**本步以构造方式消掉了它 —— 不需要任何奇偶性论证**,`omega` 直接闭合。

两个新引理:`card_ordPairs_eq_two_mul`(图侧)、`card_filter_ordAdj_eq`(群侧)。
两个方向的映射都是**全函数**,所以只用 `Finset.card_nbij`,不需要依值的 `Finset.card_bij`。

陈述包括 `[NeZero m]` 在内与第 4 步草稿完全一致(成品证明用不到它,但签名照台账保留,
文件内就地关掉 `linter.unusedSectionVars` 并写明理由)。

### `Main.lean` —— 收尾与主定理(3 条,全部核销)

| 原位置 | 声明 | 对应论文 | 怎么证的 |
|---|---|---|---|
| `Main.lean:24` | `exists_admissible` | Prop 2.5 传到平面 | 见下 |
| **`Main.lean:45`** | **`erdos960`** | **Theorem 2.1 主定理** | §2.3 逐字 |
| `Main.lean:110` | `F_ne_neg_one_of_admissible` | §2.1 退化约定 | 新的 `F_eq_sSup` + `omega` |

`exists_admissible` 的四个分量,以及**两条假设各自落在哪里**:

- `A.card = 6m + s` —— `CurveModel.card_pts`(`emb` 单射)+ `card_Aset`;
- `NoKCollinear A k` —— `CurveModel.noKCollinear_pts`,即论文 Lemma 2.3。
  **`k ≥ 4` 在这里被消耗**:构造里真的存在三点共线(弦与三次曲线交于三点),
  所以它对 `k = 4` 合法、对 `k = 3` 不合法 —— 门槛非装饰;
- `CliqueFree r` —— `Aset_bipartite`(Prop 2.5 (2))沿 `emb` 推到 `↥A` 上的
  `SimpleGraph.IsBipartiteWith`,再接 `cliqueFree_of_isBipartite`。
  **`r ≥ 3` 在这里被消耗**;
- `3m² − 3ms ≤ ord A` —— `ord_Aset_ge`(Prop 2.5 (3))经 `edgeCount_eq_ord`。

`erdos960` 本身:`exists_decomp` 写 `n = 6m + s`(`s ≤ 5`)→ `m_ge_twelve` 得 `m ≥ 12`
(**`n ≥ 72` 在这里被消耗**)→ `exists_admissible` → `le_F` → `final_bound` 丢掉非负松弛
`7s²/12 + (10/3 − 2s/3)n` → `linarith`。

本步**新增**(不是替换)两条,用来把诚实度做实:

- `F_ne_neg_one_of_erdos960_hyps` —— 退化分支在**主定理自己的假设下**被排除,
  而不只是“给定一个合法构型”;
- `erdos960_of_curveModelAssumption` —— 同一条定理,但假设用 `CurveModelAssumption` 命名,
  这样 README 可以指向一个定义,而不是指向签名里的一个假设。

---

## ✅ 第 4 步核销记录(`Curve.lean`,零 sorry)

| 原位置 | 声明 | 对应论文 | 状态 |
|---|---|---|---|
| `Curve.lean:126` | `CurveModel.ordinaryLine_iff` | Prop 2.4 的归约,几何 ⇄ 群论主桥 | ✅ 已证 |
| `Curve.lean:132` | `CurveModel.noKCollinear_pts` | Lemma 2.3 ⇒ `NoKCollinear`(`k ≥ 4`) | ✅ 已证 |
| `Curve.lean:155` | `exists_curveModel_zmod` | Lemma 2.2 + 2.3 | ✅ 已消解:Lemma 2.3 变定理,Lemma 2.2 变显式假设 `CurveModelAssumption`(无 `sorry`) |

其他无 `sorry` 的新结论:`third_eq_iff`、`CurveModel.emb_ne`、`CurveModel.mem_pts`、
`CurveModel.mem_line_iff`、**`CurveModel.no_four_collinear`**(论文 Lemma 2.3,由假设升级为定理)、
`collinear_coe_of_isLine`(本步移入 `Defs.lean`),以及 **`Concrete` 命名空间**:
具体曲线 `y² = x³ − x + 1` 上今天就能从 Mathlib 走通的部分 —— `E_Δ = -368`、与论文 `−23`
的 16 倍换算(`E_Δ_eq_sixteen_mul_paper`)、`E_Δ_ne_zero`、`E_nonsingular`、以及论文
Lemma 2.3 对具体曲线的代数证明 `Concrete.card_le_three_of_line`(走 `Polynomial.card_roots'`
而非 Bézout)。这部分主定理用不到,作用是把缺口**精确定位**到只剩 Lemma 2.2。

---

## ✅ 第 3 步核销记录(`Combinatorial.lean`,零 sorry)

`Erdos960/Combinatorial.lean` 自身零 `sorry`,28 个对外结论的 `#print axioms` 只出现
`propext` / `Classical.choice` / `Quot.sound`(真实输出见 `COMBINATORIAL-REPORT.md` §3.4)。
**无一条陈述被削弱** —— 逐条对照见该报告 §6。

| 原位置 | 声明 | 对应论文 | 状态 |
|---|---|---|---|
| `Combinatorial.lean:45` | `card_C` | §2.2.2 `\|C_i\| = m` | ✅ 已证 |
| `Combinatorial.lean:50` | `C_disjoint` | §2.2.2 `C = C_0 ⊔ … ⊔ C_6` | ✅ 已证 |
| `Combinatorial.lean:54` | `mem_C_iff` | §2.2.2 `C_i` 是 `resid` 的纤维 | ✅ 已证 |
| `Combinatorial.lean:67` | `card_A₀` | §2.2.2 `\|A_0\| = 6m` | ✅ 已证 |
| `Combinatorial.lean:127` | `ordAdj_residues` | Prop 2.4 边分类:`j ≡ −i`、`−2i`、`3i` | ✅ 已证 |
| `Combinatorial.lean:139` | `ordAdj_crosses` | Prop 2.4 二部性:每条边跨 `X`/`Y` | ✅ 已证 |
| `Combinatorial.lean:149` | `ordAdj_of_dual` | Prop 2.4 保证边 | ✅ 已证 |
| `Combinatorial.lean:154` | `ord_A₀_ge` | Prop 2.4 逐字 `ord(A_0) ≥ 3m²` | ✅ 已证 |
| `Combinatorial.lean:163` | `addOrderOf_hgen` | §2.2.3 `addOrderOf h = m` | ✅ 已证 |
| `Combinatorial.lean:166` | `hgen_mem_H` | §2.2.3 `h ∈ H` | ✅ 已证 |
| `Combinatorial.lean:183` | `card_T` | §2.2.3 `\|T_s\| = s`。**`n ≥ 72` 的唯一来源** | ✅ 已证 |
| `Combinatorial.lean:186` | `T_subset_H` | §2.2.3 `T_s ⊂ H` | ✅ 已证 |
| `Combinatorial.lean:195` | `card_Aset` | §2.2.3 `\|A\| = 6m + s = n` | ✅ 已证 |
| `Combinatorial.lean:205` | `no_edge_A₀_T` | Prop 2.5“`A_0` 与 `T_s` 间无边” | ✅ 已证 |
| `Combinatorial.lean:216` | `T_induced_bipartite` | Prop 2.5“`T_s` 内部二部” | ✅ 已证 |
| `Combinatorial.lean:225` | `Aset_bipartite` | Prop 2.5 (2)“`G_A` is bipartite” | ✅ 已证 |
| `Combinatorial.lean:237` | `card_destroyed_by` | Prop 2.5 (3)“每补点恰毁 `m` 条/对偶对” | ✅ 已证 |
| `Combinatorial.lean:242` | `ord_Aset_ge` | Prop 2.5 (3) 逐字 `ord(A) ≥ 3m² − 3ms` | ✅ 已证 |

### `n ≥ 72` 落在哪里

**唯一入口是 `zsmul_hgen_inj (hm : 12 ≤ m)`**:`a•h = b•h` ⇒ `m ∣ (a−b)`,配 `|a−b| < 12 ≤ m`
得 `a = b`。所有消费者(`card_T`、`T_ne_zero`、`T_induced_bipartite`、`card_Aset`、
`Aset_bipartite`、`ord_Aset_ge`)都经由它。已实测:假设削弱成 `0 < m` 后两处 `omega` 均无法
闭合(输出见报告 §3.3),**门槛非装饰**。实际出现的最大差是 `|7 − (−4)| = 11 < 12`。

第 5 步的 `erdos960` 经 `m_ge_twelve` 把 `n ≥ 72` 兑换成 `m ≥ 12`,接到这条上。

---

## 关于 `Gate0.lean`(本步的一处卫生处理,不是核销)

闸门 0 的探针文件 `Erdos960/Gate0.lean` 里有 **1 处真 `sorry`**(第 274 行):一条匿名
`example`,**故意**用来把“Mathlib 没有 `Collinear` ⇄ 群律这条引理”这件事写成一个
类型正确的目标。它不被 `Erdos960.lean` import、不参与 `lake build`(构建日志 0 命中),
所以从来没有进过上面任何一次计数。

但它放在库目录 `Erdos960/` 里,会让 `grep -rn -F sorry Erdos960/` 的输出看起来自相矛盾。
本步把它移到 **`gate0/Gate0Probe.lean`**,与 `GATE0.md` 放在一起 —— 它是闸门 0 的证据,
不是库的一部分,**不进 `output/`**。
