# 第 3 步报告:组合核心 `Erdos960/Combinatorial.lean` 零 sorry

**结论:本步全部 15 个认领条目已核销,`Erdos960/Combinatorial.lean` 自身零 `sorry`,
`lake build` 退出 0。** 全局仍有 4 条 `sorry`,全部在曲线侧(`Curve.lean` 3 条 +
`Bridge.lean` 1 条)和收尾侧(`Main.lean` 3 条),按台账归属第 4 步与永久缺口。

论文常数与陈述全部以 `.work/erdos-960-lean/gate0/paper-section2.md` 为唯一事实源,
**无一处削弱引理陈述**(详见文末“陈述完整性”一节)。

---

## 1. 文件边界的一处调整(必须先说明)

上游 `SORRY-LEDGER.md` 把 `edgeCount_eq_ord` 记在 `Combinatorial.lean:119` 并归属第 4 步。
但本步的验收口径是“`Combinatorial.lean` **自身**零 sorry”,两者直接冲突:该条目按台账
不该由本步证,按验收口径又不该留在本文件里。

处理方式:**把该声明原样移到新文件 `Erdos960/Bridge.lean`,陈述一字未改**,并重连 import
链(`Main.lean` 改 import `Erdos960.Bridge`;`Erdos960.lean` 两者都 import)。理由是它本质
是几何而非组合 —— 它需要 `CurveModel.ordinaryLine_iff`(弦切构造把 `Collinear` 接到群律),
那正是曲线侧的东西。这样文件边界与义务边界重合,归属没有变化,第 4 步仍然要证它。

🔴 **这不是核销。** `edgeCount_eq_ord` 仍是未证条目,只是换了位置。

---

## 2. 证明结构

整条链把“共线”彻底抽象掉:`ordAdj S x y := x ≠ y ∧ (-(x+y) ∉ S ∨ -(x+y) = x ∨ -(x+y) = y)`,
其中 `-(x+y)` 就是第三交点(`x + y + z = O` ⇒ `z = -(x+y)`)。之后全部是 `ZMod (7m)` 上的
初等数论。

### 2.1 陪集簿记(§2.2.2)

- `resid : ZMod (7*m) →+* ZMod 7` 走 `ZMod.castHom (Dvd.intro m rfl)`,**没有手搓取模**。
- `card_C i = m`:先证七个纤维等势(`card_C_eq_card_C_zero`,用平移 `x ↦ x - x₀` 作双射,
  `x₀` 由 `resid` 满射取到),再用 `∑ᵢ |C_i| = 7m` 解出 `|C_0| = m`。
- `card_A₀ = 6m`:`A₀` 与 `H` 是 `resid ≠ 0` / `= 0` 的互补 filter,
  `Finset.card_filter_add_card_filter_not` + `card_H = m`。

### 2.2 二部性 ⇒ 三角自由(Prop 2.4)

**把整个论证压成 4 条 `ZMod 7` 上的可判定命题**,全部 `by decide`:

| 引理 | 内容 |
|---|---|
| `resid_case_notMem` | `-(a+b) = 0 → b = -a`(第三点落在 `H`) |
| `resid_case_eq_fst` | `-(a+a) = -2a`(第三点 `= x`,即 `y = -2x`) |
| `resid_case_eq_snd` | `t = 3·(-(t+t))`(第三点 `= y`,即 `x = -2y` ⇒ `j ≡ 3i`) |
| `bipartite_arith` | `i ≠ 0` 且 `j ∈ {-i, -2i, 3i}` ⇒ `(i∈U ∧ j∈V) ∨ (i∈V ∧ j∈U)` |

⚠ 第三条关系确实是 `j ≡ 3i` 而不是 `j ≡ -2i` 的重复:它来自 `i ≡ -2j`,在 `ZMod 7` 里用
`-2·3 = 1`(`neg_two_mul_three`)解出。这一点按论文 §2.2.2 的警告单独核对过。

`ordAdj_residues` 三分支逐个对上;`ordAdj_crosses` 由它 + `bipartite_arith` 直接得到。
显式二部划分是 `Xpart = {resid ∈ U}`、`Ypart = {resid ∈ V}`,`U = {1,2,4}`、`V = {3,5,6}`。

### 2.3 边数下界 `3m²`(Prop 2.4 计数)

`Dual := (univ.erase 0).biUnion (fun i => C m i ×ˢ C m (-i))`,即六个非零余类的**有序**对偶对。

- `card_Dual = 6m²`:`Finset.card_biUnion`(不同 `i` 的第一坐标余类不同 ⇒ 两两不交)
  + `card_C` 两次。
- `Dual_mem_A₀`:每个对偶对都是 `A₀` 内的 ordinary 对。`x ≠ y` 自动成立,因为
  `i ≠ -i`(7 为奇数,`ne_neg_self` by `decide`)⇒ `C_i` 与 `C_{-i}` 不同。
- `ord_A₀_ge`:`3m² ≤ 6m²/2`。

**这里有一个让整段变短的关键点:不需要任何奇偶性论证。** `edgeCount` 定义成
`card(filter)/2`(ℕ 整除),而 `Nat.le_div_iff_mul_le` 把 `k ≤ N/2` 直接等价成 `2k ≤ N`。
所以“给出 `2k` 个有序对”正好就是需要的东西 —— 无需证 `N` 是偶数。这是 `le_edgeCount`
这条桥引理的全部内容。

### 2.4 规模调整(§2.2.3)

`hgen := (7 : ℕ) : ZMod (7*m)`,`addOrderOf_hgen` 用 `ZMod.addOrderOf_coe` 得
`(7m)/gcd(7m,7) = m`。

`T s` 是列表 `[h, 2h, -3h, 3h, -4h]` 的前 `s` 项。`T_eq_map` 把它改写成 **ℤ 系数**形式
`(Tcoeff.take s).map (· • hgen)`,`Tcoeff = [1,2,-3,3,-4]`。之后所有判断都变成“小整数属于
小整数列表”,这是让 Prop 2.5 可控的关键改写。

**`n ≥ 72` 在哪里被用到 —— 只在一处:**

```
zsmul_hgen_inj (hm : 12 ≤ m) {a b : ℤ} (hab : |a - b| < 12) :
    a • hgen = b • hgen → a = b
```

`a•h = b•h` ⇒ `m ∣ (a-b)`(`addOrderOf_dvd_iff_zsmul_eq_zero`),再由 `|a-b| < 12 ≤ m` 与
`Int.eq_zero_of_abs_lt_dvd` 得 `a = b`。所有消费者(`card_T`、`T_ne_zero`、
`T_induced_bipartite`、`card_Aset`、`Aset_bipartite`、`ord_Aset_ge`)都经由它。

**门槛是真的,不是装饰。** 实测:把假设换成 `0 < m` 后,`card_T` 与 `zsmul_hgen_inj`
两处 `omega` 都无法闭合(输出见 §3.3)。阈值 12 也确实够用:本证明中实际出现的最大差是
`|7 - (-4)| = 11 < 12`(来自 `(-3h, -4h)` 这一对的第三点 `7h`)。

`card_T = s` 由 `List.Nodup.map_on` + `List.Nodup.sublist (List.take_sublist ..)` 给出。
另外补证了论文提到的 `T_ne_zero`(补点非零,因为它们必须是 `E(ℝ)\{O}` 的真点)——
台账里没有这一条,但第 4 步需要,顺手证掉。

### 2.5 Prop 2.5

- `no_edge_A₀_T`:`t ∈ H`、`x ∈ C_i`(`i ≠ 0`)⇒ 第三点余类 `-i ≠ 0` ⇒ 它在 `A₀` 里,
  且 `-i ≠ 0`、`-i ≠ i` ⇒ 三个析取支全部失败。算术部分 `no_edge_arith` by `decide`。

- `T_induced_bipartite`:**只用两个划分,而不是论文的六种情形逐个验。** 这是本步最大的
  结构简化:
  - `s ≤ 2`:`T_s ⊆ {h, 2h}`,把两点放在对立两侧 ⇒ **每一对都跨划分**,完全不需要分析
    哪些是边。这一举覆盖论文“`s = 0,1,2`:团数 ≤ 2”三种情形。
  - `3 ≤ s ≤ 5`:`P = {h, 2h, -3h}`、`Q = {3h, -4h}`。这**一个**划分同时对上论文的三种
    情形(`s=3` 无边、`s=4` 星、`s=5` 4-圈)。唯一需要验的是 `P` 内 3 对 + `Q` 内 1 对
    共 4 对不是边,而它们的第三点分别是 `-3h`、`2h`、`h`、`h`,`s ≥ 3` 时都已在 `T_s` 内
    ⇒ 都不是边。逐对核对结果与论文给的边表完全一致(见 §4)。

- `Aset_bipartite`:划分取 `Xpart ∪ (P ∩ H)` vs `Ypart ∪ (Q ∩ H)`。三类边分别由
  `ordAdj_crosses`(经 `ordAdj_of_superset` 回落到 `A₀`)、`T_induced_bipartite`、
  `no_edge_A₀_T` 处理。与 `H` 取交是为了让两半与 `Xpart`/`Ypart ⊆ A₀` 不交。

  `ordAdj_of_superset` 就是论文“加点只会毁边不会造边”那句话的形式化。

- `card_destroyed_by = m`:`resid t = 0` ⇒ 对每个 `x ∈ C_i` 都有 `resid(-t-x) = -i`,
  故 filter 条件恒真,`Finset.filter_true_of_mem` + `card_C`。

- `ord_Aset_ge`:`Bad`/`Good` 是 `Dual` 按“第三点是否落进 `T_s`”的互补 filter。
  `card_Bad_le` 用 `Bad ⊆ (T s).biUnion (fun t => A₀.image (fun x => (x, -t-x)))`
  ⇒ `|Bad| ≤ s · 6m = 6ms`。于是 `|Good| ≥ 6m² - 6ms`,减半得 `3m² - 3ms`。

  ℕ/ℝ 转换集中在**一条**桥上:因 `m ≥ 12 > 5 ≥ s` 有 `s ≤ m`,故 ℕ 截断减法 `m - s` 精确,
  `((3*m*(m-s) : ℕ) : ℤ) = 3m² - 3ms`(一次 `push_cast [Nat.cast_sub hsm]`)。没有到处
  `push_cast`。

### 2.6 `-10n/3` 的出处(按事实源核对)

按 `paper-section2.md` 第 216–219 行:该项**完全来自 §2.2.3 的补点**,不是凑出来的常数。
每个补点毁 `3m` 条,`s` 个毁 `3ms` ⇒ `ord(A) ≥ 3m² - 3ms`;换元 `n = 6m + s` 后
`3m² - 3ms = n²/12 - (2s/3)n + 7s²/12`(`key_identity`,`by ring`),再用 `0 ≤ s ≤ 5`
丢掉非负的 `7s²/12` 并把 `2s/3` 放大到 `10/3`(`final_bound`,`by nlinarith`)。
`s = 0`(即 `6 | n`)时没有这一项。

---

## 3. 机械验收:命令与真实输出

### 3.1 `lake build`

```
$ cd .work/erdos-960-lean/lean && lake build 2>&1 | tee build.log
⚠ [8927/8930] Built Erdos960.Bridge (5.2s)
warning: Erdos960/Bridge.lean:29:8: declaration uses `sorry`
⚠ [8928/8930] Built Erdos960.Main (4.0s)
warning: Erdos960/Main.lean:24:8: declaration uses `sorry`
warning: Erdos960/Main.lean:45:8: declaration uses `sorry`
warning: Erdos960/Main.lean:110:8: declaration uses `sorry`
✔ [8929/8930] Built Erdos960 (4.6s)
Build completed successfully (8930 jobs).

LAKE-EXIT=0
```

零 error。

### 3.2 `Combinatorial.lean` 零 sorry

```
$ grep -n -F 'sorry' Erdos960/Combinatorial.lean
11:**Status: this file is `sorry`-free.** The one obligation that used to live here,
```

唯一命中是文件头说明自己零 sorry 的那句散文,**无代码 sorry**。

```
$ grep -F "declaration uses \`sorry\`" build.log | grep -c -F "Combinatorial.lean"
0
```

全局分布(13 条 warning,全部是 `declaration uses 'sorry'`,来自 `Defs.lean` 6 /
`Curve.lean` 3 / `Bridge.lean` 1 / `Main.lean` 3):`Combinatorial.lean` 占 **0** 条。

### 3.3 `n ≥ 72` 是否真被用上

把假设削弱成 `0 < m` 后重新elaborate,两处都应失败:

```
$ lake env lean Probe.lean          # card_T / zsmul_hgen_inj with (hm : 0 < m)
Probe.lean:16:13: error: omega could not prove the goal:
Probe.lean:21:21: error: omega could not prove the goal:
```

两处都拒绝 ⇒ 门槛真实。

### 3.4 `#print axioms`(28 个对外结论,全部)

```
$ lake env lean Axioms.lean
'Erdos960.card_C' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.card_H' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.C_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.mem_C_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.card_A₀' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.A₀_disjoint_H' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.ordAdj_residues' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.ordAdj_crosses' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.ordAdj_of_dual' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.card_Dual' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.ord_A₀_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.addOrderOf_hgen' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.hgen_mem_H' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.zsmul_hgen_inj' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.card_T' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.T_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.T_subset_H' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.card_Aset' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.no_edge_A₀_T' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.T_induced_bipartite' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.Aset_bipartite' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.card_destroyed_by' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.card_Bad_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.ord_Aset_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.key_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.final_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.m_ge_twelve' depends on axioms: [propext, Quot.sound]
'Erdos960.exists_decomp' depends on axioms: [propext, Quot.sound]

$ grep -E "sorryAx|axiom " step3-axioms.log
NONE
```

**28 / 28 只依赖 `propext`、`Classical.choice`、`Quot.sound`**(末两条连 `Classical.choice`
都不用)。无 `sorryAx`,无自定义 `axiom`。合格。

---

## 4. `T_s` 内部边表:与论文逐对核对

`u = a•h`、`v = b•h` 的第三点是 `c•h`,`c = -(a+b)`;`{u,v}` 是边 ⟺ `c•h ∉ T_s` 或
`c = a` 或 `c = b`。系数取自 `{1, 2, -3, 3, -4}`。

`s = 5`(`T_5` 全部五点):

| `(a,b)` | `c = -(a+b)` | `c•h ∈ T_5`? | 是边? | 论文 |
|---|---|---|---|---|
| `(1,2)` | `-3` | 是 | 否 | 否 ✔ |
| `(1,-3)` | `2` | 是 | 否 | 否 ✔ |
| `(1,3)` | `-4` | 是 | 否 | 否 ✔(`s=4` 时是边,加入 `-4h` 后消失) |
| `(1,-4)` | `3` | 是 | 否 | 否 ✔ |
| `(2,-3)` | `1` | 是 | 否 | 否 ✔ |
| `(2,3)` | `-5` | 否 | **是** | `{2h,3h}` ✔ |
| `(2,-4)` | `2` | 是,但 `c = a` | **是** | `{2h,-4h}` ✔ |
| `(-3,3)` | `0` | 否(补点非零) | **是** | `{3h,-3h}` ✔ |
| `(-3,-4)` | `7` | 否 | **是** | `{-4h,-3h}` ✔ |
| `(3,-4)` | `1` | 是 | 否 | 否 ✔ |

得 4-圈 `2 — 3 — (-3) — (-4) — 2`,与论文 `s=5` 的边表一致。`P = {h,2h,-3h}`、
`Q = {3h,-4h}` 把它正确二染色(`h` 是孤立点,放 `P`)。

`s = 4`:同法得边 `{1,3}`、`{2,3}`、`{-3,3}`,即以 `3h` 为心的星 —— 与论文一致,
同一个 `P`/`Q` 仍然有效。
`s = 3`:三对第三点 `-3h`、`2h`、`h` 全在 `T_3` 内 ⇒ 无边,与论文一致。

⚠ 记一处实现上的发现:**不存在对 `s = 0..5` 统一的二部划分。** `s = 2` 要求 `h`、`2h`
分处两侧(那时 `{h,2h}` 是边),而 `s = 4` 要求 `h`、`2h` 同侧(都与 `3h` 相邻)。
故必须按 `s ≤ 2` / `s ≥ 3` 分两支 —— 这就是 `T_induced_bipartite` 里那个 `by_cases` 的
原因,不是随手写的。

---

## 5. 用到的 Mathlib 声明

计数与 Finset:
`Finset.card_nbij'`、`Finset.card_eq_sum_card_fiberwise`、`Finset.card_biUnion`、
`Finset.card_biUnion_le`、`Finset.card_image_le`、`Finset.card_product`、
`Finset.card_union_of_disjoint`、`Finset.card_filter_add_card_filter_not`、
`Finset.card_erase_of_mem`、`Finset.card_le_card`、`Finset.filter_true_of_mem`、
`Finset.sum_const`、`Finset.sum_le_sum`、`Finset.disjoint_left`、
`Finset.disjoint_of_subset_left/right`、`Finset.mem_offDiag`、`Finset.mem_product`。

`ZMod` 与群论:
`ZMod.castHom`、`ZMod.castHom_surjective`、`ZMod.card`、`ZMod.addOrderOf_coe`、
`addOrderOf_dvd_iff_zsmul_eq_zero`、`map_zsmul`、`map_natCast`、`map_sub`、`map_neg`、
`map_add`、`neg_zsmul`、`add_zsmul`、`sub_zsmul`。

数论与列表:
`Int.eq_zero_of_abs_lt_dvd`、`Nat.le_div_iff_mul_le`、`Nat.gcd_eq_left`、`Nat.gcd_comm`、
`Nat.cast_sub`、`Nat.sub_add_cancel`、`List.Nodup.map_on`、`List.Nodup.sublist`、
`List.take_sublist`、`List.mem_of_mem_take`、`List.toFinset_card_of_nodup`、
`List.map_take`、`List.length_take`。

战术:`decide`(13 处,全部是 `ZMod 7` 上的有限验证)、`omega`、`ring`、`nlinarith`、
`push_cast`、`positivity`、`linear_combination`、`interval_cases`。

**`SimpleGraph` 侧刻意没有碰。** 本文件把二部性表述成“显式划分 `P`/`Q` + 每条边跨划分”
这个纯 Finset 形式,而不是 `SimpleGraph.IsBipartite`。原因:`edgeCount`/`ordAdj` 本身就是
群侧的 Finset 结构,套 `SimpleGraph` 只会多一层 coercion;`Defs.lean` 已有
`cliqueFree_of_isBipartite`(归第 4 步)负责“二部 ⇒ `CliqueFree r`”那一跳,由它消费本文件
`Aset_bipartite` 给出的划分即可。**这不是削弱** —— 给出显式划分严格强于断言“存在二部结构”。

---

## 6. 陈述完整性(有无削弱)

逐条对照上游陈述:**15 个认领条目全部按原陈述证出,零削弱、零加强假设。**

- 类型与假设签名一字未改的:`card_C`、`C_disjoint`、`mem_C_iff`、`card_A₀`、
  `ordAdj_residues`、`ordAdj_crosses`、`ordAdj_of_dual`、`ord_A₀_ge`、`addOrderOf_hgen`、
  `hgen_mem_H`、`card_T`、`T_subset_H`、`card_Aset`、`no_edge_A₀_T`、
  `T_induced_bipartite`、`Aset_bipartite`、`card_destroyed_by`、`ord_Aset_ge`。
- 新增的**辅助**引理(不在台账、不替代任何条目):`card_H`、`mem_H_iff`、`mem_A₀_iff`、
  `A₀_disjoint_H`、`card_C_eq_card_C_zero`、`sum_card_C`、`ordAdj_symm`、
  `ordAdj_of_superset`、`not_ordAdj_of_third`、`le_edgeCount`、`resid_case_*`、
  `bipartite_arith`、`ne_neg_self`、`nonzero_mem_U_or_V`、`zero_notMem_U/V`、
  `resid_hgen`、`resid_zsmul_hgen`、`zsmul_hgen_mem_H`、`zsmul_hgen_inj`、
  `zsmul_hgen_ne`、`Tcoeff`、`Tcoeff_cases`、`T_eq_map`、`mem_T_iff`、`T_ne_zero`、
  `dualSet`、`Dual`、`mem_Dual_iff`、`Dual_mem_A₀`、`card_Dual`、`Bad`、`Good`、
  `card_Bad_add_card_Good`、`card_Bad_le`、`Good_mem_Aset`、`no_edge_arith`、
  `not_ordAdj_within`、`A₀_subset_Aset`、`T_subset_Aset`、`A₀_disjoint_T`。
- 定义 `resid`、`C`、`H`、`A₀`、`U`、`V`、`ordAdj`、`edgeCount`、`Xpart`、`Ypart`、
  `hgen`、`T`、`Aset`、`dualPairs` 全部沿用上游,**未改动**。

唯一的结构性变更是 §1 说明的 `edgeCount_eq_ord` 移文件,陈述未改、归属未改。

---

## 7. 交给第 4 步的东西

可以直接消费的:

- `ord_Aset_ge : 3m² - 3ms ≤ edgeCount (Aset s)` —— 群侧下界,已证。
- `Aset_bipartite` —— 显式划分,喂给 `Defs.lean` 的 `cliqueFree_of_isBipartite`。
- `card_Aset : |Aset s| = 6m + s` —— 点数。
- `T_ne_zero` —— 补点非零,`M.pts` 需要它排除 `O`。
- `final_bound`、`key_identity`、`m_ge_twelve`、`exists_decomp` —— §2.3 的全部代数。

仍需第 4 步做的(本步未动,也不该动):

- `Bridge.lean` 的 `edgeCount_eq_ord` —— 群侧 `edgeCount` ⇄ 几何 `ord`。
- `Curve.lean` 的 `ordinaryLine_iff`、`noKCollinear_pts`。
- `Defs.lean` 的 6 条、`Main.lean` 的 3 条。
- `Curve.lean:155` `exists_curveModel_zmod` —— 🔴 永久缺口,不由任何步骤核销。
