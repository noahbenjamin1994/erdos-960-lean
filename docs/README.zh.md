> 📁 **路径说明**：本文写于交付时的目录结构。整理成仓库后，Lake 包已上移到仓库根目录，说明文档移到 `docs/`。文中的 `Erdos960/`、`Axioms.lean` 在仓库根目录；其余 `.md` 报告与本文同在 `docs/`。
> 仓库级说明见根目录 [`README.md`](../README.md)（英文）。

# Erdős Problem 960 — Theorem 2.1 的 Lean 4 形式化

一个 2038 行的 Lean 4 lake 工程,把 arXiv 2604.06609 第 2 节 Theorem 2.1 的证明重建为
机器可验证明。**从干净状态 39.4 秒编译通过,库内零 `sorry`,123 条对外声明的
`#print axioms` 全部只依赖 `propext` / `Classical.choice` / `Quot.sound`。**

主定理是一条**条件定理**:论文 Lemma 2.2 作为显式假设进入签名。这不是疏漏,而是
经闸门 0 判定、并写在用户契约里的取舍,第 3 节逐条交代。

---

## 1. Credit 声明

**本仓库不解数学。**

Theorem 2.1 的数学结论与证明属于论文原作者 —— B. Alexeev、M. Putterman、M. Sawhney、
M. Sellke、G. Valiant,*Short proofs in combinatorics, probability and number theory II*,
arXiv:2604.06609,第 2 节。**prover credit 全部归他们。**

- 论文:https://arxiv.org/abs/2604.06609
- Erdős Problem 960:https://www.erdosproblems.com/960

本工作主张的是**独立的 formalizer credit**:把该证明重建为 Lean 4 机器可验证明。
构造、引理、常数、`n ≥ 72` 这个门槛 —— 没有一样是我们发明的;我们做的是把它们写成
Lean 4 并让 kernel 接受。

论文 §2.2 逐字授权了“参数化掉具体曲线”:"while we use a specific elliptic curve below
for concreteness, any (non-degenerate) elliptic curve suffices"。它**没有**授权省掉
Lemma 2.2 —— 那一步的省略是我们的取舍,不是论文的,见第 3 节。

---

## 2. 主定理

### Lean 陈述原文

`Erdos960/Main.lean`:

```lean
theorem erdos960
    (r k n : ℕ) (hr : 3 ≤ r) (hk : 4 ≤ k) (hn : 72 ≤ n)
    (hcurve : ∀ m : ℕ, 0 < m → Nonempty (CurveModel (ZMod (7 * m)))) :
    (n : ℝ) ^ 2 / 12 - 10 * (n : ℝ) / 3 ≤ (F r k n : ℝ)
```

### 自然语言解读

固定整数 `r ≥ 3`、`k ≥ 4`、`n ≥ 72`。假设对每个 `m ≥ 1`,`7m` 阶循环群能嵌入实平面、
且嵌入后三点共线当且仅当三者群和为零(`hcurve`,即论文 Lemma 2.2 加共线判据)。那么

```
F_{r,k}(n) ≥ n²/12 − 10n/3
```

其中 `F_{r,k}(n)` 是在“任何直线至多含 `k−1` 个点”且“不存在 `r` 点子集使其中每对点都
张成 ordinary line”两个约束下,`n` 点集 ordinary line 条数的最大值。
Erdős 猜 `F_{r,k}(n) = o(n²)`;这条界说明答案为否。

### 它为什么忠实于论文

逐条对照在 `statement-fidelity.md`;要点是:

1. **`ord(A)` 是真的平面几何量,不是组合替身。** `ptsOn`、`IsLine`、`ordinaryLine` 全部
   定义在 `ℝ × ℝ` 与 `AffineSubspace ℝ (ℝ × ℝ)` 上;`IsLine L` 要求 `L` 由两个不同点张成
   (排除空集与单点,否则 `Collinear` 会把它们一起算进来)。`ord A` 是
   `{L | ordinaryLine A L}` 的 `Set.ncard`。
2. **`ord` 的有限性是被证明的,不是假设的。** `Set.ncard` 对无限集返回 `0`,所以
   “`ord` 有意义”本身是一条义务:`ordinaryLines_finite`(一条 ordinary 直线由它上面那
   两个 `A`-点决定)。不证它,整条界就可能是在说 `0 ≥ …`。
3. **界写在 `ℝ` 上。** `n²/12` 与 `10n/3` 一般不是整数(`n = 73` 时是 `803/4`),写在
   `ℕ`/`ℤ` 上会被截断除法悄悄改掉含义。`F` 落在 `ℤ` 是因为论文的退化值 `−1` 在 `ℕ` 里
   无处安放 —— 论文 §2.1 逐字:"If no such configuration exists, set `F_{r,k}(n) = −1`"。
4. **三条数值假设都真的被消耗,不是装饰。**
   - `k ≥ 4` 被 `CurveModel.noKCollinear_pts` 消耗:构造里真的有三点共线(弦与三次曲线
     交于三点),所以它对 `k = 4` 合法、对 `k = 3` **不**合法。
   - `r ≥ 3` 被 `cliqueFree_of_isBipartite` 消耗(二部 ⇒ `2`-可着色 ⇒ 无 `K_r`,`r > 2`)。
   - `n ≥ 72` 经 `m_ge_twelve` 兑换成 `m ≥ 12`,唯一入口是 `zsmul_hgen_inj`。已实测把它
     削弱成 `0 < m` 后两处 `omega` 均无法闭合(输出见 `COMBINATORIAL-REPORT.md` §3.3)。
5. **反空转检查。** `bound_pos_at_72` 证明界在 `n = 72` 处为 `192 > 0`,所以结论不是
   `F ≥ -1` 或 `F ≥ 0` 白送的;`F_ne_neg_one_of_erdos960_hyps` 证明在主定理**自己的假设
   下**退化分支被排除;`decomp_at_72` / `decomp_at_73` 给出 `s = 0` 与 `s = 1` 两个数值
   实例(后者 `−3ms` 项是活的)。

---

## 3. 闸门 0 结论

完整报告在 `GATE0.md`(`VERDICT: PROCEED`)。三项缺口的判定:

| 缺口 | 判定 | 结果 |
|---|---|---|
| **G0-1** `E(ℝ)` 连通 ⇒ 同构于圆群 `ℝ/ℤ` | **需现造整个理论 ⇒ 绕开** | 成为假设的一部分 |
| **G0-2** `M` 阶循环子群存在性 | **完全现成** | 已证,两个独立见证 |
| **G0-3** 共线 ⟺ 群和为零 | **Mathlib 无现成引理;按定义式改写可绕开** | 成为假设的一部分 |

### `E(ℝ) ≅ ℝ/ℤ` 为什么被绕开

闸门 0 对 `Mathlib/AlgebraicGeometry/EllipticCurve/` 全目录检索 `TopologicalSpace`、
`IsTopologicalAddGroup`、`IsConnected`、`LieGroup`、`Circle` —— **零命中**;对整个 Mathlib
检索 `WeierstrassCurve.*TopologicalSpace` 等模式 —— **零命中**。

也就是说:**Mathlib 里 `WeierstrassCurve.Affine.Point` 连拓扑空间实例都没有**,更谈不上
李群。它是一个 `inductive`,群结构经 coordinate ring 的理想类群纯代数地建立。同时
`Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean` 里的 ℘ 函数与曲线点群没有
任何连接(检索 `Point`、`AddEquiv`、`≃+` 全部零命中),即 **Mathlib 没有单值化
`ℂ/Λ ≅ E(ℂ)`**。

按论文 Lemma 2.2 的字面路线走,需要先给 `Point` 装拓扑、证它是拓扑群、再证紧连通一维
交换李群同构于圆 —— 这是“现造整个理论”,正是用户契约里要求**暂停而非硬上**的情形。

### 绕开路线是什么

把曲线侧需要的性质打包成一个结构,只留**一个**非结构性字段:

```lean
structure CurveModel (G : Type*) [AddCommGroup G] where
  emb : G → ℝ × ℝ
  emb_injective : Function.Injective emb
  collinear_iff : ∀ x y z : G, x ≠ y → y ≠ z → x ≠ z →
    (Collinear ℝ ({emb x, emb y, emb z} : Set (ℝ × ℝ)) ↔ x + y + z = 0)

def CurveModelAssumption (m : ℕ) : Prop := Nonempty (CurveModel (ZMod (7 * m)))
```

`CurveModelAssumption` **不是 `axiom`**(没有被断言为真),也**不是 `sorry`**。它以显式
假设的形式进入 `erdos960` 的签名,所以:

- `#print axioms Erdos960.erdos960` 只输出那三条标准公理 —— 没有偷偷断言任何东西;
- 代价是 `erdos960` 是一条**条件定理**,假设写在签名里,读者一眼可见。

**交付的不是 Theorem 2.1 的完整机器验证**,而是“给定曲线侧的群论 + 几何假设,论文
§2.2.2–§2.3 的全部论证成立”的机器验证。这一句写在 `Curve.lean` 文件头、
`SORRY-LEDGER.md`、`statement-fidelity.md` 与这里,共四处。

### 缺口比闸门 0 设想的更小:Lemma 2.3 是定理,不是假设

`GATE0.md` 路线 (0) 把论文 Lemma 2.3(Bézout ⇒ 无四点共线)也列为要假设的东西。
**它不是。** `CurveModel.no_four_collinear` 由共线判据单独推出,全程纯群论:若
`w, x, y, z` 四点两两不同且共线,则 `{w,x,y}` 与 `{w,x,z}` 都共线,判据给出
`w+x+y = 0 = w+x+z`,`add_left_cancel` 得 `y = z`,矛盾。

⇒ 永久缺口从“Lemma 2.2 **加** Lemma 2.3”收缩为“**仅** Lemma 2.2(加共线判据)”。
这是相对闸门 0 的偏差,方向是**收紧假设集**,不是放松。

### 这个取舍为什么不削弱主定理

三条独立的理由:

1. **假设不是空的,而且有两个独立见证。** `HasCyclicSubgroupOfOrder` 被
   `zmod_hasCyclicSubgroup`(`ZMod (7m)`,生成元 `1`)与 `addCircle_hasCyclicSubgroup`
   (`AddCircle (1:ℝ)`,经 `AddCircle.addOrderOf_period_div`)分别满足,两者都已证。
   所以 `hcurve` 不是一条从假中推一切的空假设。
2. **假设更弱 ⇒ 定理更强。** `collinear_iff` 只在两两不同的三点上要求双向等价
   (论文说“counted with multiplicity”,三点互异时重数概念为空)。要求得越少,满足它
   的模型越多,结论覆盖面越广 —— 方向是安全的。
3. **缺口被精确定位,而不是笼统甩出。** `Curve.lean` 的 `Concrete` 命名空间把具体曲线
   `y² = x³ − x + 1` 上今天就能从 Mathlib 走通的部分全部证了:判别式 `E_Δ = -368`、与论文
   `−23` 的 16 倍换算(`E_Δ_eq_sixteen_mul_paper`,Mathlib 用 LMFDB 归一化)、
   `E_Δ_ne_zero`、`E_nonsingular`(⇒ 它确实是椭圆曲线、确实带群结构),以及**论文
   Lemma 2.3 对这条具体曲线的完整代数证明** `Concrete.card_le_three_of_line`(任何仿射
   直线与 `E(ℝ)` 至多交 3 点,走 `Polynomial.card_roots'` 而非 Bézout)。
   这部分主定理用不到 —— 它的作用是把缺口钉死在“`7m` 阶循环子群的存在性”这一点上。

---

## 4. 编译方法

### 环境

| 项 | 值 |
|---|---|
| Lean toolchain | `leanprover/lean4:v4.34.0`(`lean-toolchain`) |
| Mathlib | tag `v4.34.0`,commit `5ed2965256430c3649e86755f9576b54eca72435`(`lake-manifest.json`) |
| 平台 | x86_64-unknown-linux-gnu,4 核 / 16 GiB,无 GPU |

**不要改 `lean-toolchain` 或 `lake-manifest.json` 的 pin** —— 本工程的证明是对着这个
Mathlib commit 的 API 写的。

### 逐条命令

```
curl -sSfL https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --no-modify-path --default-toolchain none
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get          # 下载 mathlib 的 olean 缓存,约 10-20 分钟,6.7 GB
lake build                  # 本工程
lake env lean Axioms.lean   # 公理审计,123 条
```

### 实测耗时

| 阶段 | 耗时 |
|---|---|
| 冷启动全流程(elan + clone + `cache get` + `build`) | 约 7 分钟 |
| **从干净 `.lake/build` 重建本工程**(保留 `.lake/packages`) | **39.4 秒**,8930 jobs |
| 增量重建(无改动) | 约 5 秒 |

`.lake` 体积 6.7 GB,**不在本交付包内**(交付只含文本源码)。

### 零 sorry / `#print axioms` 的真实输出

完整、未经编辑的验收记录在 **`ACCEPTANCE.md`**。摘录:

```
$ rm -rf .lake/build
$ time lake build 2>&1 | tee build.log
Build completed successfully (8930 jobs).
real	0m39.448s

$ grep -rn -F 'sorry' Erdos960/ || echo "NO-SORRY-IN-SOURCE"
Erdos960/Bridge.lean:4:`Combinatorial.lean` is the `ZMod (7m)` side and is `sorry`-free; this file holds the
Erdos960/Combinatorial.lean:11:**Status: this file is `sorry`-free.** The one obligation that used to live here,

$ grep -c -F "declaration uses 'sorry'" build.log
0

$ grep -c -F "error" build.log
0
```

上面 `grep` 命中的两行都是**散文** —— 文件头说明里的 `` `sorry`-free `` 字样,不是
`sorry` 项。机械判据是第三条命令:Lean 自己报的 `declaration uses 'sorry'` 计数为 **0**。

`#print axioms`,全部 123 条对外声明(清单是 `Axioms.lean`,它 `import Erdos960`,即全库):

```
$ lake env lean Axioms.lean > axioms.log ; echo $?
0
$ wc -l axioms.log
123 axioms.log
$ grep -c -F "sorryAx" axioms.log
0
$ grep -v -E "^.+ depends on axioms: \[(propext|Classical.choice|Quot.sound)(, …)*\]$" axioms.log
(无输出 —— 123 条全部落在允许集合内)
```

主定理与其直接组件,逐字摘录:

```
'Erdos960.erdos960' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.erdos960_of_curveModelAssumption' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.exists_admissible' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.F_ne_neg_one_of_erdos960_hyps' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.edgeCount_eq_ord' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.card_edgeFinset_ordGraph' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.ordinaryLines_finite' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.le_F' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.ord_Aset_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.Aset_bipartite' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.CurveModel.ordinaryLine_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.CurveModel.no_four_collinear' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos960.CurveModelAssumption' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`CurveModelAssumption` 出现在这张表里,是因为它是一条 `def … : Prop`,**它自身的定义**
只用到那三条标准公理;它并**没有**被断言为真,所以任何依赖它的定理都必须把它写进签名。
这正是“条件定理”与“偷偷加公理”的区别。

---

## 5. 文件结构

```
Erdos960/Defs.lean            328 行  §2.1:ptsOn / IsLine / ordinaryLine / ord / G_A / F
Erdos960/Curve.lean           482 行  曲线侧:CurveModel、Lemma 2.3(已证)、Concrete 命名空间
Erdos960/Combinatorial.lean   873 行  §2.2.2-§2.3:ZMod (7m) 上的初等数论(Prop 2.4 / 2.5)
Erdos960/Bridge.lean          142 行  几何 ⇄ 群论:edgeCount = ord
Erdos960/Main.lean            213 行  Theorem 2.1 + 反空转数值实例
Axioms.lean                          123 条 #print axioms 的审计清单
```

论证的骨架(每一步都对应论文的一个编号结论):

```
共线判据(假设)
  ├─ no_four_collinear ............. Lemma 2.3(已证,不是假设)
  │    └─ noKCollinear_pts ......... 满足 Admissible 的 k ≥ 4 一半
  └─ ordinaryLine_iff .............. Prop 2.4 归约:几何 ⇄ ZMod 算术
       └─ edgeCount_eq_ord ......... e(G_A) = ord(A),经有序对精确折半
            ├─ ord_A₀_ge ........... Prop 2.4:ord(A_0) ≥ 3m²
            ├─ Aset_bipartite ...... Prop 2.5(2):G_A 二部 ⇒ 无 K_r(r ≥ 3)
            └─ ord_Aset_ge ......... Prop 2.5(3):ord(A) ≥ 3m² − 3ms
                 └─ erdos960 ....... §2.3:丢掉松弛 7s²/12,得 n²/12 − 10n/3
```

配套文档:`SORRY-LEDGER.md`(13 条义务的逐条核销记录,已清零)、
`ACCEPTANCE.md`(验收命令的真实输出)、`GATE0.md`(缺口判定)、
`statement-fidelity.md`(逐条忠实性对照与七条有意取舍)、
`COMBINATORIAL-REPORT.md` 与 `CURVE-REPORT.md`(组合侧与曲线侧的分步报告)、
`SETUP.md`(环境复现)。

---

## 6. 提交去向

目标仓库是 **`TheJustinSunPrize/awards`**。

🔴 **推送是人工后续步骤。本次没有推送,也没有提交。**

原因是本容器没有推送能力,不是选择不推:

- 没有 `gh` CLI;
- 没有该仓库的写权限凭据;
- 因此**没有尝试 push**,也不存在任何已提交的 PR 或 commit。

需要人工完成的动作:

1. 把本目录的内容放进目标仓库的相应位置;
2. `lake exe cache get && lake build && lake env lean Axioms.lean`,自行复核第 4 节的
   验收输出 —— 不要只信这份 README;
3. 开 PR,在描述里带上第 1 节的 credit 声明与第 3 节的条件性说明。
   **不要把它描述成 Theorem 2.1 的完整形式化** —— 它是条件形式化。

---

## 7. 竞争状态(2026-09-17 快照)

| 渠道 | 状态 |
|---|---|
| JSP issue | **0 条** |
| GitHub 相关仓库 | **无** |
| `formal-conjectures` 的 statement PR #5872 | **已关闭** |
| `formal-conjectures` 的 issue #1037 | **仍开着** |

即:据这份快照,Erdős 960 的 Lean 形式化此前没有已落地的公开成果;formal-conjectures 侧
连**陈述**都还没有合进去(PR 已关、issue 仍开)。

---

## 8. 已知边界(诚实清单)

1. **`hcurve` 未被证明。** 第 3 节全文。这是唯一的数学缺口。
2. **具体曲线 `y² = x³ − x + 1` 没有被接到主定理上。** `Concrete` 里证的东西(判别式非零、
   非奇异、任何直线至多交 3 点)主定理一条都没用 —— 缺的就是把 `E(ℝ)` 的 `7m` 阶子群做成
   一个 `CurveModel`,而那要过 G0-1。
3. **`collinear_iff` 比论文原句窄**(限制在两两不同的三点上,不处理“计重数”的切线情形)。
   因为它是**假设**字段,变窄意味着假设更弱、定理更强。
4. **不出论文、不出报告四件套。** 用户明确要求“Lean 4 证明代码为主,闸门 0 结论以注释 /
   README 附带”,且本计划不含实验 / 训练 / 评测步骤,因此**有意**不追加 paper-writer
   阶段。这是一个明示的决定,不是漏项。
