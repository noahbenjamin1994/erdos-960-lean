> **⚠ 2026-09-18 更新:数字已过时。**
> 本文记录的是交付时那次验收(8930 jobs、123 条 `#print axioms`)。补上 Lemma 2.2 之后是
> 8931 jobs、133 条。当前那一次干净重建的原始输出在仓库根目录的 `verification/`。

# 零 sorry 机械验收 —— 真实输出(未经编辑)

本文件的每一段都是命令的真实 stdout。命令本身写在 `$` 行上,可以照抄复跑。

- toolchain:`leanprover/lean4:v4.34.0`
- mathlib pin:`5ed2965256430c3649e86755f9576b54eca72435`(`lake-manifest.json`,tag `v4.34.0`)
- 工作目录:`.work/erdos-960-lean/lean`
- 日期:2026-09-17

## 1. 从干净状态重建

只删本包的 build 产物,保留 `.lake/packages`(mathlib 不重新 clone)。

```
$ rm -rf .lake/build
$ time lake build 2>&1 | tee build.log
✔ [8927/8930] Built Erdos960.Bridge (5.0s)
✔ [8928/8930] Built Erdos960.Main (5.5s)
✔ [8929/8930] Built Erdos960 (4.5s)
Build completed successfully (8930 jobs).
real	0m39.448s
user	0m40.724s
sys	0m12.204s
$ echo $?
0
```

## 2. 源码里没有 sorry

```
$ grep -rn -F 'sorry' Erdos960/ || echo "NO-SORRY-IN-SOURCE"
Erdos960/Bridge.lean:4:`Combinatorial.lean` is the `ZMod (7m)` side and is `sorry`-free; this file holds the
Erdos960/Combinatorial.lean:11:**Status: this file is `sorry`-free.** The one obligation that used to live here,
```

命中的两行都是**散文** —— 写在文件头说明里的 `` `sorry`-free `` 字样,不是 `sorry` 项。
机械判据见第 3 节:Lean 自己报的 `declaration uses 'sorry'` 计数为 0。

> 本步发现并处理的一件事:真 `sorry` 曾存在于闸门 0 探针文件 `Gate0.lean`(第 274 行,
> 一条**故意**用来标记“Mathlib 没有这条”的匿名 `example`)。该文件不被 `Erdos960.lean`
> import、不参与 `lake build`(构建日志 0 命中),但它放在库目录里,会让这条 `grep` 的输出
> 看起来像在说谎。已移到 `gate0/Gate0Probe.lean`,与 `GATE0.md` 放在一起,**不进交付**。

## 3. 构建日志里没有 sorry 警告、没有 error

```
$ grep -c -F "declaration uses 'sorry'" build.log
0
$ grep -c -F "error" build.log
0
```

## 4. `#print axioms` —— 全部 123 条对外声明

只允许 `propext` / `Classical.choice` / `Quot.sound`;`sorryAx` 或任何自定义
`axiom` 出现即为不合格。审计清单是 `Axioms.lean`(`import Erdos960`,即全库)。

```
$ lake env lean Axioms.lean > axioms.log ; echo $?
0
$ wc -l axioms.log
123 axioms.log
$ # 列出任何不是那三条的行:
$ grep -v -E "^.+ depends on axioms: \[(propext|Classical.choice|Quot.sound)(, …)*\]$" axioms.log
$ # (无输出 —— 123 条全部落在允许集合内)
$ grep -c -F "sorryAx" axioms.log
0
```

主定理与其直接组件,从 `axioms.log` 逐字摘录:

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

`CurveModelAssumption`(论文 Lemma 2.2 + 共线判据)**不是 `axiom`** —— 它是一条
`def … : Prop`,以显式假设的形式进入 `erdos960` 的签名,所以它不可能、也确实没有
出现在上面任何一行的 axiom 列表里。这正是“条件定理”与“偷偷加公理”的区别所在。
