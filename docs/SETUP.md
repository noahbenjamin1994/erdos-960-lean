# Lean 4 + Mathlib 环境(闸门 0 固定,后续每步照此重建)

## 锁死的版本

| 项 | 值 |
|---|---|
| Lean toolchain | `leanprover/lean4:v4.34.0` |
| Mathlib tag | `v4.34.0`(**已发布稳定 tag,不跟 master**) |
| Mathlib commit | `5ed2965256430c3649e86755f9576b54eca72435` |
| 包名 | `erdos960`,库 `Erdos960` |
| 工程根 | `.work/erdos-960-lean/lean/` |

依赖 commit(来自 `lake-manifest.json`,已锁):

```
batteries   e92c9f15fdfacc8536f31cfb3b7ad26c3c8cd204
aesop       6a489d9af5d0c47e5b259e2e8bcdfc1811b5a259
Qq          f2effa3d803fda822b1f97b806c47cf2adfbcbc2
proofwidgets 355695d523e41d0554926416cba2a2b3544fbbc9
importGraph 106ff4fafc74ef4ac99d81dbf3ab399118f497a5
LeanSearchClient ddf04cf3949fa556442341e87d47f9f6e6074707
plausible   118aa17ee84656b8bd727fef7c458ee8c833385c
Cli         e928b72544873815af278d38681b31c0293588e3
```

🔴 **不要动 `lean-toolchain` 和 `lake-manifest.json`。** 不要 `lake update`(会重新解析
到 master)。只跑 `lake exe cache get` + `lake build`。

## 每步开头的幂等 bootstrap

脚本已落盘:`.work/erdos-960-lean/bootstrap.sh`。直接跑:

```bash
cd "$(git rev-parse --show-toplevel)"
nohup bash .work/erdos-960-lean/bootstrap.sh > .work/erdos-960-lean/logs/bootstrap.log 2>&1 &
python3 .claude/skills/_shared/scripts/wait_for.py \
        --file .work/erdos-960-lean/logs/bootstrap.log --pattern 'BOOTSTRAP_DONE'
```

⚠ 脚本里目前带了 `lake update -R`。**第 2 步起应把那一行删掉** —— manifest 已经生成并锁死,
再跑 `update` 有把 pin 冲掉的风险。保留 `cache get` 与 `build` 两行即可。

手工等价命令:

```bash
cd "$(git rev-parse --show-toplevel)"
export ELAN_HOME="$PWD/.work/erdos-960-lean/elan"    # ~/.elan 不跨 step 保留
export PATH="$ELAN_HOME/bin:$PATH"
export OMP_NUM_THREADS=4
cd .work/erdos-960-lean/lean
lake exe cache get      # 后台跑
lake build              # 后台跑
```

## elan 安装(仅当 `.work/erdos-960-lean/elan/` 没被快照带过来)

```bash
cd "$(git rev-parse --show-toplevel)"
export ELAN_HOME="$PWD/.work/erdos-960-lean/elan"
export PATH="$ELAN_HOME/bin:$PATH"
command -v lake >/dev/null 2>&1 || \
  curl -sSfL https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --no-modify-path --default-toolchain none
```

`ELAN_HOME` **必须**指向工作区内,默认的 `~/.elan` 跨 step 会丢。

## 实测耗时与体积(闸门 0 这一步真实测量)

| 阶段 | 耗时 | 备注 |
|---|---|---|
| elan 安装 | < 1 min | 13 MB 单二进制,硬链接成 7 个入口 |
| `lake update -R`(clone mathlib + 8 个依赖) | ~4 min | mathlib 源码 ~1.4 GB |
| `lake exe cache get`(下载 olean) | 含在上面这段里 | 解包后 `.lake` 共 **6.7 GB** |
| `lake build`(8926 jobs,几乎全命中缓存) | ~2 min | 自身代码只编 2 个 job |
| **合计冷启动** | **约 7 分钟** | 远低于计划里预估的 10–20 min |

磁盘:`/` 有 200 GB(用了 32 GB),6.7 GB 的 `.lake` 不构成压力。
内存:4 核 / 16 GiB;`lake build` 走缓存时峰值很低,自己写的文件 `import Mathlib` 时
单文件 elaboration 约 2.5–5.5 s。

## 校验环境是否完好

```bash
cd "$(git rev-parse --show-toplevel)/.work/erdos-960-lean/lean"
export PATH="$(git rev-parse --show-toplevel)/.work/erdos-960-lean/elan/bin:$PATH"
lean --version                                   # 期望 4.34.0
git -C .lake/packages/mathlib rev-parse HEAD     # 期望 5ed2965256430c...
du -sh .lake/packages/mathlib/.lake              # 期望 ~6.7G(olean 在位)
lake build                                       # 期望 Build completed successfully
```

若 `.lake/` 没被快照带过来:**只需重跑 `lake exe cache get`**,不要重新 clone mathlib。

## 查 Mathlib 声明的正确姿势

优先本地源码,别开浏览器:

```bash
M="$(git rev-parse --show-toplevel)/.work/erdos-960-lean/lean/.lake/packages/mathlib"
grep -rn -F 'addOrderOf_period_div' $M/Mathlib/Topology/Instances/AddCircle/Defs.lean
grep -n -E '^(theorem|lemma|def) ' $M/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean
```

⚠ `grep` 只用来找行号,再用 `sed -n 'a,bp'` 取窗口。不要用区间量词 `{m,n}`(守卫会拦)。

在线文档:https://leanprover-community.github.io/mathlib4_docs/
