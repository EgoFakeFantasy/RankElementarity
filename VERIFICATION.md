# 完成验收记录

验收日期：2026-09-11。

原定的基数版本已完整形式化。最终公开入口为
`RankReflection.rankElementaryInclusion_unbounded`。

它的完整前提只有 `a < b`、`b < c`、`V_a ≺ V_b` 和 `V_b ≺ V_c`。
结论为每个 `xi < b.ord` 都有 `xi < delta < b.ord`，且 `V_a ≺ V_delta`。
`RankElementaryInclusion` 使用 Mathlib 的全一阶初等嵌入，并要求底层集合逐点不变，
所以表达的确实是自然包含的初等子结构关系。

同时证明了更强的序数版本 `exists_rankElementaryInclusion_between`：
无需假设三个高度是基数，并可取得 `max alpha xi < delta`。

## 与原任务逐项核对

| 要求 | 验证依据 | 结果 |
|---|---|---|
| 实际的累积层级 V_a | `RankDomain` 是实际 `ZFSet` 中秩小于高度的集合；层级公式经递归唯一性识别为 `ZFSet.vonNeumann` | 通过 |
| 全一阶初等自然包含 | `RankElementaryInclusion` 的定义和 `rankElementaryInclusion_iff` 的双向语义桥 | 通过 |
| 基数 a < b < c 的原命题 | 默认构建中的 `#check rankElementaryInclusion_unbounded` 完整类型 | 通过 |
| 在 b 中无界 | 最终结论对任意 `xi < b.ord` 给出严格更大的 `delta < b.ord` | 通过 |
| 不添加不可达、正则或模型假设 | 最终类型只有原始四条前提；极限和 omega 界由初等包含推出 | 通过 |
| 统一满足关系实际存在 | 真值集合由分离构造；有限初等性公式的双向正确性已证明 | 通过 |
| 无残留未证接口 | 最终证明中初等性公式、层级识别、反射和见证解码全部闭合 | 通过 |
| 所有新 Lean 模块纳入默认构建 | `RankReflection.lean` 导入全部模块与公理审计 | 通过 |
| 构建 | `lake build`，共 1244 jobs | 通过 |
| 公理审计 | 全部 102 个项目定理常量的传递公理依赖检查 | 通过 |
| 依赖版本 | 10 个依赖的提交均与登记版本一致，已跟踪源码无改动；公开配置锁定相同提交 | 通过 |
| 命名 | 延续 PCF / FullMarkedBLP 的数学语义命名约定 | 通过 |

## 编译器报告

```text
RankReflection.rankElementaryInclusion_unbounded.{u} {a b c : Cardinal.{u}}
  (hAB : a < b) (hBC : b < c)
  (hElemAB : RankReflection.RankElementaryInclusion a.ord b.ord)
  (hElemBC : RankReflection.RankElementaryInclusion b.ord c.ord)
  (xi : Ordinal.{u}) :
  xi < b.ord → ∃ delta, xi < delta ∧ delta < b.ord ∧
    RankReflection.RankElementaryInclusion a.ord delta

'RankReflection.rankElementaryInclusion_unbounded' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'RankReflection.exists_rankElementaryInclusion_between' depends on axioms:
  [propext, Classical.choice, Quot.sound]
RankReflection kernel audit passed: 102 theorem constants;
  axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (1244 jobs).
```

公理审计属于默认构建的一部分；出现任何其他公理会直接导致构建失败。
另行扫描全部新 Lean 源码，未发现 `sorry`、`admit`、`native_decide`、`sorryAx`、
顶层 `axiom` 或 `unsafe` 声明。新模块没有编译警告；输出中只有既有依赖的提示。

## 规模和复现范围

- 新增 12 个 Lean 文件，共 905 个物理行，795 个非空行，包含根入口和审计模块。
- 上述统计不包含 FullMarkedBLP、Mathlib 或其他复用依赖。
- 实际代码量低于规划估计，主要因为通用量词限制转换直接复用了旧库的真值矩阵，
  初等包含自身也足以推出全部所需高度条件。
- 原始验收使用已有本地依赖缓存。公开版本已改为 Git 依赖，所有提交在
  `lake-manifest.json` 中锁定，不再要求本机目录布局；版本与原始验收一致。
- GitHub Actions 在全新 Ubuntu 检出中检查源码哈希、下载依赖缓存、构建全部模块，
  并重新运行完整项目公理审计。当前运行状态见
  [验证工作流](https://github.com/EgoFakeFantasy/RankElementarity/actions/workflows/lean.yml)。
- 本成果是 Lean/Mathlib 中关于实际 `ZFSet` 的数学定理，不包含另外的
  YesMetaZFC 对象级推导证书。

机器可读快照及源码哈希见 `verification.json`；依赖提交见 `dependencies.json`。
