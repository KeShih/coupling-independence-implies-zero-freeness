# Coupling Independence Implies Zero-Freeness — Lean

这是《Coupling Independence Implies Zero-Freeness》正文 Potts 与 Holant 部分的形式化。两个模型的完成状态分别记录，不能相互替代。

**Potts：严格阈值 `q > 11Δ/6` 的统一无零点主定理已完成；实际 CI、两端联合归纳、统一半径与拼接均通过 Lean 检查。等号情形仅保留明确的外部硬着色 CI 输入。** 任意诱导子图封闭图族的 transfer 版本仍在补齐。没有以公理或占位证明掩盖未完成步骤。

**Holant：正文部分已完整形式化。** 已证明残余引理、实际 CI、统一复 polytube 主定理、开放正交锥与统一对角邻域，以及 b-matching 和 b-edge-cover 的全部正文推论。最终入口不保留未证明的外部输入，46 个 Holant 模块均已接入全库构建与公理审计。

## Potts 已证明的结果

| 论文中的内容 | Lean 文件与核心结果 |
| --- | --- |
| 真实有限简单图、任意 pinning 的复配分多项式；与实数模型一致 | `CI2ZF/PottsModel.lean`：`normalizedPartition_ofReal` |
| 去除 pinned-only 单色边的强制零因子，等式在零点也成立 | 同上：`fullPolynomial_eq`、`fullPartition_eq` |
| q ≥ Δ+1 时硬可行性、归一化配分函数在所有非负实参数处非零 | 同上：`exists_hardAdmissible_of_succ_le`、`normalizedPartition_nonnegative_ne_zero` |
| 正文实际新增一个 pinned 顶点的递推；包括 blocked 颜色的 normalized child | 同上：`normalizedPartition_pinVertex_recursion`、`rootChildPartition_zero_ne_zero` |
| 复平均引理：两个平均非零，Log 比较常数为 2A W+4δ | `CI2ZF/PaperComplexAverage.lean`：`paper_complex_average` |
| 从零同时缩放得到的规范化 Log 分支 | 同上：`differentiableOn_scaledCenteredAverageLogRatio`、`exp_scaledCenteredAverageLogRatio` |
| 不相交 shell 上的真实边缘分布满足 Σ W ≤ 全局 W，并可选出小 W 的 shell | `CI2ZF/ShellMarginals.lean`：`sum_W_shellMarginal_le`、`exists_low_W_shellMarginal` |
| 给定有限局部多项式族的统一相对扰动控制；零点与正温邻域拼接 | `CI2ZF/LocalStability.lean`：`finite_polynomial_relative_stability`、`patch_endpoint_and_positive` |
| 非零圆盘上的规范化解析对数存在与唯一性 | `CI2ZF/AnalyticLog.lean`；真实 Potts 实例的接口在 `CI2ZF/PottsAnalytic.lean` |
| 原始 pinned 配分多项式在零点的重数恰等于 pinned-only 单色边数 | `CI2ZF/PottsAnalytic.lean`：`fullPolynomial_rootMultiplicity_zero` |
| 每个固定图和 pinning 在 [0,1] 附近有某个正的零自由半径 | `CI2ZF/FixedGraph.lean`：`fixed_instance_zero_free`、`fixed_instance_zero_free_of_vigoda` |

这些定理处理任意 pinning，不要求 pinned 部分本身为 proper colouring。归一化通过有限多项式直接定义，没有在零点除以零。

复平均引理保留正文的振幅条件，而没有额外要求原始 h 的范数小。证明先共同中心化，使两个平均位于 1 附近，再控制其主值对数之差。缩放分支在零参数取零，并指数化为原始平均的商。有限运输距离使用 `PottsCI.FinDist.W` 的耦合成本下确界定义；这是有限分布实现，未对接 mathlib 的一般测度 Wasserstein 接口。证明不需要假定最优耦合存在。

## Potts coupling independence 的实际证明链

这里始终使用真实有限图、列表约束和 `hardStep` / `softVigodaKernel` 的转移概率。

| 环节 | 已通过 Lean 检查的结果 |
| --- | --- |
| 具体硬分量翻转的保合法性、可逆性与平稳性 | `PottsCI/Vigoda/ComponentCoupling.lean` |
| 可行分量的精确转移质量 `p_s/(nq)`，holding 质量至少 `1/q` | `CI2ZF/HardMoveMass.lean` |
| 共同 Bernoulli 激活的真实联合分布、边数期望与根列表预算 | `CommonCoins`、`ActivationLaw`、`ActivationAverage`、`ActiveDegree` |
| 新增一条真实边界约束的硬/软转移扰动界 | `HardFlipBoundary`、`BoundaryActivation`、`SoftFlipBoundary` |
| 真实删根模型与两种新增 pinning 的边界比较 | `RootChildren`、`RootBoundary` |
| 共同根外翻转、全量根分量配对、按邻居分摊的实际残余匹配 | `HardConditionalCoupling`、`HardRootAllocation`、`HardRegularAllocation` |
| 所有剩余正概率转移的完整分类 | `HardMoveClassification.hardCommon_residual_exhaustion` |
| 普通颜色的完整 `11m/6−allowed` 界，覆盖 0/1/2/≥3 邻居和 blocked 情形 | `RegularColourTwo.perColourCharge_le` |
| 两个根颜色的实际匹配规则、容量、合并及完整费用界 | `HardRootColours`、`RootColourCharge.rootColourCharge_le` |
| 所有颜色的实际分配同时满足转移概率容量；乘积补齐得到完整耦合 | `HardRootColourSeparation.fullHardPartial` / `fullHardCoupling` |
| 所有颜色的费用合计不超过 `11/6 × unionDegree − commonListCard` | `HardChargeSum.sum_hardColourCharge_le` |
| 实际转移状态、不同分量和 scalar residual/share 的精确等式 | `HardRegularRates`、`HardIncidenceRates`、`HardPieceSums` |

数值证书使用实际 Vigoda profile `1, 13/42, 1/6, 2/21, 1/21, 1/84, 0, …`。先证明将尺寸截断到七保持整个费用表达式，再用 Lean 内核检查有限整数案例；没有使用 `native_decide` 或信任外部 Python 数值输出。

`HardCouplingCost.hardStep_W_drift_le` 已完成最后的全局成本汇总，直接给出真实硬核的条件漂移界。`PottsCITheorem.conditionalHardCouplingEstimate` 将它应用到共同激活；`PottsCITheorem.lean` 中的下列定理消去了 `RootCI.lean` 条件接口的最后硬耦合输入：

- `root_strict_ci`：对 `q > 11Δ/6` 和 `x∈[0,1]`，真实根条件分布的 Hamming Wasserstein 距离不超过 `2(1−x)Δ / (q−11(1−x)Δ/6)`。
- `root_strict_uniform_ci`：同一严格区间的统一常数 `2/(q/Δ−11/6)`，量化所有有限图和任意 pinning；包括 x=0、x=1 和空的剩余图。
- `root_critical_uniform_ci`：当 `q=11Δ/6` 时，在任意 `[δ,1]`、`δ>0` 上给出 `12/(11δ)`。

这些定理不要求调用者提供匹配、容量、漂移、收缩或平稳性假设。临界等号的零温 CI 作为用户允许保留的明确外部输入处理，不能从发散的 `12/(11δ)` 界令 δ 趋零得到。准确接口与来源见 [EXTERNAL_INPUTS.md](EXTERNAL_INPUTS.md)。

`OptionCI.lean` 还将同一完整结论推广到任意边界颜色计数的 `PinningData (Option O) C`：`none` 是根，`O` 是共同剩余顶点集。该接口保留度约束，允许重复边界计数，供分隔后的较小实例使用。`RootGibbsSemantics.lean` 证明这些归一化分布与原图条件权重的关系：正活动参数时直接一致；零点原图条件分布需要 pinned 部分可行，而 normalized child 对任意 pinning 都有定义。

## Potts 图上的分隔恒等式

`Separator.lean` 在显式顶点分解 `U ⊕ (S ⊕ O)` 和真实无 U–O 边条件下，从原始有限配分和证明内外因式分解。等式在任意交换半环上成立，因而也包括复活动参数和零点。

`SeparatorResponse.lean` 将复配分函数响应写成真实 Gibbs 壳边缘分布下的内外响应乘积的平均。`SeparatorExterior.lean` 把外部因子进一步识别为 O 上真正的较小 `PinningData` 配分函数，S–O 边成为边界颜色计数。这里没有把分隔等式作为假设传入。

`BoundedLocalFamily.lean` 进一步证明有限局部多项式族的实际编码：自由顶点数不超过 B、最大度不超过 Δ 时，至多有 `q^B` 个单项式，每个次数不超过 `2BΔ`。`bounded_local_potts_relative_stability` 因而给出只依赖颜色数、Δ、B、紧实轴基点集合和误差容限的半径，量化所有顶点类型及任意 pinning；有限性不是外加假设。

以下从实际模型到分析估计的连接也已完成：

| 环节 | 文件及已证明内容 |
| --- | --- |
| 真实 BFS 球与球面、球大小界、无内外跨边、空球面与有限分量 | `BFSShells`、`BFSShellMarginals` |
| 将已证明的 CI 用于父图 BFS，得到真实根子分布的小运输代价球面 | `OptionShellMarginals.strict_root_exists_low_sphere`，覆盖严格区间的两个端点 |
| 图重标号的有限乘积和配分函数不变，BFS 重标号保留度界 | `SeparatorRelabel`、`SeparatorDegree` |
| 根连通分量分解与两子项共同外部因子的消去 | `ComponentFactorization`、`RootComponentFactorization` |
| 实际 inside 因子的单项式表达、有限编码、正温统一稳定性、零点加性误差 | `SeparatorInsidePolynomial`；固定 shell 不需要在零点可行 |
| 统一局部稳定性产生整个活动圆盘上的小解析 Log | `LocalResponseLog.bounded_inside_positive_log_stability` |
| 解除一个 shell 顶点的 pinning 得到严格更小的实际模型 | `OptionPinning`、`ExteriorRepinning` |
| 较小根响应界经解析分支唯一性得到外部响应的完整 Hamming Lipschitz 界 | `ExteriorAnalyticResponses`、`HammingResponses` |
| 实际根子项的硬计数比较 `Z_d(0) ≤ q^Δ Z_e(0)` | `HardCountComparison`，由局部重着色及计数注入证明 |
| 真实 shell 单坐标硬权重比较与可行锚点 | `ExteriorHardComparison`、`SeparatorHardAnchor` |
| 硬端点有限缺陷和的统一界 `q^(N+s) H^s exp(αs) |z|` | `HardEndpointRelativeError`，保留锚点响应因子 |
| 实际硬分隔响应等于可行主平均加缺陷项 | `SeparatorHardResponse`，不除以可能为零的 inside 因子 |
| 主平均的模下界、缺陷商和修正 Log 的控制 | `HardMainPerturbation` |
| 在实际活动变量上继续的正温/硬端点平均 Log 界 | `AnalyticComplexAverage`、`HardAnalyticAverage` |
| 给定小的子响应 Log 时实际父递推非零 | `PositiveParent`、`HardParent`；硬端点的可用根颜色和硬计数比自动证明 |
| 任意边界计数数据的实际父递推，在任意交换半环上成立 | `OptionPartition.option_parent_partition` |
| 给定外部坐标响应界时实际硬分隔实例非零 | `HardSeparatorStep`，锚点、硬权重及缺陷界均已消去 |

表中的单步辅助定理保留合法的较小实例假设。`UniformInduction`、`PositiveUniformTransfer`、`HardUniformTransfer` 已通过实际强归纳消去这些假设；最终 `PottsMainTheorem` 不要求调用者提供任何复非零性或响应界。

## Potts 统一主定理

`fixed_instance_zero_free_of_vigoda` 已证明正文参数条件下的固定实例结论，但其量词顺序是：

\[
\forall G,\tau,\quad \exists\varepsilon(G,\tau)>0,\quad
\widetilde Z_G^\tau(z)\ne0\quad
(\operatorname{dist}(z,[0,1])<\varepsilon(G,\tau)).
\]

现在 `strict_potts_zero_free` 已证明先选半径，再量化所有图和 pinning：

\[
\exists\varepsilon(q,\Delta)>0,\quad \forall G,\tau,\quad
\widetilde Z_G^\tau(z)\ne0\quad
(\operatorname{dist}(z,[0,1])<\varepsilon(q,\Delta)).
\]

固定实例结论仅需 q ≥ Δ+1；统一结论使用完整 CI 机制。最终入口 `CI2ZF/PottsMainTheorem.lean` 包含 `strict_potts_zero_free`（无外部 CI 假设）、`critical_potts_zero_free`（仅外部硬 CI）与合并弱不等式的 `potts_zero_free`。结论还给出非归一化配分函数的强制零点及其精确重数。

| 完成的连接 | 模块 |
| --- | --- |
| 同一父图 BFS 分隔与真实 Gibbs 边缘识别 | `OptionBFSSplit`、`OptionBFSCardinality`、`GenericGibbsRelabel`、`OptionBFSMarginals` |
| 正温及零温大分量实际解析响应界 | `PositiveSeparatorLog`、`HardSeparatorLog`、`PositiveBFSResponseStep`、`HardBFSResponseStep` |
| 图无关的深度、体积、对数预算与局部半径 | `TransferScales`、`UniformLocalLogs`、`TransferLocalControls` |
| 任意根重标号、小分量消去和父递推 | `RootOptionRelabel`、`OptionComponentFactorization`、`OptionParentNonzero` |
| 按实际自由顶点数的同步强归纳 | `UniformInduction`、`InductionComponentSteps`、`InductionParentSteps` |
| 两端完整归纳与原图主结论 | `PositiveUniformTransfer`、`HardUniformTransfer`、`UniformZeroFreePackaging`、`PottsMainTheorem` |

## Potts 尚待完成的关键链条

原文 transfer 允许任意对诱导子图封闭的图族，并只假定该族中原图的所有 pinning 满足 CI。当前 `bounded_degree_potts_transfer` 使用全部满足度界的 `PinningData` 的 CI。要覆盖原文较一般的量词，仍须证明各分隔、解除 shell pinning 和删根步骤属于同一可实现图族，再将归纳限于该族。不能仅要求自由图在图族中，因为一般图族不一定对添加用于实现边界计数的叶子封闭。

该补充正在 `PinningRestriction`、`PinningFamily` 及相关 family/ambient 模块中完成。未完成模块不导入主入口。临界硬端点按用户授权保留为明确外部输入，不作为未完成的正文证明步骤。

## Holant 的统一零自由证明链

`HolantModel.lean` 从实际有限图上的边子集和定义布尔 Holant 配分函数；每个顶点的签名只依赖所选关联边数。`Signature` 同时记录有限元数、非负性、无内部零点的支撑、对数凹性和 `f(0)>0`。对一个有限签名族 F 和度上界 Δ，半径只依赖 F、Δ 和实盒上界 R，在量化图、顶点签名和独立边活动参数之前选择。

| 环节 | 文件与关键入口 |
| --- | --- |
| 支撑为初始区间、交叉比值单调、归一化残余的复合与有限封闭族 | `HolantSignatures.lean`：`ratio_cross_le`、`shift_monotonicity`、`normalizedResidual_comp`、`residualFamily_closed` |
| 实际归一化模型、删边的零/一子实例、非归一化模型的恢复、死边分支 | `HolantResidualModel.lean`：`complexPartition_deletion`、`complexPartition_dead_edge`、`complexPartition_normalize` |
| 实际 Gibbs 分布上的端点递归耦合及精确 CI 常数 | `HolantCouplingTheorem.lean`：`residual_family_sharp_child_W_le` |
| 图线图的度界、实际球面及有界局部球、低运输成本球面的选取 | `HolantGeometry.lean`、`HolantAmbientGraph.lean`、`HolantShellSelection.lean`、`HolantShellCostSelection.lean` |
| 实际内外分隔恒等式、共同可行 shell 状态及两子项的真实边缘分布 | `HolantSeparator.lean`、`HolantInstanceSeparator.lean`、`HolantShellMarginals.lean` |
| 局部多项式系数界、多重线性扰动界及统一数值预算 | `HolantCoefficientBounds.lean`、`HolantSeparatorCoefficients.lean`、`HolantPolynomialStability.lean`、`HolantTransferParameters.lean` |
| 从较小实例构造实际外部解析 Log，并沿可行布尔路径累积响应 | `HolantInductiveExterior.lean`、`HolantSupportGeometry.lean`、`HolantShellLipschitz.lean` |
| 两子项的实际分隔误差、解析平均延拓和父递推非零 | `HolantSeparatorEstimates.lean`、`HolantSeparatorResponse.lean`、`HolantAnalyticContinuation.lean`、`HolantPathParent.lean` |
| 用上述实际对象完成响应归纳步 | `HolantUniformResponse.lean`：`uniform_response_step` |
| 按剩余边数同时归纳非零性与子项 Log 响应界 | `HolantStrongInduction.lean`：`path_simultaneous_of_response_step` |
| 消去响应步骤回调和全部较小实例假设的总入口，先选半径再量化所有图 | `HolantTheorem.lean`：`uniform_path_nonzero_and_response`、`exists_uniform_holant_polytube` |
| 将路径结论提升到原始配分函数、polytube、正交锥和对角邻域 | `HolantTubeTheorem.lean`、`HolantPolytube.lean` |
| 有容量匹配与补集覆盖的模型恒等式及通用应用 | `HolantCapacities.lean`、`HolantApplications.lean` |
| 消去应用接口输入的全部正文推论 | `HolantCorollaries.lean`：`holant_orthant`、`holant_uniform_diagonal`、`bmatching_uniform_polytube`、`bmatching_orthant`、`bmatching_uniform_diagonal`、`bcover_uniform_polytube`、`bcover_orthant`、`bcover_uniform_diagonal` |

Holant 的 CI 也在库内完整证明，最终定理不要求外部 CI 假设。证明使用实际 `signatureGibbs` 权重、归一化零/一子分布、剩余质量的递归耦合以及有限分布的 `FinDist.W`。若 A 是归一化残余族的一阶签名值与 0 的最大值，则 `residual_family_sharp_child_W_le` 给出正文常数

\[
C=2\bigl((1+A^2R)^\Delta-1\bigr).
\]

零活动坐标直接由真实分布和零权重事件处理，无需假定活动参数严格为正。边子集的对称差成本与布尔 Hamming 成本之间的等式也已证明。

`HolantUniformResponse.lean` 将这个 CI 界用于实际球面边缘分布，并构造共同的有限 shell 状态空间、分隔系数及外部响应。局部系数由残余签名的统一增长界控制；局部多项式的扰动误差通过显式多重线性估计得到，允许实基点处某些局部因子为零。所用可行锚点、空状态的正权重、实际外部模型和相邻状态对应的较小桥接实例均由模型定义证明，没有作为调用者需提供的假设。

几何实现采用一个与正文等价的组织方式：固定原始图的线图作为环境图，每一步把它的球面与当前剩余边集相交。已经删去的边以及非边坐标不参与配分函数。环境图的度仍由 `2(Δ−1)` 控制，局部球有只依赖 Δ 和球面层数的大小界；空交集球面也作为合法分隔统一处理。这样无需在每个递归实例重建距离，也无需另设空球面的局部证明分支。外部和桥接实例的边数严格下降、无内外跨边以及实际 shell 运输界都在 Lean 中逐项证明。

`HolantStrongInduction.lean` 是保留响应步骤回调的通用装配引理；`HolantTheorem.lean` 用 `uniform_response_step` 消去该回调，同时归纳剩余实例的非零性和规范化解析 Log 响应界。最终路径定理只保留签名族、图的度界、实盒范围及已构造的统一数值参数，不保留耦合、分隔等式、外部 Log 或较小实例非零假设。空边集和死边也在同一归纳中处理。

对任意有限签名族 F，结论的量词顺序是

\[
\forall\Delta\in\mathbb N,\ R\ge0,\quad
\exists\varepsilon(F,\Delta,R)>0,\quad
\forall G,f,\boldsymbol{x},\boldsymbol{z},\quad
\left(\boldsymbol{x}\in[0,R]^{E(G)}\quad\land\quad
|z_e-x_e|<\varepsilon\ \forall e\right)
\Longrightarrow Z_{G,f}(\boldsymbol{z})\ne0,
\]

其中 G 为最大度不超过 Δ 的有限简单图，顶点签名来自 F，且元数等于其度。这是整个图族统一的独立活动参数结论。`HolantTubeTheorem.lean` 中名称以 `_of_paths` 结尾的引理负责几何提升，其路径输入由总入口消去；它们本身不是另一个外加零自由假设。

`HolantPolytube.lean` 将不同 R 的实盒 polytube 取并，得到包含整个非负正交锥的开邻域；先在同一个 R 上取坐标乘积，再对 R 取并。对角特化得到一个包含非负实轴、对所有图统一的复平面开邻域。`HolantCapacities.lean` 把容量签名与实际 b-matching 多项式对应，并通过边集补集证明 b-cover 的倒数活动恒等式；覆盖应用在严格正的实活动区间使用已证明的倒数 polytube 界。上述覆盖条件包括每个顶点的需求不超过其度。

## 构建与验证

固定版本：Lean **4.33.1**；mathlib **v4.33.1**，commit `0df444a360eaa60ab8c11dca51a86af692955474`。其余依赖记录在 `lake-manifest.json`。

安装 Lean 版本管理器 elan 后，在仓库根目录执行；`lean-toolchain` 会选择所需版本：

```bash
lake exe cache get
./scripts/check.sh
```

该命令先构建 `CI2ZF.lean` 导入的全部证明，再运行 `AxiomAudit.lean`。两步都将 warning 视为错误。公理审计遍历 `CI2ZF` 和 `PottsCI` 命名空间中的所有声明，检查其传递公理依赖；仅允许 `propext`、`Classical.choice`、`Quot.sound`，发现其他依赖即失败。证明库不导入审计程序。

最近一次实际合并检查（2026-09-09，Holant 最终入口已全部导入）：构建通过（3626 jobs），3740 个项目声明的传递公理审计通过。入口包含 Potts 与 Holant 模块，该数目是整个导入库的声明数，不是论文定理的数量。Holant 共 46 个模块、8076 行 Lean 源码；全部从聚合入口可达。逐文件校验记录见 `holant-source-manifest.json`。

当前机器的官方 Lean 编译器安装在本目录的 `.tools/` 内，`scripts/lake.sh` 自动选用它；没有修改全局 Lean 环境。`.tools/`、`.lake/` 和缓存不属于源代码交付。在其他机器使用 `lean-toolchain` 指定的 Lean/Lake 安装依赖后，也可运行同一检查脚本。

## 代码来源与范围

`CI2ZF/` 是针对当前正文新增的证明，其中 `PartialCoupling.lean` 的通用残余补齐基础节选自旧项目并继续扩展。`PottsCI/` 的有限分布、路径耦合、图模型、pinning、活动约束、具体 Vigoda 核和平稳分布比较等 11 个模块，复用了此前的 `CI2ZF/anc/lean-potts-ci` 项目，并修复 Lean 4.33.1 的兼容问题及分量几何证明问题。导入前各文件哈希见 `legacy-source-manifest.json`；当前论文源文件和工具链的来源记录见 `source-manifest.json`。

复用的通用 `SoftKernel` 接口已在 `Vigoda/ComponentCoupling` 中实例化为具体 Vigoda 核，并证明其平稳性。端点连续性和 stationary comparison 的应用见 `CouplingIndependence` 与 `RootCI`；临界硬端点通过 `CriticalHardColouringInput` 显式传递，没有加入自定义公理。

本目录当前范围包括上述正文 Potts 主定理与 Holant 证明链。Potts 的一般图族 transfer、以及其他未列出的外场与高 girth 等扩展，不因新增结果而视为已经覆盖。
