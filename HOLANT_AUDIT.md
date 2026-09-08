# Holant 统一归纳独立审查

审查日期：2026-09-09。范围：固定 ambient graph 的归纳方案，以及 `HolantAmbientGraph`、`HolantShellSelection`、`HolantPaths`、`HolantInductiveExterior`、`HolantSeparatorEstimates`、`HolantSeparatorResponse`、`HolantPathParent` 与实际模型、残余签名、Gibbs 边缘的接口；最终复核覆盖 `HolantUniformResponse`、`HolantStrongInduction`、`HolantTubeTheorem` 与 `HolantTheorem.exists_uniform_holant_polytube`。

**结论：未发现该统一归纳方案的数学循环、空壳例外或零活动漏洞；正文统一 Holant polytube 主定理已由真实强归纳和量词封装完成。** 允许空的 ambient shell 可以统一覆盖小连通分量，无须另设连通分量分支。`uniform_response_step` 已实际调用耦合、shell 选择和 separator 估计，`uniform_path_nonzero_and_response` 已由同时强归纳消去所有小实例假设，`exists_uniform_holant_polytube` 已从原始签名得到图规模无关的独立坐标非零性。它的公开假设中没有待证的耦合、响应界或非零性质。

## 已核查的关键点

- **删除后仍可使用原 metric。** `ambientLineGraph G` 把原图非边置为孤立点；`ambientLineGraph_compatible` 只要求当前边集包含于原图边集，确保当前共享端点的不同边在 ambient graph 中相邻。BFS 内外分离只使用这一方向，不需要删除前后距离相等。当前边集与固定球壳取交后，仍保持分离、层间不交以及统一球体积上界。原图不连通时，不可达边自然进入 exterior，证明仍有效。
- **归纳严格下降。** exterior 排除根边；改变一个 shell 位的 bridge 边集为 `insert a exterior`，仍排除原根边。因此这两个实例都严格小于当前实例。`exists_inductive_exterior_logs` 对整个参数圆盘调用小实例非零性，再对严格较小 bridge 调用响应界，没有借用当前实例的非零性。
- **`ResponseBound` 不被真空使用。** 该定义单独看是对所有归一化解析 logarithm 的条件式断言。`PathParent.exists_response_log` 明确用两个较小子实例在整个圆盘上的非零性构造实际 logarithm，再使用响应界。因此全局归纳必须同时输出非零性和响应界，并保留这一调用顺序。
- **零边、一条边与空 shell。** 空 normalized instance 的配分函数为 1。空 shell 的共同可行状态集只有空集，Hamming 邻接条件真空、振幅为 0；exterior 仍因排除根边而严格较小。一条边时两个 child 都无边，同样落入上述规则。`layers_pos` 只要求所选层数正，不要求任一当前 shell 非空。
- **不可行 one-child。** `complexPartition_dead_edge` 从真实有限和推出父模型等于 zero-child；此分支不需要构造不存在的归一化 one-child。幸存分支的两端首项正性由 `OneSurvives` 明确提供。
- **零活动与共同支撑。** shell 状态由 signature 结构可行性决定，而非实际活动权重决定。零活动产生零概率但不会删去结构状态。`law_eq_projected_gibbs` 已把 typed law 证明为实际 Gibbs 投影；fallback 只作用于零质量状态。局部误差为 `D(z)-D(x)`，从不除以 `D(x)` 或活动。`exterior_real_le_child` 对共同域中 one-child 不可行的状态也成立，故其误差比较没有隐藏的正概率假设。
- **解析分支与独立活动。** 外部 logarithm 从小实例在同一圆盘上的非零性构造，差分再由 bridge 响应界控制；`continued_additive_response` 用归一化解析分支唯一性对接实际响应，不假设配分函数值全局避开主值分支切线。`exists_activity_path_to` 将任意严格逐坐标扰动嵌入一个半径大于 1 的解析圆盘，允许各坐标独立变化。
- **常数不依赖图规模。** `TransferParameters` 仅依赖 `D,A,R,C`；`D=2(Δ-1)`、残余族增长界 `A` 与耦合常数 `C` 可仅由 `Δ,F,R` 给出。localSize 取固定 ambient 球上界，局部系数只涉及局部选边数；任意多个孤立顶点的 normalized 因子均为 1，不引入顶点数依赖。使用比正文更保守的球界和更小半径，不削弱其存在性结论。

## 最终全局主定理审查

已逐项复核 `HolantTheorem.exists_uniform_holant_polytube` 的 Lean 声明及其实际证明：

1. **统一宽度的量词顺序正确。** 声明为固定 `F, Δ, R` 后先取 `∃ ε > 0`，再量化 `∀ (V : Type u) [Fintype V] [DecidableEq V]`、图 `G`、原始签名赋值 `f` 和独立活动 `z`。证明在引入这些对象之前调用 `exists_transferParameters`。没有以固定实例的紧性半径替代图族统一半径。声明具有宇宙参数 `.{u}`，可以在任意顶点类型宇宙实例化；数值参数构造不含顶点类型或宇宙数据。
2. **只约束真实边。** 活动函数的载体虽为 `Sym2 V → ℂ`，前提明确仅量化 `e ∈ G.edgeFinset`，并为每条真实边独立选择 `[0,R]` 中的锚点。非边坐标完全自由，`partition_congr_activities` 证明它们不影响配分函数。因此任意真实边活动赋值在非边处作任意延拓均适用。`R` 在所有边的选择之前固定。
3. **原始签名条件与正文一致。** `Signature` 的字段正是有限 arity、非负值、正支撑为区间、相邻对数凹性以及 `f(0)>0`；arity 外补零只是有限签名的编码。公开定理只要求每个 `f v ∈ F` 和 `(f v).arity = G.degree v`，没有要求原始签名已归一化，也没有额外限制 `F` 中未被使用的 arity。`F : Finset Signature` 表达任意有限签名族。`Fintype` 和 `DecidableEq` 是有限类型及其可经典取得的比较结构，不增加数学限制。定理允许任意 `Δ : ℕ` 与 `R ≥ 0`，包含正文 `Δ ≥ 2, R > 0` 的范围。
4. **实际完成路径和归一化转换。** `graphPartition_ne_zero_of_paths` 调用 `exists_activity_path_to` 构造半径大于 1 的解析路径，并在内部参数 `1` 处使用非零性；随后实际调用 `complexPartition_normalize`，利用每个原始 `f_v(0)>0` 所给出的非零标量乘积返回原始 graph partition。没有保留条件式转换所需的证明义务。
5. **同时强归纳已经闭合。** `uniform_path_nonzero_and_response` 以实际的 `uniform_response_step` 作为归纳步。后者由真实 Gibbs 耦合界选择共同 shell，再用严格较小 residual instances 的实际解析 logarithm 完成 separator 响应估计。公开 polytube 定理不含该归纳步、coupling independence、`ResponseBound` 或子实例非零性作为输入。
6. **拓扑与容量推论已完成最终验收。** `HolantCorollaries.lean` 的 `holant_uniform_tubes` 已将真实统一主定理代入全部应用接口。Holant、`b`-matching 和 `b`-edge-cover 的公开结论均不保留 `UniformGraphTubes` 输入；正交锥并集在同一实盒的坐标乘积之后取并，对角开集在所有图之前选定。覆盖结论始终使用用户原始容量 `b`，`degree-b` 只出现在实际补集证明内部。真实空边集也包括在内。

最终全工程检查（2026-09-09）：`scripts/check.sh` 成功，构建 3626 jobs，3740 个项目声明的传递公理审计通过；仅使用 `propext`、`Classical.choice`、`Quot.sound`。46 个 Holant 模块全部从 `CI2ZF.lean` 可达，最终入口为 `HolantTheorem.lean` 和 `HolantCorollaries.lean`。

`HolantTheorem` 已严格构建成功（3466 jobs）。独立运行 `#check`（开启宇宙显示）确认上述公开量词；`#print axioms CI2ZF.Holant.uniform_path_nonzero_and_response` 与 `#print axioms CI2ZF.Holant.exists_uniform_holant_polytube` 均仅返回 `propext`、`Classical.choice`、`Quot.sound`。最新 Holant 源文件检索未发现 `sorry`、`axiom` 或 `native_decide`。此前对真实删除递推、separator 展开、`M+E` 恒等式、实际 Gibbs 投影和 typed transport 六项关键定理，以及四个 tube lifting 定理的公理审计也仅包含这三个标准逻辑公理。
