# Appendix Potts 证明导航

七个区域的统一入口是 [CompletedRegions.lean](../../CI2ZF/Appendix/CompletedRegions.lean)。定理的完整条件与外部文献输入见 [STATUS.md](STATUS.md)；旧、新模块路径的逐项对应见 [MODULE_MOVES.tsv](MODULE_MOVES.tsv)。

| 区域 | 主要入口 |
| --- | --- |
| Near-Vigoda 区域 | [NearVigoda/Theorem.lean](../../CI2ZF/Appendix/NearVigoda/Theorem.lean) |
| Carlson–Vigoda 1.809 区域 | [CV/ZeroFree.lean](../../CI2ZF/Appendix/CV/ZeroFree.lean)，[CV 聚合入口](../../CI2ZF/Appendix/CV.lean) |
| Edge-Potts 区域 | [Edge/ZeroFree.lean](../../CI2ZF/Appendix/Edge/ZeroFree.lean) |
| 大 girth 区域 | [Girth/High/Theorem.lean](../../CI2ZF/Appendix/Girth/High/Theorem.lean) |
| 高温区域 | [HighTemperature/ZeroFree.lean](../../CI2ZF/Appendix/HighTemperature/ZeroFree.lean) |
| BBR 大 girth 区间 | [BBR/High.lean](../../CI2ZF/Appendix/BBR/High.lean) |
| 固定 girth 五区域 | [Girth/Five/ZeroFree.lean](../../CI2ZF/Appendix/Girth/Five/ZeroFree.lean) |

三个 girth 区域的论文原图结论统一见 [Girth/Transfer/ResidualOriginal.lean](../../CI2ZF/Appendix/Girth/Transfer/ResidualOriginal.lean)：允许任意原图 pinning，只要求自由残余图满足相应 girth 条件，girth 五与 q≥Δ+3 两区域还刻画完整多项式的强制零点及其精确重数；BBR 区域在避开零的正温邻域中证明归一化与完整配分函数均非零。

## Girth 五的阅读顺序

1. 谱隙：[Five/Poincare.lean](../../CI2ZF/Appendix/Girth/Five/Poincare.lean) 与 [Five/ClosedPoincare.lean](../../CI2ZF/Appendix/Girth/Five/ClosedPoincare.lean)。具体图上的 heat-bath、star 和 Schur 证明位于 `Girth/Spectral/`。
2. 插入估计：[Covariance/Insertion/ActualEstimates.lean](../../CI2ZF/Appendix/Girth/Covariance/Insertion/ActualEstimates.lean)，连接实际插入律与已证明的谱隙。
3. 逐点条件化：[Covariance/Doob/PinningVertex.lean](../../CI2ZF/Appendix/Girth/Covariance/Doob/PinningVertex.lean) 与 [Doob/ResponseBounds.lean](../../CI2ZF/Appendix/Girth/Covariance/Doob/ResponseBounds.lean)，保留完整加性源。
4. 响应归纳：[Covariance/Response/Induction.lean](../../CI2ZF/Appendix/Girth/Covariance/Response/Induction.lean) 推出 [Five/Response.lean](../../CI2ZF/Appendix/Girth/Five/Response.lean) 的统一加权源定理。
5. 球面到耦合：[Common/CLMM/Ambient.lean](../../CI2ZF/Appendix/Common/CLMM/Ambient.lean) 固定 ambient 图及其球面；[Transfer/SphereCoupling.lean](../../CI2ZF/Appendix/Girth/Transfer/SphereCoupling.lean) 对所有进一步 pinning 应用 CLMM Lemma 5.13，并处理实参数端点。
6. 复零点结论：[Five/Transfer.lean](../../CI2ZF/Appendix/Girth/Five/Transfer.lean)、[Five/ZeroFree.lean](../../CI2ZF/Appendix/Girth/Five/ZeroFree.lean) 和 [Transfer/ResidualOriginal.lean](../../CI2ZF/Appendix/Girth/Transfer/ResidualOriginal.lean)。

## 构建与审计

在仓库根目录运行：

```sh
./scripts/check-appendix.sh
```

该命令构建全部区域并执行传递公理审计。主文与 Appendix 联合检查使用 `./scripts/check-all.sh`，该命令也显式构建十个兼容入口；仅检查主文仍可使用 `./scripts/check.sh`。完整 Appendix 审计文件是 [audit/appendix/Full.lean](../../audit/appendix/Full.lean)。

## 路径兼容

此次整理只改变文件和 import 路径；声明名称与 namespace 保持不变。`CompletedRegions`、`CV`、`Regimes` 三个入口原位保留。

以下十个旧模块路径保留 import 包装，均以 `CI2ZF.Appendix.` 为前缀：`BBRHigh`、`CLMMTransfer`、`CVZeroFree`、`EdgePottsZeroFree`、`GirthHigh`、`GirthResidualOriginal`、`GirthFiveClosedPoincare`、`GirthFiveZeroFree`、`HighTemperatureZeroFree`、`NearVigoda`。其余内部模块使用 [MODULE_MOVES.tsv](MODULE_MOVES.tsv) 中的新路径。


## 正文 Lee–Yang 色场推论

上述实际硬着色 CI 同时接入正文的独立色场证明，统一入口为 [CI2ZF/LeeYang.lean](../../CI2ZF/LeeYang.lean)。覆盖 near-Vigoda、CV 1.809、大 girth `q≥Δ+3` 三个顶点范围，以及 `q≥3Δ` 的边着色范围。字段转移证明与模型语义见 [LEE_YANG_PROOF_MAP.md](../../LEE_YANG_PROOF_MAP.md)。原有七个附录证明均保留。
