# 正文 Potts 证明的外部输入

用户允许不形式化证明明确的外部输入。库采用显式定理参数表示此边界，不使用 `axiom`、`sorry` 或绕过内核的证明。

## 临界等号的硬着色 coupling independence

来源：[Chen–Feng–Guo–Zhang–Zou, *Deterministic counting from coupling independence*, arXiv:2410.23225v2, Theorem 20](https://arxiv.org/html/2410.23225v2)。原文第二个参数范围在 `Δ ≥ 3`、`q ≥ (11/6 − ε₀)Δ` 下给出只依赖 `q,Δ` 的有限 Hamming CI 常数，覆盖需要的临界等号。其证明明确允许不 proper 的部分着色，并以剩余列表模型定义条件律。

代码中的准确接口是 `CI2ZF.Potts.CriticalHardColouringInput`，定义在 `CI2ZF/TransferCouplingInputs.lean`：存在一个实常数 `cost`，使所有满足度约束的实际 `PinningData (Option O) C` 在活动参数零处，两种根颜色的归一化 child Gibbs 律满足 `W ham ≤ cost`。根已从两种配置的共同状态空间中删除；省略 pinned-only 约束。这是正文使用的 normalized root CI 形式。

`critical_transfer_coupling_inputs` 在此参数之外，调用已经完成的正温 CI 证明。`critical_potts_zero_free` 再调用完整的正温、零温强归纳与端点拼接。`potts_zero_free` 仅在等号分支使用该输入。

`strict_potts_zero_free` 不需要这个输入，也不需要任何待证耦合、收缩、平稳性或复非零性假设。

## 内核审计的含义

显式数学假设不会成为 Lean 的额外公理。所有导入定理的传递公理依赖仍仅为 `propext`、`Classical.choice`、`Quot.sound`。因此审计通过同时意味着没有隐藏占位证明；它不意味着 Lean 已证明上述外部硬 CI 参数成立。
