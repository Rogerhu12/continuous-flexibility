# 58 个里程碑的 Lean 目标层

本目录把主蓝图的每个节点写成可展开的 Lean 命题，并用同一个穷尽索引
`Milestone.statement` 连接全部 58 个节点：主链 55 个，旁支 3 个。

这里记录的是**目标类型编译**。它不证明这些命题，不更新原蓝图或 514 项细分任务的
证明完成数，也不提供 `FlatAnnularCore`、`RadialReference` 或 `ClosedBending` 的实例。
结构自动生成的投影定理、可判定相等性定理不计作里程碑证明。

## 完整主定理

`MainGeometry.lean` 中的入口是：

```lean
def MainStatement : Prop := Nonempty ClosedBending
abbrev MAINStatement : Prop := MainStatement
```

`ClosedBending` 的字段要求标准单位球面上的光滑正定黎曼度量和联合光滑族，
每个实参数成员都是光滑嵌入，实际流形导数保持同一切空间内积，一周期，
固定真实内圆盘和补帽，存在两个像集对所有欧氏仿射等距变换均非全等。
面积使用实际像集上的规范化二维欧氏 Hausdorff 测度；体积使用真实有界内部区域的
Lebesgue 测度；向外有向平均曲率由 `df ∘ S = -dn` 和 `trace(S)/2` 定义，
并要求其在真实面积测度下可积。三项几何量均实际恒定，面积和体积为正且有限。
入口不假设分析核心、径向参考或 Nash–Moser 存在性结论。

`C00` 是规格节点。`C00Statement` 是主目标的别名，不能把接口编译解释为
`Nonempty ClosedBending` 已证，也不能将这个别名当作 MAIN 的独立存在性前提。
因此 58 个节点并不表示 58 个彼此独立的定理。

## 文件对应

| 文件 | 节点或作用 |
| --- | --- |
| `Scalar.lean` | S01/S02；S03–S05 的实际标量微分、局部发展、守恒、修正算子子目标 |
| `ScalarWeighted.lean` | S03–S05 的完整目标，连接实际加权空间、tame 估计与平坦端点 |
| `Radial.lean`、`RadialTargets.lean` | R01–R12、X01；真实谱、尾部、边框、分布图和逆的目标 |
| `Analysis.lean` | W01–W03、H01–H03；实际弱导数图、空间与微分定义 |
| `Nonlinear.lean`、`NonlinearCompletion.lean` | N01–N12、X02；实际特征、固定域、耦合逆与存在性目标 |
| `MainGeometry.lean` | C00、D01/D02、G01–G16、MAIN |
| `FiniteFourier.lean` | X03；一般正系数 E 下有限 Fourier 平方的完整阻碍目标 |
| `Milestones.lean` | 58 个节点的穷尽 Lean 索引 |
| `Audit.lean` | 实际导入项目的 owner 全声明公理及 unsafe 审计；核对 58 个闭合 Prop |
| `manifest.json`、`build.log` | 手稿定位、目标声明、源及编译产物摘要、真实编译与审计输出 |

上述都是具体函数、积分、导数、图、算子与量词；没有把未知数学性质替换为
任意输入命题。条件性局部节点仍写出其真实输入。N12 和 MAIN 的存在性目标没有
未实例化的分析存在性前提。

N01–N11 是对一套具体构造的存在性目标：每个阶段都显式存在同一参考、空间和
该阶段所需的数据，并合取它们的实际性质。没有将论文的特定构造擅自推广成
“任意满足较弱接口的参考或 chart 都能反演”。跨节点组装仍须使用同一套构造，
不能混用各个存在命题中互不相关的见证；N11、N12、MAIN 的闭合目标没有存在性输入。

三类源测度的对应分阶段落实：W02 构造物理空间及圆序列模型，R02 给实际
Liouville 线性等距同构和物理 `dr` 配对，N04 给实际 canonical Jacobian
配对，N07 给带范数界的连续源转换及同一基本解的身份。W02 不依赖尚未构造的
canonical chart；这些具体实例化的位置在逐项对应表中单列。

## 验证

在项目根目录运行：

```text
python ContinuousFlexibility/Statements/check_statements.py --build
python ContinuousFlexibility/Statements/check_statements.py
```

第一条命令设置 `LEAN_NUM_THREADS=4`，顺序编译几何审计及全量索引/审计，
检查 58 个声明的类型确为闭合 `Prop`，按实际模块 owner 检查所有导入项目声明，
包括私有辅助项和结构生成项。它拒绝项目公理、手写 unsafe/partial 声明及三条标准
逻辑公理以外的传递公理。Lean 为正常递归定义生成的运行时辅助项必须有同模块、
同类型的安全原定义，辅助项本身也接受公理检查。检查器在整个项目导入闭包上检查
源码禁用项，并保存实际输出、源摘要和编译产物摘要。核对结果还绑定原蓝图陈述及
验收条件。第二条核对已保存证据。
大型编译与总控错峰运行；此目录的目标尚需总控审查后才成为冻结的公共合同。

`manifest.json` 逐节点保留原手稿定位、验收条件和依赖。手稿与 Lean 目标之间的
数学对应仍属于人工语义审阅，不是假装由名称匹配自动证明的等价关系。
后续工作是证明这些目标、接入已有成果并完成统一组装。
