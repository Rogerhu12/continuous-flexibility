# 细分证明任务

由 `parts/*.json` 经 `check.py --write` 生成。原58节点仍是里程碑，编号和数学要求不变。

共 **514 个工作单元**：主链 494，旁支 20。完整完成 **65**，部分完成 **87**，尚未实现 **362**。

完成数对应冻结源码的局部任务陈述；原58个里程碑的状态不自动改变，实际Core及完整主定理仍须另行构造与验收。

行数区间只用于控制拆分粒度；数学难度未经实际证明校准，不能据此直接计算完成百分比或剩余总行数。

## 里程碑索引

| 里程碑 | 子任务数 | 原状态 |
| --- | ---: | --- |
| [C00 主定理语义与四个接口](#c00) | 7 | partial |
| [S01 余度量正定与余标架](#s01) | 1 | formalized |
| [S02 线性系数行列式与残差修正](#s02) | 1 | formalized |
| [R01 真实导数下的对数幂 gauge](#r01) | 1 | formalized |
| [S03 高度微分、Cartan连接与真实变分](#s03) | 7 | partial |
| [S04 归一化残差的可去延拓和守恒](#s04) | 6 | partial |
| [S05 固定类型的真实修正算子](#s05) | 7 | partial |
| [R02 Liouville变换与径向实现](#r02) | 6 | partial |
| [R03 中央谐振子模型的完整实现](#r03) | 12 | partial |
| [R04 Morse模型的两类非共振](#r04) | 11 | partial |
| [R05 真实单元、连接与累积平坦轮廓](#r05) | 11 | partial |
| [R06 深尾连续算子逆与唯一衰减线](#r06) | 16 | partial |
| [R07 过渡区与所有频率同时选高](#r07) | 9 | planned |
| [R08 保留二模的中央目标连接](#r08) | 7 | planned |
| [R09 正buffer压缩与Poisson边界矩阵](#r09) | 8 | planned |
| [R10 全局匹配Green逆](#r10) | 12 | planned |
| [R11 同一几何上的双权全局估计](#r11) | 9 | planned |
| [R12 固定径向参考与闭图域双侧逆](#r12) | 13 | planned |
| [W01 材料坐标与连续权函数](#w01) | 9 | partial |
| [H01 分次空间、方向微分与tame基础](#h01) | 14 | partial |
| [W02 加权高度、源与圆序列空间](#w02) | 17 | partial |
| [W03 正指数弱空间的全阶平坦延拓](#w03) | 8 | partial |
| [N01 共同低阶几何邻域](#n01) | 9 | partial |
| [N02 圆返回残差与小除数逆](#n02) | 9 | planned |
| [N03 固定特征返回的残差修正](#n03) | 9 | planned |
| [N04 根坐标、正区间拼接与固定transmission](#n04) | 20 | planned |
| [N05 增广参考逆和共同闭图域](#n05) | 15 | planned |
| [N06 同一Banach空间的相对小扰动](#n06) | 12 | planned |
| [H02 逆族smooth tame定理](#h02) | 8 | planned |
| [N07 扰动标量逆及高阶恢复](#n07) | 9 | planned |
| [N08 联合残差、真实控制列与smoothing](#n08) | 10 | planned |
| [N09 耦合高度与圆方程的逆](#n09) | 11 | planned |
| [N10 两个独立残差的精确二次误差](#n10) | 8 | planned |
| [H03 带二次误差的Nash–Moser隐函数定理](#h03) | 24 | partial |
| [N11 弱权非线性解支](#n11) | 7 | planned |
| [N12 最小平坦环带核心](#n12) | 10 | partial |
| [D01 曲面二阶几何与刚体运动自然性](#d01) | 8 | partial |
| [D02 曲面面积和有向积分接口](#d02) | 11 | partial |
| [G01 平坦端点扩大为真实开领圈](#g01) | 4 | partial |
| [G02 填盘后的归一化平面发展](#g02) | 8 | partial |
| [G03 发展唯一性和内盘中心定位](#g03) | 4 | partial |
| [G04 局部发展成为全局微分同胚](#g04) | 5 | partial |
| [G05 等距图盘](#g05) | 4 | partial |
| [G06 隔离的固定标记补帽](#g06) | 14 | partial |
| [G07 标准球面参数化和固定度量](#g07) | 10 | partial |
| [G08 相位族联合光滑、周期与固定区域](#g08) | 6 | partial |
| [G09 每一相位均为同度量嵌入](#g09) | 6 | partial |
| [G10 径向盘的边界等距刚性](#g10) | 12 | partial |
| [G11 移动盘像不恒定](#g11) | 6 | partial |
| [G12 全等变换的有限候选集](#g12) | 7 | partial |
| [G13 闭球面像确实非全等](#g13) | 7 | partial |
| [G14 面积不变](#g14) | 3 | partial |
| [G15 显式围成区域及体积不变](#g15) | 13 | partial |
| [G16 总向外有向平均曲率不变](#g16) | 5 | partial |
| [MAIN 闭球面光滑周期等距弯曲主定理](#main) | 8 | partial |
| [X01 所有端点指数的同一几何加强](#x01) | 5 | planned |
| [X02 双倍端点权和二次控制加强](#x02) | 7 | planned |
| [X03 有限角向截断的障碍](#x03) | 8 | planned |

<a id="c00"></a>
## C00 主定理语义与四个接口

**原节点完整目标：** 固定标准单位球面 S²⊂E³。目标是光滑正定黎曼度量 gΣ、联合光滑 F:S²×ℝ→E³、非退化固定内盘及补帽，使每个 Fτ 为嵌入、Fτ*δ=gΣ、Fτ+1=Fτ；存在两个像不被任何欧氏仿射等距变换联系，且面积、围成体积、总向外有向平均曲率不变。

**原上游里程碑：** 无

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [01-introduction.tex:18–39](../../paper/flexible-surface-rewrite/01-introduction.tex#L18)

<a id="c00-01"></a>
### C00.01 标准球面与光滑阶的类型接口

**输出：** 固定E3、标准S2及现有球面光滑结构，统一C∞所用ContDiff/ContMDiff阶为∞。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- S2确为标准单位球面的子类型。
- 平坦bump相关接口不使用解析阶⊤。

**本轮核对：** 项目已固定真实E3和C∞阶，但快照没有标准S2类型及其球面图册接口。

**源码证据 `ContinuousFlexibility/Geometry/GraphEmbedding.lean`：** `ContinuousFlexibility.E3`

E3为实际三维EuclideanSpace；现有ContDiff阶使用∞。

**未完成内容：**
- 固定标准单位球面子类型及ContMDiff光滑图册接口。

**逐条验收：**
- acceptance.01 [partial]：项目已固定真实E3和C∞阶，但快照没有标准S2类型及其球面图册接口。
- acceptance.02 [partial]：项目已固定真实E3和C∞阶，但快照没有标准S2类型及其球面图册接口。

<a id="c00-02"></a>
### C00.02 环带输入字段与条件输出区分

**输出：** 逐字段核对FlatAnnularCore及AnnularSolution的实际函数、两端常数、正性区域和扩大领圈；给出条件性发展输出的统一参数接口。

**局部依赖：** C00.01。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 扩大环带上的w=0领圈不被要求严格正。
- Core到发展的条件构造不充当Core非空。

**本轮核对：** 实际Core与扩大领圈接口及同一Core参数化的发展输出均已构造；这些定理显式以A:FlatAnnularCore为输入，没有产生Core非空假设之外的存在性声明。

**源码证据 `ContinuousFlexibility/Contracts/Annular.lean`：** `ContinuousFlexibility.FlatAnnularCore`, `ContinuousFlexibility.AnnularSolution`, `ContinuousFlexibility.FlatAnnularCore.enlarge`, `ContinuousFlexibility.AnnularSolution.left_collar`, `ContinuousFlexibility.AnnularSolution.right_collar`, `ContinuousFlexibility.AnnularSolution.left_collar_nonempty`, `ContinuousFlexibility.AnnularSolution.right_collar_nonempty`

Core只在Ioo a b要求w>0；AnnularSolution继承同一w,z且两侧真实领圈w=0、高度分别cLeft/cRight。

**源码证据 `ContinuousFlexibility/Contracts/IsometricGraph.lean`：** `ContinuousFlexibility.IsometricGraphDevelopment`, `ContinuousFlexibility.FlatAnnularCore.exists_isometricGraphDevelopment`, `ContinuousFlexibility.FlatAnnularCore.graphDevelopment`, `ContinuousFlexibility.AnnularSolution.exists_isometricGraphDisk`

输出indexed by同一A并由A实际构造发展/图盘；没有Nonempty FlatAnnularCore结论。

**逐条验收：**
- acceptance.01 [covered]：Core正性字段只限原环带，左右collar定理实际给w=0及独立常高度。
- acceptance.02 [covered]：所有输出定理都保留显式A输入；实例化Core仍是N12/MAIN.01义务。

<a id="c00-03"></a>
### C00.03 径向参考与共同闭域接口

**输出：** 给RadialReference指定同一几何上的核、真实边框、兼容源、分布图域及双侧逆的精确类型；不把逆存在写作最终假设。

**局部依赖：** C00.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- β及β±ε使用同一几何和自然逆。
- 源密度dr与谱测度的转换必须有后续证明位置。

**本轮核对：** 快照没有该完整接口的实际Lean声明；现有条件图盘接口不能替代标准闭球面或完整径向参考规格。

**未完成内容：**
- 给RadialReference指定同一几何上的核、真实边框、兼容源、分布图域及双侧逆的精确类型；不把逆存在写作最终假设。

**逐条验收：**
- acceptance.01 [uncovered]：快照没有该完整接口的实际Lean声明；现有条件图盘接口不能替代标准闭球面或完整径向参考规格。
- acceptance.02 [uncovered]：快照没有该完整接口的实际Lean声明；现有条件图盘接口不能替代标准闭球面或完整径向参考规格。

<a id="c00-04"></a>
### C00.04 闭曲面嵌入与拉回度量接口

**输出：** 为ClosedBending指定F:S2×ℝ→E3联合光滑、每相位smooth embedding及切向量内积等式的精确类型。

**局部依赖：** C00.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 度量要求为实际dF的切向量配对。
- 成员嵌入同时包含immersion和全局topological embedding。

**本轮核对：** 快照没有该完整接口的实际Lean声明；现有条件图盘接口不能替代标准闭球面或完整径向参考规格。

**未完成内容：**
- 为ClosedBending指定F:S2×ℝ→E3联合光滑、每相位smooth embedding及切向量内积等式的精确类型。

**逐条验收：**
- acceptance.01 [uncovered]：快照没有该完整接口的实际Lean声明；现有条件图盘接口不能替代标准闭球面或完整径向参考规格。
- acceptance.02 [uncovered]：快照没有该完整接口的实际Lean声明；现有条件图盘接口不能替代标准闭球面或完整径向参考规格。

<a id="c00-05"></a>
### C00.05 固定区域与像集非全等接口

**输出：** 规定非退化内盘、补帽拓扑及逐点固定条件，规定量化全部AffineIsometryEquiv的两个range非全等。

**局部依赖：** C00.04。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 内盘有非空内部且位于图盘内部。
- 非全等覆盖反射并比较像集。

**本轮核对：** 快照没有该完整接口的实际Lean声明；现有条件图盘接口不能替代标准闭球面或完整径向参考规格。

**未完成内容：**
- 规定非退化内盘、补帽拓扑及逐点固定条件，规定量化全部AffineIsometryEquiv的两个range非全等。

**逐条验收：**
- acceptance.01 [uncovered]：快照没有该完整接口的实际Lean声明；现有条件图盘接口不能替代标准闭球面或完整径向参考规格。
- acceptance.02 [uncovered]：快照没有该完整接口的实际Lean声明；现有条件图盘接口不能替代标准闭球面或完整径向参考规格。

<a id="c00-06"></a>
### C00.06 几何积分语义接口

**输出：** 给面积、实际有界内部的Lebesgue体积、向外H=(k1+k2)/2积分指定接口及标准含义桥接的后续义务。

**局部依赖：** C00.04。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 积分对象不是任意常值别名。
- 区域和向外法向的识别列入D02/G15/G16后续证据要求。

**本轮核对：** 快照没有该完整接口的实际Lean声明；现有条件图盘接口不能替代标准闭球面或完整径向参考规格。

**未完成内容：**
- 给面积、实际有界内部的Lebesgue体积、向外H=(k1+k2)/2积分指定接口及标准含义桥接的后续义务。

**逐条验收：**
- acceptance.01 [uncovered]：快照没有该完整接口的实际Lean声明；现有条件图盘接口不能替代标准闭球面或完整径向参考规格。
- acceptance.02 [uncovered]：快照没有该完整接口的实际Lean声明；现有条件图盘接口不能替代标准闭球面或完整径向参考规格。

<a id="c00-07"></a>
### C00.07 完整量词与同一见证接口

**输出：** 把联合光滑、所有实相位、一周期、同一度量和三项不变量合为同一个ClosedBending规格。

**局部依赖：** C00.02, C00.03, C00.04, C00.05, C00.06。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 150–450 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 所有结论使用同一Core、发展、帽与F。
- 规格不声称所定义输入或输出结构非空。

**本轮核对：** 快照没有该完整接口的实际Lean声明；现有条件图盘接口不能替代标准闭球面或完整径向参考规格。

**未完成内容：**
- 把联合光滑、所有实相位、一周期、同一度量和三项不变量合为同一个ClosedBending规格。

**逐条验收：**
- acceptance.01 [uncovered]：快照没有该完整接口的实际Lean声明；现有条件图盘接口不能替代标准闭球面或完整径向参考规格。
- acceptance.02 [uncovered]：快照没有该完整接口的实际Lean声明；现有条件图盘接口不能替代标准闭球面或完整径向参考规格。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：固定标准单位球面 S²⊂E³。目标是光滑正定黎曼度量 gΣ、联合光滑 F:S²×ℝ→E³、非退化固定内盘及补帽，使每个 Fτ 为嵌入、Fτ*δ=gΣ、Fτ+1=Fτ；存在两个像不被任何欧氏仿射等距变换联系，且面积、围成体积、总向外有向平均曲率不变。 | C00.07（组合全部子任务） |
| acceptance.01：不得用环境距离 Isometry 替代拉回度量等式 | C00.04 |
| acceptance.02：非全等比较 range 像集并量化全部 AffineIsometryEquiv | C00.05 |
| acceptance.03：三项积分按标准几何/测度定义，不得以常值函数定义替代 | C00.06 |
| acceptance.04：本Lean版本的光滑阶为ContDiff ℝ ∞；⊤/ω表示解析，不得用于非平凡平坦bump的目标 | C00.01 |
| remaining.01：实际标准球面主定理的全部几何与测度类型仍需落实，ClosedBending尚未构造 | C00.04, C00.05, C00.06, C00.07 |
| remaining.02：RadialReference及加权共同闭域、耦合逆接口尚未构造；未证明FlatAnnularCore非空 | C00.02, C00.03, C00.07 |

<a id="s01"></a>
## S01 余度量正定与余标架

**原节点完整目标：** r>0、E>0 时，余度量坐标二次型正定 ⇔ D=E(1-p²)-k²>0；并有 D>0 ⇔ k²/E+p²<1、两个对角因子正性及余标架平方和等式。

**原上游里程碑：** 无

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [03-height-equation.tex:13–24](../../paper/flexible-surface-rewrite/03-height-equation.tex#L13)

<a id="s01-01"></a>
### S01.01 保留已有完整局部证明

**输出：** r>0、E>0 时，余度量坐标二次型正定 ⇔ D=E(1-p²)-k²>0；并有 D>0 ⇔ k²/E+p²<1、两个对角因子正性及余标架平方和等式。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** retained_proof。**初始粒度：** 0–0 行。已登记完整局部证明，不为增加节点数量而重拆。

**验收条件：**

- 现有 Positivity 的10条及 Coframe 的1条精确覆盖此节点
- 尚未声称识别了流形范数或曲率

**可复用基础：** 原节点lean_evidence及coordination/checkpoint-2026-11-11-coordination.json；这里继承记录，不声称本次重新构建。

**本轮核对：** 原已完整登记的点态局部结果；本次重新核对源码并将以快照重编和owner审计复核。

**源码证据 `ContinuousFlexibility/Scalar/Positivity.lean`：** `ContinuousFlexibility.radialEnergy_pos`, `ContinuousFlexibility.angular_factor_pos_of_discriminant_pos`, `ContinuousFlexibility.radial_factor_pos_of_discriminant_pos`, `ContinuousFlexibility.discriminant_pos_iff_height_norm_sq_lt_one`, `ContinuousFlexibility.remainder_matrix_determinant`, `ContinuousFlexibility.remainder_complete_square`, `ContinuousFlexibility.remainderPositive_of_discriminant_pos`, `ContinuousFlexibility.discriminant_pos_of_remainderPositive`, `ContinuousFlexibility.remainderPositive_iff_discriminant_pos`, `ContinuousFlexibility.radial_remainderPositive_iff_discriminant_pos`

原局部节点精确陈述的完整证据；不增加流形曲率或真实微分解释。

**源码证据 `ContinuousFlexibility/Scalar/Coframe.lean`：** `ContinuousFlexibility.coframe_square_sum`

原局部节点精确陈述的完整证据；不增加流形曲率或真实微分解释。

**逐条验收：**
- acceptance.01 [covered]：原已完整登记的点态局部结果；本次重新核对源码并将以快照重编和owner审计复核。
- acceptance.02 [covered]：原已完整登记的点态局部结果；本次重新核对源码并将以快照重编和owner审计复核。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：r>0、E>0 时，余度量坐标二次型正定 ⇔ D=E(1-p²)-k²>0；并有 D>0 ⇔ k²/E+p²<1、两个对角因子正性及余标架平方和等式。 | S01.01（组合全部子任务） |
| acceptance.01：现有 Positivity 的10条及 Coframe 的1条精确覆盖此节点 | S01.01 |
| acceptance.02：尚未声称识别了流形范数或曲率 | S01.01 |

<a id="s02"></a>
## S02 线性系数行列式与残差修正

**原节点完整目标：** 对明确坐标残差 Nres 和系数 a,b,c，r≠0、D>0 时 ac-b²=K₀/D²+E D^(-3/2)Nres；再加 Q≠0，c̄=c-E Nres/Q 给 ac̄-b²=K₀/D²。含径向特化与零残差时修正消失。

**原上游里程碑：** 无

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [03-height-equation.tex:47–115](../../paper/flexible-surface-rewrite/03-height-equation.tex#L47)；[03-height-equation.tex:336–360](../../paper/flexible-surface-rewrite/03-height-equation.tex#L336)

<a id="s02-01"></a>
### S02.01 保留已有完整局部证明

**输出：** 对明确坐标残差 Nres 和系数 a,b,c，r≠0、D>0 时 ac-b²=K₀/D²+E D^(-3/2)Nres；再加 Q≠0，c̄=c-E Nres/Q 给 ac̄-b²=K₀/D²。含径向特化与零残差时修正消失。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** retained_proof。**初始粒度：** 0–0 行。已登记完整局部证明，不为增加节点数量而重拆。

**验收条件：**

- 14条定理已覆盖点态代数
- 实际残差的微分识别另在S03/S05

**可复用基础：** 原节点lean_evidence及coordination/checkpoint-2026-11-11-coordination.json；这里继承记录，不声称本次重新构建。

**本轮核对：** 原已完整登记的点态局部结果；本次重新核对源码并将以快照重编和owner审计复核。

**源码证据 `ContinuousFlexibility/Scalar/Determinant.lean`：** `ContinuousFlexibility.correctedAngular_eq_residual_correction`, `ContinuousFlexibility.correctedAngular_of_residual_zero`, `ContinuousFlexibility.heightQ_discriminant_identity`, `ContinuousFlexibility.linear_determinant_scaled`, `ContinuousFlexibility.inverseDThreeHalves_sq`, `ContinuousFlexibility.inverseDThreeHalves_pos`, `ContinuousFlexibility.discriminant_mul_inverseDThreeHalves_sq`, `ContinuousFlexibility.linear_determinant`, `ContinuousFlexibility.corrected_determinant_scaled`, `ContinuousFlexibility.corrected_determinant`, `ContinuousFlexibility.heightDiscriminant_radial`, `ContinuousFlexibility.inverseDThreeHalves_one`, `ContinuousFlexibility.radial_linear_coefficients`, `ContinuousFlexibility.radial_coordinate_residual_zero`

原局部节点精确陈述的完整证据；不增加流形曲率或真实微分解释。

**逐条验收：**
- acceptance.01 [covered]：原已完整登记的点态局部结果；本次重新核对源码并将以快照重编和owner审计复核。
- acceptance.02 [covered]：原已完整登记的点态局部结果；本次重新核对源码并将以快照重编和owner审计复核。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：对明确坐标残差 Nres 和系数 a,b,c，r≠0、D>0 时 ac-b²=K₀/D²+E D^(-3/2)Nres；再加 Q≠0，c̄=c-E Nres/Q 给 ac̄-b²=K₀/D²。含径向特化与零残差时修正消失。 | S02.01（组合全部子任务） |
| acceptance.01：14条定理已覆盖点态代数 | S02.01 |
| acceptance.02：实际残差的微分识别另在S03/S05 | S02.01 |

<a id="r01"></a>
## R01 真实导数下的对数幂 gauge

**原节点完整目标：** u(r)=r^aV(log r)、r>0，在现有明确可微假设下计算实际一二阶导数及 L_a u。令 p(y)=w(e^y)e^((2a-1)y)，有 (pV')'+a(a-1)pV=e^((a+1)y)L_a u(e^y)；取 a=j²。

**原上游里程碑：** 无

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [05-flat-end-chain.tex:252–268](../../paper/flexible-surface-rewrite/05-flat-end-chain.tex#L252)

<a id="r01-01"></a>
### R01.01 保留已有完整局部证明

**输出：** u(r)=r^aV(log r)、r>0，在现有明确可微假设下计算实际一二阶导数及 L_a u。令 p(y)=w(e^y)e^((2a-1)y)，有 (pV')'+a(a-1)pV=e^((a+1)y)L_a u(e^y)；取 a=j²。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** retained_proof。**初始粒度：** 0–0 行。已登记完整局部证明，不为增加节点数量而重拆。

**验收条件：**

- 10条定理覆盖此局部微分节点
- Green配对与闭算子域换元仍由R06/R12证明

**可复用基础：** 原节点lean_evidence及coordination/checkpoint-2026-11-11-coordination.json；这里继承记录，不声称本次重新构建。

**本轮核对：** 10个实际局部微分定理覆盖原R01精确陈述；闭域和全局配对本来不在此局部节点范围。

**源码证据 `ContinuousFlexibility/Radial/Gauge.lean`：** `ContinuousFlexibility.Radial.hasDerivAt_gaugeLift`, `ContinuousFlexibility.Radial.deriv_gaugeLift`, `ContinuousFlexibility.Radial.hasDerivAt_gaugeFirst`, `ContinuousFlexibility.Radial.deriv_deriv_gaugeLift`, `ContinuousFlexibility.Radial.radialJacobi_gauge`, `ContinuousFlexibility.Radial.radialJacobi_gauge_divided`, `ContinuousFlexibility.Radial.logGaugeWeight_eq`, `ContinuousFlexibility.Radial.logGaugeEquation_eq`, `ContinuousFlexibility.Radial.logGaugeEquation_source_identity`, `ContinuousFlexibility.Radial.radialJacobi_gauge_eq_zero_iff`

实际一阶、二阶导数、L_a共轭和非齐次源exp((a+1)y)因子；没有引入闭域或Green端点结论。

**逐条验收：**
- acceptance.01 [covered]：所列10个定理逐项覆盖导数、方程及源因子。
- acceptance.02 [covered]：证据仅为局部微分恒等式，未将R06/R12的Green配对或闭域结论混入；保留原任务边界。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：u(r)=r^aV(log r)、r>0，在现有明确可微假设下计算实际一二阶导数及 L_a u。令 p(y)=w(e^y)e^((2a-1)y)，有 (pV')'+a(a-1)pV=e^((a+1)y)L_a u(e^y)；取 a=j²。 | R01.01（组合全部子任务） |
| acceptance.01：10条定理覆盖此局部微分节点 | R01.01 |
| acceptance.02：Green配对与闭算子域换元仍由R06/R12证明 | R01.01 |

<a id="s03"></a>
## S03 高度微分、Cartan连接与真实变分

**原节点完整目标：** 对光滑w,z及r>0,D>0，证明 rp_r=kθ-p、所示余标架的结构方程、α=D^(-1/2)(dθ+k dp/(1-p²))、dα=rNres dr∧dθ，以及实际高度变分的对称散度表达式。

**原上游里程碑：** C00, S01, S02

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [03-height-equation.tex:29–115](../../paper/flexible-surface-rewrite/03-height-equation.tex#L29)

<a id="s03-01"></a>
### S03.01 实际高度jet与混合导数

**输出：** 把p、k及各偏导绑定到实际w,z，证明r∂rp=∂θk-p与所需混合导数交换。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 量化真实可微函数而非自由jet。
- r>0及可微阶假设足够且明确。

**本轮核对：** p、k都由真实fderiv定义；C²条件下混合偏导交换和高度兼容恒等式已实际证明。

**源码证据 `ContinuousFlexibility/Scalar/HeightDerivatives.lean`：** `ContinuousFlexibility.radial_angular_commute`, `ContinuousFlexibility.height_compatibility`, `ContinuousFlexibility.radialPartial_polarDiscriminant`, `ContinuousFlexibility.angularPartial_polarDiscriminant`

精确r p_r=kθ-p与真实混合偏导。

**逐条验收：**
- acceptance.01 [covered]：p、k都由真实fderiv定义；C²条件下混合偏导交换和高度兼容恒等式已实际证明。
- acceptance.02 [covered]：p、k都由真实fderiv定义；C²条件下混合偏导交换和高度兼容恒等式已实际证明。

<a id="s03-02"></a>
### S03.02 真实余标架结构方程

**输出：** 对实际余标架逐坐标证明Cartan一阶结构方程。

**局部依赖：** S03.01。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 平方根和除法只用于D>0区域。
- 与S01的同一个余度量配对。

**本轮核对：** 真实Cartan方程由实际高度jet与正定余标架给出，平方根仅用于D>0且与S01同一余度量平方和相连。

**源码证据 `ContinuousFlexibility/Scalar/Cartan.lean`：** `ContinuousFlexibility.polar_cartan_equations`, `ContinuousFlexibility.polar_coframe_determinant_pos`

由实际w,z及r≠0,D>0得到两个结构方程及定向。

**源码证据 `ContinuousFlexibility/Geometry/HeightCoframe.lean`：** `ContinuousFlexibility.heightCoframe_square_sum`, `ContinuousFlexibility.heightCoframe_cartan`

同一height coframe的实际二次型和Cartan形式版本。

**逐条验收：**
- acceptance.01 [covered]：真实Cartan方程由实际高度jet与正定余标架给出，平方根仅用于D>0且与S01同一余度量平方和相连。
- acceptance.02 [covered]：真实Cartan方程由实际高度jet与正定余标架给出，平方根仅用于D>0且与S01同一余度量平方和相连。

<a id="s03-03"></a>
### S03.03 连接与残差的二阶识别

**输出：** 证明真实α的表达式与dα=rNres dr∧dθ。

**局部依赖：** S03.01, S03.02。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 角向源密度的r因子不丢失。
- 残差零给真正闭连接。

**本轮核对：** 连接由实际系数定义；真实外微分严格等于r乘原残差，因此残差零给闭连接，dr∧dθ因子显式保留。

**源码证据 `ContinuousFlexibility/Scalar/Connection.lean`：** `ContinuousFlexibility.polar_connectionCurl_eq_residual`, `ContinuousFlexibility.polar_connection_closed_iff`

连接curl与rNres的真实二阶导数识别。

**源码证据 `ContinuousFlexibility/Geometry/HeightCoframe.lean`：** `ContinuousFlexibility.heightConnectionForm`, `ContinuousFlexibility.heightConnection_exterior_eq_residual`, `ContinuousFlexibility.heightConnection_closed_of_residual_zero`

实际一形式α及闭连接结论。

**逐条验收：**
- acceptance.01 [covered]：连接由实际系数定义；真实外微分严格等于r乘原残差，因此残差零给闭连接，dr∧dθ因子显式保留。
- acceptance.02 [covered]：连接由实际系数定义；真实外微分严格等于r乘原残差，因此残差零给闭连接，dr∧dθ因子显式保留。

<a id="s03-04"></a>
### S03.04 高度变分的实际导数

**输出：** 对z+sη求实际参数导数，证明对称散度系数及混合偏导相容。

**局部依赖：** S03.01, S03.02, S03.03。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 含全部高度一二阶变化项。
- 结论是微分恒等式而非形式系数定义。

**本轮核对：** 仿射高度族的全部一二阶空间jet参数导数已证明，并组合成真实HasDerivAt的对称散度线性化。

**源码证据 `ContinuousFlexibility/Scalar/HeightVariation.lean`：** `ContinuousFlexibility.hasDerivAt_heightRadial_heightFamily`, `ContinuousFlexibility.hasDerivAt_heightAngular_heightFamily`, `ContinuousFlexibility.hasDerivAt_radialPartial_heightRadial_heightFamily`, `ContinuousFlexibility.hasDerivAt_radialPartial_heightAngular_heightFamily`, `ContinuousFlexibility.hasDerivAt_angularPartial_heightAngular_heightFamily`, `ContinuousFlexibility.hasDerivAt_polarCoordinateResidual_heightFamily`

高度一二阶变化及原残差实际参数导数。

**源码证据 `ContinuousFlexibility/Scalar/Linearization.lean`：** `ContinuousFlexibility.heightLinearizedDivergence_eq_variation`, `ContinuousFlexibility.polarResidualVariation_eq_divergence`, `ContinuousFlexibility.hasDerivAt_polarCoordinateResidual_divergence`, `ContinuousFlexibility.hasDerivAt_radialScaledResidual_divergence`

扩展系数被识别为真实散度而非独立jet代数。

**逐条验收：**
- acceptance.01 [covered]：仿射高度族的全部一二阶空间jet参数导数已证明，并组合成真实HasDerivAt的对称散度线性化。
- acceptance.02 [covered]：仿射高度族的全部一二阶空间jet参数导数已证明，并组合成真实HasDerivAt的对称散度线性化。

<a id="s03-05"></a>
### S03.05 零残差的局部发展桥接

**输出：** 把闭连接、旋转余标架和局部积分连成实际局部欧氏余度量结论。

**局部依赖：** S03.02, S03.03。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 局部原函数的区域条件明确。
- 不假设环带连接有全局实原函数。

**本轮核对：** 在明确凸开局部域上，从真实残差零、闭连接和闭余标架积分得到实际C∞局部发展、余度量等式及光滑局部逆；不要求环带上的全局primitive。

**源码证据 `ContinuousFlexibility/Geometry/Primitive.lean`：** `ContinuousFlexibility.exists_primitive_of_closed`, `ContinuousFlexibility.exists_smooth_development_of_closed_coframe`

原函数只在凸开域使用。

**源码证据 `ContinuousFlexibility/Geometry/FlatDevelopment.lean`：** `ContinuousFlexibility.exists_smooth_remainder_development`, `ContinuousFlexibility.exists_locally_invertible_remainder_development`, `ContinuousFlexibility.development_pullback_bilinear`

实际平方和、双线性配对和局部C∞逆。

**逐条验收：**
- acceptance.01 [covered]：在明确凸开局部域上，从真实残差零、闭连接和闭余标架积分得到实际C∞局部发展、余度量等式及光滑局部逆；不要求环带上的全局primitive。
- acceptance.02 [covered]：在明确凸开局部域上，从真实残差零、闭连接和闭余标架积分得到实际C∞局部发展、余度量等式及光滑局部逆；不要求环带上的全局primitive。

<a id="s03-06"></a>
### S03.06 函数空间光滑与导数接口

**输出：** 在W02实际levels上把上述坐标公式提升为联合smooth tame映射及其实际方向导数。

**局部依赖：** S03.01, S03.02, S03.03, S03.04。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 点态C∞与函数空间smooth tame分别证明。
- 全部估计使用同一低阶邻域及固定损失。

**细分后补充依赖：** W02：原剩余义务明确要求函数空间smooth tame，须使用实际加权levels而非点态公式。

**本轮核对：** 没有实际W02加权levels上的联合smooth tame残差接口；当前只有坐标/有限维参数C∞。

**未完成内容：**
- 实际加权函数空间、全阶方向微分与同一低阶邻域估计。

**逐条验收：**
- acceptance.01 [uncovered]：没有实际W02加权levels上的联合smooth tame残差接口；当前只有坐标/有限维参数C∞。
- acceptance.02 [uncovered]：没有实际W02加权levels上的联合smooth tame残差接口；当前只有坐标/有限维参数C∞。

<a id="s03-07"></a>
### S03.07 标量核心局部节点组合

**输出：** 将真实坐标微分、闭连接/发展、散度变分和函数空间接口合为原S03完整结论。

**局部依赖：** S03.01, S03.02, S03.03, S03.04, S03.05, S03.06。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 150–450 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 逐条核对prop:scalar-core对应公式。
- 源仍是dr dθ而不是未识别的加权测度。

**本轮核对：** 真实标量坐标计算和局部发展均已有，但节点要求的函数空间接口尚未实现。

**源码证据 `ContinuousFlexibility/Scalar/Linearization.lean`：** `ContinuousFlexibility.hasDerivAt_radialScaledResidual_divergence`

源仍为dr dθ的实际线性化。

**未完成内容：**
- S03.06全部函数空间smooth tame接口。

**逐条验收：**
- acceptance.01 [partial]：真实标量坐标计算和局部发展均已有，但节点要求的函数空间接口尚未实现。
- acceptance.02 [partial]：真实标量坐标计算和局部发展均已有，但节点要求的函数空间接口尚未实现。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：对光滑w,z及r>0,D>0，证明 rp_r=kθ-p、所示余标架的结构方程、α=D^(-1/2)(dθ+k dp/(1-p²))、dα=rNres dr∧dθ，以及实际高度变分的对称散度表达式。 | S03.07（组合全部子任务） |
| acceptance.01：不得以自由jet代数代替真实微分 | S03.01, S03.04 |
| acceptance.02：源密度明确为dr dθ | S03.03, S03.04 |
| acceptance.03：Nres的零集必须实际给出局部欧氏余度量 | S03.03, S03.05 |
| remaining.01：接入后续加权空间的函数空间光滑性与公共接口，不能把点态C∞等同smooth tame | S03.06 |

<a id="s04"></a>
## S04 归一化残差的可去延拓和守恒

**原节点完整目标：** F_q(w,u)=rN_h(h+qu)/q 在q=0光滑延拓为 ℒ_wu，满足积分表示。对常高度端领圈或适当平坦端点，∫⟨F_q⟩dr=0；其全部高度和度量微分保持兼容性。

**原上游里程碑：** S03

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [03-height-equation.tex:287–326](../../paper/flexible-surface-rewrite/03-height-equation.tex#L287)

<a id="s04-01"></a>
### S04.01 参数商的可去延拓

**输出：** 以参数线段积分定义Fq在q=0的真实延拓并识别其值为线性化。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- q≠0处等于rN(h+qu)/q。
- q=0处真实可微而不是分段命名。

**本轮核对：** q=0的真实C∞可去延拓及q≠0商等式已证明；采用显式二次多项式因子化，尚未给任务明确要求的参数线段积分表示/定义。

**源码证据 `ContinuousFlexibility/Scalar/Normalization.lean`：** `ContinuousFlexibility.normalizedHeightResidual`, `ContinuousFlexibility.normalizedHeightResidual_of_ne_zero`, `ContinuousFlexibility.normalizedHeightResidual_eq_factored`, `ContinuousFlexibility.contDiffAt_normalizedHeightResidual_of_residual_zero`

真实连续/光滑可去延拓，不只是命名q=0值。

**未完成内容：**
- 以参数线段积分表示同一个Fq并识别q=0线性化值的完整恒等式。

**逐条验收：**
- acceptance.01 [partial]：q=0的真实C∞可去延拓及q≠0商等式已证明；采用显式二次多项式因子化，尚未给任务明确要求的参数线段积分表示/定义。
- acceptance.02 [partial]：q=0的真实C∞可去延拓及q≠0商等式已证明；采用显式二次多项式因子化，尚未给任务明确要求的参数线段积分表示/定义。

<a id="s04-02"></a>
### S04.02 高度与度量的混合参数导数

**输出：** 证明Fq对q、u、w的混合方向微分及积分表达式，包含h_w的变化。

**局部依赖：** S04.01。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 度量变化时基准高度随w求导。
- 有限矩形中的参数与积分交换条件明确。

**本轮核对：** 已有高度参数导数和独立E,k,p的连接变化公式，但没有Fq对w,u,q全部混合方向导数及h_w随w变化的完整积分交换结论。

**源码证据 `ContinuousFlexibility/Scalar/ConnectionVariation.lean`：** `ContinuousFlexibility.hasDerivAt_connectionInverseRoot`, `ContinuousFlexibility.hasDerivAt_connectionB1`, `ContinuousFlexibility.hasDerivAt_connectionAngularValue`

含dE,dk,dp的真实有限维参数导数。

**源码证据 `ContinuousFlexibility/Scalar/HeightVariation.lean`：** `ContinuousFlexibility.hasDerivAt_polarCoordinateResidual_heightFamily`

固定w的高度导数。

**未完成内容：**
- 将w变化、h_w变化及混合参数积分表达式组合到同一Fq。

**逐条验收：**
- acceptance.01 [partial]：已有高度参数导数和独立E,k,p的连接变化公式，但没有Fq对w,u,q全部混合方向导数及h_w随w变化的完整积分交换结论。
- acceptance.02 [partial]：已有高度参数导数和独立E,k,p的连接变化公式，但没有Fq对w,u,q全部混合方向导数及h_w随w变化的完整积分交换结论。

<a id="s04-03"></a>
### S04.03 有限领圈守恒与角平均

**输出：** 由真实连接period推导常高度领圈情况下的归一化源积分为零。

**局部依赖：** S04.01, S04.02。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 两端连接period均为2π。
- 角平均明确归一化测度且源为dr。

**本轮核对：** 有限矩形上实际连接守恒、左右独立常高度领圈的标准连接、归一化角平均及包括q=0的基线Fq积分零均已证明。

**源码证据 `ContinuousFlexibility/Scalar/Conservation.lean`：** `ContinuousFlexibility.heightConnection_of_flat_collar`, `ContinuousFlexibility.integral_heightResidual_eq_zero_of_flat_collars`, `ContinuousFlexibility.integral_mean_heightResidual_eq_zero`

两边真实α=dθ，T=2π时各period均为2π；FTC+Fubini保留物理dr源和1/T角平均。

**源码证据 `ContinuousFlexibility/Scalar/NormalizedConservation.lean`：** `ContinuousFlexibility.integral_mean_normalizedHeightResidual_eq_zero_of_ne_zero`, `ContinuousFlexibility.integral_mean_normalizedHeightResidual_radialHeight_eq_zero`

同一归一化Fq的零均值包含q≠0和实际径向基线q=0。

**逐条验收：**
- acceptance.01 [covered]：有限矩形上实际连接守恒、左右独立常高度领圈的标准连接、归一化角平均及包括q=0的基线Fq积分零均已证明。
- acceptance.02 [covered]：有限矩形上实际连接守恒、左右独立常高度领圈的标准连接、归一化角平均及包括q=0的基线Fq积分零均已证明。

<a id="s04-04"></a>
### S04.04 加权平坦端点的守恒极限

**输出：** 用W03端点估计将有限截断守恒推进原环带，证明边界项与参数导数交换的统一控制。

**局部依赖：** S04.02, S04.03。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 不是重新假定端点边界项为零。
- 所有所需导数共用一个参数邻域。

**细分后补充依赖：** W03：原remaining要求实际加权端点延拓来消除有限矩形边界假设。

**本轮核对：** 尚无实际W03加权端点估计到有限截断守恒极限的共同参数证明。

**未完成内容：**
- 端点项真实极限、所有参数导数交换及同一参数邻域。

**逐条验收：**
- acceptance.01 [uncovered]：尚无实际W03加权端点估计到有限截断守恒极限的共同参数证明。
- acceptance.02 [uncovered]：尚无实际W03加权端点估计到有限截断守恒极限的共同参数证明。

<a id="s04-05"></a>
### S04.05 归一化残差的smooth tame兼容性

**输出：** 在实际加权空间证明Fq联合smooth tame以及全部高度/度量导数落在兼容源子空间。

**局部依赖：** S04.01, S04.02, S04.04。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 零均值来自实际积分等式。
- 包含q=0及非零q同一开集。

**细分后补充依赖：** W02：归一化残差须在实际源/高度空间而非仅点态参数上smooth tame。

**本轮核对：** 实际W02/W03源空间及联合smooth tame残差未实现。

**未完成内容：**
- Fq在实际加权开集的smooth tame与全部混合导数源兼容。

**逐条验收：**
- acceptance.01 [uncovered]：实际W02/W03源空间及联合smooth tame残差未实现。
- acceptance.02 [uncovered]：实际W02/W03源空间及联合smooth tame残差未实现。

<a id="s04-06"></a>
### S04.06 守恒节点完整组合

**输出：** 统一可去延拓、全部真实混合微分、端点极限及兼容源约束。

**局部依赖：** S04.01, S04.02, S04.03, S04.04, S04.05。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 150–450 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 原积分表示和q=0值同时成立。
- 以后N08能直接使用同一个Fq。

**本轮核对：** 点态归一化与有限矩形守恒有证明；全阶混合导数、加权端点极限和函数空间兼容性未组合。

**源码证据 `ContinuousFlexibility/Scalar/NormalizedConservation.lean`：** `ContinuousFlexibility.integral_mean_normalizedHeightResidual_radialHeight_eq_zero`

有限矩形、明确边界jet下的实际Fq守恒。

**未完成内容：**
- S04.01的积分表示、S04.02、S04.04、S04.05完整覆盖。

**逐条验收：**
- acceptance.01 [partial]：点态归一化与有限矩形守恒有证明；全阶混合导数、加权端点极限和函数空间兼容性未组合。
- acceptance.02 [partial]：点态归一化与有限矩形守恒有证明；全阶混合导数、加权端点极限和函数空间兼容性未组合。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：F_q(w,u)=rN_h(h+qu)/q 在q=0光滑延拓为 ℒ_wu，满足积分表示。对常高度端领圈或适当平坦端点，∫⟨F_q⟩dr=0；其全部高度和度量微分保持兼容性。 | S04.06（组合全部子任务） |
| acceptance.01：包括度量变化时h_w的变化 | S04.02 |
| acceptance.02：两端连接period均为2π | S04.03 |
| acceptance.03：明确推广到后来加权平坦空间的边界极限 | S04.04 |
| remaining.01：证明加权空间中的联合smooth tame、所有高度及度量微分兼容性 | S04.02, S04.05 |
| remaining.02：以实际加权端点延拓和统一参数邻域实例化目前明确的有限矩形假设 | S04.04, S04.05 |

<a id="s05"></a>
## S05 固定类型的真实修正算子

**原节点完整目标：** 在共同正性邻域，真实 D_uF_qη= L̄η+q∂θ(B A ηθ)，B=E/(rQ)；L̄具有固定转型圆、同一法向通量、形式对称并杀常数，负区特征速度具有根点平方根退化。

**原上游里程碑：** S02, S03, S04

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [03-height-equation.tex:336–375](../../paper/flexible-surface-rewrite/03-height-equation.tex#L336)

<a id="s05-01"></a>
### S05.01 真实修正算子系数识别

**输出：** 将S02代数代入S03真实变分，得到Lbar及q∂θ(B A ηθ)精确恒等式。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- B=E/(rQ)仅在合法区域使用。
- 不把残差误差量级代替精确恒等式。

**本轮核对：** 已证明精确系数/空间散度比较及真实rN高度导数；但尚未证明固定q时u↦normalizedHeightResidual的实际方向导数等于该空间散度，尤其q=0。论文左端D_u Fq的桥接不能省略。

**源码证据 `ContinuousFlexibility/Scalar/TypeCorrection.lean`：** `ContinuousFlexibility.polarTypeB`, `ContinuousFlexibility.polarCorrectedC_eq_residual_correction`, `ContinuousFlexibility.polarCorrectedC_eq_typeB`, `ContinuousFlexibility.heightLinearizedDivergence_eq_corrected_of_smooth`, `ContinuousFlexibility.hasDerivAt_radialScaledResidual_corrected`, `ContinuousFlexibility.heightLinearizedDivergence_eq_corrected_normalized`

不是O(q)估计，而是原修正Lbar与q∂θ(B Fq ηθ)的精确恒等式；hQ和D>0用于真实系数正则。

**未完成内容：**
- 对u+tη、固定q证明normalizedHeightResidual真实state-path方向导数，包括q=0，再与精确q角向散度恒等式合并。

**逐条验收：**
- acceptance.01 [partial]：实际高度变分的修正散度比较、B=E/(rQ)定义及同一归一化源产生的精确q角向散度误差均已证明；合法域条件显式。
- acceptance.02 [partial]：实际高度变分的修正散度比较、B=E/(rQ)定义及同一归一化源产生的精确q角向散度误差均已证明；合法域条件显式。

<a id="s05-02"></a>
### S05.02 独立残差与增量双线性

**输出：** 将修正误差单独定义于独立残差和高度增量并验证各变量线性。

**局部依赖：** S05.01。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 不是只验证代入实际残差后的大小界。
- 散度形式保持源兼容。

**本轮核对：** 已有代入实际残差的精确误差乘积，但未对独立任意残差r及增量η定义并证明双线性和源兼容。

**源码证据 `ContinuousFlexibility/Scalar/TypeCorrection.lean`：** `ContinuousFlexibility.heightLinearizedDivergence_eq_corrected_normalized`

实际残差代入后的精确角向散度。

**未完成内容：**
- 独立变量的线性/双线性映射及兼容源证明。

**逐条验收：**
- acceptance.01 [partial]：已有代入实际残差的精确误差乘积，但未对独立任意残差r及增量η定义并证明双线性和源兼容。
- acceptance.02 [partial]：已有代入实际残差的精确误差乘积，但未对独立任意残差r及增量η定义并证明双线性和源兼容。

<a id="s05-03"></a>
### S05.03 法向通量与Green配对

**输出：** 对明确端点/测试函数条件证明修正不改法向通量、形式对称且杀常数。

**局部依赖：** S05.01, S05.02。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- S05只改角向系数。
- Green配对与dr dθ源的密度一致。

**本轮核对：** 修正前后法向通量的A,B定义完全相同；真实Green配对、明确周期/Dirichlet/Robin或端点jet条件及杀常数均已证明。

**源码证据 `ContinuousFlexibility/Scalar/TypeCorrection.lean`：** `ContinuousFlexibility.heightCorrectedDivergence`, `ContinuousFlexibility.heightCorrectedDivergence_const`, `ContinuousFlexibility.heightLinearizedDivergence_eq_corrected`

修正只改角向C，法向A u_r+B uθ逐字相同。

**源码证据 `ContinuousFlexibility/Scalar/GreenIdentity.lean`：** `ContinuousFlexibility.symmetricNormalFlux`, `ContinuousFlexibility.greenNormalFlux_eq_zero_of_robin`, `ContinuousFlexibility.greenNormalFlux_eq_zero_of_dirichlet`, `ContinuousFlexibility.heightCorrected_green_identity`, `ContinuousFlexibility.integral_heightCorrected_green_eq_zero_of_admissible`, `ContinuousFlexibility.integral_heightCorrected_green_eq_zero_of_boundary_jets`

实际dr dθ积分的形式对称，端点/测试函数条件显式。

**逐条验收：**
- acceptance.01 [covered]：修正前后法向通量的A,B定义完全相同；真实Green配对、明确周期/Dirichlet/Robin或端点jet条件及杀常数均已证明。
- acceptance.02 [covered]：修正前后法向通量的A,B定义完全相同；真实Green配对、明确周期/Dirichlet/Robin或端点jet条件及杀常数均已证明。

<a id="s05-04"></a>
### S05.04 固定转型圆与特征斜率

**输出：** 由实际系数行列式识别w′变号的类型及负区根点附近的特征斜率。

**局部依赖：** S05.01。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 类型不是w变号。
- 平方根退化从简单转点推导。

**本轮核对：** 实际行列式零集及正负号与w′一致已证明；还没有一般负区特征斜率及简单根附近平方根退化的完整推导。

**源码证据 `ContinuousFlexibility/Scalar/TypeCorrection.lean`：** `ContinuousFlexibility.polar_corrected_determinant_zero_iff`, `ContinuousFlexibility.polar_corrected_determinant_pos_iff`, `ContinuousFlexibility.polar_corrected_determinant_neg_iff`

在w>0,D>0与合法Q下识别类型。

**未完成内容：**
- 负区实际特征斜率与简单转点平方根退化。

**逐条验收：**
- acceptance.01 [partial]：实际行列式零集及正负号与w′一致已证明；还没有一般负区特征斜率及简单根附近平方根退化的完整推导。
- acceptance.02 [partial]：实际行列式零集及正负号与w′一致已证明；还没有一般负区特征斜率及简单根附近平方根退化的完整推导。

<a id="s05-05"></a>
### S05.05 加权端点系数延拓

**输出：** 在实际W02/W03 levels对A、B、修正C逐项处理平坦端点可去性和共同域。

**局部依赖：** S05.01, S05.03。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 不在平坦端点假设Q非零。
- 系数延拓与原内部表达式一致。

**细分后补充依赖：** W03：原剩余义务要求实际加权端点延拓和共同域，不由内部代数自动得到。

**本轮核对：** 现有内部系数正则显式要求Q≠0，不能用于平坦端点。

**未完成内容：**
- 在实际W02/W03 levels上对A/B/C作可去延拓并识别共同闭域。

**逐条验收：**
- acceptance.01 [uncovered]：现有内部系数正则显式要求Q≠0，不能用于平坦端点。
- acceptance.02 [uncovered]：现有内部系数正则显式要求Q≠0，不能用于平坦端点。

<a id="s05-06"></a>
### S05.06 特征根点定量估计

**输出：** 在显式共同正性邻域内证明根点速度及固定类型系数的全阶有损估计。

**局部依赖：** S05.04, S05.05。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 损失和低阶小性条件不随输出阶变化。
- 这是条件系数定理，不反向依赖N01的实例化结论。

**本轮核对：** 没有共同正性低阶邻域上的全阶根点速度及固定损失估计。

**未完成内容：**
- 固定低阶小性、全阶估计、实际特征系数。

**逐条验收：**
- acceptance.01 [uncovered]：没有共同正性低阶邻域上的全阶根点速度及固定损失估计。
- acceptance.02 [uncovered]：没有共同正性低阶邻域上的全阶根点速度及固定损失估计。

<a id="s05-07"></a>
### S05.07 修正算子节点组合

**输出：** 把实际导数、独立双线性误差、通量、端点共同域和类型估计合为原S05。

**局部依赖：** S05.01, S05.02, S05.03, S05.04, S05.05, S05.06。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 150–450 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 交付供N01/N03使用的同一算子。
- 后续N03的混合系数修正不被误称为全局通量不变。

**本轮核对：** 精确修正和通量/Green结论已有；端点共同域及根点统一估计尚缺。

**源码证据 `ContinuousFlexibility/Scalar/TypeCorrection.lean`：** `ContinuousFlexibility.heightLinearizedDivergence_eq_corrected_normalized`

已证实际修正核心等式。

**未完成内容：**
- S05.02、S05.04–06未闭合。

**逐条验收：**
- acceptance.01 [partial]：精确修正和通量/Green结论已有；端点共同域及根点统一估计尚缺。
- acceptance.02 [partial]：精确修正和通量/Green结论已有；端点共同域及根点统一估计尚缺。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：在共同正性邻域，真实 D_uF_qη= L̄η+q∂θ(B A ηθ)，B=E/(rQ)；L̄具有固定转型圆、同一法向通量、形式对称并杀常数，负区特征速度具有根点平方根退化。 | S05.07（组合全部子任务） |
| acceptance.01：对称性列出测试函数/端点条件 | S05.03 |
| acceptance.02：修正误差对独立残差和增量双线性 | S05.02 |
| acceptance.03：类型是w'变号而非w变号 | S05.04 |
| remaining.01：加权端点下实际A、B、修正C的光滑延拓与共同闭域 | S05.05 |
| remaining.02：根点特征速度与固定类型逆所需定量估计；不得在平坦端点假设Q非零 | S05.04, S05.06 |

<a id="r02"></a>
## R02 Liouville变换与径向实现

**原节点完整目标：** 在半径方程和 r_X=v>0 下，严格推导由谱势到径向轮廓的Liouville变换，给出真实L_j的共轭表达式、源因子和两种测度。

**原上游里程碑：** R01

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [04-designing-the-profile.tex:118–137](../../paper/flexible-surface-rewrite/04-designing-the-profile.tex#L118)；[04-designing-the-profile.tex:272–301](../../paper/flexible-surface-rewrite/04-designing-the-profile.tex#L272)

<a id="r02-01"></a>
### R02.01 实际半径坐标的可逆性

**输出：** 对构造的模型半径r，证明r_X=v>0并确定range，构造实际逆坐标及其光滑性。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 200–500 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- v>0由模型的已证明结论提供而非最终新增假设
- 双向复合恒等式与导数公式齐备

**可复用基础：** CentralRadius.lean与CentralRadiusMetric.lean已有中央模型支持，通用接口仍需核对。

**本轮核对：** 中央模型的实际半径逆完整；任务按R02模型级通用/两类模型接口理解，尚无Morse实际保留区半径及相同逆接口。

**源码证据 `ContinuousFlexibility/Radial/CentralRadius.lean`：** `ContinuousFlexibility.Radial.centralRadius`, `ContinuousFlexibility.Radial.hasDerivAt_centralRadius`, `ContinuousFlexibility.Radial.deriv_centralRadius_pos`, `ContinuousFlexibility.Radial.strictMono_centralRadius`, `ContinuousFlexibility.Radial.contDiff_centralRadius`

中央半径来自实际Laplace–Gaussian积分，严格正导数是已证结论。

**源码证据 `ContinuousFlexibility/Radial/CentralRadiusMetric.lean`：** `ContinuousFlexibility.Radial.range_centralRadius`, `ContinuousFlexibility.Radial.centralModelCoordinate_radius`, `ContinuousFlexibility.Radial.centralRadius_modelCoordinate`, `ContinuousFlexibility.Radial.hasStrictDerivAt_centralModelCoordinate`, `ContinuousFlexibility.Radial.contDiffAt_centralModelCoordinate`

中央半径range=Ioi 0、真实invFun的两向复合、逆导数及C∞已证。

**未完成内容：**
- Morse保留区半径的实际正导数、range和逆坐标。
- 将模型级接口统一为原R02所需的构造结果。

**逐条验收：**
- acceptance.01 [partial]：中央模型没有假设r_X>0；Morse模型尚未实际构造半径。
- acceptance.02 [partial]：中央模型两向复合和逆导数齐备；尚未提供覆盖待构造Morse单元的同一接口。

<a id="r02-02"></a>
### R02.02 径向轮廓和基线高度

**输出：** 由同一模型P,v与逆坐标定义w(r)=λP(X(r))v(X(r))和实际高度primitive，证明正性、C∞及pullback恒等式。

**局部依赖：** R02.01。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 200–550 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 同一半径逆用于profile和height
- λ>0以及全域/区间边界明确

**本轮核对：** 真实中央profile已构造，但同一profile的实际基线高度primitive及统一profile/height输出尚缺。

**源码证据 `ContinuousFlexibility/Radial/CentralRadiusMetric.lean`：** `ContinuousFlexibility.Radial.centralPulledProfile`, `ContinuousFlexibility.Radial.centralRadialProfile`, `ContinuousFlexibility.Radial.centralRadialProfile_pullback`, `ContinuousFlexibility.Radial.centralRadialProfile_pos`, `ContinuousFlexibility.Radial.contDiffOn_centralRadialProfile`

同一中央逆坐标定义真实profile并有pullback、正性和Ioi 0上的C∞。

**源码证据 `ContinuousFlexibility/Radial/RadialHeight.lean`：** `ContinuousFlexibility.Radial.radialHeightField`, `ContinuousFlexibility.Radial.heightRadial_radialHeightField`, `ContinuousFlexibility.Radial.normalizedHeightResidual_radialHeightField_zero`

径向高度的一般结论仍以给定h及h′=w为前提，未构造当前profile的primitive。

**未完成内容：**
- 实际定义并证明同一profile的height primitive、C∞和导数。
- 建立模型级共同profile/height接口。

**逐条验收：**
- acceptance.01 [partial]：profile确实使用中央半径逆；高度模块只处理给定primitive。
- acceptance.02 [partial]：c>0与r>0下profile正且C∞，但height的全域构造和共同pullback未完成。

<a id="r02-03"></a>
### R02.03 Liouville共轭与源因子

**输出：** 把已有坐标恒等式实例化到实际构造的L_j，精确证明非齐次方程两向等价及source Jacobian。

**局部依赖：** R02.01, R02.02。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 200–450 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 源项缩放符号与λ因子逐项保持
- 使用真实导数而非形式微分

**可复用基础：** Liouville.lean已有微分恒等式。

**本轮核对：** 通用共轭和source因子已证，实际中央二模齐次实例也存在；任务要求实际构造L_j上一般非齐次方程的完整实例化，尚未形成。

**源码证据 `ContinuousFlexibility/Radial/Liouville.lean`：** `ContinuousFlexibility.Radial.liouville_flux_at`, `ContinuousFlexibility.Radial.radialJacobi_liouville`, `ContinuousFlexibility.Radial.liouville_forcing_iff`, `ContinuousFlexibility.Radial.liouvilleSource`, `ContinuousFlexibility.Radial.liouville_source_pairing_density`

通用真实导数恒等式和非齐次源两向等价、source因子完整。

**源码证据 `ContinuousFlexibility/Radial/CentralModel.lean`：** `ContinuousFlexibility.Radial.radialJacobi_centralKernel`, `ContinuousFlexibility.Radial.centralKernelHeight_liouville_pullback`

已经对实际中央profile与明确二模零解实例化；并未对任意forcing/source作同样模型封装。

**未完成内容：**
- 把真实半径、profile和任意模型高度/source数据代入非齐次共轭，消去其所有结构假设。

**逐条验收：**
- acceptance.01 [partial]：通用恒等式保留λ及负号，实际模型仅有明确中央二模零源实例。
- acceptance.02 [covered]：所有微分由HasDerivAt/deriv和局部函数相等推导。

<a id="r02-04"></a>
### R02.04 两种测度的积分运输

**输出：** 将dr源配对和varpi dr谱测度在同一实际逆坐标下运输，证明可积条件及积分等式。

**局部依赖：** R02.01, R02.03。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 250–600 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- dr与谱测度分别给出等式
- 全域结果由截断极限证明而非仅有限区间

**可复用基础：** RadiusChange.lean已有有限区间积分换元。

**本轮核对：** 有限区间上的两种测度换元已完成；全域可积性、截断极限和全域等式尚未证明。

**源码证据 `ContinuousFlexibility/Radial/RadiusChange.lean`：** `ContinuousFlexibility.Radial.liouville_source_pairing_integral`, `ContinuousFlexibility.Radial.liouville_hilbert_integral`

两种真正有限区间积分换元都有明确条件并分别保留dr和12w/r²dr。

**未完成内容：**
- 全域可积性运输和截断极限。
- 将全域结论绑定同一实际模型逆坐标。

**逐条验收：**
- acceptance.01 [covered]：两个定理分别给普通source配对与谱Hilbert范数的精确密度。
- acceptance.02 [uncovered]：现有定理明确只处理A..B有限区间，没有全域截断极限。

<a id="r02-05"></a>
### R02.05 L²等价类与共轭映射

**输出：** 由测度运输构造实际L²等价类之间的线性等距同构，证明反向映射与微分表达式兼容。

**局部依赖：** R02.03, R02.04。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- a.e.代表元不影响映射
- 闭算子域识别留给R03/R06/R12而不从形式共轭推断

**本轮核对：** 尚未构造对应的全域L²等价类Liouville同构与反向微分兼容映射。

**未完成内容：**
- 由测度运输构造实际L²等价类之间的线性等距同构，证明反向映射与微分表达式兼容。
- 尚需满足：a.e.代表元不影响映射
- 尚需满足：闭算子域识别留给R03/R06/R12而不从形式共轭推断

**逐条验收：**
- acceptance.01 [uncovered]：尚未构造对应的全域L²等价类Liouville同构与反向微分兼容映射。
- acceptance.02 [uncovered]：尚未构造对应的全域L²等价类Liouville同构与反向微分兼容映射。

<a id="r02-06"></a>
### R02.06 组合并验收Liouville变换与径向实现

**输出：** 在半径方程和 r_X=v>0 下，严格推导由谱势到径向轮廓的Liouville变换，给出真实L_j的共轭表达式、源因子和两种测度。

**局部依赖：** R02.01, R02.02, R02.03, R02.04, R02.05。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 120–300 行。组合已证明输出和核对原合同，数学重负担已列为前置子任务。

**验收条件：**

- 逐项实例化此前子任务并导出原节点完整结论
- 不得把r_X>0假设当作模型构造
- 保留dr源配对与Hilbert谱测度的区别

**本轮核对：** 原R02核心微分公式有真实证明，完整构造/全域运输仍未组合闭合。

**源码证据 `ContinuousFlexibility/Radial/Liouville.lean`：** `ContinuousFlexibility.Radial.radialJacobi_liouville`, `ContinuousFlexibility.Radial.liouville_forcing_iff`, `ContinuousFlexibility.Radial.liouville_hilbert_density`

原节点的核心坐标表达式和两向source因子已证。

**源码证据 `ContinuousFlexibility/Radial/CentralRadiusMetric.lean`：** `ContinuousFlexibility.Radial.centralRadialProfile_pullback`, `ContinuousFlexibility.Radial.centralRadialProfile_pos`, `ContinuousFlexibility.Radial.range_centralRadius`

中央实际半径及profile支持模型实例；Morse和完整高度接口仍未提供。

**源码证据 `ContinuousFlexibility/Radial/RadiusChange.lean`：** `ContinuousFlexibility.Radial.liouville_source_pairing_integral`, `ContinuousFlexibility.Radial.liouville_hilbert_integral`

目前只有有限区间积分运输，不是全域L²等价类同构。

**未完成内容：**
- 先完成R02.01–05中尚缺的模型与全域接口，再导出完整原节点。

**逐条验收：**
- acceptance.01 [partial]：R02.01–05尚有实际模型/height/全域Hilbert运输义务。
- acceptance.02 [partial]：中央半径正性确为构造结论；待构造Morse仍缺。
- acceptance.03 [covered]：source配对和谱测度明确区分，有限区间恒等式实际保留密度。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：在半径方程和 r_X=v>0 下，严格推导由谱势到径向轮廓的Liouville变换，给出真实L_j的共轭表达式、源因子和两种测度。 | R02.06（组合全部子任务） |
| acceptance.01：不得把r_X>0假设当作模型构造 | R02.01, R02.02 |
| acceptance.02：保留dr源配对与Hilbert谱测度的区别 | R02.03, R02.04, R02.05 |
| remaining.01：把给定模型经实际半径逆构造成径向profile/height的完整接口 | R02.01, R02.02, R02.03 |
| remaining.02：全线Hilbert同构和闭算子域换元在R06/R12中继续处理 | R02.04, R02.05 |

**覆盖说明 R02.remaining.02：** R02.04–05提供全域Hilbert运输与共轭桥；真实闭微分域的具体识别由后继R03.04、R06.07–09、R12.01/06–08承担。此映射不将后继域结论标成R02已证明。

<a id="r03"></a>
## R03 中央谐振子模型的完整实现

**原节点完整目标：** 中央模型的闭二次型实现具有文中完整谱；二模恰一维零核，其余偶模有所需零能隙；得到正递增半径、端渐近、约化逆和双侧加权resolvent估计。另证明中央负区旅行角T_c=π/(2√2)及全部k≥1上的|sin(kT_c)|≥c/k。

**原上游里程碑：** R02

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [04-designing-the-profile.tex:177–301](../../paper/flexible-surface-rewrite/04-designing-the-profile.tex#L177)

<a id="r03-01"></a>
### R03.01 真实Hermite Hilbert基

**输出：** 把已证明的归一化Hermite总性实现为实际HilbertBasis，证明系数展开和Parseval。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 200–500 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 基向量与已有真实L²函数相等
- 展开在L²拓扑收敛

**可复用基础：** HermiteCompleteness.lean已证明实际L²完备性，HermiteBasis.lean属于活动工作。

**本轮核对：** 全部statement与两条验收均被真实HilbertBasis和L²收敛定理覆盖。

**源码证据 `ContinuousFlexibility/Radial/HermiteBasis.lean`：** `ContinuousFlexibility.Radial.hermiteBasis`, `ContinuousFlexibility.Radial.hermiteBasis_apply`, `ContinuousFlexibility.Radial.hermiteBasis_coeFn`, `ContinuousFlexibility.Radial.hermiteCoefficientTransform`, `ContinuousFlexibility.Radial.hermiteExpansion_hasSum`, `ContinuousFlexibility.Radial.hermiteExpansion_partialSums`, `ContinuousFlexibility.Radial.hermiteCoefficient_parseval`

真正Lebesgue L²等价类HilbertBasis、系数等距同构、L²展开收敛和Parseval全部存在。

**逐条验收：**
- acceptance.01 [covered]：hermiteBasis_apply/coeFn识别与原normalizedOscillatorHermite同一a.e.向量。
- acceptance.02 [covered]：HasSum和partialSums在实际HermiteL2范数拓扑收敛；Parseval给系数平方和。

<a id="r03-02"></a>
### R03.02 对角闭算子的图域

**输出：** 在Hermite系数中定义带实际能级的平方可和图域，证明对角算子闭合与自伴。

**局部依赖：** R03.01。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 350–700 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 域条件是能级乘系数属于l²
- 证明稠密和图范数完备

**本轮核对：** 图域、闭合、稠密、完备和自伴关系均已有实际定理；此处没有把它混同于尚未建成的Friedrichs二次型域。

**源码证据 `ContinuousFlexibility/Radial/OscillatorClosedGraph.lean`：** `ContinuousFlexibility.Radial.centralFiniteGraph`, `ContinuousFlexibility.Radial.centralClosedGraph`, `ContinuousFlexibility.Radial.mem_centralClosedGraph_iff`, `ContinuousFlexibility.Radial.centralClosedGraph_domain_iff`, `ContinuousFlexibility.Radial.centralClosedGraph_isClosed`, `ContinuousFlexibility.Radial.centralClosedGraph_domain_dense`

图是实际L²×L²闭包，域恰为能级乘系数属于l²，并证明闭合与稠密。

**源码证据 `ContinuousFlexibility/Radial/CentralGraphAdjoint.lean`：** `ContinuousFlexibility.Radial.centralClosedGraph_symmetric`, `ContinuousFlexibility.Radial.centralClosedGraph_pairing_iff`, `ContinuousFlexibility.Radial.centralClosedGraph_completeSpace`

真实图内积对称与graph-adjoint最大性给自伴关系；闭图子空间在实际product graph norm下完备。

**逐条验收：**
- acceptance.01 [covered]：centralClosedGraph_domain_iff准确为Memℓp(E_n c_n) 2。
- acceptance.02 [covered]：domain_dense和completeSpace分别给稠密与product graph norm完备；pairing_iff给adjoint relation的两向刻画。

<a id="r03-03"></a>
### R03.03 微分闭二次型实现

**输出：** 构造谐振子实际微分二次型及其闭包，证明cutoff核心稠密与分部积分。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 350–750 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 表述为真实弱导数和X加权L²条件
- 边界项由cutoff极限消失

**本轮核对：** 已有物理微分能量和紧支撑微分图核心，但尚未定义并识别真实弱一阶导数加X加权L²的闭二次型域/Friedrichs实现。

**源码证据 `ContinuousFlexibility/Radial/CentralEnergyIdentity.lean`：** `ContinuousFlexibility.Radial.oscillatorEnergyPairing`, `ContinuousFlexibility.Radial.shiftedCentralEnergyPairing`, `ContinuousFlexibility.Radial.oscillator_form_pairing`, `ContinuousFlexibility.Radial.central_shifted_form_pairing`, `ContinuousFlexibility.Radial.finiteHermiteFunction_shifted_energy`

真实整实线Lebesgue微分能量、积分分部和有限Hermite和的精确能量公式已证。

**源码证据 `ContinuousFlexibility/Radial/OscillatorCompactCore.lean`：** `ContinuousFlexibility.Radial.compactHermiteFunction_tendsto_L2`, `ContinuousFlexibility.Radial.compactHermiteImage_tendsto_L2`, `ContinuousFlexibility.Radial.centralCompactSmoothGraph_closure`

真实紧支撑cutoff在微分graph norm收敛；这是算子图核心，不自动等于闭形式核心。

**未完成内容：**
- 构造真实弱一阶导数与Xψ属于L²的闭形式域，证明其完备及稠密。
- 证明紧支撑C∞核心在形式范数稠密。
- 识别该闭形式关联的Friedrichs算子与现有最大弱微分图。

**逐条验收：**
- acceptance.01 [partial]：已有真实deriv和Xψ的积分公式；现有OscillatorEnergyDomain仍要求C²，不是完成的弱导数闭形式域。
- acceptance.02 [partial]：整线积分分部和微分图cutoff收敛已证；形式范数下的cutoff核心稠密、闭包识别仍缺。

<a id="r03-04"></a>
### R03.04 微分域与谱域识别

**输出：** 证明实际谐振子微分实现等于Hermite对角实现，两种域双向包含。

**局部依赖：** R03.01, R03.02, R03.03。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 350–750 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 不能只用候选本征方程推出域相等
- 逐项闭包极限与分布方程一致

**本轮核对：** 已经有真正紧支撑测试的分布弱微分图与Hermite图的双向等价，不再只是把谱图定义当作微分域。

**源码证据 `ContinuousFlexibility/Radial/OscillatorClosedGraph.lean`：** `ContinuousFlexibility.Radial.mem_centralClosedGraph_iff`, `ContinuousFlexibility.Radial.centralClosedGraph_domain_iff`

Hermite对角图及平方可和域有完整双向刻画。

**源码证据 `ContinuousFlexibility/Radial/OscillatorCompactCore.lean`：** `ContinuousFlexibility.Radial.CentralCompactWeakEquation`, `ContinuousFlexibility.Radial.centralClosedGraph_iff_compact_weak`, `ContinuousFlexibility.Radial.central_smooth_energy_graph`, `ContinuousFlexibility.Radial.centralCompactSmoothGraph_closure`

最大紧支撑C∞测试弱微分方程与同一Hermite图双向等价；真实紧支撑微分图闭包也被识别。

**逐条验收：**
- acceptance.01 [covered]：centralClosedGraph_iff_compact_weak通过所有C∞紧支撑测试函数给双向弱方程，不仅是本征函数候选。
- acceptance.02 [covered]：compactHermite的函数及实际微分像同时L²收敛，centralCompactSmoothGraph_closure把闭包与真实微分方程一致地识别。

<a id="r03-05"></a>
### R03.05 偶频零能隙与二模核

**输出：** 把中央能级整数分解估计接到实际闭谱，证明所有偶j≥4的统一零能隙和j=2核恰为高斯一维。

**局部依赖：** R03.04。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 200–550 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 所有m同时覆盖
- 算术下界作用于已识别完整谱

**可复用基础：** CentralSpectralGap.lean在活动工作中，只能作为待核对支持。

**本轮核对：** 所有偶频的算术gap已作用于有完整域刻画的真实弱微分图，并已有同图有界双侧逆和精确核，达到原路线允许的零能估计意义。

**源码证据 `ContinuousFlexibility/Radial/CentralSpectralGap.lean`：** `ContinuousFlexibility.Radial.centralGapDelta_pos`, `ContinuousFlexibility.Radial.centralSpectralLevel_two`, `ContinuousFlexibility.Radial.centralSpectralLevel_even_gap`, `ContinuousFlexibility.Radial.central_normalizedHermite_spectralLevel`

全部m、全部偶j≥4的实际中央能级统一正gap，j=2能级=4m。

**源码证据 `ContinuousFlexibility/Radial/OscillatorClosedGraph.lean`：** `ContinuousFlexibility.Radial.mem_centralClosedGraph_iff`, `ContinuousFlexibility.Radial.centralClosedGraph_domain_iff`

完整闭图用所有Hermite系数双向刻画，排除仅凭候选本征函数外推。

**源码证据 `ContinuousFlexibility/Radial/CentralGraphAdjoint.lean`：** `ContinuousFlexibility.Radial.centralClosedGraph_two_kernel_iff`, `ContinuousFlexibility.Radial.centralClosedGraph_even_kernel_iff`, `ContinuousFlexibility.Radial.centralClosedGraph_pairing_iff`

同一闭图二模核恰归一化Gaussian一维，其余偶模核零，图伴随最大。

**源码证据 `ContinuousFlexibility/Radial/CentralSpectralInverse.lean`：** `ContinuousFlexibility.Radial.centralHilbertInverse_norm_le`, `ContinuousFlexibility.Radial.centralHilbertInverse_graph`, `ContinuousFlexibility.Radial.centralHilbertInverse_left`, `ContinuousFlexibility.Radial.centralClosedGraph_even_exists_unique`

同一完整图上实际有界双侧逆给所需零能resolvent界，覆盖全部源。

**源码证据 `ContinuousFlexibility/Radial/OscillatorCompactCore.lean`：** `ContinuousFlexibility.Radial.centralClosedGraph_iff_compact_weak`

该完整图就是最大弱微分图，不能遗漏额外分布L²齐次解。

**逐条验收：**
- acceptance.01 [covered]：uniform gap对每个m和偶j同时成立；两类kernel定理和逆结论也没有有限截断限制。
- acceptance.02 [covered]：以完整系数图刻画、真实弱域等价及全源双侧逆检验零能隙，绝非只列候选能级；未宣称Friedrichs闭形式已建成。

<a id="r03-06"></a>
### R03.06 实际约化逆和投影

**输出：** 用真实正交投影构造j=2约化逆及其两向逆恒等式，并由零能隙构造其它偶频逆。

**局部依赖：** R03.05。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 250–600 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- j=2只在核的正交补反演
- 逆映回实际微分域

**本轮核对：** 实际正交投影、二模约化逆和其它偶频逆均已构造，并由compact-test桥接属于真实弱微分域。

**源码证据 `ContinuousFlexibility/Radial/CentralSpectralInverse.lean`：** `ContinuousFlexibility.Radial.centralHilbertInverse`, `ContinuousFlexibility.Radial.centralHilbertInverse_graph`, `ContinuousFlexibility.Radial.centralHilbertInverse_left`, `ContinuousFlexibility.Radial.centralReducedHilbertInverse`, `ContinuousFlexibility.Radial.centralReducedHilbertInverse_zero_coefficient`, `ContinuousFlexibility.Radial.centralReducedHilbertInverse_graph`, `ContinuousFlexibility.Radial.centralReducedHilbertInverse_left`, `ContinuousFlexibility.Radial.centralGroundProjection`, `ContinuousFlexibility.Radial.centralGroundProjection_idempotent`, `ContinuousFlexibility.Radial.centralGroundProjection_orthogonal`, `ContinuousFlexibility.Radial.centralReducedHilbertInverse_graph_projected`, `ContinuousFlexibility.Radial.centralReducedHilbertInverse_left_projected`

实际有界无权逆、ground正交投影和约化逆，均在同一真实Hermite闭图满足两向恒等式。

**源码证据 `ContinuousFlexibility/Radial/OscillatorCompactCore.lean`：** `ContinuousFlexibility.Radial.centralClosedGraph_iff_compact_weak`

逆输出所属的闭图与真实最大弱微分域双向相等。

**逐条验收：**
- acceptance.01 [covered]：zero_coefficient与投影的idempotent/orthogonal性质保证在真实ground正交补反演；projected两向公式保留核分量。
- acceptance.02 [covered]：graph和left定理给两向逆关系，compact_weak等价将值域识别为实际弱微分域。

<a id="r03-07"></a>
### R03.07 中央高阶端渐近

**输出：** 对实际Laplace–Gaussian半径和其逆证明论文所需各固定阶端渐近及权upsilon增长界。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 300–700 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 任意固定阶常数可依赖阶数
- 渐近绑定同一真实r而非替代模型

**可复用基础：** CentralRadius.lean已有正递增半径和实际ODE。

**本轮核对：** 实际半径与两端基本极限已有，论文所需各固定阶精确端渐近、逆坐标渐近和upsilon定量增长尚缺。

**源码证据 `ContinuousFlexibility/Radial/CentralRadiusMetric.lean`：** `ContinuousFlexibility.Radial.centralRadius_le_exp_of_nonpos`, `ContinuousFlexibility.Radial.tendsto_centralRadius_atBot`, `ContinuousFlexibility.Radial.tendsto_centralRadius_atTop`, `ContinuousFlexibility.Radial.range_centralRadius`

真实中央半径有两端基本极限与左端粗上界，但不是所有固定阶渐近。

**源码证据 `ContinuousFlexibility/Radial/CentralRadius.lean`：** `ContinuousFlexibility.Radial.contDiff_centralRadius`, `ContinuousFlexibility.Radial.centralRadius_ode`

真实C∞半径和实际ODE可供继续推导jets。

**未完成内容：**
- 各固定阶半径及逆坐标端渐近。
- 论文实际upsilon的统一上下界和固定阶导数控制。

**逐条验收：**
- acceptance.01 [partial]：当前仅有低阶基本极限，未给所有固定阶渐近常数。
- acceptance.02 [covered]：所有已有界均作用于同一真实Laplace–Gaussian半径。

<a id="r03-08"></a>
### R03.08 中央转点简单性

**输出：** 由实际半径/profile导数证明两个内部转点简单，并确定负区间与旅行角积分区间。

**局部依赖：** R03.07。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 200–500 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 转点处二阶量非零
- 负区间端点与真实profile对应

**可复用基础：** CentralTurningPoints.lean为活动文件，不登记为本子任务已完成。

**本轮核对：** 实际两个转点的简单性、真实profile负区和旅行角区间均可由现有精确定理衔接。

**源码证据 `ContinuousFlexibility/Radial/CentralTurningPoints.lean`：** `ContinuousFlexibility.Radial.centralRadialProfile_critical_iff`, `ContinuousFlexibility.Radial.central_turning_radii_pos_ordered`, `ContinuousFlexibility.Radial.centralRadialProfile_second_deriv_left_neg`, `ContinuousFlexibility.Radial.centralRadialProfile_second_deriv_right_pos`

真实profile恰有两个正且有序临界半径，二阶导数分别严格负/正。

**源码证据 `ContinuousFlexibility/Radial/CentralModel.lean`：** `ContinuousFlexibility.Radial.centralRadialProfile_deriv_scaled`, `ContinuousFlexibility.Radial.centralRadialProfile_deriv_neg_iff`, `ContinuousFlexibility.Radial.centralRadialProfile_deriv_pos_iff`

真实profile导数负区在X坐标恰由X²<A_c识别。

**源码证据 `ContinuousFlexibility/Radial/CentralRadius.lean`：** `ContinuousFlexibility.Radial.centralRadius_liouvilleRho`

同一半径和密度的真实Liouville rho恰A_c-X²。

**源码证据 `ContinuousFlexibility/Radial/CentralTravelAngle.lean`：** `ContinuousFlexibility.Radial.quadratic_positive_component`

ρ正分量严格是(-sqrt A_c,sqrt A_c)，与真实profile负导数区间一致。

**逐条验收：**
- acceptance.01 [covered]：左右转点二阶导数严格异号，因而均非零。
- acceptance.02 [covered]：有序正半径、导数sign iff、实际rho识别和positive_component共同给负区与旅行积分端点。

<a id="r03-09"></a>
### R03.09 双侧加权resolvent

**输出：** 先证upsilon H_j⁻¹单侧界，再以伴随与能量吸收证明upsilon H_j⁻¹ upsilon双侧界，二模使用约化逆。

**局部依赖：** R03.06, R03.07。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 350–750 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 给出实际有界算子及其定义域
- 不能把无权谱隙直接当作双权界

**本轮核对：** 尚未实现本项的实际upsilon加权逆或紧支撑辅助border；已有无权逆/ground正交投影不替代该目标。

**未完成内容：**
- 先证upsilon H_j⁻¹单侧界，再以伴随与能量吸收证明upsilon H_j⁻¹ upsilon双侧界，二模使用约化逆。
- 尚需满足：给出实际有界算子及其定义域
- 尚需满足：不能把无权谱隙直接当作双权界

**逐条验收：**
- acceptance.01 [uncovered]：尚未实现本项的实际upsilon加权逆或紧支撑辅助border；已有无权逆/ground正交投影不替代该目标。
- acceptance.02 [uncovered]：尚未实现本项的实际upsilon加权逆或紧支撑辅助border；已有无权逆/ground正交投影不替代该目标。

<a id="r03-10"></a>
### R03.10 辅助二模边框和缩放

**输出：** 构造紧支撑g₀及row ℓ₀，证明∫g₀φ₀dr=1、增广逆界和w高度缩放下的Hilbert归一化。

**局部依赖：** R03.06, R03.09。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 250–600 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 同一row/column用于后续buffer
- λ缩放后行列范数有统一界

**本轮核对：** 尚未实现本项的实际upsilon加权逆或紧支撑辅助border；已有无权逆/ground正交投影不替代该目标。

**未完成内容：**
- 构造紧支撑g₀及row ℓ₀，证明∫g₀φ₀dr=1、增广逆界和w高度缩放下的Hilbert归一化。
- 尚需满足：同一row/column用于后续buffer
- 尚需满足：λ缩放后行列范数有统一界

**逐条验收：**
- acceptance.01 [uncovered]：尚未实现本项的实际upsilon加权逆或紧支撑辅助border；已有无权逆/ground正交投影不替代该目标。
- acceptance.02 [uncovered]：尚未实现本项的实际upsilon加权逆或紧支撑辅助border；已有无权逆/ground正交投影不替代该目标。

<a id="r03-11"></a>
### R03.11 中央实际旅行角小除数

**输出：** 把已有T_c=π/(2√2)和所有k≥1的正小除数下界绑定到同一实际负区间。

**局部依赖：** R03.08。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 150–400 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 旅行角与谱相位分别陈述
- 零频不套用正频不等式

**可复用基础：** CentralTravelAngle.lean和CentralSmallDivisor.lean已有明确积分及算术定理。

**本轮核对：** 真实中央负区的旅行积分已计算，并在同一积分上证明全部正整数频率的定量小除数。

**源码证据 `ContinuousFlexibility/Radial/CentralTravelAngle.lean`：** `ContinuousFlexibility.Radial.quadratic_positive_component`, `ContinuousFlexibility.Radial.central_travel_integral_eq`, `ContinuousFlexibility.Radial.central_travel_integral_small_divisor`, `ContinuousFlexibility.Radial.exists_central_travel_integral_small_divisor`

实际sqrt(A-X²)积分及全部k≥1小除数下界已有；正区间端点明示。

**源码证据 `ContinuousFlexibility/Radial/CentralRadius.lean`：** `ContinuousFlexibility.Radial.centralRadius_liouvilleRho`

实际中央模型的rho正是积分所用A_c-X²。

**源码证据 `ContinuousFlexibility/Radial/CentralModel.lean`：** `ContinuousFlexibility.Radial.centralRadialProfile_deriv_neg_iff`

同一实际profile的负导数区与该rho正区对应。

**源码证据 `ContinuousFlexibility/Radial/CentralSmallDivisor.lean`：** `ContinuousFlexibility.Radial.centralTravelAngle`, `ContinuousFlexibility.Radial.central_sine_small_divisor`

旅行角的算术估计单独于谱gap处理，k≥1条件明确。

**逐条验收：**
- acceptance.01 [covered]：rho和profile区间桥接实际积分；旅行角证明与谱能级gap是不同模块和定理。
- acceptance.02 [covered]：所有正频率定理有1≤k前提，没有对零模套用下界。

<a id="r03-12"></a>
### R03.12 组合并验收中央谐振子模型的完整实现

**输出：** 中央模型的闭二次型实现具有文中完整谱；二模恰一维零核，其余偶模有所需零能隙；得到正递增半径、端渐近、约化逆和双侧加权resolvent估计。另证明中央负区旅行角T_c=π/(2√2)及全部k≥1上的|sin(kT_c)|≥c/k。

**局部依赖：** R03.01, R03.02, R03.03, R03.04, R03.05, R03.06, R03.07, R03.08, R03.09, R03.10, R03.11。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 120–300 行。组合已证明输出和核对原合同，数学重负担已列为前置子任务。

**验收条件：**

- 逐项实例化此前子任务并导出原节点完整结论
- 候选能级间隔不等于完整谱证明
- 约化逆保留二模边框
- 实际半径/权函数与抽象谱模型联系完整

**本轮核对：** 已完成多项局部/弱微分成果；闭二次型Friedrichs、全阶渐近、双侧权界和紧支撑辅助边框尚未闭合，不能认定中央模型完整。

**源码证据 `ContinuousFlexibility/Radial/HermiteBasis.lean`：** `ContinuousFlexibility.Radial.hermiteBasis`, `ContinuousFlexibility.Radial.hermiteCoefficient_parseval`

完整真实Hilbert基已经构造。

**源码证据 `ContinuousFlexibility/Radial/OscillatorCompactCore.lean`：** `ContinuousFlexibility.Radial.centralClosedGraph_iff_compact_weak`, `ContinuousFlexibility.Radial.centralCompactSmoothGraph_closure`

实际最大弱微分图和紧支撑微分core闭包识别完成。

**源码证据 `ContinuousFlexibility/Radial/CentralSpectralInverse.lean`：** `ContinuousFlexibility.Radial.centralHilbertInverse_graph`, `ContinuousFlexibility.Radial.centralReducedHilbertInverse_graph_projected`

同图无权逆和二模约化逆完成。

**源码证据 `ContinuousFlexibility/Radial/CentralTurningPoints.lean`：** `ContinuousFlexibility.Radial.centralRadialProfile_critical_iff`, `ContinuousFlexibility.Radial.centralRadialProfile_second_deriv_left_neg`, `ContinuousFlexibility.Radial.centralRadialProfile_second_deriv_right_pos`

真实简单转点完成。

**源码证据 `ContinuousFlexibility/Radial/CentralTravelAngle.lean`：** `ContinuousFlexibility.Radial.central_travel_integral_eq`, `ContinuousFlexibility.Radial.central_travel_integral_small_divisor`

实际旅行积分与正频下界完成。

**未完成内容：**
- R03.03闭形式/Friedrichs识别。
- R03.07完整固定阶渐近。
- R03.09双侧upsilon权resolvent。
- R03.10紧支撑辅助row/column及高度缩放界。

**逐条验收：**
- acceptance.01 [partial]：R03.03、R03.07、R03.09、R03.10未闭合。
- acceptance.02 [covered]：已有全系数图、弱域和有界逆，未仅凭候选能级宣称谱完成。
- acceptance.03 [partial]：ground正交投影的约化逆已完成；论文compact辅助border未构造。
- acceptance.04 [partial]：真实半径/转点/旅行角已绑定；Friedrichs及upsilon加权实现仍缺。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：中央模型的闭二次型实现具有文中完整谱；二模恰一维零核，其余偶模有所需零能隙；得到正递增半径、端渐近、约化逆和双侧加权resolvent估计。另证明中央负区旅行角T_c=π/(2√2)及全部k≥1上的 / sin(kT_c) / ≥c/k。 | R03.12（组合全部子任务） |
| acceptance.01：候选能级间隔不等于完整谱证明 | R03.01, R03.02, R03.03, R03.04, R03.05 |
| acceptance.02：约化逆保留二模边框 | R03.06, R03.09, R03.10 |
| acceptance.03：实际半径/权函数与抽象谱模型联系完整 | R03.07, R03.08, R03.09, R03.11 |
| remaining.01：完整高阶端渐近、转型非退化与约化逆界 | R03.06, R03.07, R03.08, R03.09 |
| remaining.02：Hermite–Gaussian实际L²完备性已证明，仍需识别闭微分算子域及二次型实现；不能仅由basis总性宣称已识别完整闭谱 | R03.01, R03.02, R03.03, R03.04 |
| remaining.03：其余偶模零能隙及双权resolvent定量估计仍待证明 | R03.05, R03.06, R03.09 |

<a id="r04"></a>
## R04 Morse模型的两类非共振

**原节点完整目标：** Morse闭实现具有所需离散谱和essential threshold，非平方参数给零能逆界；另精确计算旅行角并证明全部正频率的特征返回小除数下界。

**原上游里程碑：** R02

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [04-designing-the-profile.tex:304–377](../../paper/flexible-surface-rewrite/04-designing-the-profile.tex#L304)

<a id="r04-01"></a>
### R04.01 Morse实际闭二次型

**输出：** 对真实Morse势构造稠密半有界闭二次型及其Friedrichs微分实现。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 350–750 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- cutoff core的闭包条件明确
- 算子域由分布表达识别

**本轮核对：** 已有实际强能量数据和有限区间形式恒等式，但无稠密闭弱二次型及Friedrichs微分实现。

**源码证据 `ContinuousFlexibility/Radial/MorseModel.lean`：** `ContinuousFlexibility.Radial.MorseEnergyDomain`, `ContinuousFlexibility.Radial.morseGround_energyDomain`, `ContinuousFlexibility.Radial.integral_morse_factor`, `ContinuousFlexibility.Radial.integral_morse_shifted_nonneg`

真实强能量谓词、基态成员、有限区间积分分部和Dirichlet平方非负性已有；并非闭弱形式域。

**未完成内容：**
- 构造真实弱导数加指数权的闭形式域并证明稠密/完备。
- 识别Friedrichs算子及分布微分域。

**逐条验收：**
- acceptance.01 [uncovered]：没有cutoff core的形式闭包/完备性识别。
- acceptance.02 [uncovered]：没有闭Morse算子域的分布刻画。

<a id="r04-02"></a>
### R04.02 Morse一阶因子分解

**输出：** 在共同cutoff核心证明Dα及其伴随的两条因子恒等式，再以闭包推广至所需域。

**局部依赖：** R04.01。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 250–650 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 伴随包含边界条件
- 形式恒等式须实际延伸到闭域

**本轮核对：** 两条真实微分因子式已有，闭域伴随和闭包推广尚缺。

**源码证据 `ContinuousFlexibility/Radial/MorseModel.lean`：** `ContinuousFlexibility.Radial.morseExpression_factor`, `ContinuousFlexibility.Radial.morseExpression_partner_factor`, `ContinuousFlexibility.Radial.hasDerivAt_morseAnnihilation`, `ContinuousFlexibility.Radial.hasDerivAt_morseCreation`, `ContinuousFlexibility.Radial.integral_morse_factor`, `ContinuousFlexibility.Radial.integral_morse_shifted_nonneg`

C²实际函数上的两条微分因子分解和有限区间边界项已证，不是仅形式符号。

**未完成内容：**
- 定义并识别Dα的闭实现及真正Hilbert伴随域。
- 通过cutoff闭包将因子恒等式推广到目标闭域。

**逐条验收：**
- acceptance.01 [partial]：有限区间的真实boundary term已给；闭伴随operator domain和无穷端点条件尚未识别。
- acceptance.02 [uncovered]：没有把两条恒等式推广到已证明闭域。

<a id="r04-03"></a>
### R04.03 Morse基态的精确L²条件

**输出：** 对exp(-αX-ωexp(-X))证明微分方程及α>0恰为L²条件，并证明基态核一维。

**局部依赖：** R04.02。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 250–600 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 左右两端可积分别处理
- α≤0的排除不靠未证明谱公式

**本轮核对：** 基态公式、真实微分方程及精确L²条件完成；仍未证明目标闭Morse实现的基态核恰一维。

**源码证据 `ContinuousFlexibility/Radial/MorseModel.lean`：** `ContinuousFlexibility.Radial.morseGround_equation`, `ContinuousFlexibility.Radial.morseGround_paper_equation`, `ContinuousFlexibility.Radial.integrable_morseGround_sq`, `ContinuousFlexibility.Radial.memLp_morseGround_iff`, `ContinuousFlexibility.Radial.not_memLp_morseGround_of_nonpos`, `ContinuousFlexibility.Radial.morseGround_energyDomain`

实际基态微分方程与w>0时α>0恰L²条件、α≤0排除均已证明。

**未完成内容：**
- 证明Dα或相应闭Morse基态方程的所有L²解均为该基态的常数倍。
- 连接到实际闭Morse域，而非只有C²候选函数。

**逐条验收：**
- acceptance.01 [covered]：正α可积证明和非正α下界排除共同覆盖两端条件，非正支由半直线下界发散得到。
- acceptance.02 [covered]：not_memLp_morseGround_of_nonpos用真实函数下界，不依赖Morse谱公式。

<a id="r04-04"></a>
### R04.04 Morse升降与离散能级

**输出：** 用交织算子逐阶构造并识别E_m,j=j²B-(α_j-m)²的简单离散能级。

**局部依赖：** R04.02, R04.03。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 350–750 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 升降映射非零与域成员实际证明
- 整数m范围0≤m<α_j严格限定

**本轮核对：** 显式基态level及形式升降的真实微分基础存在；高m交织域、非零性和简单离散谱识别未完成。

**源码证据 `ContinuousFlexibility/Radial/MorseModel.lean`：** `ContinuousFlexibility.Radial.morseGround_paper_equation`, `ContinuousFlexibility.Radial.morseGround_paper_energyDomain`, `ContinuousFlexibility.Radial.morseExpression_factor`, `ContinuousFlexibility.Radial.morseExpression_partner_factor`

已证明m=0候选函数实际方程和强energy成员，并有真实微分伙伴因子式；尚不是完整闭谱升降。

**未完成内容：**
- 真正闭域上的升降交织、非零性、所有允许m的能级和简单性。

**逐条验收：**
- acceptance.01 [partial]：基态energy成员已有，升降后的所有域成员及非零性尚缺。
- acceptance.02 [uncovered]：没有以0≤m<α_j刻画完整升降能级的定理。

<a id="r04-05"></a>
### R04.05 Morse无遗漏离散谱

**输出：** 下降至-1<α≤0时用非负形式排除阈值下残余谱，证明能级表完整。

**局部依赖：** R04.04。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 350–750 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 明确有限下降终止
- 不把候选本征函数当作完整性

**本轮核对：** 目前只有MorseModel的实际基态和有限区间因子式；没有本项所需完整闭谱/全频参数/旅行角构造。

**未完成内容：**
- 下降至-1<α≤0时用非负形式排除阈值下残余谱，证明能级表完整。
- 尚需满足：明确有限下降终止
- 尚需满足：不把候选本征函数当作完整性

**逐条验收：**
- acceptance.01 [uncovered]：目前只有MorseModel的实际基态和有限区间因子式；没有本项所需完整闭谱/全频参数/旅行角构造。
- acceptance.02 [uncovered]：目前只有MorseModel的实际基态和有限区间因子式；没有本项所需完整闭谱/全频参数/旅行角构造。

<a id="r04-06"></a>
### R04.06 Morse本质谱阈值

**输出：** 对左端约束势和右端指数趋常势，证明阈值j²B及零能resolvent所需的谱隔离。

**局部依赖：** R04.01, R04.05。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 350–750 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 实际闭实现上作紧扰动或等价充分估计
- 阈值与离散能级分开处理

**本轮核对：** 目前只有MorseModel的实际基态和有限区间因子式；没有本项所需完整闭谱/全频参数/旅行角构造。

**未完成内容：**
- 对左端约束势和右端指数趋常势，证明阈值j²B及零能resolvent所需的谱隔离。
- 尚需满足：实际闭实现上作紧扰动或等价充分估计
- 尚需满足：阈值与离散能级分开处理

**逐条验收：**
- acceptance.01 [uncovered]：目前只有MorseModel的实际基态和有限区间因子式；没有本项所需完整闭谱/全频参数/旅行角构造。
- acceptance.02 [uncovered]：目前只有MorseModel的实际基态和有限区间因子式；没有本项所需完整闭谱/全频参数/旅行角构造。

<a id="r04-07"></a>
### R04.07 非平方参数算术隙

**输出：** 对同一非平方整数d的A,B证明所有允许j,m的离散能级零能下界及阈值下界。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- A>4B>0实际验证
- 覆盖全部j≥2而非有限检查

**本轮核对：** 目前只有MorseModel的实际基态和有限区间因子式；没有本项所需完整闭谱/全频参数/旅行角构造。

**未完成内容：**
- 对同一非平方整数d的A,B证明所有允许j,m的离散能级零能下界及阈值下界。
- 尚需满足：A>4B>0实际验证
- 尚需满足：覆盖全部j≥2而非有限检查

**逐条验收：**
- acceptance.01 [uncovered]：目前只有MorseModel的实际基态和有限区间因子式；没有本项所需完整闭谱/全频参数/旅行角构造。
- acceptance.02 [uncovered]：目前只有MorseModel的实际基态和有限区间因子式；没有本项所需完整闭谱/全频参数/旅行角构造。

<a id="r04-08"></a>
### R04.08 Morse实际零能逆

**输出：** 将谱隔离和非平方算术隙组合成实际闭算子的有界双侧逆及8d⁹型范数界。

**局部依赖：** R04.05, R04.06, R04.07。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 250–600 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 逆的值域落在真实算子域
- 参数依赖和常数界明确

**本轮核对：** 目前只有MorseModel的实际基态和有限区间因子式；没有本项所需完整闭谱/全频参数/旅行角构造。

**未完成内容：**
- 将谱隔离和非平方算术隙组合成实际闭算子的有界双侧逆及8d⁹型范数界。
- 尚需满足：逆的值域落在真实算子域
- 尚需满足：参数依赖和常数界明确

**逐条验收：**
- acceptance.01 [uncovered]：目前只有MorseModel的实际基态和有限区间因子式；没有本项所需完整闭谱/全频参数/旅行角构造。
- acceptance.02 [uncovered]：目前只有MorseModel的实际基态和有限区间因子式；没有本项所需完整闭谱/全频参数/旅行角构造。

<a id="r04-09"></a>
### R04.09 Morse旅行角积分

**输出：** 求ρ正区间的两个简单根，严格积分得到T=π(√A/2-√B)=π/(2√d)。

**局部依赖：** R04.07。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 250–600 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 换元积分的端点奇性受控
- 绑定与谱算术相同的A,B,d

**本轮核对：** 目前只有MorseModel的实际基态和有限区间因子式；没有本项所需完整闭谱/全频参数/旅行角构造。

**未完成内容：**
- 求ρ正区间的两个简单根，严格积分得到T=π(√A/2-√B)=π/(2√d)。
- 尚需满足：换元积分的端点奇性受控
- 尚需满足：绑定与谱算术相同的A,B,d

**逐条验收：**
- acceptance.01 [uncovered]：目前只有MorseModel的实际基态和有限区间因子式；没有本项所需完整闭谱/全频参数/旅行角构造。
- acceptance.02 [uncovered]：目前只有MorseModel的实际基态和有限区间因子式；没有本项所需完整闭谱/全频参数/旅行角构造。

<a id="r04-10"></a>
### R04.10 Morse正频返回下界

**输出：** 由非平方整数分解和最近整数估计证明所有k≥1的|sin(kT)|≥1/(3k√d)。

**局部依赖：** R04.09。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 小k与大k分支齐全
- 不得用谱能隙代替特征返回非共振

**本轮核对：** 目前只有MorseModel的实际基态和有限区间因子式；没有本项所需完整闭谱/全频参数/旅行角构造。

**未完成内容：**
- 由非平方整数分解和最近整数估计证明所有k≥1的|sin(kT)|≥1/(3k√d)。
- 尚需满足：小k与大k分支齐全
- 尚需满足：不得用谱能隙代替特征返回非共振

**逐条验收：**
- acceptance.01 [uncovered]：目前只有MorseModel的实际基态和有限区间因子式；没有本项所需完整闭谱/全频参数/旅行角构造。
- acceptance.02 [uncovered]：目前只有MorseModel的实际基态和有限区间因子式；没有本项所需完整闭谱/全频参数/旅行角构造。

<a id="r04-11"></a>
### R04.11 组合并验收Morse模型的两类非共振

**输出：** Morse闭实现具有所需离散谱和essential threshold，非平方参数给零能逆界；另精确计算旅行角并证明全部正频率的特征返回小除数下界。

**局部依赖：** R04.01, R04.02, R04.03, R04.04, R04.05, R04.06, R04.07, R04.08, R04.09, R04.10。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 120–300 行。组合已证明输出和核对原合同，数学重负担已列为前置子任务。

**验收条件：**

- 逐项实例化此前子任务并导出原节点完整结论
- 正频率k≥1，零模另处理
- 谱相位与特征相位不可混同
- 闭算子实现和resolvent界不能由形式谱公式代替

**本轮核对：** Morse实际局部基态与因子式已有；父任务的闭谱、逆和特征返回链未闭合。

**源码证据 `ContinuousFlexibility/Radial/MorseModel.lean`：** `ContinuousFlexibility.Radial.morseGround_paper_equation`, `ContinuousFlexibility.Radial.memLp_morseGround_iff`, `ContinuousFlexibility.Radial.morseExpression_factor`, `ContinuousFlexibility.Radial.morseExpression_partner_factor`

存在实际基态和微分因子分解支持，但全闭谱、阈值、逆和旅行角均未完成。

**未完成内容：**
- 闭Morse实现、完整离散谱/本质阈值、非平方全频隙、实际零能逆。
- 实际Morse旅行积分和全部正频率返回下界。

**逐条验收：**
- acceptance.01 [partial]：R04.01–10尚有核心未完成义务。
- acceptance.02 [uncovered]：Morse所有正频率的旅行角返回下界尚未实现。
- acceptance.03 [partial]：源码没有将基态公式当作旅行角结果，但两条非共振的完整结论仍缺。
- acceptance.04 [uncovered]：没有实际闭Morse谱实现及有界resolvent。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：Morse闭实现具有所需离散谱和essential threshold，非平方参数给零能逆界；另精确计算旅行角并证明全部正频率的特征返回小除数下界。 | R04.11（组合全部子任务） |
| acceptance.01：正频率k≥1，零模另处理 | R04.07, R04.08, R04.10 |
| acceptance.02：谱相位与特征相位不可混同 | R04.07, R04.09, R04.10 |
| acceptance.03：闭算子实现和resolvent界不能由形式谱公式代替 | R04.01, R04.02, R04.04, R04.05, R04.06, R04.08 |

<a id="r05"></a>
## R05 真实单元、连接与累积平坦轮廓

**原节点完整目标：** 对所有足够大的N及全部高度选择σ_n∈[1,2]，构造Morse单元和正连接，使半径累积于正的有限端点、轮廓正、转点简单、零延拓C∞平坦；推出质量/阻力、离散尺度和全部固定阶jet界。

**原上游里程碑：** R04, R01

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [05-flat-end-chain.tex:20–268](../../paper/flexible-surface-rewrite/05-flat-end-chain.tex#L20)

<a id="r05-01"></a>
### R05.01 非平方单元参数与尺度预算

**输出：** 实际选择d_n及A_n,B_n,λ_n(σ)，证明统一于σ∈[1,2]^ℕ的指数比较和可继续增大N的阈值。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 250–600 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 指数阶数2<5/2<3的吸收逐条证明
- 常数与N、σ的允许依赖登记

**本轮核对：** 冻结源码没有实际Morse径向单元、正连接、无限累积profile或其统一定量估计；中央profile不能替代该构造。

**未完成内容：**
- 实际选择d_n及A_n,B_n,λ_n(σ)，证明统一于σ∈[1,2]^ℕ的指数比较和可继续增大N的阈值。
- 尚需满足：指数阶数2<5/2<3的吸收逐条证明
- 尚需满足：常数与N、σ的允许依赖登记

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有实际Morse径向单元、正连接、无限累积profile或其统一定量估计；中央profile不能替代该构造。
- acceptance.02 [uncovered]：冻结源码没有实际Morse径向单元、正连接、无限累积profile或其统一定量估计；中央profile不能替代该构造。

<a id="r05-02"></a>
### R05.02 单个Morse半径的Volterra构造

**输出：** 按指定右转点初值实际解半径系统，并在保留区证明r=1+O(A)与v>0。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 350–750 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 存在唯一的真实光滑解
- 不能将v>0留为输入假设

**本轮核对：** 冻结源码没有实际Morse径向单元、正连接、无限累积profile或其统一定量估计；中央profile不能替代该构造。

**未完成内容：**
- 按指定右转点初值实际解半径系统，并在保留区证明r=1+O(A)与v>0。
- 尚需满足：存在唯一的真实光滑解
- 尚需满足：不能将v>0留为输入假设

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有实际Morse径向单元、正连接、无限累积profile或其统一定量估计；中央profile不能替代该构造。
- acceptance.02 [uncovered]：冻结源码没有实际Morse径向单元、正连接、无限累积profile或其统一定量估计；中央profile不能替代该构造。

<a id="r05-03"></a>
### R05.03 Morse单元几何的统一估计

**输出：** 由真实半径解证明左右cut处r,v及长正区间界，确定两个转点的简单性。

**局部依赖：** R05.02。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–700 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 所有小A常数统一
- 保留区与cut位置精确定义

**本轮核对：** 冻结源码没有实际Morse径向单元、正连接、无限累积profile或其统一定量估计；中央profile不能替代该构造。

**未完成内容：**
- 由真实半径解证明左右cut处r,v及长正区间界，确定两个转点的简单性。
- 尚需满足：所有小A常数统一
- 尚需满足：保留区与cut位置精确定义

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有实际Morse径向单元、正连接、无限累积profile或其统一定量估计；中央profile不能替代该构造。
- acceptance.02 [uncovered]：冻结源码没有实际Morse径向单元、正连接、无限累积profile或其统一定量估计；中央profile不能替代该构造。

<a id="r05-04"></a>
### R05.04 正连接的光滑插值

**输出：** 构造实际正连接profile，匹配两端全jets并证明长度A_n¹²型控制与所需正类型符号。

**局部依赖：** R05.01, R05.03。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–700 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 不是仅匹配函数值或一阶
- 高度对比允许很大

**本轮核对：** 冻结源码没有实际Morse径向单元、正连接、无限累积profile或其统一定量估计；中央profile不能替代该构造。

**未完成内容：**
- 构造实际正连接profile，匹配两端全jets并证明长度A_n¹²型控制与所需正类型符号。
- 尚需满足：不是仅匹配函数值或一阶
- 尚需满足：高度对比允许很大

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有实际Morse径向单元、正连接、无限累积profile或其统一定量估计；中央profile不能替代该构造。
- acceptance.02 [uncovered]：冻结源码没有实际Morse径向单元、正连接、无限累积profile或其统一定量估计；中央profile不能替代该构造。

<a id="r05-05"></a>
### R05.05 无限单元的径向累积

**输出：** 递推放置并缩放真实单元和连接，证明半径端点有限、正且所有单元无重叠地覆盖尾。

**局部依赖：** R05.01, R05.03, R05.04。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–700 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 对整个高度参数立方体统一
- 左右方向分别确定

**本轮核对：** 冻结源码没有实际Morse径向单元、正连接、无限累积profile或其统一定量估计；中央profile不能替代该构造。

**未完成内容：**
- 递推放置并缩放真实单元和连接，证明半径端点有限、正且所有单元无重叠地覆盖尾。
- 尚需满足：对整个高度参数立方体统一
- 尚需满足：左右方向分别确定

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有实际Morse径向单元、正连接、无限累积profile或其统一定量估计；中央profile不能替代该构造。
- acceptance.02 [uncovered]：冻结源码没有实际Morse径向单元、正连接、无限累积profile或其统一定量估计；中央profile不能替代该构造。

<a id="r05-06"></a>
### R05.06 轮廓全阶平坦延拓

**输出：** 证明无限拼接w内部正且C∞，每个固定阶径向导数在有限端点趋零并有实际零延拓。

**局部依赖：** R05.05。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–700 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 每个阶数均由一致jet估计推出
- 有限接缝和累积端点分别处理

**本轮核对：** 冻结源码没有实际Morse径向单元、正连接、无限累积profile或其统一定量估计；中央profile不能替代该构造。

**未完成内容：**
- 证明无限拼接w内部正且C∞，每个固定阶径向导数在有限端点趋零并有实际零延拓。
- 尚需满足：每个阶数均由一致jet估计推出
- 尚需满足：有限接缝和累积端点分别处理

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有实际Morse径向单元、正连接、无限累积profile或其统一定量估计；中央profile不能替代该构造。
- acceptance.02 [uncovered]：冻结源码没有实际Morse径向单元、正连接、无限累积profile或其统一定量估计；中央profile不能替代该构造。

<a id="r05-07"></a>
### R05.07 真实质量与阻力积分

**输出：** 由同一w,r计算μ_n,R_n^I,ν_n,R_n的两侧估计，包含连接误差和半径缩放因子。

**局部依赖：** R05.03, R05.04, R05.05。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–700 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 使用真实积分而非定义为近似值
- mass与resistance两种测度均显式

**本轮核对：** 冻结源码没有实际Morse径向单元、正连接、无限累积profile或其统一定量估计；中央profile不能替代该构造。

**未完成内容：**
- 由同一w,r计算μ_n,R_n^I,ν_n,R_n的两侧估计，包含连接误差和半径缩放因子。
- 尚需满足：使用真实积分而非定义为近似值
- 尚需满足：mass与resistance两种测度均显式

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有实际Morse径向单元、正连接、无限累积profile或其统一定量估计；中央profile不能替代该构造。
- acceptance.02 [uncovered]：冻结源码没有实际Morse径向单元、正连接、无限累积profile或其统一定量估计；中央profile不能替代该构造。

<a id="r05-08"></a>
### R05.08 离散增长与衰减尺度

**输出：** 从积分估计证明H_n,E_n,S_n及μ_nR_n等全部离散比较和累计误差界。

**局部依赖：** R05.01, R05.07。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 250–600 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 每个比较保留索引阈值
- 对所有σ统一常数

**本轮核对：** 冻结源码没有实际Morse径向单元、正连接、无限累积profile或其统一定量估计；中央profile不能替代该构造。

**未完成内容：**
- 从积分估计证明H_n,E_n,S_n及μ_nR_n等全部离散比较和累计误差界。
- 尚需满足：每个比较保留索引阈值
- 尚需满足：对所有σ统一常数

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有实际Morse径向单元、正连接、无限累积profile或其统一定量估计；中央profile不能替代该构造。
- acceptance.02 [uncovered]：冻结源码没有实际Morse径向单元、正连接、无限累积profile或其统一定量估计；中央profile不能替代该构造。

<a id="r05-09"></a>
### R05.09 深尾条件的频率范围

**输出：** 证明j²A_n√log(A_n/B_n)足够小时真实尾满足全部deep-tail不等式。

**局部依赖：** R05.07, R05.08。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 250–600 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 质量-阻力三类小量和两类大量分别验证
- 左端一格索引移动预先注明

**本轮核对：** 冻结源码没有实际Morse径向单元、正连接、无限累积profile或其统一定量估计；中央profile不能替代该构造。

**未完成内容：**
- 证明j²A_n√log(A_n/B_n)足够小时真实尾满足全部deep-tail不等式。
- 尚需满足：质量-阻力三类小量和两类大量分别验证
- 尚需满足：左端一格索引移动预先注明

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有实际Morse径向单元、正连接、无限累积profile或其统一定量估计；中央profile不能替代该构造。
- acceptance.02 [uncovered]：冻结源码没有实际Morse径向单元、正连接、无限累积profile或其统一定量估计；中央profile不能替代该构造。

<a id="r05-10"></a>
### R05.10 高度参数的局部与全局依赖

**输出：** 证明半径cut与σ无关、σ_n同比缩放后续profile；建立有限prefix光滑依赖和所需product连续性。

**局部依赖：** R05.04, R05.05, R05.08。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–550 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 不得把自然端线连续性提前当假设
- 仅几何数据在此闭合

**本轮核对：** 冻结源码没有实际Morse径向单元、正连接、无限累积profile或其统一定量估计；中央profile不能替代该构造。

**未完成内容：**
- 证明半径cut与σ无关、σ_n同比缩放后续profile；建立有限prefix光滑依赖和所需product连续性。
- 尚需满足：不得把自然端线连续性提前当假设
- 尚需满足：仅几何数据在此闭合

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有实际Morse径向单元、正连接、无限累积profile或其统一定量估计；中央profile不能替代该构造。
- acceptance.02 [uncovered]：冻结源码没有实际Morse径向单元、正连接、无限累积profile或其统一定量估计；中央profile不能替代该构造。

<a id="r05-11"></a>
### R05.11 组合并验收真实单元、连接与累积平坦轮廓

**输出：** 对所有足够大的N及全部高度选择σ_n∈[1,2]，构造Morse单元和正连接，使半径累积于正的有限端点、轮廓正、转点简单、零延拓C∞平坦；推出质量/阻力、离散尺度和全部固定阶jet界。

**局部依赖：** R05.01, R05.02, R05.03, R05.04, R05.05, R05.06, R05.07, R05.08, R05.09, R05.10。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 120–300 行。组合已证明输出和核对原合同，数学重负担已列为前置子任务。

**验收条件：**

- 逐项实例化此前子任务并导出原节点完整结论
- 显式保留N可继续增大的构造自由
- 零延拓包括全部阶数
- 证明估计对整个参数立方体一致

**本轮核对：** 冻结源码没有实际Morse径向单元、正连接、无限累积profile或其统一定量估计；中央profile不能替代该构造。

**未完成内容：**
- 对所有足够大的N及全部高度选择σ_n∈[1,2]，构造Morse单元和正连接，使半径累积于正的有限端点、轮廓正、转点简单、零延拓C∞平坦；推出质量/阻力、离散尺度和全部固定阶jet界。
- 尚需满足：逐项实例化此前子任务并导出原节点完整结论
- 尚需满足：显式保留N可继续增大的构造自由
- 尚需满足：零延拓包括全部阶数
- 尚需满足：证明估计对整个参数立方体一致

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有实际Morse径向单元、正连接、无限累积profile或其统一定量估计；中央profile不能替代该构造。
- acceptance.02 [uncovered]：冻结源码没有实际Morse径向单元、正连接、无限累积profile或其统一定量估计；中央profile不能替代该构造。
- acceptance.03 [uncovered]：冻结源码没有实际Morse径向单元、正连接、无限累积profile或其统一定量估计；中央profile不能替代该构造。
- acceptance.04 [uncovered]：冻结源码没有实际Morse径向单元、正连接、无限累积profile或其统一定量估计；中央profile不能替代该构造。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：对所有足够大的N及全部高度选择σ_n∈[1,2]，构造Morse单元和正连接，使半径累积于正的有限端点、轮廓正、转点简单、零延拓C∞平坦；推出质量/阻力、离散尺度和全部固定阶jet界。 | R05.11（组合全部子任务） |
| acceptance.01：显式保留N可继续增大的构造自由 | R05.01, R05.08, R05.09, R05.10 |
| acceptance.02：零延拓包括全部阶数 | R05.04, R05.05, R05.06 |
| acceptance.03：证明估计对整个参数立方体一致 | R05.01, R05.03, R05.05, R05.07, R05.08, R05.10 |

<a id="r06"></a>
## R06 深尾连续算子逆与唯一衰减线

**原节点完整目标：** 深尾条件下，A_p=-p⁻¹(p∂x)'的Dirichlet/Friedrichs实现具有文中逆界，端点恰有一条自然L²齐次解线；其衰减、原半径平坦性、Green核衰减和参数连续性成立。

**原上游里程碑：** R01, R05

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [05-flat-end-chain.tex:271–505](../../paper/flexible-surface-rewrite/05-flat-end-chain.tex#L271)

<a id="r06-01"></a>
### R06.01 阻力坐标和边界方向

**输出：** 在真实deep tail上构造ds=dx/p，证明测度和方程换元，明确左端初始阻力边及后续一格索引。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 250–600 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 两侧source Jacobian精确保留
- 有限入口Dirichlet条件与外端条件分别陈述

**本轮核对：** 冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。

**未完成内容：**
- 在真实deep tail上构造ds=dx/p，证明测度和方程换元，明确左端初始阻力边及后续一格索引。
- 尚需满足：两侧source Jacobian精确保留
- 尚需满足：有限入口Dirichlet条件与外端条件分别陈述

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。
- acceptance.02 [uncovered]：冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。

<a id="r06-02"></a>
### R06.02 单边Dirichlet Green核

**输出：** 构造有限edge零势核G₀，证明核乘积不等式与Λ∫ωG₀(s,s)≤3η。

**局部依赖：** R06.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 250–600 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- edge端点和核对角点包括在陈述中
- 实际积分与权密度对应

**本轮核对：** 冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。

**未完成内容：**
- 构造有限edge零势核G₀，证明核乘积不等式与Λ∫ωG₀(s,s)≤3η。
- 尚需满足：edge端点和核对角点包括在陈述中
- 尚需满足：实际积分与权密度对应

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。
- acceptance.02 [uncovered]：冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。

<a id="r06-03"></a>
### R06.03 单边实际逆与Poisson函数

**输出：** 在同一edge空间用收敛核级数构造GΛ及v₀,v₁，证明比较界、零边界能量界和实际方程。

**局部依赖：** R06.02。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 350–750 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 先证同空间有界小量再用Neumann
- Poisson边界值与Green零边界均验证

**本轮核对：** 冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。

**未完成内容：**
- 在同一edge空间用收敛核级数构造GΛ及v₀,v₁，证明比较界、零边界能量界和实际方程。
- 尚需满足：先证同空间有界小量再用Neumann
- 尚需满足：Poisson边界值与Green零边界均验证

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。
- acceptance.02 [uncovered]：冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。

<a id="r06-04"></a>
### R06.04 精确边界导数矩阵

**输出：** 由Green恒等式计算edge的c_n,d_n,i，证明c_n≈R_n⁻¹和b_n≈Λμ_n。

**局部依赖：** R06.03。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 250–650 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 所有有向符号正确
- 初始阻力边独立包含

**本轮核对：** 冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。

**未完成内容：**
- 由Green恒等式计算edge的c_n,d_n,i，证明c_n≈R_n⁻¹和b_n≈Λμ_n。
- 尚需满足：所有有向符号正确
- 尚需满足：初始阻力边独立包含

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。
- acceptance.02 [uncovered]：冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。

<a id="r06-05"></a>
### R06.05 节点插值的L²两侧界

**输出：** 对Ta=a_nv₀+a_n+1v₁证明l²(μ)到连续L²(pdx)的两侧范数界。

**局部依赖：** R06.03, R06.04。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 250–650 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 无限求和收敛实际证明
- 相邻误差索引移动受控

**本轮核对：** 冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。

**未完成内容：**
- 对Ta=a_nv₀+a_n+1v₁证明l²(μ)到连续L²(pdx)的两侧范数界。
- 尚需满足：无限求和收敛实际证明
- 尚需满足：相邻误差索引移动受控

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。
- acceptance.02 [uncovered]：冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。

<a id="r06-06"></a>
### R06.06 节点Jacobi算子逆

**输出：** 在加权l²中证明节点矩阵对角占优、有界可逆及C/Λ界。

**局部依赖：** R06.04。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 250–650 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 算子定义于完整l²而非仅有限矩阵
- 常数独立截断长度

**本轮核对：** 冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。

**未完成内容：**
- 在加权l²中证明节点矩阵对角占优、有界可逆及C/Λ界。
- 尚需满足：算子定义于完整l²而非仅有限矩阵
- 尚需满足：常数独立截断长度

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。
- acceptance.02 [uncovered]：冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。

<a id="r06-07"></a>
### R06.07 连续闭形式域分解

**输出：** 构造真实连续闭二次型，证明每个域元素的节点trace属于l²并唯一分解为Ta+v，v各节点为零。

**局部依赖：** R06.03, R06.05。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 350–750 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- trace由能量估计控制
- 两部分对shifted form正交

**本轮核对：** 冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。

**未完成内容：**
- 构造真实连续闭二次型，证明每个域元素的节点trace属于l²并唯一分解为Ta+v，v各节点为零。
- 尚需满足：trace由能量估计控制
- 尚需满足：两部分对shifted form正交

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。
- acceptance.02 [uncovered]：冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。

<a id="r06-08"></a>
### R06.08 Friedrichs实现和实际逆公式

**输出：** 从闭形式分解识别连续Dirichlet/Friedrichs算子，证明其逆为G_D+T D⁻¹T*及C/Λ界。

**局部依赖：** R06.05, R06.06, R06.07。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 350–750 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 不是只把逆的像定义成目标域
- 正反向逆恒等式都在实际域上成立

**本轮核对：** 冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。

**未完成内容：**
- 从闭形式分解识别连续Dirichlet/Friedrichs算子，证明其逆为G_D+T D⁻¹T*及C/Λ界。
- 尚需满足：不是只把逆的像定义成目标域
- 尚需满足：正反向逆恒等式都在实际域上成立

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。
- acceptance.02 [uncovered]：冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。

<a id="r06-09"></a>
### R06.09 有限Dirichlet截断强极限

**输出：** 证明有限edge直和和节点逆压缩均强收敛，并识别极限为前项Friedrichs逆。

**局部依赖：** R06.06, R06.08。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–700 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 有限截断的边界条件一致
- 极限不能仅由统一范数界推断

**本轮核对：** 冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。

**未完成内容：**
- 证明有限edge直和和节点逆压缩均强收敛，并识别极限为前项Friedrichs逆。
- 尚需满足：有限截断的边界条件一致
- 尚需满足：极限不能仅由统一范数界推断

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。
- acceptance.02 [uncovered]：冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。

<a id="r06-10"></a>
### R06.10 自然衰减节点解的构造

**输出：** 在[1,2]上证明后向continued fraction统一收缩，由外墙极限构造正y_n及精确比值界。

**局部依赖：** R06.04, R06.06。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–700 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 全部height参数统一收缩常数
- 证明y_n非零且满足真实节点方程

**本轮核对：** 冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。

**未完成内容：**
- 在[1,2]上证明后向continued fraction统一收缩，由外墙极限构造正y_n及精确比值界。
- 尚需满足：全部height参数统一收缩常数
- 尚需满足：证明y_n非零且满足真实节点方程

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。
- acceptance.02 [uncovered]：冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。

<a id="r06-11"></a>
### R06.11 连续L²自然线的唯一性

**输出：** 将节点解插值为连续齐次解，并用离散Wronskian公式证明任何独立解的连续L²质量发散。

**局部依赖：** R06.05, R06.10。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–700 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 不能仅证明节点l²发散而漏掉连续质量
- 得出limit-point及恰一维自然线

**本轮核对：** 冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。

**未完成内容：**
- 将节点解插值为连续齐次解，并用离散Wronskian公式证明任何独立解的连续L²质量发散。
- 尚需满足：不能仅证明节点l²发散而漏掉连续质量
- 尚需满足：得出limit-point及恰一维自然线

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。
- acceptance.02 [uncovered]：冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。

<a id="r06-12"></a>
### R06.12 原半径衰减与全阶平坦性

**输出：** 累计比值证明e^{-(S_k-S_m)}型衰减，再恢复gauge及各固定阶真实径向导数，构造平坦延拓。

**局部依赖：** R06.10, R06.11。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–700 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- gauge有界性只在已证deep频段使用
- 每阶极限实际证明

**本轮核对：** 冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。

**未完成内容：**
- 累计比值证明e^{-(S_k-S_m)}型衰减，再恢复gauge及各固定阶真实径向导数，构造平坦延拓。
- 尚需满足：gauge有界性只在已证deep频段使用
- 尚需满足：每阶极限实际证明

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。
- acceptance.02 [uncovered]：冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。

<a id="r06-13"></a>
### R06.13 端线的product拓扑连续性

**输出：** 用continued fraction统一尾误差和有限prefix连续依赖证明自然端线随所有σ的product拓扑连续。

**局部依赖：** R06.09, R06.10, R06.11。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 250–600 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 不要求不合理的全参数一致范数拓扑
- 对任意固定频率和入口给连续性

**本轮核对：** 冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。

**未完成内容：**
- 用continued fraction统一尾误差和有限prefix连续依赖证明自然端线随所有σ的product拓扑连续。
- 尚需满足：不要求不合理的全参数一致范数拓扑
- 尚需满足：对任意固定频率和入口给连续性

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。
- acceptance.02 [uncovered]：冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。

<a id="r06-14"></a>
### R06.14 离散Green列和局域核界

**输出：** 构造节点逆的Green列，借自然线商与对称性证明两侧e^{-|S_n-S_m|}界，再加入same-edge项。

**局部依赖：** R06.06, R06.08, R06.10, R06.11, R06.12。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–700 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 插值符号和邻边项不遗漏
- 绝对核界与算子范数分别陈述

**本轮核对：** 冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。

**未完成内容：**
- 构造节点逆的Green列，借自然线商与对称性证明两侧e^{-|S_n-S_m|}界，再加入same-edge项。
- 尚需满足：插值符号和邻边项不遗漏
- 尚需满足：绝对核界与算子范数分别陈述

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。
- acceptance.02 [uncovered]：冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。

<a id="r06-15"></a>
### R06.15 径向源配对和端点Green项

**输出：** 恢复真实L_j的dr Green核、B_j逆Cj⁻⁴界及两种入口impedance，证明自然端点Green pairing消失。

**局部依赖：** R06.01, R06.08, R06.11, R06.14。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–700 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 明确g²w/r² dr密度与非齐次因子
- 初始阻力edge的impedance符号独立检查

**本轮核对：** 冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。

**未完成内容：**
- 恢复真实L_j的dr Green核、B_j逆Cj⁻⁴界及两种入口impedance，证明自然端点Green pairing消失。
- 尚需满足：明确g²w/r² dr密度与非齐次因子
- 尚需满足：初始阻力edge的impedance符号独立检查

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。
- acceptance.02 [uncovered]：冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。

<a id="r06-16"></a>
### R06.16 组合并验收深尾连续算子逆与唯一衰减线

**输出：** 深尾条件下，A_p=-p⁻¹(p∂x)'的Dirichlet/Friedrichs实现具有文中逆界，端点恰有一条自然L²齐次解线；其衰减、原半径平坦性、Green核衰减和参数连续性成立。

**局部依赖：** R06.01, R06.02, R06.03, R06.04, R06.05, R06.06, R06.07, R06.08, R06.09, R06.10, R06.11, R06.12, R06.13, R06.14, R06.15。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 120–300 行。组合已证明输出和核对原合同，数学重负担已列为前置子任务。

**验收条件：**

- 逐项实例化此前子任务并导出原节点完整结论
- 连续与离散form domain对应
- 有限截断极限确实实现目标连续算子
- 唯一解线、平坦性及product-topology连续性分别证明
- 左端x=−log r时显式处理mass/resistance顺序的一格索引移动及源Jacobian

**本轮核对：** 冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。

**未完成内容：**
- 深尾条件下，A_p=-p⁻¹(p∂x)'的Dirichlet/Friedrichs实现具有文中逆界，端点恰有一条自然L²齐次解线；其衰减、原半径平坦性、Green核衰减和参数连续性成立。
- 尚需满足：逐项实例化此前子任务并导出原节点完整结论
- 尚需满足：连续与离散form domain对应
- 尚需满足：有限截断极限确实实现目标连续算子
- 尚需满足：唯一解线、平坦性及product-topology连续性分别证明
- 尚需满足：左端x=−log r时显式处理mass/resistance顺序的一格索引移动及源Jacobian

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。
- acceptance.02 [uncovered]：冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。
- acceptance.03 [uncovered]：冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。
- acceptance.04 [uncovered]：冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。
- acceptance.05 [uncovered]：冻结源码没有真实deep-tail密度/edge/节点系统及连续Dirichlet–Friedrichs实现；中央Hermite闭图不替代尾部闭域。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：深尾条件下，A_p=-p⁻¹(p∂x)'的Dirichlet/Friedrichs实现具有文中逆界，端点恰有一条自然L²齐次解线；其衰减、原半径平坦性、Green核衰减和参数连续性成立。 | R06.16（组合全部子任务） |
| acceptance.01：连续与离散form domain对应 | R06.05, R06.06, R06.07, R06.08 |
| acceptance.02：有限截断极限确实实现目标连续算子 | R06.07, R06.08, R06.09 |
| acceptance.03：唯一解线、平坦性及product-topology连续性分别证明 | R06.10, R06.11, R06.12, R06.13 |
| acceptance.04：左端x=−log r时显式处理mass/resistance顺序的一格索引移动及源Jacobian | R06.01, R06.04, R06.15 |

<a id="r07"></a>
## R07 过渡区与所有频率同时选高

**原节点完整目标：** 每个偶正频率具有唯一过渡单元；存在同一个高度序列(σ_n)，使所有频率的incoming line与自然端线具有文中定量角度下界。

**原上游里程碑：** R04, R05, R06

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [05-flat-end-chain.tex:507–667](../../paper/flexible-surface-rewrite/05-flat-end-chain.tex#L507)

<a id="r07-01"></a>
### R07.01 所有偶频的唯一band划分

**输出：** 证明H_n单调趋无穷，含首band的I_n对全部偶j≥2恰好分区，下一单元已deep且更早单元有大正cap action。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 250–600 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 没有遗漏中间频段
- 频率区间边界等号归属唯一

**本轮核对：** 冻结源码没有真实频带、辅助cone、height-ratio坏集或全频同时选高的证明。

**未完成内容：**
- 证明H_n单调趋无穷，含首band的I_n对全部偶j≥2恰好分区，下一单元已deep且更早单元有大正cap action。
- 尚需满足：没有遗漏中间频段
- 尚需满足：频率区间边界等号归属唯一

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有真实频带、辅助cone、height-ratio坏集或全频同时选高的证明。
- acceptance.02 [uncovered]：冻结源码没有真实频带、辅助cone、height-ratio坏集或全频同时选高的证明。

<a id="r07-02"></a>
### R07.02 辅助正cone的实际incoming线

**输出：** 构造真实w=cr cone与正插值，证明r^±j incoming线、Dirichlet逆界及首band符号。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 250–600 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- cone幅度选择先于σ_N
- 最终只保留有限cone片段

**本轮核对：** 冻结源码没有真实频带、辅助cone、height-ratio坏集或全频同时选高的证明。

**未完成内容：**
- 构造真实w=cr cone与正插值，证明r^±j incoming线、Dirichlet逆界及首band符号。
- 尚需满足：cone幅度选择先于σ_N
- 尚需满足：最终只保留有限cone片段

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有真实频带、辅助cone、height-ratio坏集或全频同时选高的证明。
- acceptance.02 [uncovered]：冻结源码没有真实频带、辅助cone、height-ratio坏集或全频同时选高的证明。

<a id="r07-03"></a>
### R07.03 incoming斜率统一区间

**输出：** 由正cap上的实际ODE比较证明ζ_j/u∈[-3/2,-1/2]，覆盖左右方向和首band。

**局部依赖：** R07.01, R07.02。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–700 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- normalization u=1合法且非零
- 常数统一于其它高度参数

**本轮核对：** 冻结源码没有真实频带、辅助cone、height-ratio坏集或全频同时选高的证明。

**未完成内容：**
- 由正cap上的实际ODE比较证明ζ_j/u∈[-3/2,-1/2]，覆盖左右方向和首band。
- 尚需满足：normalization u=1合法且非零
- 尚需满足：常数统一于其它高度参数

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有真实频带、辅助cone、height-ratio坏集或全频同时选高的证明。
- acceptance.02 [uncovered]：冻结源码没有真实频带、辅助cone、height-ratio坏集或全频同时选高的证明。

<a id="r07-04"></a>
### R07.04 短连接真实传递误差

**输出：** 采用Y=(u,wζ_j/W_in)消去w′/w，证明实际基本解矩阵与恒等阵相差o(e^-n²)。

**局部依赖：** R07.01, R07.03。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–700 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 使用真实Volterra级数及矩阵范数
- 不以大导数上界破坏短连接预算

**本轮核对：** 冻结源码没有真实频带、辅助cone、height-ratio坏集或全频同时选高的证明。

**未完成内容：**
- 采用Y=(u,wζ_j/W_in)消去w′/w，证明实际基本解矩阵与恒等阵相差o(e^-n²)。
- 尚需满足：使用真实Volterra级数及矩阵范数
- 尚需满足：不以大导数上界破坏短连接预算

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有真实频带、辅助cone、height-ratio坏集或全频同时选高的证明。
- acceptance.02 [uncovered]：冻结源码没有真实频带、辅助cone、height-ratio坏集或全频同时选高的证明。

<a id="r07-05"></a>
### R07.05 单坐标坏角集合测度

**输出：** 证明B(σ)=(B₁,σΞ_nB₂)的坏角集合长度≤Cδ_n，并把传递误差加入真实incoming角。

**局部依赖：** R07.03, R07.04。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–700 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- B₁=0单独处理
- 常数独立于其余全部σ

**本轮核对：** 冻结源码没有真实频带、辅助cone、height-ratio坏集或全频同时选高的证明。

**未完成内容：**
- 证明B(σ)=(B₁,σΞ_nB₂)的坏角集合长度≤Cδ_n，并把传递误差加入真实incoming角。
- 尚需满足：B₁=0单独处理
- 尚需满足：常数独立于其余全部σ

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有真实频带、辅助cone、height-ratio坏集或全频同时选高的证明。
- acceptance.02 [uncovered]：冻结源码没有真实频带、辅助cone、height-ratio坏集或全频同时选高的证明。

<a id="r07-06"></a>
### R07.06 有限立方体同时选高

**输出：** 在任意有限band集合上用Fubini、可测性和并集界证明存在同时满足全部好角条件的σ。

**局部依赖：** R07.01, R07.05。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 250–650 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 实际证明ΣC#I_nδ_n<1/2
- 未来ratios固定后估计仍统一

**本轮核对：** 冻结源码没有真实频带、辅助cone、height-ratio坏集或全频同时选高的证明。

**未完成内容：**
- 在任意有限band集合上用Fubini、可测性和并集界证明存在同时满足全部好角条件的σ。
- 尚需满足：实际证明ΣC#I_nδ_n<1/2
- 尚需满足：未来ratios固定后估计仍统一

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有真实频带、辅助cone、height-ratio坏集或全频同时选高的证明。
- acceptance.02 [uncovered]：冻结源码没有真实频带、辅助cone、height-ratio坏集或全频同时选高的证明。

<a id="r07-07"></a>
### R07.07 无限好条件的闭性

**输出：** 将固定频率角度写成prefix传递与自然端线的连续函数，证明good set在紧乘积中闭。

**局部依赖：** R07.04, R07.05。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 250–600 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 自然线使用R06已证product连续性
- 不能只取每频率不同的几何

**本轮核对：** 冻结源码没有真实频带、辅助cone、height-ratio坏集或全频同时选高的证明。

**未完成内容：**
- 将固定频率角度写成prefix传递与自然端线的连续函数，证明good set在紧乘积中闭。
- 尚需满足：自然线使用R06已证product连续性
- 尚需满足：不能只取每频率不同的几何

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有真实频带、辅助cone、height-ratio坏集或全频同时选高的证明。
- acceptance.02 [uncovered]：冻结源码没有真实频带、辅助cone、height-ratio坏集或全频同时选高的证明。

<a id="r07-08"></a>
### R07.08 同一高度序列覆盖全部频率

**输出：** 由有限维可满足性和乘积紧性得到一个σ_n序列满足所有偶正频率，并为两端分别选择再配成同一几何。

**局部依赖：** R07.06, R07.07。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 250–650 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 量词严格为∃σ∀j
- 极限保持每个定量δ_n下界

**本轮核对：** 冻结源码没有真实频带、辅助cone、height-ratio坏集或全频同时选高的证明。

**未完成内容：**
- 由有限维可满足性和乘积紧性得到一个σ_n序列满足所有偶正频率，并为两端分别选择再配成同一几何。
- 尚需满足：量词严格为∃σ∀j
- 尚需满足：极限保持每个定量δ_n下界

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有真实频带、辅助cone、height-ratio坏集或全频同时选高的证明。
- acceptance.02 [uncovered]：冻结源码没有真实频带、辅助cone、height-ratio坏集或全频同时选高的证明。

<a id="r07-09"></a>
### R07.09 组合并验收过渡区与所有频率同时选高

**输出：** 每个偶正频率具有唯一过渡单元；存在同一个高度序列(σ_n)，使所有频率的incoming line与自然端线具有文中定量角度下界。

**局部依赖：** R07.01, R07.02, R07.03, R07.04, R07.05, R07.06, R07.07, R07.08。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 120–300 行。组合已证明输出和核对原合同，数学重负担已列为前置子任务。

**验收条件：**

- 逐项实例化此前子任务并导出原节点完整结论
- 量词为∃(σ_n)∀j，而非∀j∃(σ_n)
- 无限条件的闭性与线连续性
- 核验过渡/深尾频率区域确实穷尽全部偶正频率

**本轮核对：** 冻结源码没有真实频带、辅助cone、height-ratio坏集或全频同时选高的证明。

**未完成内容：**
- 每个偶正频率具有唯一过渡单元；存在同一个高度序列(σ_n)，使所有频率的incoming line与自然端线具有文中定量角度下界。
- 尚需满足：逐项实例化此前子任务并导出原节点完整结论
- 尚需满足：量词为∃(σ_n)∀j，而非∀j∃(σ_n)
- 尚需满足：无限条件的闭性与线连续性
- 尚需满足：核验过渡/深尾频率区域确实穷尽全部偶正频率

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有真实频带、辅助cone、height-ratio坏集或全频同时选高的证明。
- acceptance.02 [uncovered]：冻结源码没有真实频带、辅助cone、height-ratio坏集或全频同时选高的证明。
- acceptance.03 [uncovered]：冻结源码没有真实频带、辅助cone、height-ratio坏集或全频同时选高的证明。
- acceptance.04 [uncovered]：冻结源码没有真实频带、辅助cone、height-ratio坏集或全频同时选高的证明。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：每个偶正频率具有唯一过渡单元；存在同一个高度序列(σ_n)，使所有频率的incoming line与自然端线具有文中定量角度下界。 | R07.09（组合全部子任务） |
| acceptance.01：量词为∃(σ_n)∀j，而非∀j∃(σ_n) | R07.06, R07.07, R07.08 |
| acceptance.02：无限条件的闭性与线连续性 | R07.07, R07.08 |
| acceptance.03：核验过渡/深尾频率区域确实穷尽全部偶正频率 | R07.01, R07.02, R07.03 |

<a id="r08"></a>
## R08 保留二模的中央目标连接

**原节点完整目标：** 构造把两个已选尾和中央模型连起来的光滑径向轮廓及非零全局二模平坦解φ*，保留可调cut/cone-head长度并不改变负区旅行角。

**原上游里程碑：** R03, R07

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [06-global-reference-inverse.tex:50–98](../../paper/flexible-surface-rewrite/06-global-reference-inverse.tex#L50)

<a id="r08-01"></a>
### R08.01 两条自然尾线的统一归一化

**输出：** 从已选左右尾自然解选择非零归一化代表，固定真实入口值/flux以及允许的cut参数。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 左右方向符号一致
- 不更改已选高度序列和旅行角

**本轮核对：** 冻结源码没有已选自然双尾与中央保核连接的实际构造；明确中央二模解不等于全局平坦φ*。

**未完成内容：**
- 从已选左右尾自然解选择非零归一化代表，固定真实入口值/flux以及允许的cut参数。
- 尚需满足：左右方向符号一致
- 尚需满足：不更改已选高度序列和旅行角

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有已选自然双尾与中央保核连接的实际构造；明确中央二模解不等于全局平坦φ*。
- acceptance.02 [uncovered]：冻结源码没有已选自然双尾与中央保核连接的实际构造；明确中央二模解不等于全局平坦φ*。

<a id="r08-02"></a>
### R08.02 中央二模解的cut状态

**输出：** 在实际中央模型两个远cut提取二模核解及对数斜率，证明可连接的严格不等式。

**局部依赖：** R08.01。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 250–600 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 沿真实半径逆计算
- cut仍可增大而未提前冻结

**本轮核对：** 已构造实际中央二模解，但没有两个可调远cut上的完整state/log斜率和连接不等式。

**源码证据 `ContinuousFlexibility/Radial/CentralModel.lean`：** `ContinuousFlexibility.Radial.centralKernelHeight`, `ContinuousFlexibility.Radial.centralKernelHeight_pos`, `ContinuousFlexibility.Radial.centralKernelHeight_pullback`, `ContinuousFlexibility.Radial.centralKernelHeight_liouville_pullback`, `ContinuousFlexibility.Radial.radialJacobi_centralKernel`

中央真实非零二模解和pullback状态已有；尚未形成远cut的可连接log斜率不等式。

**未完成内容：**
- 给出两个可调远cut的值/flux/log斜率及严格可连接估计。
- 证明增大cut参数仍满足同一构造接口。

**逐条验收：**
- acceptance.01 [partial]：二模解通过实际半径逆定义并满足真实径向方程；远cut log斜率仍缺。
- acceptance.02 [uncovered]：没有带未冻结cut参数及其允许范围的输出定理。

<a id="r08-03"></a>
### R08.03 保核正连接的实际构造

**输出：** 按二模解对数斜率设计正连接w并构造非零φ，证明L₂φ=0及两端全jets匹配。

**局部依赖：** R08.01, R08.02。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 350–750 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- φ不通过除零的入口值归一化
- 连接内w>0且无新增负区

**本轮核对：** 冻结源码没有已选自然双尾与中央保核连接的实际构造；明确中央二模解不等于全局平坦φ*。

**未完成内容：**
- 按二模解对数斜率设计正连接w并构造非零φ，证明L₂φ=0及两端全jets匹配。
- 尚需满足：φ不通过除零的入口值归一化
- 尚需满足：连接内w>0且无新增负区

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有已选自然双尾与中央保核连接的实际构造；明确中央二模解不等于全局平坦φ*。
- acceptance.02 [uncovered]：冻结源码没有已选自然双尾与中央保核连接的实际构造；明确中央二模解不等于全局平坦φ*。

<a id="r08-04"></a>
### R08.04 中央和双尾的全局光滑拼合

**输出：** 把中央、两条连接和尾拼为同一w*及φ*，证明内部光滑、两端平坦、φ*非零。

**局部依赖：** R08.03。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–700 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 无限端点平坦性继承真实估计
- 接口值和flux精确匹配

**本轮核对：** 冻结源码没有已选自然双尾与中央保核连接的实际构造；明确中央二模解不等于全局平坦φ*。

**未完成内容：**
- 把中央、两条连接和尾拼为同一w*及φ*，证明内部光滑、两端平坦、φ*非零。
- 尚需满足：无限端点平坦性继承真实估计
- 尚需满足：接口值和flux精确匹配

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有已选自然双尾与中央保核连接的实际构造；明确中央二模解不等于全局平坦φ*。
- acceptance.02 [uncovered]：冻结源码没有已选自然双尾与中央保核连接的实际构造；明确中央二模解不等于全局平坦φ*。

<a id="r08-05"></a>
### R08.05 旅行角与已选角的保持

**输出：** 证明新增正连接不改变每个原负区旅行角，人工incoming的先定方向保持不变，变化仅进入后续Eb误差。

**局部依赖：** R08.03, R08.04。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–550 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 不宣称任意中央改动自动保持全局角度
- 明确R10应控制的Eb项

**本轮核对：** 冻结源码没有已选自然双尾与中央保核连接的实际构造；明确中央二模解不等于全局平坦φ*。

**未完成内容：**
- 证明新增正连接不改变每个原负区旅行角，人工incoming的先定方向保持不变，变化仅进入后续Eb误差。
- 尚需满足：不宣称任意中央改动自动保持全局角度
- 尚需满足：明确R10应控制的Eb项

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有已选自然双尾与中央保核连接的实际构造；明确中央二模解不等于全局平坦φ*。
- acceptance.02 [uncovered]：冻结源码没有已选自然双尾与中央保核连接的实际构造；明确中央二模解不等于全局平坦φ*。

<a id="r08-06"></a>
### R08.06 cut和head参数的依赖登记

**输出：** 建立带cut/cone-head参数的同一构造族和允许冻结次序，证明后续只调未冻结参数。

**局部依赖：** R08.02, R08.04, R08.05。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 180–450 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 已有σ和M₀不能因输出阶数重选
- 给出供R10/R11调用的参数范围

**本轮核对：** 冻结源码没有已选自然双尾与中央保核连接的实际构造；明确中央二模解不等于全局平坦φ*。

**未完成内容：**
- 建立带cut/cone-head参数的同一构造族和允许冻结次序，证明后续只调未冻结参数。
- 尚需满足：已有σ和M₀不能因输出阶数重选
- 尚需满足：给出供R10/R11调用的参数范围

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有已选自然双尾与中央保核连接的实际构造；明确中央二模解不等于全局平坦φ*。
- acceptance.02 [uncovered]：冻结源码没有已选自然双尾与中央保核连接的实际构造；明确中央二模解不等于全局平坦φ*。

<a id="r08-07"></a>
### R08.07 组合并验收保留二模的中央目标连接

**输出：** 构造把两个已选尾和中央模型连起来的光滑径向轮廓及非零全局二模平坦解φ*，保留可调cut/cone-head长度并不改变负区旅行角。

**局部依赖：** R08.01, R08.02, R08.03, R08.04, R08.05, R08.06。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 120–300 行。组合已证明输出和核对原合同，数学重负担已列为前置子任务。

**验收条件：**

- 逐项实例化此前子任务并导出原节点完整结论
- φ*是真实非零解
- 新增连接不破坏已选角度
- 后续不得暗中重选已冻结的几何

**本轮核对：** 冻结源码没有已选自然双尾与中央保核连接的实际构造；明确中央二模解不等于全局平坦φ*。

**未完成内容：**
- 构造把两个已选尾和中央模型连起来的光滑径向轮廓及非零全局二模平坦解φ*，保留可调cut/cone-head长度并不改变负区旅行角。
- 尚需满足：逐项实例化此前子任务并导出原节点完整结论
- 尚需满足：φ*是真实非零解
- 尚需满足：新增连接不破坏已选角度
- 尚需满足：后续不得暗中重选已冻结的几何

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有已选自然双尾与中央保核连接的实际构造；明确中央二模解不等于全局平坦φ*。
- acceptance.02 [uncovered]：冻结源码没有已选自然双尾与中央保核连接的实际构造；明确中央二模解不等于全局平坦φ*。
- acceptance.03 [uncovered]：冻结源码没有已选自然双尾与中央保核连接的实际构造；明确中央二模解不等于全局平坦φ*。
- acceptance.04 [uncovered]：冻结源码没有已选自然双尾与中央保核连接的实际构造；明确中央二模解不等于全局平坦φ*。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：构造把两个已选尾和中央模型连起来的光滑径向轮廓及非零全局二模平坦解φ*，保留可调cut/cone-head长度并不改变负区旅行角。 | R08.07（组合全部子任务） |
| acceptance.01：φ*是真实非零解 | R08.01, R08.02, R08.03, R08.04 |
| acceptance.02：新增连接不破坏已选角度 | R08.03, R08.05 |
| acceptance.03：后续不得暗中重选已冻结的几何 | R08.01, R08.02, R08.05, R08.06 |

<a id="r09"></a>
## R09 正buffer压缩与Poisson边界矩阵

**原节点完整目标：** 从full-model或bordered inverse及正势下界，得到保留区Dirichlet逆、Poisson lift及boundary derivative矩阵的实际界和正定性。

**原上游里程碑：** R03, R04

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [06-global-reference-inverse.tex:100–229](../../paper/flexible-surface-rewrite/06-global-reference-inverse.tex#L100)

<a id="r09-01"></a>
### R09.01 正buffer的单位边界能量

**输出：** 在有真实闭实现的正势区域构造自然/Dirichlet单位边界解，证明α_in,α_out≈m。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–700 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 自然外端条件明确
- 使用真实能量下界及试函数上界

**本轮核对：** 冻结源码没有正buffer的实际边界能量、点源Green列、Dirichlet压缩或Poisson/边界矩阵证明。

**未完成内容：**
- 在有真实闭实现的正势区域构造自然/Dirichlet单位边界解，证明α_in,α_out≈m。
- 尚需满足：自然外端条件明确
- 尚需满足：使用真实能量下界及试函数上界

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有正buffer的实际边界能量、点源Green列、Dirichlet压缩或Poisson/边界矩阵证明。
- acceptance.02 [uncovered]：冻结源码没有正buffer的实际边界能量、点源Green列、Dirichlet压缩或Poisson/边界矩阵证明。

<a id="r09-02"></a>
### R09.02 cut附近点源Green近似列

**输出：** 构造带cutoff的局部Green列K_i，证明其分布像为δ_ci+f_i及L²残差界。

**局部依赖：** R09.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 350–750 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 点源明确放在分布空间
- f_i是真正L²源且避开scalar border support

**本轮核对：** 冻结源码没有正buffer的实际边界能量、点源Green列、Dirichlet压缩或Poisson/边界矩阵证明。

**未完成内容：**
- 构造带cutoff的局部Green列K_i，证明其分布像为δ_ci+f_i及L²残差界。
- 尚需满足：点源明确放在分布空间
- 尚需满足：f_i是真正L²源且避开scalar border support

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有正buffer的实际边界能量、点源Green列、Dirichlet压缩或Poisson/边界矩阵证明。
- acceptance.02 [uncovered]：冻结源码没有正buffer的实际边界能量、点源Green列、Dirichlet压缩或Poisson/边界矩阵证明。

<a id="r09-03"></a>
### R09.03 精确Green列与cut矩阵

**输出：** 以全模型逆纠正f_i，证明Γ_ik=g_k(c_i)及双重衰减误差D^½ΓD^½=I+E。

**局部依赖：** R09.02。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–700 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 点值trace由正buffer估计获得
- i,k方向各贡献一个衰减因子

**本轮核对：** 冻结源码没有正buffer的实际边界能量、点源Green列、Dirichlet压缩或Poisson/边界矩阵证明。

**未完成内容：**
- 以全模型逆纠正f_i，证明Γ_ik=g_k(c_i)及双重衰减误差D^½ΓD^½=I+E。
- 尚需满足：点值trace由正buffer估计获得
- 尚需满足：i,k方向各贡献一个衰减因子

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有正buffer的实际边界能量、点源Green列、Dirichlet压缩或Poisson/边界矩阵证明。
- acceptance.02 [uncovered]：冻结源码没有正buffer的实际边界能量、点源Green列、Dirichlet压缩或Poisson/边界矩阵证明。

<a id="r09-04"></a>
### R09.04 保留区Dirichlet逆公式

**输出：** 证明切割矩阵Γ可逆及H_D⁻¹=RH⁻¹ι-g_IΓ⁻¹g_I*，并证明不存在隐藏Dirichlet核。

**局部依赖：** R09.03。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–700 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 不能由形式Schur公式跳过域成员
- 保留scalar coordinate及row

**本轮核对：** 冻结源码没有正buffer的实际边界能量、点源Green列、Dirichlet压缩或Poisson/边界矩阵证明。

**未完成内容：**
- 证明切割矩阵Γ可逆及H_D⁻¹=RH⁻¹ι-g_IΓ⁻¹g_I*，并证明不存在隐藏Dirichlet核。
- 尚需满足：不能由形式Schur公式跳过域成员
- 尚需满足：保留scalar coordinate及row

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有正buffer的实际边界能量、点源Green列、Dirichlet压缩或Poisson/边界矩阵证明。
- acceptance.02 [uncovered]：冻结源码没有正buffer的实际边界能量、点源Green列、Dirichlet压缩或Poisson/边界矩阵证明。

<a id="r09-05"></a>
### R09.05 Poisson lift的真实界

**输出：** 由g_IΓ⁻¹构造row-zero Poisson map，证明真实边界值、齐次方程和归一化L²界。

**局部依赖：** R09.03, R09.04。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 250–600 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 按D^-½作边界规范化
- 边框row确实为零

**本轮核对：** 冻结源码没有正buffer的实际边界能量、点源Green列、Dirichlet压缩或Poisson/边界矩阵证明。

**未完成内容：**
- 由g_IΓ⁻¹构造row-zero Poisson map，证明真实边界值、齐次方程和归一化L²界。
- 尚需满足：按D^-½作边界规范化
- 尚需满足：边框row确实为零

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有正buffer的实际边界能量、点源Green列、Dirichlet压缩或Poisson/边界矩阵证明。
- acceptance.02 [uncovered]：冻结源码没有正buffer的实际边界能量、点源Green列、Dirichlet压缩或Poisson/边界矩阵证明。

<a id="r09-06"></a>
### R09.06 边界导数矩阵和正定性

**输出：** 证明Λ=Γ⁻¹-diag α_out，推导归一化误差和Λ正定。

**局部依赖：** R09.01, R09.03, R09.04, R09.05。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 250–650 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- outward导数符号精确
- 紧支撑对称border在Green恒等式中无遗漏项

**本轮核对：** 冻结源码没有正buffer的实际边界能量、点源Green列、Dirichlet压缩或Poisson/边界矩阵证明。

**未完成内容：**
- 证明Λ=Γ⁻¹-diag α_out，推导归一化误差和Λ正定。
- 尚需满足：outward导数符号精确
- 尚需满足：紧支撑对称border在Green恒等式中无遗漏项

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有正buffer的实际边界能量、点源Green列、Dirichlet压缩或Poisson/边界矩阵证明。
- acceptance.02 [uncovered]：冻结源码没有正buffer的实际边界能量、点源Green列、Dirichlet压缩或Poisson/边界矩阵证明。

<a id="r09-07"></a>
### R09.07 径向norm和flux运输

**输出：** 把buffer结论运输回同一径向模型，保留Liouville中央gauge附加impedance并证明幅度λ消去。

**局部依赖：** R09.04, R09.05, R09.06。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 250–650 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- Morse与中央分别实例化
- 中央λa_c diag(ε_iP_i)项不得丢弃

**本轮核对：** Liouville norm/flux基础已证；实际buffer结论、中央gauge边界矩阵及λ归一化还未组合。

**源码证据 `ContinuousFlexibility/Radial/Liouville.lean`：** `ContinuousFlexibility.Radial.liouville_flux_at`, `ContinuousFlexibility.Radial.liouville_hilbert_density`

真实flux和谱norm密度运输的基本恒等式已有。

**源码证据 `ContinuousFlexibility/Radial/RadiusChange.lean`：** `ContinuousFlexibility.Radial.liouville_hilbert_integral`

有限区间真实Hilbert积分换元已有；尚未运输实际buffer boundary matrix。

**未完成内容：**
- 实际buffer Dirichlet/Poisson/derivative结论的径向运输。
- 中央附加gauge impedance与绝对幅度λ消去的矩阵估计。

**逐条验收：**
- acceptance.01 [partial]：中央/Morse通用微分换元可用，但没有两个实际buffer模型的完整实例化。
- acceptance.02 [uncovered]：未发现中央λa_c diag(ε_iP_i)边界矩阵定理。

<a id="r09-08"></a>
### R09.08 组合并验收正buffer压缩与Poisson边界矩阵

**输出：** 从full-model或bordered inverse及正势下界，得到保留区Dirichlet逆、Poisson lift及boundary derivative矩阵的实际界和正定性。

**局部依赖：** R09.01, R09.02, R09.03, R09.04, R09.05, R09.06, R09.07。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 120–300 行。组合已证明输出和核对原合同，数学重负担已列为前置子任务。

**验收条件：**

- 逐项实例化此前子任务并导出原节点完整结论
- 标量边框support远离cut
- 点源不能当作普通L²源
- 得到可用于拼接的边界配对和符号

**本轮核对：** 冻结源码没有正buffer的实际边界能量、点源Green列、Dirichlet压缩或Poisson/边界矩阵证明。

**未完成内容：**
- 从full-model或bordered inverse及正势下界，得到保留区Dirichlet逆、Poisson lift及boundary derivative矩阵的实际界和正定性。
- 尚需满足：逐项实例化此前子任务并导出原节点完整结论
- 尚需满足：标量边框support远离cut
- 尚需满足：点源不能当作普通L²源
- 尚需满足：得到可用于拼接的边界配对和符号

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有正buffer的实际边界能量、点源Green列、Dirichlet压缩或Poisson/边界矩阵证明。
- acceptance.02 [uncovered]：冻结源码没有正buffer的实际边界能量、点源Green列、Dirichlet压缩或Poisson/边界矩阵证明。
- acceptance.03 [uncovered]：冻结源码没有正buffer的实际边界能量、点源Green列、Dirichlet压缩或Poisson/边界矩阵证明。
- acceptance.04 [uncovered]：冻结源码没有正buffer的实际边界能量、点源Green列、Dirichlet压缩或Poisson/边界矩阵证明。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：从full-model或bordered inverse及正势下界，得到保留区Dirichlet逆、Poisson lift及boundary derivative矩阵的实际界和正定性。 | R09.08（组合全部子任务） |
| acceptance.01：标量边框support远离cut | R09.02, R09.04, R09.05, R09.06 |
| acceptance.02：点源不能当作普通L²源 | R09.02, R09.03, R09.04 |
| acceptance.03：得到可用于拼接的边界配对和符号 | R09.01, R09.05, R09.06, R09.07 |

<a id="r10"></a>
## R10 全局匹配Green逆

**原节点完整目标：** 保留完整正interface能量构造内部逆，构造不除入口高度的外逆，证明最终2×2匹配矩阵可逆，得到真实全局matched Green逆和对称block公式。

**原上游里程碑：** R06, R07, R08, R09

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [06-global-reference-inverse.tex:231–590](../../paper/flexible-surface-rewrite/06-global-reference-inverse.tex#L231)

<a id="r10-01"></a>
### R10.01 正interface骨架能量

**输出：** 组装所有保留区边界数据与正connector能量，证明完整骨架S₀及其归一化正定性。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–700 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 保留跨interface全部正能量
- 二模scalar border贯穿

**本轮核对：** 冻结源码没有构造全局径向参考的内部/外部matched Green逆、interface骨架或2×2匹配矩阵。

**未完成内容：**
- 组装所有保留区边界数据与正connector能量，证明完整骨架S₀及其归一化正定性。
- 尚需满足：保留跨interface全部正能量
- 尚需满足：二模scalar border贯穿

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有构造全局径向参考的内部/外部matched Green逆、interface骨架或2×2匹配矩阵。
- acceptance.02 [uncovered]：冻结源码没有构造全局径向参考的内部/外部matched Green逆、interface骨架或2×2匹配矩阵。

<a id="r10-02"></a>
### R10.02 内部局部误差的全频压制

**输出：** 证明早期单元、中央远cut和首cone-head误差在任意高频下统一小，登记M₀→C*→N→cut/head次序。

**局部依赖：** R10.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–700 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 覆盖j远高于局部threshold的频率
- 几何选择不依赖输出微分阶数

**本轮核对：** 冻结源码没有构造全局径向参考的内部/外部matched Green逆、interface骨架或2×2匹配矩阵。

**未完成内容：**
- 证明早期单元、中央远cut和首cone-head误差在任意高频下统一小，登记M₀→C*→N→cut/head次序。
- 尚需满足：覆盖j远高于局部threshold的频率
- 尚需满足：几何选择不依赖输出微分阶数

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有构造全局径向参考的内部/外部matched Green逆、interface骨架或2×2匹配矩阵。
- acceptance.02 [uncovered]：冻结源码没有构造全局径向参考的内部/外部matched Green逆、interface骨架或2×2匹配矩阵。

<a id="r10-03"></a>
### R10.03 真实内部逆与Poisson插值

**输出：** 反演同一骨架小扰动并证明内部G_h、T_h及加权源/边界估计，包含scalar row。

**局部依赖：** R10.01, R10.02。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 350–750 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 先证同空间有界小扰动
- 频率、截断长度的统一界实际给出

**本轮核对：** 冻结源码没有构造全局径向参考的内部/外部matched Green逆、interface骨架或2×2匹配矩阵。

**未完成内容：**
- 反演同一骨架小扰动并证明内部G_h、T_h及加权源/边界估计，包含scalar row。
- 尚需满足：先证同空间有界小扰动
- 尚需满足：频率、截断长度的统一界实际给出

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有构造全局径向参考的内部/外部matched Green逆、interface骨架或2×2匹配矩阵。
- acceptance.02 [uncovered]：冻结源码没有构造全局径向参考的内部/外部matched Green逆、interface骨架或2×2匹配矩阵。

<a id="r10-04"></a>
### R10.04 过渡核心基本解和外端列

**输出：** 在过渡单元构造真实基本解及接自然端线的V，证明归一化状态和有限核心增长界。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–700 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 允许入口高度分量为零
- 从同一已选自然线取得列

**本轮核对：** 冻结源码没有构造全局径向参考的内部/外部matched Green逆、interface骨架或2×2匹配矩阵。

**未完成内容：**
- 在过渡单元构造真实基本解及接自然端线的V，证明归一化状态和有限核心增长界。
- 尚需满足：允许入口高度分量为零
- 尚需满足：从同一已选自然线取得列

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有构造全局径向参考的内部/外部matched Green逆、interface骨架或2×2匹配矩阵。
- acceptance.02 [uncovered]：冻结源码没有构造全局径向参考的内部/外部matched Green逆、interface骨架或2×2匹配矩阵。

<a id="r10-05"></a>
### R10.05 外部非齐次Green逆

**输出：** 由规范化状态构造外逆R_o，证明真实方程、自然端条件和包含deep块的局域范数界。

**局部依赖：** R10.04。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 350–750 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 核的λ^-1由实际mass/Poisson范数抵消
- 交叉block各自估计

**本轮核对：** 冻结源码没有构造全局径向参考的内部/外部matched Green逆、interface骨架或2×2匹配矩阵。

**未完成内容：**
- 由规范化状态构造外逆R_o，证明真实方程、自然端条件和包含deep块的局域范数界。
- 尚需满足：核的λ^-1由实际mass/Poisson范数抵消
- 尚需满足：交叉block各自估计

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有构造全局径向参考的内部/外部matched Green逆、interface骨架或2×2匹配矩阵。
- acceptance.02 [uncovered]：冻结源码没有构造全局径向参考的内部/外部matched Green逆、interface骨架或2×2匹配矩阵。

<a id="r10-06"></a>
### R10.06 内部截断列及残差衰减

**输出：** 构造近似内部Poisson列L_i和真实F_i=B_hL_i，证明zero row、独立support及前一正cap衰减。

**局部依赖：** R10.02, R10.03。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–700 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 分别留出buffer与cutoff的固定份额
- 残差实际属于Hilbert源空间

**本轮核对：** 冻结源码没有构造全局径向参考的内部/外部matched Green逆、interface骨架或2×2匹配矩阵。

**未完成内容：**
- 构造近似内部Poisson列L_i和真实F_i=B_hL_i，证明zero row、独立support及前一正cap衰减。
- 尚需满足：分别留出buffer与cutoff的固定份额
- 尚需满足：残差实际属于Hilbert源空间

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有构造全局径向参考的内部/外部matched Green逆、interface骨架或2×2匹配矩阵。
- acceptance.02 [uncovered]：冻结源码没有构造全局径向参考的内部/外部matched Green逆、interface骨架或2×2匹配矩阵。

<a id="r10-07"></a>
### R10.07 真实内部导数矩阵的修正

**输出：** 证明P_h=L-G_hF及D_b=Q_h(L,L)-F*G_hF=D₀+E_b，得到每个矩阵元的双衰减界。

**局部依赖：** R10.03, R10.06。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–700 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 完成平方时scalar项不遗漏
- 等式与误差估计分别证明

**本轮核对：** 冻结源码没有构造全局径向参考的内部/外部matched Green逆、interface骨架或2×2匹配矩阵。

**未完成内容：**
- 证明P_h=L-G_hF及D_b=Q_h(L,L)-F*G_hF=D₀+E_b，得到每个矩阵元的双衰减界。
- 尚需满足：完成平方时scalar项不遗漏
- 尚需满足：等式与误差估计分别证明

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有构造全局径向参考的内部/外部matched Green逆、interface骨架或2×2匹配矩阵。
- acceptance.02 [uncovered]：冻结源码没有构造全局径向参考的内部/外部matched Green逆、interface骨架或2×2匹配矩阵。

<a id="r10-08"></a>
### R10.08 两边值匹配的精确矩阵

**输出：** 从真实内部/外部flux恒等式推出K=A(D₀+E_b)-B及全部source列的匹配方程。

**局部依赖：** R10.04, R10.05, R10.07。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 250–600 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 不是只从形式状态猜矩阵
- 左右方向和归一化λ_i明确

**本轮核对：** 冻结源码没有构造全局径向参考的内部/外部matched Green逆、interface骨架或2×2匹配矩阵。

**未完成内容：**
- 从真实内部/外部flux恒等式推出K=A(D₀+E_b)-B及全部source列的匹配方程。
- 尚需满足：不是只从形式状态猜矩阵
- 尚需满足：左右方向和归一化λ_i明确

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有构造全局径向参考的内部/外部matched Green逆、interface骨架或2×2匹配矩阵。
- acceptance.02 [uncovered]：冻结源码没有构造全局径向参考的内部/外部matched Green逆、interface骨架或2×2匹配矩阵。

<a id="r10-09"></a>
### R10.09 选高角到匹配矩阵可逆

**输出：** 证明原选高frame到当前frame条件数有界，|v₁d-v₂|≥cδ_n，再用δ_n^-1||E_b||小证明K逆界。

**局部依赖：** R10.02, R10.07, R10.08。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–700 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- v₁=0仍合法
- 首band用已保留head长度单独压制

**本轮核对：** 冻结源码没有构造全局径向参考的内部/外部matched Green逆、interface骨架或2×2匹配矩阵。

**未完成内容：**
- 证明原选高frame到当前frame条件数有界，|v₁d-v₂|≥cδ_n，再用δ_n^-1||E_b||小证明K逆界。
- 尚需满足：v₁=0仍合法
- 尚需满足：首band用已保留head长度单独压制

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有构造全局径向参考的内部/外部matched Green逆、interface骨架或2×2匹配矩阵。
- acceptance.02 [uncovered]：冻结源码没有构造全局径向参考的内部/外部matched Green逆、interface骨架或2×2匹配矩阵。

<a id="r10-10"></a>
### R10.10 返回固定内部的代价吸收

**输出：** 证明E_n^Cδ_n^-1 exp(C_oτ_n,j-cτ_n-1,j)<1/4及其首band版本。

**局部依赖：** R10.02, R10.06, R10.09。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 250–600 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- C*及N在常数之后选择
- 不能依赖增大输出权来控制固定内部

**本轮核对：** 冻结源码没有构造全局径向参考的内部/外部matched Green逆、interface骨架或2×2匹配矩阵。

**未完成内容：**
- 证明E_n^Cδ_n^-1 exp(C_oτ_n,j-cτ_n-1,j)<1/4及其首band版本。
- 尚需满足：C*及N在常数之后选择
- 尚需满足：不能依赖增大输出权来控制固定内部

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有构造全局径向参考的内部/外部matched Green逆、interface骨架或2×2匹配矩阵。
- acceptance.02 [uncovered]：冻结源码没有构造全局径向参考的内部/外部matched Green逆、interface骨架或2×2匹配矩阵。

<a id="r10-11"></a>
### R10.11 全局对称block公式

**输出：** 证明matched G的完整block表达及中间矩阵对称性，保留辅助二模border和dr源密度运输。

**局部依赖：** R10.03, R10.05, R10.07, R10.08, R10.09, R10.10。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–700 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 实际值/conormal在所有有限interface匹配
- 两条逆恒等式先在光滑有限频源上验证

**本轮核对：** 冻结源码没有构造全局径向参考的内部/外部matched Green逆、interface骨架或2×2匹配矩阵。

**未完成内容：**
- 证明matched G的完整block表达及中间矩阵对称性，保留辅助二模border和dr源密度运输。
- 尚需满足：实际值/conormal在所有有限interface匹配
- 尚需满足：两条逆恒等式先在光滑有限频源上验证

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有构造全局径向参考的内部/外部matched Green逆、interface骨架或2×2匹配矩阵。
- acceptance.02 [uncovered]：冻结源码没有构造全局径向参考的内部/外部matched Green逆、interface骨架或2×2匹配矩阵。

<a id="r10-12"></a>
### R10.12 组合并验收全局匹配Green逆

**输出：** 保留完整正interface能量构造内部逆，构造不除入口高度的外逆，证明最终2×2匹配矩阵可逆，得到真实全局matched Green逆和对称block公式。

**局部依赖：** R10.01, R10.02, R10.03, R10.04, R10.05, R10.06, R10.07, R10.08, R10.09, R10.10, R10.11。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 120–300 行。组合已证明输出和核对原合同，数学重负担已列为前置子任务。

**验收条件：**

- 逐项实例化此前子任务并导出原节点完整结论
- Hilbert测度12w/r² dr与源dr显式转换
- 辅助二模边框贯穿拼接
- 匹配矩阵恒等式与其定量可逆性分开

**本轮核对：** 冻结源码没有构造全局径向参考的内部/外部matched Green逆、interface骨架或2×2匹配矩阵。

**未完成内容：**
- 保留完整正interface能量构造内部逆，构造不除入口高度的外逆，证明最终2×2匹配矩阵可逆，得到真实全局matched Green逆和对称block公式。
- 尚需满足：逐项实例化此前子任务并导出原节点完整结论
- 尚需满足：Hilbert测度12w/r² dr与源dr显式转换
- 尚需满足：辅助二模边框贯穿拼接
- 尚需满足：匹配矩阵恒等式与其定量可逆性分开

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有构造全局径向参考的内部/外部matched Green逆、interface骨架或2×2匹配矩阵。
- acceptance.02 [uncovered]：冻结源码没有构造全局径向参考的内部/外部matched Green逆、interface骨架或2×2匹配矩阵。
- acceptance.03 [uncovered]：冻结源码没有构造全局径向参考的内部/外部matched Green逆、interface骨架或2×2匹配矩阵。
- acceptance.04 [uncovered]：冻结源码没有构造全局径向参考的内部/外部matched Green逆、interface骨架或2×2匹配矩阵。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：保留完整正interface能量构造内部逆，构造不除入口高度的外逆，证明最终2×2匹配矩阵可逆，得到真实全局matched Green逆和对称block公式。 | R10.12（组合全部子任务） |
| acceptance.01：Hilbert测度12w/r² dr与源dr显式转换 | R10.05, R10.08, R10.11 |
| acceptance.02：辅助二模边框贯穿拼接 | R10.01, R10.03, R10.06, R10.07, R10.11 |
| acceptance.03：匹配矩阵恒等式与其定量可逆性分开 | R10.08, R10.09 |

<a id="r11"></a>
## R11 同一几何上的双权全局估计

**原节点完整目标：** 先固定β=3/4和一个ε∈(0,1/4)，在同一几何上对β−ε、β、β+ε获得足够的加权block/Schur逆界和一阶法向估计。

**原上游里程碑：** R05, R10

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [06-global-reference-inverse.tex:570–764](../../paper/flexible-surface-rewrite/06-global-reference-inverse.tex#L570)

<a id="r11-01"></a>
### R11.01 固定β与邻近指数的权

**输出：** 固定β=3/4及0<ε<1/4，构造三指数在同一几何上的source/output weights并证明相邻权比统一界。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–550 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 先冻结M₀和几何再选允许的输出权
- 不能每个γ另造profile

**本轮核对：** 冻结源码没有同一已构造径向几何的三指数weighted block/Schur逆及径向局部恢复估计；通用权函数基础不能替代。

**未完成内容：**
- 固定β=3/4及0<ε<1/4，构造三指数在同一几何上的source/output weights并证明相邻权比统一界。
- 尚需满足：先冻结M₀和几何再选允许的输出权
- 尚需满足：不能每个γ另造profile

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有同一已构造径向几何的三指数weighted block/Schur逆及径向局部恢复估计；通用权函数基础不能替代。
- acceptance.02 [uncovered]：冻结源码没有同一已构造径向几何的三指数weighted block/Schur逆及径向局部恢复估计；通用权函数基础不能替代。

<a id="r11-02"></a>
### R11.02 外部block的精确指数预算

**输出：** 对R_o、外列及leading lifts分别证明加权block指数式，显式吸收source measure与transition index成本。

**局部依赖：** R11.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–700 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 输出索引在过渡区外是使用增大M₁的前提
- 所有邻居索引偏移实际控制

**本轮核对：** 冻结源码没有同一已构造径向几何的三指数weighted block/Schur逆及径向局部恢复估计；通用权函数基础不能替代。

**未完成内容：**
- 对R_o、外列及leading lifts分别证明加权block指数式，显式吸收source measure与transition index成本。
- 尚需满足：输出索引在过渡区外是使用增大M₁的前提
- 尚需满足：所有邻居索引偏移实际控制

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有同一已构造径向几何的三指数weighted block/Schur逆及径向局部恢复估计；通用权函数基础不能替代。
- acceptance.02 [uncovered]：冻结源码没有同一已构造径向几何的三指数weighted block/Schur逆及径向局部恢复估计；通用权函数基础不能替代。

<a id="r11-03"></a>
### R11.03 双索引Schur求和

**输出：** 由q慢变和S_n增量下界证明外部block kernel的统一行列可和界及有界算子。

**局部依赖：** R11.02。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 250–650 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 无限求和由实际Schur估计完成
- 两尾和localizer有界重叠计入常数

**本轮核对：** 冻结源码没有同一已构造径向几何的三指数weighted block/Schur逆及径向局部恢复估计；通用权函数基础不能替代。

**未完成内容：**
- 由q慢变和S_n增量下界证明外部block kernel的统一行列可和界及有界算子。
- 尚需满足：无限求和由实际Schur估计完成
- 尚需满足：两尾和localizer有界重叠计入常数

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有同一已构造径向几何的三指数weighted block/Schur逆及径向局部恢复估计；通用权函数基础不能替代。
- acceptance.02 [uncovered]：冻结源码没有同一已构造径向几何的三指数weighted block/Schur逆及径向局部恢复估计；通用权函数基础不能替代。

<a id="r11-04"></a>
### R11.04 外Poisson列的双符号权界

**输出：** 对同一外列V证明W和W^-1两种权下的平方和界，保留e^{C_oτ_n,j}成本。

**局部依赖：** R11.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 250–650 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 伴随列的权符号实际反转
- 边界两端采用同一band权

**本轮核对：** 冻结源码没有同一已构造径向几何的三指数weighted block/Schur逆及径向局部恢复估计；通用权函数基础不能替代。

**未完成内容：**
- 对同一外列V证明W和W^-1两种权下的平方和界，保留e^{C_oτ_n,j}成本。
- 尚需满足：伴随列的权符号实际反转
- 尚需满足：边界两端采用同一band权

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有同一已构造径向几何的三指数weighted block/Schur逆及径向局部恢复估计；通用权函数基础不能替代。
- acceptance.02 [uncovered]：冻结源码没有同一已构造径向几何的三指数weighted block/Schur逆及径向局部恢复估计；通用权函数基础不能替代。

<a id="r11-05"></a>
### R11.05 返回内部block的有界性

**输出：** 把G_hF、K⁻¹、V*三个实际有界因子组合，以前一cap衰减吸收过渡核心增长。

**局部依赖：** R11.04。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 250–650 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 固定内部输出的控制不依赖改M₁
- 首band用同一固定head长度

**本轮核对：** 冻结源码没有同一已构造径向几何的三指数weighted block/Schur逆及径向局部恢复估计；通用权函数基础不能替代。

**未完成内容：**
- 把G_hF、K⁻¹、V*三个实际有界因子组合，以前一cap衰减吸收过渡核心增长。
- 尚需满足：固定内部输出的控制不依赖改M₁
- 尚需满足：首band用同一固定head长度

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有同一已构造径向几何的三指数weighted block/Schur逆及径向局部恢复估计；通用权函数基础不能替代。
- acceptance.02 [uncovered]：冻结源码没有同一已构造径向几何的三指数weighted block/Schur逆及径向局部恢复估计；通用权函数基础不能替代。

<a id="r11-06"></a>
### R11.06 全部边界修正项的闭合

**输出：** 分别控制转置block、两残差列项和一残差一leading lift项，合并为真实G的全局加权界。

**局部依赖：** R11.03, R11.05。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 250–650 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 转置block使用反号权
- 不得把一个cross block界代替全部校正项

**本轮核对：** 冻结源码没有同一已构造径向几何的三指数weighted block/Schur逆及径向局部恢复估计；通用权函数基础不能替代。

**未完成内容：**
- 分别控制转置block、两残差列项和一残差一leading lift项，合并为真实G的全局加权界。
- 尚需满足：转置block使用反号权
- 尚需满足：不得把一个cross block界代替全部校正项

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有同一已构造径向几何的三指数weighted block/Schur逆及径向局部恢复估计；通用权函数基础不能替代。
- acceptance.02 [uncovered]：冻结源码没有同一已构造径向几何的三指数weighted block/Schur逆及径向局部恢复估计；通用权函数基础不能替代。

<a id="r11-07"></a>
### R11.07 局部径向一阶恢复

**输出：** 在扩大单元上由实际方程和插值/Young不等式证明u_r的L²局部界，含cutoff项与二模compact border。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–700 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 不对未识别的谱展开逐项微分
- 全部系数cost记入E_m固定幂

**本轮核对：** 冻结源码没有同一已构造径向几何的三指数weighted block/Schur逆及径向局部恢复估计；通用权函数基础不能替代。

**未完成内容：**
- 在扩大单元上由实际方程和插值/Young不等式证明u_r的L²局部界，含cutoff项与二模compact border。
- 尚需满足：不对未识别的谱展开逐项微分
- 尚需满足：全部系数cost记入E_m固定幂

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有同一已构造径向几何的三指数weighted block/Schur逆及径向局部恢复估计；通用权函数基础不能替代。
- acceptance.02 [uncovered]：冻结源码没有同一已构造径向几何的三指数weighted block/Schur逆及径向局部恢复估计；通用权函数基础不能替代。

<a id="r11-08"></a>
### R11.08 同一逆上的三指数验收

**输出：** 将全局界与一阶恢复同时用于β-ε、β、β+ε，证明各指数使用同一自然端点逆和同一row/column。

**局部依赖：** R11.01, R11.06, R11.07。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–550 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 只改变范数常数与允许输出权
- 几何和domain选择不随指数或输出阶数重选

**本轮核对：** 冻结源码没有同一已构造径向几何的三指数weighted block/Schur逆及径向局部恢复估计；通用权函数基础不能替代。

**未完成内容：**
- 将全局界与一阶恢复同时用于β-ε、β、β+ε，证明各指数使用同一自然端点逆和同一row/column。
- 尚需满足：只改变范数常数与允许输出权
- 尚需满足：几何和domain选择不随指数或输出阶数重选

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有同一已构造径向几何的三指数weighted block/Schur逆及径向局部恢复估计；通用权函数基础不能替代。
- acceptance.02 [uncovered]：冻结源码没有同一已构造径向几何的三指数weighted block/Schur逆及径向局部恢复估计；通用权函数基础不能替代。

<a id="r11-09"></a>
### R11.09 组合并验收同一几何上的双权全局估计

**输出：** 先固定β=3/4和一个ε∈(0,1/4)，在同一几何上对β−ε、β、β+ε获得足够的加权block/Schur逆界和一阶法向估计。

**局部依赖：** R11.01, R11.02, R11.03, R11.04, R11.05, R11.06, R11.07, R11.08。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 120–300 行。组合已证明输出和核对原合同，数学重负担已列为前置子任务。

**验收条件：**

- 逐项实例化此前子任务并导出原节点完整结论
- 不同指数必须共用w*,φ*,边框和自然端点逆
- 几何不依赖最终微分阶数
- 全(0,1)紧区间版本另列X01，不是不同指数分别造几何

**本轮核对：** 冻结源码没有同一已构造径向几何的三指数weighted block/Schur逆及径向局部恢复估计；通用权函数基础不能替代。

**未完成内容：**
- 先固定β=3/4和一个ε∈(0,1/4)，在同一几何上对β−ε、β、β+ε获得足够的加权block/Schur逆界和一阶法向估计。
- 尚需满足：逐项实例化此前子任务并导出原节点完整结论
- 尚需满足：不同指数必须共用w*,φ*,边框和自然端点逆
- 尚需满足：几何不依赖最终微分阶数
- 尚需满足：全(0,1)紧区间版本另列X01，不是不同指数分别造几何

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有同一已构造径向几何的三指数weighted block/Schur逆及径向局部恢复估计；通用权函数基础不能替代。
- acceptance.02 [uncovered]：冻结源码没有同一已构造径向几何的三指数weighted block/Schur逆及径向局部恢复估计；通用权函数基础不能替代。
- acceptance.03 [uncovered]：冻结源码没有同一已构造径向几何的三指数weighted block/Schur逆及径向局部恢复估计；通用权函数基础不能替代。
- acceptance.04 [uncovered]：冻结源码没有同一已构造径向几何的三指数weighted block/Schur逆及径向局部恢复估计；通用权函数基础不能替代。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：先固定β=3/4和一个ε∈(0,1/4)，在同一几何上对β−ε、β、β+ε获得足够的加权block/Schur逆界和一阶法向估计。 | R11.09（组合全部子任务） |
| acceptance.01：不同指数必须共用w*,φ*,边框和自然端点逆 | R11.01, R11.06, R11.08 |
| acceptance.02：几何不依赖最终微分阶数 | R11.01, R11.07, R11.08 |
| acceptance.03：全(0,1)紧区间版本另列X01，不是不同指数分别造几何 | R11.01, R11.08 |

<a id="r12"></a>
## R12 固定径向参考与闭图域双侧逆

**原节点完整目标：** 实例化RadialReference：同一w*,φ*,g*,ℓ*满足偶余弦二模核恰一维、其余偶模核零、返回小除数、边框归一化及兼容源上的双侧逆。图域有分布意义、smooth core闭包识别；右端归零、左端常数自由。

**原上游里程碑：** R06, R08, R10, R11

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [04-designing-the-profile.tex:74–106](../../paper/flexible-surface-rewrite/04-designing-the-profile.tex#L74)；[06-global-reference-inverse.tex:766–908](../../paper/flexible-surface-rewrite/06-global-reference-inverse.tex#L766)

<a id="r12-01"></a>
### R12.01 实际分布图域与source空间

**输出：** 定义§4 source范数、兼容源及含左常数a_Lχ_L的实际ambient空间，再以分布L_w建立最大图域。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–700 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 不能将域只定义成逆的像
- 不依赖§7物理空间W02

**本轮核对：** 冻结源码没有真实全局RadialReference、其weighted最大图域、零模primitive逆或最终度量变分border。

**未完成内容：**
- 定义§4 source范数、兼容源及含左常数a_Lχ_L的实际ambient空间，再以分布L_w建立最大图域。
- 尚需满足：不能将域只定义成逆的像
- 尚需满足：不依赖§7物理空间W02

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有真实全局RadialReference、其weighted最大图域、零模primitive逆或最终度量变分border。
- acceptance.02 [uncovered]：冻结源码没有真实全局RadialReference、其weighted最大图域、零模primitive逆或最终度量变分border。

<a id="r12-02"></a>
### R12.02 零模第一primitive及尾界

**输出：** 对∫f₀dr=0构造p₀(r)=∫左至r f₀=-∫r至右 f₀，证明真实导数和端点权界。

**局部依赖：** R12.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 250–600 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 原dr测度和正负符号明确
- 无非零homogeneous flux混入

**本轮核对：** 冻结源码没有真实全局RadialReference、其weighted最大图域、零模primitive逆或最终度量变分border。

**未完成内容：**
- 对∫f₀dr=0构造p₀(r)=∫左至r f₀=-∫r至右 f₀，证明真实导数和端点权界。
- 尚需满足：原dr测度和正负符号明确
- 尚需满足：无非零homogeneous flux混入

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有真实全局RadialReference、其weighted最大图域、零模primitive逆或最终度量变分border。
- acceptance.02 [uncovered]：冻结源码没有真实全局RadialReference、其weighted最大图域、零模primitive逆或最终度量变分border。

<a id="r12-03"></a>
### R12.03 零模高度primitive与唯一性

**输出：** 构造右端归零u₀=-∫r至右 p₀/w，证明收敛、左常数有界及减去a_Lχ_L后的权估计和齐次唯一性。

**局部依赖：** R12.02。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–700 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 允许左右常数不同
- 以增长排除非零flux而非新增端点trace假设

**本轮核对：** 冻结源码没有真实全局RadialReference、其weighted最大图域、零模primitive逆或最终度量变分border。

**未完成内容：**
- 构造右端归零u₀=-∫r至右 p₀/w，证明收敛、左常数有界及减去a_Lχ_L后的权估计和齐次唯一性。
- 尚需满足：允许左右常数不同
- 尚需满足：以增长排除非零flux而非新增端点trace假设

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有真实全局RadialReference、其weighted最大图域、零模primitive逆或最终度量变分border。
- acceptance.02 [uncovered]：冻结源码没有真实全局RadialReference、其weighted最大图域、零模primitive逆或最终度量变分border。

<a id="r12-04"></a>
### R12.04 兼容光滑有限频source稠密

**输出：** 实际截断、mollify及有限Fourier逼近source，并以固定紧bump恢复均值兼容。

**局部依赖：** R12.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–700 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 修复积分后的范数误差趋零
- scalar row一并逼近

**本轮核对：** 冻结源码没有真实全局RadialReference、其weighted最大图域、零模primitive逆或最终度量变分border。

**未完成内容：**
- 实际截断、mollify及有限Fourier逼近source，并以固定紧bump恢复均值兼容。
- 尚需满足：修复积分后的范数误差趋零
- 尚需满足：scalar row一并逼近

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有真实全局RadialReference、其weighted最大图域、零模primitive逆或最终度量变分border。
- acceptance.02 [uncovered]：冻结源码没有真实全局RadialReference、其weighted最大图域、零模primitive逆或最终度量变分border。

<a id="r12-05"></a>
### R12.05 真实角向重建与右逆恒等式

**输出：** 在兼容source上用非零模matched逆加零模primitive，证明Fourier重建收敛并得L_w G_w=I。

**局部依赖：** R12.03, R12.04。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 350–750 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 取值确实属于最大分布图域
- 先在光滑有限频源验证再由有界性和稠密推广

**本轮核对：** 冻结源码没有真实全局RadialReference、其weighted最大图域、零模primitive逆或最终度量变分border。

**未完成内容：**
- 在兼容source上用非零模matched逆加零模primitive，证明Fourier重建收敛并得L_w G_w=I。
- 尚需满足：取值确实属于最大分布图域
- 尚需满足：先在光滑有限频源验证再由有界性和稠密推广

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有真实全局RadialReference、其weighted最大图域、零模primitive逆或最终度量变分border。
- acceptance.02 [uncovered]：冻结源码没有真实全局RadialReference、其weighted最大图域、零模primitive逆或最终度量变分border。

<a id="r12-06"></a>
### R12.06 最大图域齐次解的唯一性

**输出：** 对任意图域齐次差证明局部H²和finite interface匹配，权蕴含自然端L²，从端线与K可逆推出零。

**局部依赖：** R12.01, R12.03。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 350–750 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 每个频率上的代表元和trace实际可用
- 不额外强加flat端点边界条件

**本轮核对：** 冻结源码没有真实全局RadialReference、其weighted最大图域、零模primitive逆或最终度量变分border。

**未完成内容：**
- 对任意图域齐次差证明局部H²和finite interface匹配，权蕴含自然端L²，从端线与K可逆推出零。
- 尚需满足：每个频率上的代表元和trace实际可用
- 尚需满足：不额外强加flat端点边界条件

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有真实全局RadialReference、其weighted最大图域、零模primitive逆或最终度量变分border。
- acceptance.02 [uncovered]：冻结源码没有真实全局RadialReference、其weighted最大图域、零模primitive逆或最终度量变分border。

<a id="r12-07"></a>
### R12.07 左逆与最大图域闭合

**输出：** 证明G_w L_w=I，并用图收敛下分布像收敛证明最大图域闭合。

**局部依赖：** R12.05, R12.06。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 250–650 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 左逆适用于所有图域元素
- 闭合不由逆的像定义获得

**本轮核对：** 冻结源码没有真实全局RadialReference、其weighted最大图域、零模primitive逆或最终度量变分border。

**未完成内容：**
- 证明G_w L_w=I，并用图收敛下分布像收敛证明最大图域闭合。
- 尚需满足：左逆适用于所有图域元素
- 尚需满足：闭合不由逆的像定义获得

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有真实全局RadialReference、其weighted最大图域、零模primitive逆或最终度量变分border。
- acceptance.02 [uncovered]：冻结源码没有真实全局RadialReference、其weighted最大图域、零模primitive逆或最终度量变分border。

<a id="r12-08"></a>
### R12.08 smooth admissible core的图闭包

**输出：** 证明稠密光滑source之逆像是真实smooth admissible field，并在graph norm逼近全部域元素。

**局部依赖：** R12.04, R12.05, R12.07。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 350–750 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 有限接缝光滑及source外自然平坦实际证明
- 图闭包等于最大分布域

**本轮核对：** 冻结源码没有真实全局RadialReference、其weighted最大图域、零模primitive逆或最终度量变分border。

**未完成内容：**
- 证明稠密光滑source之逆像是真实smooth admissible field，并在graph norm逼近全部域元素。
- 尚需满足：有限接缝光滑及source外自然平坦实际证明
- 尚需满足：图闭包等于最大分布域

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有真实全局RadialReference、其weighted最大图域、零模primitive逆或最终度量变分border。
- acceptance.02 [uncovered]：冻结源码没有真实全局RadialReference、其weighted最大图域、零模primitive逆或最终度量变分border。

<a id="r12-09"></a>
### R12.09 普通dr Green reciprocity

**输出：** 把局部积分分部、自然端边界项消失和对称block矩阵合成为真实全局dr配对恒等式，含scalar border。

**局部依赖：** R12.05, R12.07, R12.08。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 300–700 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 不是误用Hilbert varpi dr代替源配对
- 无限端点及Fourier极限的可积性逐一核对

**本轮核对：** 局部Green分部积分和有限区间dr转换已有，但真实全局w*、自然端点项、对称matched逆及无限模极限尚缺。

**源码证据 `ContinuousFlexibility/Scalar/GreenIdentity.lean`：** `ContinuousFlexibility.symmetric_green_identity`, `ContinuousFlexibility.integral_symmetric_green_eq_zero_of_periodic`

一般真实对称散度在有限矩形/周期角向的局部Green配对和积分恒等式可作为局部支持。

**源码证据 `ContinuousFlexibility/Radial/RadiusChange.lean`：** `ContinuousFlexibility.Radial.liouville_source_pairing_integral`

普通dr源配对的有限区间运输已有；未当作谱测度。

**未完成内容：**
- 把局部配对实例化到同一全局径向参考和scalar border。
- 实际自然端点boundary term消失、无限端点及Fourier求和极限。
- 与matched逆的全局对称block公式组合。

**逐条验收：**
- acceptance.01 [covered]：有限区间运输明确是普通dr源配对，与谱Hilbert测度分开。
- acceptance.02 [uncovered]：没有全局构造的自然端线及Fourier重建上的可积极限定理。

<a id="r12-10"></a>
### R12.10 无边框核与二模归一化

**输出：** 由增广逆的单射性证明全局无边框二模核恰ℝφ*、其它偶模核为零，规范化辅助row。

**局部依赖：** R12.06, R12.07。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–550 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- 非零φ*沿R08同一见证
- 不由局部候选核推断全局核

**本轮核对：** 冻结源码没有真实全局RadialReference、其weighted最大图域、零模primitive逆或最终度量变分border。

**未完成内容：**
- 由增广逆的单射性证明全局无边框二模核恰ℝφ*、其它偶模核为零，规范化辅助row。
- 尚需满足：非零φ*沿R08同一见证
- 尚需满足：不由局部候选核推断全局核

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有真实全局RadialReference、其weighted最大图域、零模primitive逆或最终度量变分border。
- acceptance.02 [uncovered]：冻结源码没有真实全局RadialReference、其weighted最大图域、零模primitive逆或最终度量变分border。

<a id="r12-11"></a>
### R12.11 真实度量变分border的非零配对

**输出：** 在右正connector选择非零χ≥0，实际分部积分证明a*=∫φ*L′₂,w[wχ]φ*dr<0。

**局部依赖：** R12.09, R12.10。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 250–650 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- support位于φ*′/φ*<0的真实连接区
- L′是已识别的实际度量变分

**本轮核对：** 冻结源码没有真实全局RadialReference、其weighted最大图域、零模primitive逆或最终度量变分border。

**未完成内容：**
- 在右正connector选择非零χ≥0，实际分部积分证明a*=∫φ*L′₂,w[wχ]φ*dr<0。
- 尚需满足：support位于φ*′/φ*<0的真实连接区
- 尚需满足：L′是已识别的实际度量变分

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有真实全局RadialReference、其weighted最大图域、零模primitive逆或最终度量变分border。
- acceptance.02 [uncovered]：冻结源码没有真实全局RadialReference、其weighted最大图域、零模primitive逆或最终度量变分border。

<a id="r12-12"></a>
### R12.12 替换row和column后的同一逆

**输出：** 定义χ*=χ/a*,g*=L′₂,w[wχ*]φ*和ℓ*u=∫g*u₂dr，以有限秩改造构造最终增广逆并证明三指数有界及双侧恒等式保留。

**局部依赖：** R12.07, R12.08, R12.09, R12.10, R12.11。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–700 行。单个明确构造或估计；按实际辅助引理数量复核，超过800行继续拆分。

**验收条件：**

- ∫g*φ*dr=1精确成立
- 同一g*,ℓ*,域闭包在三个指数上一致

**本轮核对：** 冻结源码没有真实全局RadialReference、其weighted最大图域、零模primitive逆或最终度量变分border。

**未完成内容：**
- 定义χ*=χ/a*,g*=L′₂,w[wχ*]φ*和ℓ*u=∫g*u₂dr，以有限秩改造构造最终增广逆并证明三指数有界及双侧恒等式保留。
- 尚需满足：∫g*φ*dr=1精确成立
- 尚需满足：同一g*,ℓ*,域闭包在三个指数上一致

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有真实全局RadialReference、其weighted最大图域、零模primitive逆或最终度量变分border。
- acceptance.02 [uncovered]：冻结源码没有真实全局RadialReference、其weighted最大图域、零模primitive逆或最终度量变分border。

<a id="r12-13"></a>
### R12.13 组合并验收固定径向参考与闭图域双侧逆

**输出：** 实例化RadialReference：同一w*,φ*,g*,ℓ*满足偶余弦二模核恰一维、其余偶模核零、返回小除数、边框归一化及兼容源上的双侧逆。图域有分布意义、smooth core闭包识别；右端归零、左端常数自由。

**局部依赖：** R12.01, R12.02, R12.03, R12.04, R12.05, R12.06, R12.07, R12.08, R12.09, R12.10, R12.11, R12.12。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 120–300 行。组合已证明输出和核对原合同，数学重负担已列为前置子任务。

**验收条件：**

- 逐项实例化此前子任务并导出原节点完整结论
- 不能仅把域定义成逆的像而略去物理域识别
- ℓ*u=∫g*u₂dr且∫g*φ*dr=1
- R12只使用§4源范数/§6图域，不依赖§7物理空间W02，防止循环

**本轮核对：** 冻结源码没有真实全局RadialReference、其weighted最大图域、零模primitive逆或最终度量变分border。

**未完成内容：**
- 实例化RadialReference：同一w*,φ*,g*,ℓ*满足偶余弦二模核恰一维、其余偶模核零、返回小除数、边框归一化及兼容源上的双侧逆。图域有分布意义、smooth core闭包识别；右端归零、左端常数自由。
- 尚需满足：逐项实例化此前子任务并导出原节点完整结论
- 尚需满足：不能仅把域定义成逆的像而略去物理域识别
- 尚需满足：ℓ*u=∫g*u₂dr且∫g*φ*dr=1
- 尚需满足：R12只使用§4源范数/§6图域，不依赖§7物理空间W02，防止循环

**逐条验收：**
- acceptance.01 [uncovered]：冻结源码没有真实全局RadialReference、其weighted最大图域、零模primitive逆或最终度量变分border。
- acceptance.02 [uncovered]：冻结源码没有真实全局RadialReference、其weighted最大图域、零模primitive逆或最终度量变分border。
- acceptance.03 [uncovered]：冻结源码没有真实全局RadialReference、其weighted最大图域、零模primitive逆或最终度量变分border。
- acceptance.04 [uncovered]：冻结源码没有真实全局RadialReference、其weighted最大图域、零模primitive逆或最终度量变分border。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：实例化RadialReference：同一w*,φ*,g*,ℓ*满足偶余弦二模核恰一维、其余偶模核零、返回小除数、边框归一化及兼容源上的双侧逆。图域有分布意义、smooth core闭包识别；右端归零、左端常数自由。 | R12.13（组合全部子任务） |
| acceptance.01：不能仅把域定义成逆的像而略去物理域识别 | R12.01, R12.05, R12.06, R12.07, R12.08 |
| acceptance.02：ℓ*u=∫g*u₂dr且∫g*φ*dr=1 | R12.10, R12.11, R12.12 |
| acceptance.03：R12只使用§4源范数/§6图域，不依赖§7物理空间W02，防止循环 | R12.01, R12.02, R12.03, R12.04, R12.05 |

<a id="w01"></a>
## W01 材料坐标与连续权函数

**原节点完整目标：** 定义x∂,H,E₀,M,ℓ,ρ并证明ρ为全实轴光滑坐标；E₀^A≤C_AM、H^ε M^A≤C_{A,ε}，材料导数和径向导数各阶换算系数受控，且与离散单元尺度一致。

**原上游里程碑：** R05

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [07-fixed-geometry.tex:22–59](../../paper/flexible-surface-rewrite/07-fixed-geometry.tex#L22)

<a id="w01-01"></a>
### W01.01 左右端尺度的实际光滑延拓

**输出：** 在固定环带两端构造x∂、ℓ及正权H,E₀,M，并给出与中段正光滑延拓相合的明确函数。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 200–500 行。围绕“左右端尺度的实际光滑延拓”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 两端分别匹配论文显式公式；中段分母保持严格正。
- ContDiff ℝ ∞作用于实际函数；端点距离的非光滑中点不用作全局公式。

**本轮核对：** 固定规范开区间(0,1)上的实际正尺度和正权已经构造，满足两端公式与中段光滑性；与R05离散轮廓一致性另属W01.07。

**源码证据 `ContinuousFlexibility/Analysis/MaterialInterval.lean`：** `ContinuousFlexibility.Analysis.materialIntervalXL_pos`, `ContinuousFlexibility.Analysis.materialIntervalXR_pos`, `ContinuousFlexibility.Analysis.materialIntervalEll_pos`, `ContinuousFlexibility.Analysis.materialIntervalEll_eq_left`, `ContinuousFlexibility.Analysis.materialIntervalEll_eq_right`, `ContinuousFlexibility.Analysis.contDiffOn_materialIntervalEll`, `ContinuousFlexibility.Analysis.materialIntervalTransition_eq_zero`, `ContinuousFlexibility.Analysis.materialIntervalTransition_eq_one`

真实开单位区间上两个sqrt(log)端点尺度、正ℓ和同一光滑transition；两端collar精确等于原公式。

**源码证据 `ContinuousFlexibility/Analysis/MaterialIntervalWeights.lean`：** `ContinuousFlexibility.Analysis.materialIntervalH_pos`, `ContinuousFlexibility.Analysis.materialIntervalE0_pos`, `ContinuousFlexibility.Analysis.materialIntervalM_pos`, `ContinuousFlexibility.Analysis.materialIntervalH_eq_left`, `ContinuousFlexibility.Analysis.materialIntervalH_eq_right`, `ContinuousFlexibility.Analysis.materialIntervalE0_eq_left`, `ContinuousFlexibility.Analysis.materialIntervalE0_eq_right`, `ContinuousFlexibility.Analysis.materialIntervalM_eq_left`, `ContinuousFlexibility.Analysis.materialIntervalM_eq_right`, `ContinuousFlexibility.Analysis.contDiffOn_materialIntervalH`, `ContinuousFlexibility.Analysis.contDiffOn_materialIntervalE0`, `ContinuousFlexibility.Analysis.contDiffOn_materialIntervalM`

实际H/E₀/M由两端log权光滑拼接；在Ioo(0,1)上C∞，各端collar精确匹配显式模型，未使用最近端点距离的非光滑中点。

**逐条验收：**
- acceptance.01 [covered]：两个端collar的显式等式以及全开区间正ℓ/正权均有实际定理。
- acceptance.02 [covered]：ContDiffOn ℝ ∞作用于实际开区间函数；光滑transition拼接避免最近端点距离在中点的不光滑。

<a id="w01-02"></a>
### W01.02 全局材料坐标双射

**输出：** 积分1/ℓ构造ρ:(r₋,r₊)→ℝ，证明严格单调且两端极限为±∞。

**局部依赖：** W01.01。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 200–500 行。围绕“全局材料坐标双射”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 导数等于1/ℓ且严格正。
- 用实际端点发散积分证明满射，给出同一ρ的逆。

**本轮核对：** 同一规范单位区间上的积分坐标已证明严格单调、两端发散、满射及实际逆，不包含离散单元一致性。

**源码证据 `ContinuousFlexibility/Analysis/MaterialInterval.lean`：** `ContinuousFlexibility.Analysis.hasDerivAt_materialIntervalRho`, `ContinuousFlexibility.Analysis.materialIntervalRho_deriv_pos`, `ContinuousFlexibility.Analysis.strictMonoOn_materialIntervalRho`, `ContinuousFlexibility.Analysis.exists_materialIntervalRho_eq_left`, `ContinuousFlexibility.Analysis.exists_materialIntervalRho_eq_right`, `ContinuousFlexibility.Analysis.tendsto_materialIntervalRho_left`, `ContinuousFlexibility.Analysis.tendsto_materialIntervalRho_right`, `ContinuousFlexibility.Analysis.surjOn_materialIntervalRho`, `ContinuousFlexibility.Analysis.bijective_materialIntervalRho`, `ContinuousFlexibility.Analysis.materialIntervalEquiv`, `ContinuousFlexibility.Analysis.materialIntervalInverse_mem`, `ContinuousFlexibility.Analysis.materialIntervalRho_inverse`, `ContinuousFlexibility.Analysis.materialIntervalInverse_rho`

同一正密度1/ℓ从1/2积分的ρ，两端实际极限±∞，实际双射及其同一个逆均已构造。

**逐条验收：**
- acceptance.01 [covered]：HasDerivAt_materialIntervalRho给出1/ℓ，deriv_pos证明严格正。
- acceptance.02 [covered]：两端ρ与显式端点primitive相差常数，从真实极限得到SurjOn/Bijective，并构造同一Equiv的逆。

<a id="w01-03"></a>
### W01.03 材料坐标的光滑逆

**输出：** 证明ρ及其逆均C∞，并得到D=∂ρ=ℓ∂r的一阶链式等式。

**局部依赖：** W01.02。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 200–500 行。围绕“材料坐标的光滑逆”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 逆导数来自同一个全局双射。
- 左右端符号及坐标方向与积分定义一致。

**本轮核对：** 同一ρ和逆的C∞及逆导数=ℓ已证；未找到对任意可微测试函数写明D=ℓ∂r作用的通用链式恒等式。

**源码证据 `ContinuousFlexibility/Analysis/MaterialInterval.lean`：** `ContinuousFlexibility.Analysis.contDiffOn_materialIntervalRho`, `ContinuousFlexibility.Analysis.contDiff_materialIntervalInverse`, `ContinuousFlexibility.Analysis.hasStrictDerivAt_materialIntervalInverse_rho`, `ContinuousFlexibility.Analysis.hasDerivAt_materialIntervalInverse`, `ContinuousFlexibility.Analysis.materialIntervalRho_inverse`, `ContinuousFlexibility.Analysis.materialIntervalInverse_rho`, `ContinuousFlexibility.Analysis.materialIntervalHomeomorph`

同一ρ和逆均C∞，逆的实际导数=ℓ∘inverse，方向与ρ的正积分密度一致。

**未完成内容：**
- 编译任意可微/光滑物理函数f拉回f∘materialIntervalInverse的材料一阶导数=ℓ乘径向导数的同一坐标恒等式。

**逐条验收：**
- acceptance.01 [covered]：inverse定义来自同一个materialIntervalEquiv，实际导数结论也针对它。
- acceptance.02 [covered]：ρ和inverse方向与积分正密度一致；双侧逆等式真实成立。

<a id="w01-04"></a>
### W01.04 对数权的全部材料导数界

**输出：** 对每个固定k≥1证明Dᵏlog H、Dᵏlog M、Dᵏlog ℓ在整个材料轴有界。

**局部依赖：** W01.01, W01.03。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 300–650 行。围绕“对数权的全部材料导数界”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 常数允许依赖k，坐标及中段选择不随k改变。
- 端点显式公式与紧中段估计分别闭合。

**本轮核对：** 仅端点模型的一阶D log H公式及界已证；任意k、另外两种log权和全局中段未覆盖。

**源码证据 `ContinuousFlexibility/Analysis/MaterialCoordinate.lean`：** `ContinuousFlexibility.Analysis.endpointMaterialDerivative_X`, `ContinuousFlexibility.Analysis.endpointMaterialDerivative_logH`, `ContinuousFlexibility.Analysis.endpointMaterialDerivative_logH_bounds`, `ContinuousFlexibility.Analysis.endpointMaterialDerivative_rho`

仅左端模型D log H=x/(1+x)及0到1界、Dρ=1；不覆盖任意阶或log M/log ℓ全局界。

**未完成内容：**
- 证明任意固定k≥1的Dᵏlog H、Dᵏlog M、Dᵏlog ℓ全局有界。
- 以同一中段拼接和同一坐标补齐所有阶。

**逐条验收：**
- acceptance.01 [partial]：当前k=1的log H模型界未覆盖全部k及另外两种权。
- acceptance.02 [partial]：只处理端点模型一阶log H，尚无全局紧中段全部阶拼合。

<a id="w01-05"></a>
### W01.05 两类连续权包络

**输出：** 证明∀A存在C_A使E₀^A≤C_AM，且∀A,ε>0存在C使H^εM^A≤C并在端点趋零。

**局部依赖：** W01.01。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 200–500 行。围绕“两类连续权包络”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- A为任意固定实参数，ε必须严格正。
- 把对数渐近转成全环带的真实不等式。

**本轮核对：** 实际全局拼接权满足两类包络和两个端点极限，不只给出连续对数模型的渐近陈述。

**源码证据 `ContinuousFlexibility/Analysis/MaterialIntervalWeights.lean`：** `ContinuousFlexibility.Analysis.materialIntervalE0_rpow_le_M`, `ContinuousFlexibility.Analysis.materialIntervalH_rpow_mul_M_rpow_le`, `ContinuousFlexibility.Analysis.tendsto_materialIntervalH_rpow_mul_M_left`, `ContinuousFlexibility.Analysis.tendsto_materialIntervalH_rpow_mul_M_right`

任意实A及ε>0的实际拼接权全区间包络，以及同一H^εM^A在两个端点的真实趋零。

**逐条验收：**
- acceptance.01 [covered]：A:ℝ任意；H^εM^A界和极限明确要求0<ε。
- acceptance.02 [covered]：同一materialInterval权的不等式对所有t:ℝ成立，尤其整个Ioo(0,1)，且两端有真实Tendsto。

<a id="w01-06"></a>
### W01.06 径向高阶导数的材料展开

**输出：** 用归纳将∂rᵃ展开为有限个Dʲ，给出每个系数的E₀^{C_a}上界。

**局部依赖：** W01.03, W01.04, W01.05。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“径向高阶导数的材料展开”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 包括ℓ的倒数及其全部产生的导数。
- 全部系数乘积合并后只消耗固定额外M阶。

**本轮核对：** 未找到“径向高阶导数的材料展开”对应的实际项目声明。未见所需全部高阶材料估计或真实离散profile对应声明；已有权/坐标基础不替代本项输出。

**未完成内容：**
- 尚待实际实现并证明：用归纳将∂rᵃ展开为有限个Dʲ，给出每个系数的E₀^{C_a}上界。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：包括ℓ的倒数及其全部产生的导数。
- acceptance.02 [uncovered]：本条尚无对应实际输出：全部系数乘积合并后只消耗固定额外M阶。

<a id="w01-07"></a>
### W01.07 实际单元与连续尺度比较

**输出：** 使用R05真实单元的端点距离界，证明第n单元上x∂=n+O(1)，H/E₀与H_n/ℰ_n按论文允许幂比较。

**局部依赖：** W01.01, W01.05。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“实际单元与连续尺度比较”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 结论对所有允许高度选择及足够大起始N统一。
- H与离散H_n的指数误差明确由ℰ_n幂支付。

**本轮核对：** 未找到“实际单元与连续尺度比较”对应的实际项目声明。未见所需全部高阶材料估计或真实离散profile对应声明；已有权/坐标基础不替代本项输出。

**未完成内容：**
- 尚待实际实现并证明：使用R05真实单元的端点距离界，证明第n单元上x∂=n+O(1)，H/E₀与H_n/ℰ_n按论文允许幂比较。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：结论对所有允许高度选择及足够大起始N统一。
- acceptance.02 [uncovered]：本条尚无对应实际输出：H与离散H_n的指数误差明确由ℰ_n幂支付。

<a id="w01-08"></a>
### W01.08 材料权的有限重叠比较

**输出：** 在ρ轴单位长度柱上证明M与其采样值M_i、H与其采样值H_i的双侧可比。

**局部依赖：** W01.03, W01.04。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“材料权的有限重叠比较”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 比较常数与柱索引无关。
- 给出后续局部Sobolev求和所需同一有限重叠覆盖。

**本轮核对：** 未找到“材料权的有限重叠比较”对应的实际项目声明。未见所需全部高阶材料估计或真实离散profile对应声明；已有权/坐标基础不替代本项输出。

**未完成内容：**
- 尚待实际实现并证明：在ρ轴单位长度柱上证明M与其采样值M_i、H与其采样值H_i的双侧可比。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：比较常数与柱索引无关。
- acceptance.02 [uncovered]：本条尚无对应实际输出：给出后续局部Sobolev求和所需同一有限重叠覆盖。

<a id="w01-09"></a>
### W01.09 组装：材料坐标与连续权函数

**输出：** 定义x∂,H,E₀,M,ℓ,ρ并证明ρ为全实轴光滑坐标；E₀^A≤C_AM、H^ε M^A≤C_{A,ε}，材料导数和径向导数各阶换算系数受控，且与离散单元尺度一致。

**局部依赖：** W01.01, W01.02, W01.03, W01.04, W01.05, W01.06, W01.07, W01.08。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 100–250 行。已有子结论的接口组装与完整量词核对；不把尚未证明的子结论作为新假设。

**验收条件：**

- 明确所有量词为固定阶数后存在常数
- 比较连续权和离散H_n,ℰ_n
- 普通径向导数的代价全部记账
- 逐项调用以上子任务的实际结论；所有见证、范数、参数和允许依赖与原节点一致。

**本轮核对：** 坐标、正权和包络已证，但全阶导数换算、真实离散单元一致性和最终组装尚缺。

**源码证据 `ContinuousFlexibility/Analysis/MaterialInterval.lean`：** `ContinuousFlexibility.Analysis.materialIntervalXL_pos`, `ContinuousFlexibility.Analysis.materialIntervalXR_pos`, `ContinuousFlexibility.Analysis.materialIntervalEll_pos`, `ContinuousFlexibility.Analysis.materialIntervalEll_eq_left`, `ContinuousFlexibility.Analysis.materialIntervalEll_eq_right`, `ContinuousFlexibility.Analysis.contDiffOn_materialIntervalEll`, `ContinuousFlexibility.Analysis.materialIntervalTransition_eq_zero`, `ContinuousFlexibility.Analysis.materialIntervalTransition_eq_one`

真实开单位区间上两个sqrt(log)端点尺度、正ℓ和同一光滑transition；两端collar精确等于原公式。

**源码证据 `ContinuousFlexibility/Analysis/MaterialIntervalWeights.lean`：** `ContinuousFlexibility.Analysis.materialIntervalH_pos`, `ContinuousFlexibility.Analysis.materialIntervalE0_pos`, `ContinuousFlexibility.Analysis.materialIntervalM_pos`, `ContinuousFlexibility.Analysis.materialIntervalH_eq_left`, `ContinuousFlexibility.Analysis.materialIntervalH_eq_right`, `ContinuousFlexibility.Analysis.materialIntervalE0_eq_left`, `ContinuousFlexibility.Analysis.materialIntervalE0_eq_right`, `ContinuousFlexibility.Analysis.materialIntervalM_eq_left`, `ContinuousFlexibility.Analysis.materialIntervalM_eq_right`, `ContinuousFlexibility.Analysis.contDiffOn_materialIntervalH`, `ContinuousFlexibility.Analysis.contDiffOn_materialIntervalE0`, `ContinuousFlexibility.Analysis.contDiffOn_materialIntervalM`

实际H/E₀/M由两端log权光滑拼接；在Ioo(0,1)上C∞，各端collar精确匹配显式模型，未使用最近端点距离的非光滑中点。

**源码证据 `ContinuousFlexibility/Analysis/MaterialInterval.lean`：** `ContinuousFlexibility.Analysis.hasDerivAt_materialIntervalRho`, `ContinuousFlexibility.Analysis.materialIntervalRho_deriv_pos`, `ContinuousFlexibility.Analysis.strictMonoOn_materialIntervalRho`, `ContinuousFlexibility.Analysis.exists_materialIntervalRho_eq_left`, `ContinuousFlexibility.Analysis.exists_materialIntervalRho_eq_right`, `ContinuousFlexibility.Analysis.tendsto_materialIntervalRho_left`, `ContinuousFlexibility.Analysis.tendsto_materialIntervalRho_right`, `ContinuousFlexibility.Analysis.surjOn_materialIntervalRho`, `ContinuousFlexibility.Analysis.bijective_materialIntervalRho`, `ContinuousFlexibility.Analysis.materialIntervalEquiv`, `ContinuousFlexibility.Analysis.materialIntervalInverse_mem`, `ContinuousFlexibility.Analysis.materialIntervalRho_inverse`, `ContinuousFlexibility.Analysis.materialIntervalInverse_rho`

同一正密度1/ℓ从1/2积分的ρ，两端实际极限±∞，实际双射及其同一个逆均已构造。

**源码证据 `ContinuousFlexibility/Analysis/MaterialInterval.lean`：** `ContinuousFlexibility.Analysis.contDiffOn_materialIntervalRho`, `ContinuousFlexibility.Analysis.contDiff_materialIntervalInverse`, `ContinuousFlexibility.Analysis.hasStrictDerivAt_materialIntervalInverse_rho`, `ContinuousFlexibility.Analysis.hasDerivAt_materialIntervalInverse`, `ContinuousFlexibility.Analysis.materialIntervalRho_inverse`, `ContinuousFlexibility.Analysis.materialIntervalInverse_rho`, `ContinuousFlexibility.Analysis.materialIntervalHomeomorph`

同一ρ和逆均C∞，逆的实际导数=ℓ∘inverse，方向与ρ的正积分密度一致。

**源码证据 `ContinuousFlexibility/Analysis/MaterialIntervalWeights.lean`：** `ContinuousFlexibility.Analysis.materialIntervalE0_rpow_le_M`, `ContinuousFlexibility.Analysis.materialIntervalH_rpow_mul_M_rpow_le`, `ContinuousFlexibility.Analysis.tendsto_materialIntervalH_rpow_mul_M_left`, `ContinuousFlexibility.Analysis.tendsto_materialIntervalH_rpow_mul_M_right`

任意实A及ε>0的实际拼接权全区间包络，以及同一H^εM^A在两个端点的真实趋零。

**源码证据 `ContinuousFlexibility/Analysis/MaterialCoordinate.lean`：** `ContinuousFlexibility.Analysis.endpointMaterialDerivative_X`, `ContinuousFlexibility.Analysis.endpointMaterialDerivative_logH`, `ContinuousFlexibility.Analysis.endpointMaterialDerivative_logH_bounds`, `ContinuousFlexibility.Analysis.endpointMaterialDerivative_rho`

仅左端模型D log H=x/(1+x)及0到1界、Dρ=1；不覆盖任意阶或log M/log ℓ全局界。

**未完成内容：**
- 补齐W01.04/.06的全部材料/径向高阶系数界。
- 完成W01.07/.08真实离散几何及单位柱比较。

**逐条验收：**
- acceptance.01 [partial]：包络常数量词已证；所有固定导数阶的统一估计尚缺。
- acceptance.02 [uncovered]：未找到连续权与R05真实H_n/ℰ_n比较声明。
- acceptance.03 [uncovered]：未找到所有径向阶的完整材料展开与系数代价。
- acceptance.04 [partial]：实际坐标和包络可统一，但高阶及离散子结论未齐全。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：定义x∂,H,E₀,M,ℓ,ρ并证明ρ为全实轴光滑坐标；E₀^A≤C_AM、H^ε M^A≤C_{A,ε}，材料导数和径向导数各阶换算系数受控，且与离散单元尺度一致。 | W01.09（组合全部子任务） |
| acceptance.01：明确所有量词为固定阶数后存在常数 | W01.04, W01.05, W01.06, W01.07 |
| acceptance.02：比较连续权和离散H_n,ℰ_n | W01.07 |
| acceptance.03：普通径向导数的代价全部记账 | W01.06 |
| remaining.01：构造左右端与中部的全局光滑材料坐标和正权拼接，尚非覆盖全实轴的已构造坐标 | W01.01, W01.02, W01.03 |
| remaining.02：证明各阶材料/径向导数换算及全部log权导数的固定阶界 | W01.04, W01.06 |
| remaining.03：与R05实际离散profile、单元尺度及H_n/E_n一致性比较；具体加权Sobolev空间尚待实例化 | W01.07, W01.08, W02.02, W02.07 |

**覆盖说明 W01.remaining.03：** R05单元与连续材料权比较由W01.07/.08验收；具体weighted Sobolev空间实例化归W02.02/.07。跨父覆盖定位不自动建立反向证明依赖。

<a id="h01"></a>
## H01 分次空间、方向微分与tame基础

**原节点完整目标：** 建立真实graded Fréchet或兼容Banach-scale定义、方向微分、smooth tame、固定导数损失、smoothing/retraction及线性/双线性/复合/积分/直和/投影的闭合定理。

**原上游里程碑：** 无

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [07-fixed-geometry.tex:102–150](../../paper/flexible-surface-rewrite/07-fixed-geometry.tex#L102)

<a id="h01-01"></a>
### H01.01 分次极限的实际拓扑识别

**输出：** 将已有相容Banach序列极限接口整理为可实例化的分次Fréchet空间，证明完备和逐级收敛判据。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 200–500 行。围绕“分次极限的实际拓扑识别”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 半范数确实生成原来的子空间拓扑。
- 结论引用真实相容嵌入，不能只把所有范数有限命名为完备。

**本轮核对：** 通用兼容Banach序列极限作为真实闭子空间，已具完备、局部凸、完全可度量分次拓扑和逐级收敛判据；不包含具体Sobolev实例化。

**源码证据 `ContinuousFlexibility/Analysis/Graded.lean`：** `ContinuousFlexibility.Analysis.compatibleSubmodule`, `ContinuousFlexibility.Analysis.ProjectiveLimit`, `ContinuousFlexibility.Analysis.mem_compatibleSubmodule`, `ContinuousFlexibility.Analysis.isClosed_compatibleSubmodule`, `ContinuousFlexibility.Analysis.projectiveLimit_completeSpace`, `ContinuousFlexibility.Analysis.projectiveLimit_locallyConvexSpace`, `ContinuousFlexibility.Analysis.projectiveLimit_completelyMetrizableSpace`, `ContinuousFlexibility.Analysis.projectiveCoordinate`, `ContinuousFlexibility.Analysis.projectiveCoordinate_bond`, `ContinuousFlexibility.Analysis.tendsto_projectiveLimit_iff`, `ContinuousFlexibility.Analysis.withSeminorms_coordinate`, `ContinuousFlexibility.Analysis.withSeminorms_graded`, `ContinuousFlexibility.Analysis.gradedSeminorm_monotone`, `ContinuousFlexibility.Analysis.gradedSeminorms_separate`

实际连续线性bond的闭相容子空间、完备局部凸完全可度量拓扑、生成原拓扑的单调分次半范数和逐坐标收敛判据。

**逐条验收：**
- acceptance.01 [covered]：WithSeminorms_coordinate/graded识别原product/subspace拓扑，半范数分离点。
- acceptance.02 [covered]：bond是实际ContinuousLinearMap，闭性及CompleteSpace实例是真实证明，而非仅命名范数有限集合。

<a id="h01-02"></a>
### H01.02 方向导数的定义及唯一性

**输出：** 在已选局部凸空间上用实际极限定义方向导数，并证明线性方向及唯一性所需准则。

**局部依赖：** H01.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“方向导数的定义及唯一性”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 定义与具体Banach级导数兼容。
- 连续线性映射上的导数等于该映射。

**本轮核对：** 未找到“方向导数的定义及唯一性”对应的实际项目声明。只见graded极限、线性tame和模型截断，未见此项实际方向微积分或非线性演算输出。

**未完成内容：**
- 尚待实际实现并证明：在已选局部凸空间上用实际极限定义方向导数，并证明线性方向及唯一性所需准则。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：定义与具体Banach级导数兼容。
- acceptance.02 [uncovered]：本条尚无对应实际输出：连续线性映射上的导数等于该映射。

<a id="h01-03"></a>
### H01.03 一阶链式法则

**输出：** 证明所选方向微积分的复合链式法则与二元参数链式法则。

**局部依赖：** H01.02。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“一阶链式法则”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 列明联合连续性要求，不能仅逐方向存在导数。
- 与有限维参数的ContDiff桥接使用同一导数。

**本轮核对：** 未找到“一阶链式法则”对应的实际项目声明。只见graded极限、线性tame和模型截断，未见此项实际方向微积分或非线性演算输出。

**未完成内容：**
- 尚待实际实现并证明：证明所选方向微积分的复合链式法则与二元参数链式法则。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：列明联合连续性要求，不能仅逐方向存在导数。
- acceptance.02 [uncovered]：本条尚无对应实际输出：与有限维参数的ContDiff桥接使用同一导数。

<a id="h01-04"></a>
### H01.04 高阶方向微分闭合

**输出：** 递归构造高阶方向导数，证明多线性、对称性及逐级兼容判据。

**局部依赖：** H01.02, H01.03。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“高阶方向微分闭合”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 所有阶导数均有真实定义及连续性条件。
- 函数值平滑与任意谓词命名SmoothTame明确区分。

**本轮核对：** 未找到“高阶方向微分闭合”对应的实际项目声明。只见graded极限、线性tame和模型截断，未见此项实际方向微积分或非线性演算输出。

**未完成内容：**
- 尚待实际实现并证明：递归构造高阶方向导数，证明多线性、对称性及逐级兼容判据。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：所有阶导数均有真实定义及连续性条件。
- acceptance.02 [uncovered]：本条尚无对应实际输出：函数值平滑与任意谓词命名SmoothTame明确区分。

<a id="h01-05"></a>
### H01.05 固定损失tame估计的定义

**输出：** 冻结base与loss参数，定义线性、双线性及光滑非线性tame估计的量词次序。

**局部依赖：** H01.01, H01.04。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 200–500 行。围绕“固定损失tame估计的定义”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 输出阶s变化时，base、loss与邻域不重选。
- 保留一高因子的双线性/非线性估计形式。

**本轮核对：** 固定loss/base的线性tame定义和闭合已证；双线性/非线性smooth tame定义与一高因子理论未实现。

**源码证据 `ContinuousFlexibility/Analysis/TameLinear.lean`：** `ContinuousFlexibility.Analysis.IsTameLinear`, `ContinuousFlexibility.Analysis.IsTameLinear.weaken`, `ContinuousFlexibility.Analysis.IsTameLinear.continuous`, `ContinuousFlexibility.Analysis.IsTameLinear.comp`

固定loss/base的线性tame定义、单调弱化、实际连续性和线性复合；不含非线性smooth tame。

**未完成内容：**
- 定义双线性及非线性smooth tame的真实方向导数和量词。
- 证明一高因子估计、固定邻域与高阶loss控制。

**逐条验收：**
- acceptance.01 [partial]：仅线性base/loss固定；没有非线性共同邻域及方向导数量词。
- acceptance.02 [uncovered]：没有双线性/非线性一高因子tame定义。

<a id="h01-06"></a>
### H01.06 实际序列平滑算子的高低估计

**输出：** 在指数递减序列模型构造频率截断Sθ并证明低阶到高阶与I−Sθ高阶到低阶估计。

**局部依赖：** H01.01, H01.05。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 300–650 行。围绕“实际序列平滑算子的高低估计”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- θ≥1为明确实或离散平滑尺度。
- 同一算子族同时满足增益估计和逼近估计。

**本轮核对：** 指数递减Banach值序列模型的实际截断与双向平滑估计已证，离散尺度θ_N=exp N≥1。

**源码证据 `ContinuousFlexibility/Analysis/ExponentialSequenceSpace.lean`：** `ContinuousFlexibility.Analysis.ExponentialSequenceSpace`, `ContinuousFlexibility.Analysis.exponentialSequenceRaw`, `ContinuousFlexibility.Analysis.exponentialSequence_level_eq_weighted_raw`, `ContinuousFlexibility.Analysis.exponentialSequenceOfRaw`, `ContinuousFlexibility.Analysis.exponentialSequenceSmoothing`, `ContinuousFlexibility.Analysis.exponentialSequenceSmoothing_apply`, `ContinuousFlexibility.Analysis.exponentialSequenceSmoothing_finite_support`, `ContinuousFlexibility.Analysis.exponentialSequenceSmoothing_idempotent`, `ContinuousFlexibility.Analysis.exponentialSequenceSmoothing_forward`, `ContinuousFlexibility.Analysis.exponentialSequenceSmoothing_tail`, `ContinuousFlexibility.Analysis.tendsto_exponentialSequenceSmoothing`

同一有限截断S_N具有exp((n−m)N)高阶增益、exp(−(n−m)N)尾部误差以及实际分次拓扑的趋恒等；离散尺度θ_N=exp N。

**逐条验收：**
- acceptance.01 [covered]：N:ℕ为明确离散截断，支持有限Iic N，等价平滑尺度θ_N=exp N。
- acceptance.02 [covered]：forward与tail作用于同一exponentialSequenceSmoothing，tendsto也在原分次拓扑成立。

<a id="h01-07"></a>
### H01.07 平滑插值不等式

**输出：** 从实际Sθ估计优化θ，证明所用分次尺度的插值不等式。

**局部依赖：** H01.06。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“平滑插值不等式”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 端阶、非整数插值参数和固定基阶的适用范围明确。
- 不能把插值直接添加为未经证明的普遍性质。

**本轮核对：** 未找到“平滑插值不等式”对应的实际项目声明。只见graded极限、线性tame和模型截断，未见此项实际方向微积分或非线性演算输出。

**未完成内容：**
- 尚待实际实现并证明：从实际Sθ估计优化θ，证明所用分次尺度的插值不等式。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：端阶、非整数插值参数和固定基阶的适用范围明确。
- acceptance.02 [uncovered]：本条尚无对应实际输出：不能把插值直接添加为未经证明的普遍性质。

<a id="h01-08"></a>
### H01.08 retraction传递平滑结构

**输出：** 给定连续线性tame J,P且PJ=I，从模型序列空间传递平滑和插值估计。

**局部依赖：** H01.05, H01.06, H01.07。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“retraction传递平滑结构”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 证明PSθJ的各项损失常数，不能丢掉J/P的阶移。
- 对子空间投影和有限维直和保留同一分次结构。

**本轮核对：** 未找到“retraction传递平滑结构”对应的实际项目声明。只见graded极限、线性tame和模型截断，未见此项实际方向微积分或非线性演算输出。

**未完成内容：**
- 尚待实际实现并证明：给定连续线性tame J,P且PJ=I，从模型序列空间传递平滑和插值估计。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：证明PSθJ的各项损失常数，不能丢掉J/P的阶移。
- acceptance.02 [uncovered]：本条尚无对应实际输出：对子空间投影和有限维直和保留同一分次结构。

<a id="h01-09"></a>
### H01.09 双线性及乘法微分规则

**输出：** 证明连续tame双线性映射的全部方向微分及smooth tame闭合性。

**局部依赖：** H01.03, H01.04, H01.05, H01.07。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“双线性及乘法微分规则”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 逐阶导数公式与一高因子估计对应。
- 实际Banach级乘法估计作为须验证的输入。

**本轮核对：** 未找到“双线性及乘法微分规则”对应的实际项目声明。只见graded极限、线性tame和模型截断，未见此项实际方向微积分或非线性演算输出。

**未完成内容：**
- 尚待实际实现并证明：证明连续tame双线性映射的全部方向微分及smooth tame闭合性。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：逐阶导数公式与一高因子估计对应。
- acceptance.02 [uncovered]：本条尚无对应实际输出：实际Banach级乘法估计作为须验证的输入。

<a id="h01-10"></a>
### H01.10 光滑tame复合定理

**输出：** 证明兼容base/loss的smooth tame复合仍smooth tame，并明确邻域和常数依赖。

**局部依赖：** H01.03, H01.04, H01.05, H01.07, H01.09。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 350–750 行。围绕“光滑tame复合定理”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 高阶链式展开中的中间导数用已证插值控制。
- 整体损失固定，不能随输出阶相加失控。

**本轮核对：** 未找到“光滑tame复合定理”对应的实际项目声明。只见graded极限、线性tame和模型截断，未见此项实际方向微积分或非线性演算输出。

**未完成内容：**
- 尚待实际实现并证明：证明兼容base/loss的smooth tame复合仍smooth tame，并明确邻域和常数依赖。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：高阶链式展开中的中间导数用已证插值控制。
- acceptance.02 [uncovered]：本条尚无对应实际输出：整体损失固定，不能随输出阶相加失控。

<a id="h01-11"></a>
### H01.11 积分与参数微分交换

**输出：** 对实际连续线性积分算子证明与各阶方向微分交换，并传递tame估计。

**局部依赖：** H01.02, H01.04, H01.05。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“积分与参数微分交换”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- Bochner或逐级积分的可积与一致控制条件明确。
- 参数区间固定，常数允许依赖输出阶。

**本轮核对：** 未找到“积分与参数微分交换”对应的实际项目声明。只见graded极限、线性tame和模型截断，未见此项实际方向微积分或非线性演算输出。

**未完成内容：**
- 尚待实际实现并证明：对实际连续线性积分算子证明与各阶方向微分交换，并传递tame估计。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：Bochner或逐级积分的可积与一致控制条件明确。
- acceptance.02 [uncovered]：本条尚无对应实际输出：参数区间固定，常数允许依赖输出阶。

<a id="h01-12"></a>
### H01.12 直和、闭投影与约束切片

**输出：** 证明有限直积、有限维直和、连续tame投影像及核的tame结构。

**局部依赖：** H01.01, H01.05, H01.08。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 200–500 行。围绕“直和、闭投影与约束切片”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 被投影子空间确为闭且具实际补空间。
- 归一化slice的仿射平移与切空间使用同一投影。

**本轮核对：** 有限直积拓扑及线性tame投影已证；一般投影像/核、真实补空间和归一化仿射slice未实现。

**源码证据 `ContinuousFlexibility/Analysis/TameLinear.lean`：** `ContinuousFlexibility.Analysis.finiteProductGrading`, `ContinuousFlexibility.Analysis.finiteProductGrading_monotone`, `ContinuousFlexibility.Analysis.withSeminorms_finiteProduct`, `ContinuousFlexibility.Analysis.IsTameLinear.pi`, `ContinuousFlexibility.Analysis.finiteProductProjection_isTame`, `ContinuousFlexibility.Analysis.IsTameLinear.piMap`

实际有限直积的分次拓扑、逐分量tame映射和坐标投影；未给一般tame投影像/核及归一化slice。

**未完成内容：**
- 建立一般tame投影像和核的闭性、补空间及平滑结构。
- 对真实ℓ*实现归一化仿射slice与切空间的同一投影识别。

**逐条验收：**
- acceptance.01 [partial]：已有有限直积坐标投影；未有一般tame投影像/核的全部结构。
- acceptance.02 [uncovered]：未有真实ℓ*归一化slice、仿射平移或切空间识别。

<a id="h01-13"></a>
### H01.13 具体函数场与参数导数的桥接

**输出：** 给定具明确连续评价和局部Cᵏ嵌入的具体函数模型，证明分次方向导数与函数逐点或局部Cᵏ参数导数相合。

**局部依赖：** H01.04, H01.08, H01.10, H01.11。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“具体函数场与参数导数的桥接”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 评价和局部嵌入的连续性及阶损失是明示且须由具体模型验证的前提。
- 冻结H02/H03使用的同一微积分接口；W02负责实际weighted Sobolev实例化，不反向依赖W02整节点。

**本轮核对：** 未找到“具体函数场与参数导数的桥接”对应的实际项目声明。只见graded极限、线性tame和模型截断，未见此项实际方向微积分或非线性演算输出。

**未完成内容：**
- 尚待实际实现并证明：给定具明确连续评价和局部Cᵏ嵌入的具体函数模型，证明分次方向导数与函数逐点或局部Cᵏ参数导数相合。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：评价和局部嵌入的连续性及阶损失是明示且须由具体模型验证的前提。
- acceptance.02 [uncovered]：本条尚无对应实际输出：冻结H02/H03使用的同一微积分接口；W02负责实际weighted Sobolev实例化，不反向依赖W02整节点。

<a id="h01-14"></a>
### H01.14 组装：分次空间、方向微分与tame基础

**输出：** 建立真实graded Fréchet或兼容Banach-scale定义、方向微分、smooth tame、固定导数损失、smoothing/retraction及线性/双线性/复合/积分/直和/投影的闭合定理。

**局部依赖：** H01.01, H01.02, H01.03, H01.04, H01.05, H01.06, H01.07, H01.08, H01.09, H01.10, H01.11, H01.12, H01.13。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 100–250 行。已有子结论的接口组装与完整量词核对；不把尚未证明的子结论作为新假设。

**验收条件：**

- 不得把任意谓词命名SmoothTame后视为理论
- smoothing和插值必须有实际算子与估计
- H02/H03的定理接口必须与此定义完全一致
- 逐项调用以上子任务的实际结论；所有见证、范数、参数和允许依赖与原节点一致。

**本轮核对：** 通用graded Fréchet、线性tame和模型smoothing已证；方向微积分、非线性smooth tame、插值和retraction未闭合。

**源码证据 `ContinuousFlexibility/Analysis/Graded.lean`：** `ContinuousFlexibility.Analysis.compatibleSubmodule`, `ContinuousFlexibility.Analysis.ProjectiveLimit`, `ContinuousFlexibility.Analysis.mem_compatibleSubmodule`, `ContinuousFlexibility.Analysis.isClosed_compatibleSubmodule`, `ContinuousFlexibility.Analysis.projectiveLimit_completeSpace`, `ContinuousFlexibility.Analysis.projectiveLimit_locallyConvexSpace`, `ContinuousFlexibility.Analysis.projectiveLimit_completelyMetrizableSpace`, `ContinuousFlexibility.Analysis.projectiveCoordinate`, `ContinuousFlexibility.Analysis.projectiveCoordinate_bond`, `ContinuousFlexibility.Analysis.tendsto_projectiveLimit_iff`, `ContinuousFlexibility.Analysis.withSeminorms_coordinate`, `ContinuousFlexibility.Analysis.withSeminorms_graded`, `ContinuousFlexibility.Analysis.gradedSeminorm_monotone`, `ContinuousFlexibility.Analysis.gradedSeminorms_separate`

实际连续线性bond的闭相容子空间、完备局部凸完全可度量拓扑、生成原拓扑的单调分次半范数和逐坐标收敛判据。

**源码证据 `ContinuousFlexibility/Analysis/TameLinear.lean`：** `ContinuousFlexibility.Analysis.IsTameLinear`, `ContinuousFlexibility.Analysis.IsTameLinear.weaken`, `ContinuousFlexibility.Analysis.IsTameLinear.continuous`, `ContinuousFlexibility.Analysis.IsTameLinear.comp`

固定loss/base的线性tame定义、单调弱化、实际连续性和线性复合；不含非线性smooth tame。

**源码证据 `ContinuousFlexibility/Analysis/ExponentialSequenceSpace.lean`：** `ContinuousFlexibility.Analysis.ExponentialSequenceSpace`, `ContinuousFlexibility.Analysis.exponentialSequenceRaw`, `ContinuousFlexibility.Analysis.exponentialSequence_level_eq_weighted_raw`, `ContinuousFlexibility.Analysis.exponentialSequenceOfRaw`, `ContinuousFlexibility.Analysis.exponentialSequenceSmoothing`, `ContinuousFlexibility.Analysis.exponentialSequenceSmoothing_apply`, `ContinuousFlexibility.Analysis.exponentialSequenceSmoothing_finite_support`, `ContinuousFlexibility.Analysis.exponentialSequenceSmoothing_idempotent`, `ContinuousFlexibility.Analysis.exponentialSequenceSmoothing_forward`, `ContinuousFlexibility.Analysis.exponentialSequenceSmoothing_tail`, `ContinuousFlexibility.Analysis.tendsto_exponentialSequenceSmoothing`

同一有限截断S_N具有exp((n−m)N)高阶增益、exp(−(n−m)N)尾部误差以及实际分次拓扑的趋恒等；离散尺度θ_N=exp N。

**源码证据 `ContinuousFlexibility/Analysis/TameLinear.lean`：** `ContinuousFlexibility.Analysis.finiteProductGrading`, `ContinuousFlexibility.Analysis.finiteProductGrading_monotone`, `ContinuousFlexibility.Analysis.withSeminorms_finiteProduct`, `ContinuousFlexibility.Analysis.IsTameLinear.pi`, `ContinuousFlexibility.Analysis.finiteProductProjection_isTame`, `ContinuousFlexibility.Analysis.IsTameLinear.piMap`

实际有限直积的分次拓扑、逐分量tame映射和坐标投影；未给一般tame投影像/核及归一化slice。

**未完成内容：**
- 补齐H01.02–.04方向微积分和高阶链式。
- 补齐非线性tame、插值、retraction、积分与具体函数场桥接。

**逐条验收：**
- acceptance.01 [partial]：实际graded和线性tame已定义，但非线性smooth tame尚无。
- acceptance.02 [partial]：真实S_N有双向估计，插值及具体空间retraction未证。
- acceptance.03 [uncovered]：H02/H03所需实际方向微积分接口尚无声明。
- acceptance.04 [partial]：只有部分通用子结论，全部tame基础尚不能组装。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：建立真实graded Fréchet或兼容Banach-scale定义、方向微分、smooth tame、固定导数损失、smoothing/retraction及线性/双线性/复合/积分/直和/投影的闭合定理。 | H01.14（组合全部子任务） |
| acceptance.01：不得把任意谓词命名SmoothTame后视为理论 | H01.02, H01.03, H01.04, H01.05, H01.09, H01.10 |
| acceptance.02：smoothing和插值必须有实际算子与估计 | H01.06, H01.07, H01.08 |
| acceptance.03：H02/H03的定理接口必须与此定义完全一致 | H01.13 |
| remaining.01：实例化实际weighted Sobolev levels、兼容嵌入与实际smooth fields的识别 | H01.01, H01.13, W02.02, W02.07, W02.16 |
| remaining.02：构造smoothing及smooth tame calculus与Nash–Moser迭代，尚无H03存在定理 | H01.06, H01.07, H01.08, H01.09, H01.10, H03.05, H03.07, H03.13, H03.15, H03.17, H03.22, H03.23 |

**覆盖说明 H01.remaining.01：** 通用H01.01/.13先提供相容极限及函数场微分桥接；实际weighted Sobolev级、光滑场及平滑实例化在W02.02/.07/.16验收，不能把通用理论完成冒充已实例化。

**覆盖说明 H01.remaining.02：** H01.06至.10提供真实smoothing、插值和smooth tame calculus；实际Nash–Moser迭代及存在性由H03.05/.07/.13/.15/.17/.22/.23验收。不得反加H03整节点为H01通用理论前置。

<a id="w02"></a>
## W02 加权高度、源与圆序列空间

**原节点完整目标：** 构造Xγ⁰、Xγ=Xγ⁰⊕ℝχL、Yβ=ker Q、Zγ及Kγ，证明完备拓扑、实偶半周期sector、兼容投影、tame retraction PJ=I及固定损失的乘积/倒数/复合/trace和右逆。

**原上游里程碑：** W01, H01

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [07-fixed-geometry.tex:72–150](../../paper/flexible-surface-rewrite/07-fixed-geometry.tex#L72)

<a id="w02-01"></a>
### W02.01 材料柱分割与有限重叠恒等式

**输出：** 在全ρ轴构造实际C∞函数φ_i，满足有限重叠、导数一致有界和Σφ_i²=1。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“材料柱分割与有限重叠恒等式”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 局部有限性保证求和真实光滑。
- 分割与W01同一全局ρ及采样权M_i相合。

**本轮核对：** 未找到“材料柱分割与有限重叠恒等式”对应的实际项目声明。未构造实际加权Sobolev、材料Fourier retraction或X/Y/Z/K接口，通用序列空间不替代它。

**未完成内容：**
- 尚待实际实现并证明：在全ρ轴构造实际C∞函数φ_i，满足有限重叠、导数一致有界和Σφ_i²=1。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：局部有限性保证求和真实光滑。
- acceptance.02 [uncovered]：本条尚无对应实际输出：分割与W01同一全局ρ及采样权M_i相合。

<a id="w02-02"></a>
### W02.02 加权有限阶Hilbert空间

**输出：** 按论文混合MᶜDᵃ∂θᵇ范数构造每一有限阶空间，证明相应弱导数图范数完备。

**局部依赖：** W02.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 350–750 行。围绕“加权有限阶Hilbert空间”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 权严格正且局部有界，弱导数与分布定义一致。
- 相容嵌入真实连续，不只记录形式范数。

**本轮核对：** 未找到“加权有限阶Hilbert空间”对应的实际项目声明。未构造实际加权Sobolev、材料Fourier retraction或X/Y/Z/K接口，通用序列空间不替代它。

**未完成内容：**
- 尚待实际实现并证明：按论文混合MᶜDᵃ∂θᵇ范数构造每一有限阶空间，证明相应弱导数图范数完备。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：权严格正且局部有界，弱导数与分布定义一致。
- acceptance.02 [uncovered]：本条尚无对应实际输出：相容嵌入真实连续，不只记录形式范数。

<a id="w02-03"></a>
### W02.03 材料柱混合Fourier变换

**输出：** 构造ρ方向实线Fourier及角向圆Fourier组合，证明L²等距与逆变换。

**局部依赖：** W02.01, W02.02。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 350–750 行。围绕“材料柱混合Fourier变换”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 角向实偶π周期sector与偶余弦频率精确对应。
- 所有测度及Fourier归一化常数固定。

**本轮核对：** 有限角余弦模sector、PDE分离和积分正交已证；ρ方向Fourier、无限L²等距与联合逆变换均未实现。

**源码证据 `ContinuousFlexibility/Radial/FourierModes.lean`：** `ContinuousFlexibility.Radial.cosineMode_even`, `ContinuousFlexibility.Radial.cosineMode_even_frequency_periodic`, `ContinuousFlexibility.Radial.finite_even_cosine_sum_even`, `ContinuousFlexibility.Radial.finite_even_cosine_sum_periodic`, `ContinuousFlexibility.Radial.radialPDE_cosine_lift`, `ContinuousFlexibility.Radial.radialPDE_finite_cosine_sum`

实际有限偶余弦模的实偶/π周期及PDE分离，不含无限材料柱L² Fourier变换。

**源码证据 `ContinuousFlexibility/Radial/FourierOrthogonality.lean`：** `ContinuousFlexibility.Radial.integral_cosineMode`, `ContinuousFlexibility.Radial.angularAverage_cosineMode`, `ContinuousFlexibility.Radial.angularPairing_cosineMode`

真实2π角积分归一化下正频余弦模正交；未证明完整混合变换等距和逆变换。

**未完成内容：**
- 构造材料ρ与圆变量的联合L² Fourier变换及其逆。
- 证明完整实偶π周期sector与全部偶余弦频率的双向刻画。

**逐条验收：**
- acceptance.01 [partial]：有限偶余弦模属于目标sector已证，完整无限频率对应尚缺。
- acceptance.02 [partial]：角向2π归一化和正交已证，混合变换测度与完整等距常数尚缺。

<a id="w02-04"></a>
### W02.04 局部化谱范数等价

**输出：** 证明Σ_i,j∫(M_i²+ξ²+j²)^s|F(φ_iv)|²与原混合范数双侧等价。

**局部依赖：** W02.01, W02.02, W02.03。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“局部化谱范数等价”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 柱索引上的常数统一。
- 权导数与局部化导数的全部交换项由W01支付。

**本轮核对：** 未找到“局部化谱范数等价”对应的实际项目声明。未构造实际加权Sobolev、材料Fourier retraction或X/Y/Z/K接口，通用序列空间不替代它。

**未完成内容：**
- 尚待实际实现并证明：证明Σ_i,j∫(M_i²+ξ²+j²)^s|F(φ_iv)|²与原混合范数双侧等价。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：柱索引上的常数统一。
- acceptance.02 [uncovered]：本条尚无对应实际输出：权导数与局部化导数的全部交换项由W01支付。

<a id="w02-05"></a>
### W02.05 谱壳cutoff及分析映射J

**输出：** 构造log ω上的光滑壳分割ζ_k并定义J，证明模型指数序列范数的固定阶损失估计。

**局部依赖：** W02.03, W02.04。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“谱壳cutoff及分析映射J”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 壳重叠数统一有限。
- 证明||Jv||_s≤C_s||v||_{s+1}的具体阶移。

**本轮核对：** 未找到“谱壳cutoff及分析映射J”对应的实际项目声明。未构造实际加权Sobolev、材料Fourier retraction或X/Y/Z/K接口，通用序列空间不替代它。

**未完成内容：**
- 尚待实际实现并证明：构造log ω上的光滑壳分割ζ_k并定义J，证明模型指数序列范数的固定阶损失估计。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：壳重叠数统一有限。
- acceptance.02 [uncovered]：本条尚无对应实际输出：证明||Jv||_s≤C_s||v||_{s+1}的具体阶移。

<a id="w02-06"></a>
### W02.06 重建映射P及PJ恒等式

**输出：** 用放大壳cutoff和逆Fourier定义P，证明有界性及PJ=I。

**局部依赖：** W02.01, W02.03, W02.04, W02.05。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“重建映射P及PJ恒等式”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 求和在实际Banach级收敛。
- Σφ_i²=1及壳恒等式产生原函数，而非仅稠密子集上的形式等式。

**本轮核对：** 未找到“重建映射P及PJ恒等式”对应的实际项目声明。未构造实际加权Sobolev、材料Fourier retraction或X/Y/Z/K接口，通用序列空间不替代它。

**未完成内容：**
- 尚待实际实现并证明：用放大壳cutoff和逆Fourier定义P，证明有界性及PJ=I。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：求和在实际Banach级收敛。
- acceptance.02 [uncovered]：本条尚无对应实际输出：Σφ_i²=1及壳恒等式产生原函数，而非仅稠密子集上的形式等式。

<a id="w02-07"></a>
### W02.07 高度极限空间与光滑场识别

**输出：** 用相容有限阶极限构造Xγ⁰，证明其元素恰为所需全部阶加权光滑场。

**局部依赖：** W02.02, W02.04, W02.06。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“高度极限空间与光滑场识别”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 既证明极限空间完备，也证明从弱场到实际局部光滑代表。
- 应用H01的微积分结构使用同一J/P。

**本轮核对：** 未找到“高度极限空间与光滑场识别”对应的实际项目声明。未构造实际加权Sobolev、材料Fourier retraction或X/Y/Z/K接口，通用序列空间不替代它。

**未完成内容：**
- 尚待实际实现并证明：用相容有限阶极限构造Xγ⁰，证明其元素恰为所需全部阶加权光滑场。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：既证明极限空间完备，也证明从弱场到实际局部光滑代表。
- acceptance.02 [uncovered]：本条尚无对应实际输出：应用H01的微积分结构使用同一J/P。

<a id="w02-08"></a>
### W02.08 独立端点常数直和

**输出：** 构造固定χL并证明Xγ=Xγ⁰⊕ℝχL为真实拓扑直和。

**局部依赖：** W02.07。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“独立端点常数直和”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- χL左端为1右端为0，导数支持在指定正分量。
- 额外scalar记录两端差值，不要求左右常数相等。

**本轮核对：** 未找到“独立端点常数直和”对应的实际项目声明。未构造实际加权Sobolev、材料Fourier retraction或X/Y/Z/K接口，通用序列空间不替代它。

**未完成内容：**
- 尚待实际实现并证明：构造固定χL并证明Xγ=Xγ⁰⊕ℝχL为真实拓扑直和。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：χL左端为1右端为0，导数支持在指定正分量。
- acceptance.02 [uncovered]：本条尚无对应实际输出：额外scalar记录两端差值，不要求左右常数相等。

<a id="w02-09"></a>
### W02.09 兼容源泛函Q的连续性

**输出：** 以物理dr dθ定义Q，证明它在加权源空间连续，并构造紧支ψ满足Qψ=1。

**局部依赖：** W02.02, W02.07。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“兼容源泛函Q的连续性”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 用H^βℓ的实际L²配对估计。
- 材料测度dρ与物理dr的Jacobian保留。

**本轮核对：** 未找到“兼容源泛函Q的连续性”对应的实际项目声明。未构造实际加权Sobolev、材料Fourier retraction或X/Y/Z/K接口，通用序列空间不替代它。

**未完成内容：**
- 尚待实际实现并证明：以物理dr dθ定义Q，证明它在加权源空间连续，并构造紧支ψ满足Qψ=1。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：用H^βℓ的实际L²配对估计。
- acceptance.02 [uncovered]：本条尚无对应实际输出：材料测度dρ与物理dr的Jacobian保留。

<a id="w02-10"></a>
### W02.10 兼容源投影及归一化切片

**输出：** 证明f↦f−ψQf为连续tame投影；在R12提供真实ℓ*后构造二模归一化补空间。

**局部依赖：** W02.07, W02.08, W02.09。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“兼容源投影及归一化切片”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- Q与ℓ*的实际连续性分别验证。
- 投影作用于同一实际空间，不能在R12之前假装已有真实ℓ*。

**细分后补充依赖：** R12：二模slice使用同一真实ℓ*，须在R12构造后实例化；原proof_outline已限定此选择次序。

**本轮核对：** 未找到“兼容源投影及归一化切片”对应的实际项目声明。未构造实际加权Sobolev、材料Fourier retraction或X/Y/Z/K接口，通用序列空间不替代它。

**未完成内容：**
- 尚待实际实现并证明：证明f↦f−ψQf为连续tame投影；在R12提供真实ℓ*后构造二模归一化补空间。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：Q与ℓ*的实际连续性分别验证。
- acceptance.02 [uncovered]：本条尚无对应实际输出：投影作用于同一实际空间，不能在R12之前假装已有真实ℓ*。

<a id="w02-11"></a>
### W02.11 圆序列及常数控制空间

**输出：** 构造Zγ各阶空间与角向常数sector Kγ，证明完备性和实际频率重构。

**局部依赖：** W02.02, W02.03。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“圆序列及常数控制空间”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 组件索引m的M_m/H_m权与原参考几何一致。
- 奇/偶投影保留π-equivariance和同一范数。

**本轮核对：** 未找到“圆序列及常数控制空间”对应的实际项目声明。未构造实际加权Sobolev、材料Fourier retraction或X/Y/Z/K接口，通用序列空间不替代它。

**未完成内容：**
- 尚待实际实现并证明：构造Zγ各阶空间与角向常数sector Kγ，证明完备性和实际频率重构。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：组件索引m的M_m/H_m权与原参考几何一致。
- acceptance.02 [uncovered]：本条尚无对应实际输出：奇/偶投影保留π-equivariance和同一范数。

<a id="w02-12"></a>
### W02.12 物理、谱及canonical源的转换

**输出：** 给定满足明确光滑性、非零Jacobian及配对前提的显式chart和高度因子，证明物理、谱及canonical三类源之间的转换与配对恒等式。

**局部依赖：** W02.03, W02.07, W02.09, W02.11。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 300–650 行。围绕“物理、谱及canonical源的转换”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 每次换元保留高度因子、绝对Jacobian及算子符号；逐类证明相应加权范数连续性。
- 本项为显式chart下的通用转换定理；N04构造实际chart后再实例化，不把N04存在性作为W02的前置。

**本轮核对：** 物理dr与径向谱/Hilbert源的真实配对换元已证；一般二维canonical source转换和加权范数连续性未实现。

**源码证据 `ContinuousFlexibility/Radial/RadiusChange.lean`：** `ContinuousFlexibility.Radial.liouville_source_pairing_integral`, `ContinuousFlexibility.Radial.liouville_hilbert_integral`

给定真实径向换元R,s下，物理dr源配对和Hilbert密度的实际积分换元恒等式。

**源码证据 `ContinuousFlexibility/Radial/Liouville.lean`：** `ContinuousFlexibility.Radial.liouvilleSource`, `ContinuousFlexibility.Radial.liouville_forcing_iff`, `ContinuousFlexibility.Radial.liouville_source_pairing_density`, `ContinuousFlexibility.Radial.liouville_hilbert_density`

径向Liouville源符号/因子及配对密度已明确，不等于全二维canonical源转换。

**未完成内容：**
- 对显式二维Ψ与height factor建立canonical源转换及配对保持。
- 补齐三类源的全部加权范数连续性、绝对Jacobian和物理算子符号。

**逐条验收：**
- acceptance.01 [partial]：径向因子与导数Jacobian保留；二维绝对Jacobian及所有加权连续转换尚缺。
- acceptance.02 [partial]：已有给定径向R,s下的通用条件定理，不是目标一般二维chart转换。

<a id="w02-13"></a>
### W02.13 局部Sobolev的一高因子乘积界

**输出：** 在单位材料柱证明固定基阶b>1的乘积估计，然后用有限重叠求和到全局。

**局部依赖：** W02.01, W02.02, W02.04, W02.07。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“局部Sobolev的一高因子乘积界”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 全部高阶估计至多一个因子处在高阶。
- H/E₀/M权乘积的完整系数损失按W01统一吸收。

**本轮核对：** 未找到“局部Sobolev的一高因子乘积界”对应的实际项目声明。未构造实际加权Sobolev、材料Fourier retraction或X/Y/Z/K接口，通用序列空间不替代它。

**未完成内容：**
- 尚待实际实现并证明：在单位材料柱证明固定基阶b>1的乘积估计，然后用有限重叠求和到全局。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：全部高阶估计至多一个因子处在高阶。
- acceptance.02 [uncovered]：本条尚无对应实际输出：H/E₀/M权乘积的完整系数损失按W01统一吸收。

<a id="w02-14"></a>
### W02.14 正下界倒数与光滑复合

**输出：** 在除去参考因子后分母有统一正下界的共同低阶邻域，证明倒数和所需非线性复合smooth tame。

**局部依赖：** W02.07, W02.13。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“正下界倒数与光滑复合”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 分母下界由固定低阶范数控制。
- 任意输出阶使用同一邻域及固定loss。

**本轮核对：** 未找到“正下界倒数与光滑复合”对应的实际项目声明。未构造实际加权Sobolev、材料Fourier retraction或X/Y/Z/K接口，通用序列空间不替代它。

**未完成内容：**
- 尚待实际实现并证明：在除去参考因子后分母有统一正下界的共同低阶邻域，证明倒数和所需非线性复合smooth tame。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：分母下界由固定低阶范数控制。
- acceptance.02 [uncovered]：本条尚无对应实际输出：任意输出阶使用同一邻域及固定loss。

<a id="w02-15"></a>
### W02.15 横截面trace与实际右逆

**输出：** 证明到每条横截圆的trace固定损失估计，并用固定cutoff给出右逆。

**局部依赖：** W02.02, W02.04, W02.07, W02.11。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“横截面trace与实际右逆”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- trace至少计入论文要求的一阶normal Sobolev代价。
- 右逆与组件权、实偶/奇sector和有限重叠统一。

**本轮核对：** 未找到“横截面trace与实际右逆”对应的实际项目声明。未构造实际加权Sobolev、材料Fourier retraction或X/Y/Z/K接口，通用序列空间不替代它。

**未完成内容：**
- 尚待实际实现并证明：证明到每条横截圆的trace固定损失估计，并用固定cutoff给出右逆。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：trace至少计入论文要求的一阶normal Sobolev代价。
- acceptance.02 [uncovered]：本条尚无对应实际输出：右逆与组件权、实偶/奇sector和有限重叠统一。

<a id="w02-16"></a>
### W02.16 空间平滑与全部演算接口

**输出：** 把J/P平滑与源投影、奇偶投影、端点直和协调，导出实际X/Y/Z/K上的平滑和tame演算。

**局部依赖：** W02.06, W02.07, W02.08, W02.10, W02.11, W02.13, W02.14, W02.15。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“空间平滑与全部演算接口”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 投影后的算子仍逼近恒等映射并有固定高低阶估计。
- H01定义与Nash–Moser所需空间和参数导数完全一致。

**本轮核对：** 未找到“空间平滑与全部演算接口”对应的实际项目声明。未构造实际加权Sobolev、材料Fourier retraction或X/Y/Z/K接口，通用序列空间不替代它。

**未完成内容：**
- 尚待实际实现并证明：把J/P平滑与源投影、奇偶投影、端点直和协调，导出实际X/Y/Z/K上的平滑和tame演算。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：投影后的算子仍逼近恒等映射并有固定高低阶估计。
- acceptance.02 [uncovered]：本条尚无对应实际输出：H01定义与Nash–Moser所需空间和参数导数完全一致。

<a id="w02-17"></a>
### W02.17 组装：加权高度、源与圆序列空间

**输出：** 构造Xγ⁰、Xγ=Xγ⁰⊕ℝχL、Yβ=ker Q、Zγ及Kγ，证明完备拓扑、实偶半周期sector、兼容投影、tame retraction PJ=I及固定损失的乘积/倒数/复合/trace和右逆。

**局部依赖：** W02.01, W02.02, W02.03, W02.04, W02.05, W02.06, W02.07, W02.08, W02.09, W02.10, W02.11, W02.12, W02.13, W02.14, W02.15, W02.16。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 100–250 行。已有子结论的接口组装与完整量词核对；不把尚未证明的子结论作为新假设。

**验收条件：**

- χL记录两端高度差
- 不能只定义所有范数有限而省略完备性
- 三类源测度的连接有明确连续映射
- 逐项调用以上子任务的实际结论；所有见证、范数、参数和允许依赖与原节点一致。

**本轮核对：** 有限Fourier及径向源换元已有真实结果；实际X/Y/Z/K、完备性、PJ=I和smooth tame未建立。

**源码证据 `ContinuousFlexibility/Radial/FourierModes.lean`：** `ContinuousFlexibility.Radial.cosineMode_even`, `ContinuousFlexibility.Radial.cosineMode_even_frequency_periodic`, `ContinuousFlexibility.Radial.finite_even_cosine_sum_even`, `ContinuousFlexibility.Radial.finite_even_cosine_sum_periodic`, `ContinuousFlexibility.Radial.radialPDE_cosine_lift`, `ContinuousFlexibility.Radial.radialPDE_finite_cosine_sum`

实际有限偶余弦模的实偶/π周期及PDE分离，不含无限材料柱L² Fourier变换。

**源码证据 `ContinuousFlexibility/Radial/FourierOrthogonality.lean`：** `ContinuousFlexibility.Radial.integral_cosineMode`, `ContinuousFlexibility.Radial.angularAverage_cosineMode`, `ContinuousFlexibility.Radial.angularPairing_cosineMode`

真实2π角积分归一化下正频余弦模正交；未证明完整混合变换等距和逆变换。

**源码证据 `ContinuousFlexibility/Radial/RadiusChange.lean`：** `ContinuousFlexibility.Radial.liouville_source_pairing_integral`, `ContinuousFlexibility.Radial.liouville_hilbert_integral`

给定真实径向换元R,s下，物理dr源配对和Hilbert密度的实际积分换元恒等式。

**未完成内容：**
- 构造真实加权Hilbert levels及smooth fields识别。
- 构造J/P、兼容投影、全部源测度、trace、乘积和smooth tame接口。

**逐条验收：**
- acceptance.01 [uncovered]：未定义实际Xγ直和或χL端点scalar空间。
- acceptance.02 [uncovered]：通用Graded/ExponentialSequenceSpace不识别实际Sobolev levels。
- acceptance.03 [partial]：只有径向谱/物理配对，三类完整连续转换尚缺。
- acceptance.04 [partial]：仅有限模支持引理，空间和全部接口未齐。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：构造Xγ⁰、Xγ=Xγ⁰⊕ℝχL、Yβ=ker Q、Zγ及Kγ，证明完备拓扑、实偶半周期sector、兼容投影、tame retraction PJ=I及固定损失的乘积/倒数/复合/trace和右逆。 | W02.17（组合全部子任务） |
| acceptance.01：χL记录两端高度差 | W02.08 |
| acceptance.02：不能只定义所有范数有限而省略完备性 | W02.02, W02.07, W02.11 |
| acceptance.03：三类源测度的连接有明确连续映射 | W02.03, W02.09, W02.12 |
| remaining.01：定义并证明全部加权高度、源、圆序列空间的完备拓扑及smooth tame性质 | W02.02, W02.07, W02.08, W02.09, W02.10, W02.11, W02.13, W02.14, W02.16 |
| remaining.02：无限Fourier重建、加权序列估计、兼容投影及tame retraction | W02.03, W02.04, W02.05, W02.06, W02.10, W02.11 |

<a id="w03"></a>
## W03 正指数弱空间的全阶平坦延拓

**原节点完整目标：** γ>0且u∈Xγ⁰蕴含任意a,b,k下d∂^(-k)∂r^a∂θ^b u→0，零延拓C∞；Xγ则两端分别常值延拓，参数导数同样成立。

**原上游里程碑：** W01, W02

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [07-fixed-geometry.tex:102–156](../../paper/flexible-surface-rewrite/07-fixed-geometry.tex#L102)

<a id="w03-01"></a>
### W03.01 局部Sobolev到全部mixed jets

**输出：** 对u∈Xγ⁰用材料柱嵌入控制Dᵃ∂θᵇu的逐点范数。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“局部Sobolev到全部mixed jets”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 对任意固定a,b选明确有限输入阶。
- 柱索引及角变量上的常数统一。

**本轮核对：** 未找到“局部Sobolev到全部mixed jets”对应的实际项目声明。未从实际weighted Sobolev得到本项uniform mixed jets或参数延拓，通用一变量结果不自动实例化。

**未完成内容：**
- 尚待实际实现并证明：对u∈Xγ⁰用材料柱嵌入控制Dᵃ∂θᵇu的逐点范数。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：对任意固定a,b选明确有限输入阶。
- acceptance.02 [uncovered]：本条尚无对应实际输出：柱索引及角变量上的常数统一。

<a id="w03-02"></a>
### W03.02 径向mixed jets的权衰减

**输出：** 结合W01导数转换，证明d∂^(−k)∂rᵃ∂θᵇu被seminorm乘HγE₀^{C_{a,b,k}}控制。

**局部依赖：** W03.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“径向mixed jets的权衰减”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- a,b,k可为任意固定非负整数。
- γ>0且所有产生的ℓ倒数、端点距离因子显式支付。

**本轮核对：** 未找到“径向mixed jets的权衰减”对应的实际项目声明。未从实际weighted Sobolev得到本项uniform mixed jets或参数延拓，通用一变量结果不自动实例化。

**未完成内容：**
- 尚待实际实现并证明：结合W01导数转换，证明d∂^(−k)∂rᵃ∂θᵇu被seminorm乘HγE₀^{C_{a,b,k}}控制。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：a,b,k可为任意固定非负整数。
- acceptance.02 [uncovered]：本条尚无对应实际输出：γ>0且所有产生的ℓ倒数、端点距离因子显式支付。

<a id="w03-03"></a>
### W03.03 两端全部jets一致趋零

**输出：** 把权衰减转成两端所有mixed jets的统一极限零。

**局部依赖：** W03.02。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“两端全部jets一致趋零”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 极限对θ一致，不能只逐点。
- 指数γ任意严格正，不能依赖2β>1的后验加强。

**本轮核对：** 未找到“两端全部jets一致趋零”对应的实际项目声明。未从实际weighted Sobolev得到本项uniform mixed jets或参数延拓，通用一变量结果不自动实例化。

**未完成内容：**
- 尚待实际实现并证明：把权衰减转成两端所有mixed jets的统一极限零。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：极限对θ一致，不能只逐点。
- acceptance.02 [uncovered]：本条尚无对应实际输出：指数γ任意严格正，不能依赖2β>1的后验加强。

<a id="w03-04"></a>
### W03.04 Banach值两端零延拓

**输出：** 把已证一变量Banach值延拓定理用于角向Cᵇ场，得到实际联合r/θ C∞零延拓。

**局部依赖：** W03.03。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 300–650 行。围绕“Banach值两端零延拓”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 给出所有角阶兼容的同一延拓函数。
- 实际ContDiff ℝ ∞及端点jets=0均落在同一函数。

**本轮核对：** 一变量任意Banach值域的全阶零延拓已证；角向Cᵇ场的实际应用、全部b兼容和r/θ联合C∞尚未实现。

**源码证据 `ContinuousFlexibility/Analysis/FlatExtension.lean`：** `ContinuousFlexibility.Analysis.contDiff_extendZeroOutside`, `ContinuousFlexibility.Analysis.iteratedDeriv_extendZeroOutside`, `ContinuousFlexibility.Analysis.iteratedDeriv_extendZeroOutside_eq_zero`

任意实范数值域的一变量真实C∞零延拓和普通jets=0；实际两端导数极限仍为前提，未实例化到角向Cᵇ/Sobolev。

**未完成内容：**
- 识别兼容全部角阶的角向Cᵇ Banach场。
- 由实际weighted Sobolev验证其Banach范数两端导数极限并得到联合光滑。

**逐条验收：**
- acceptance.01 [partial]：同一一变量延拓及每阶普通导数相合，但无全部角阶兼容场。
- acceptance.02 [partial]：一般Banach值C∞与端点jets=0真实成立，r/θ联合实例尚缺。

<a id="w03-05"></a>
### W03.05 独立左右常数延拓

**输出：** 对Xγ=Xγ⁰⊕ℝχL证明两端常值光滑延拓并标识两个端点值。

**局部依赖：** W03.04。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 200–500 行。围绕“独立左右常数延拓”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 右端固定归零的规范与左端scalar一致。
- 允许两端常数不同。

**本轮核对：** reference延拓一般定理允许不同端值；实际Xγ/χL直和及其端点scalar尚未定义和识别。

**源码证据 `ContinuousFlexibility/Analysis/FlatExtension.lean`：** `ContinuousFlexibility.Analysis.extendByReference`, `ContinuousFlexibility.Analysis.contDiff_extendByReference`, `ContinuousFlexibility.Analysis.extendByReference_of_mem`, `ContinuousFlexibility.Analysis.extendByReference_of_notMem`, `ContinuousFlexibility.Analysis.iteratedDeriv_extendByReference_eq`

任意全球光滑参考的实际延拓与其外部所有jets相同；允许参考在两端取不同常值，不给实际Xγ/χL空间。

**未完成内容：**
- 构造实际Xγ/χL，并把其左右常数带入真实reference。
- 证明弱端点衰减及右端0/左端scalar规范。

**逐条验收：**
- acceptance.01 [uncovered]：无实际Xγ/χL直和及右端0、左端scalar识别。
- acceptance.02 [covered]：reference允许两端不同常值，未要求相等。

<a id="w03-06"></a>
### W03.06 参数方向导数的统一衰减

**输出：** 对共同参数邻域中光滑的Xγ值映射，逐个固定参数微分得到同样mixed jet极限。

**局部依赖：** W03.01, W03.02, W03.03。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“参数方向导数的统一衰减”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 所需Banach级参数导数界在紧参数子区间统一。
- 不能为每个输出阶重选参数区间。

**本轮核对：** 未找到“参数方向导数的统一衰减”对应的实际项目声明。未从实际weighted Sobolev得到本项uniform mixed jets或参数延拓，通用一变量结果不自动实例化。

**未完成内容：**
- 尚待实际实现并证明：对共同参数邻域中光滑的Xγ值映射，逐个固定参数微分得到同样mixed jet极限。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：所需Banach级参数导数界在紧参数子区间统一。
- acceptance.02 [uncovered]：本条尚无对应实际输出：不能为每个输出阶重选参数区间。

<a id="w03-07"></a>
### W03.07 联合参数与空间的延拓光滑性

**输出：** 证明参数值延拓映射与逐阶微分交换，得到θ/q/r联合C∞及两端常值参数族。

**局部依赖：** W03.04, W03.05, W03.06。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“联合参数与空间的延拓光滑性”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 所有参数阶得到同一个实际延拓对象。
- 现有FlatExtension只作为支持，实际weighted Sobolev前提已由前项核验。

**本轮核对：** 未找到“联合参数与空间的延拓光滑性”对应的实际项目声明。未从实际weighted Sobolev得到本项uniform mixed jets或参数延拓，通用一变量结果不自动实例化。

**未完成内容：**
- 尚待实际实现并证明：证明参数值延拓映射与逐阶微分交换，得到θ/q/r联合C∞及两端常值参数族。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：所有参数阶得到同一个实际延拓对象。
- acceptance.02 [uncovered]：本条尚无对应实际输出：现有FlatExtension只作为支持，实际weighted Sobolev前提已由前项核验。

<a id="w03-08"></a>
### W03.08 组装：正指数弱空间的全阶平坦延拓

**输出：** γ>0且u∈Xγ⁰蕴含任意a,b,k下d∂^(-k)∂r^a∂θ^b u→0，零延拓C∞；Xγ则两端分别常值延拓，参数导数同样成立。

**局部依赖：** W03.01, W03.02, W03.03, W03.04, W03.05, W03.06, W03.07。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 100–250 行。已有子结论的接口组装与完整量词核对；不把尚未证明的子结论作为新假设。

**验收条件：**

- 不是只证明值趋零
- 左右常数不要求相等
- 共同参数邻域内的参数导数也覆盖
- 逐项调用以上子任务的实际结论；所有见证、范数、参数和允许依赖与原节点一致。

**本轮核对：** 普通一变量导数极限推出C∞延拓的通用结果已证；weighted Sobolev→全部r/θ/q uniform jets桥接未实现。

**源码证据 `ContinuousFlexibility/Analysis/FlatExtension.lean`：** `ContinuousFlexibility.Analysis.contDiff_extendZeroOutside`, `ContinuousFlexibility.Analysis.iteratedDeriv_extendZeroOutside`, `ContinuousFlexibility.Analysis.iteratedDeriv_extendZeroOutside_eq_zero`

任意实范数值域的一变量真实C∞零延拓和普通jets=0；实际两端导数极限仍为前提，未实例化到角向Cᵇ/Sobolev。

**源码证据 `ContinuousFlexibility/Analysis/FlatExtension.lean`：** `ContinuousFlexibility.Analysis.extendByReference`, `ContinuousFlexibility.Analysis.contDiff_extendByReference`, `ContinuousFlexibility.Analysis.extendByReference_of_mem`, `ContinuousFlexibility.Analysis.extendByReference_of_notMem`, `ContinuousFlexibility.Analysis.iteratedDeriv_extendByReference_eq`

任意全球光滑参考的实际延拓与其外部所有jets相同；允许参考在两端取不同常值，不给实际Xγ/χL空间。

**未完成内容：**
- 由实际Xγ范数推出全部weighted mixed jets极限。
- 完成角变量与共同参数区间的联合延拓和微分交换。

**逐条验收：**
- acceptance.01 [partial]：已覆盖一变量全部普通导数，不是只值趋零；但实际空间的前提未验证。
- acceptance.02 [covered]：不同端常值可由同一光滑reference覆盖。
- acceptance.03 [uncovered]：无共同q邻域的实际统一Banach值导数极限。
- acceptance.04 [partial]：仅通用延拓部件，实际weighted应用未齐。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：γ>0且u∈Xγ⁰蕴含任意a,b,k下d∂^(-k)∂r^a∂θ^b u→0，零延拓C∞；Xγ则两端分别常值延拓，参数导数同样成立。 | W03.08（组合全部子任务） |
| acceptance.01：不是只证明值趋零 | W03.01, W03.02, W03.03, W03.04 |
| acceptance.02：左右常数不要求相等 | W03.05 |
| acceptance.03：共同参数邻域内的参数导数也覆盖 | W03.06, W03.07 |
| remaining.01：实际weighted Sobolev估计推出全部普通径向导数极限 | W03.01, W03.02, W03.03 |
| remaining.02：联合θ/q光滑需要实际uniform/Banach-valued导数范数控制，尚未由论文权函数实例化 | W03.04, W03.06, W03.07 |

<a id="n01"></a>
## N01 共同低阶几何邻域

**原节点完整目标：** 存在固定b₀,ε₀,d*，使所有分量在n_{b₀}<ε₀上同时满足w/w*∈[1/2,2]、Q/w∈[7/8,9/8]、D∈[1/2,3/2]；根点germs不变，原物理系数及普通特征流的各阶变分/差具有H_m^βℰ_m^{C_s}界。根正则坐标及三阶除后系数的jet界另由N04证明。

**原上游里程碑：** R12, W01, W02, S05

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [07-fixed-geometry.tex:208–338](../../paper/flexible-surface-rewrite/07-fixed-geometry.tex#L208)

<a id="n01-01"></a>
### N01.01 固定低阶状态范数

**输出：** 把u−Φ*、ν、κ和chart变量放入实际共同状态空间，定义单一低阶n_b。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“固定低阶状态范数”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- u−Φ*不乘q，避免q=0时失去状态控制。
- 状态空间及slice使用真实W02和R12接口。

**本轮核对：** 未找到“固定低阶状态范数”对应的实际项目声明。未构造真实四未知量状态、共同低阶安全邻域或全组件变分界。

**未完成内容：**
- 尚待实际实现并证明：把u−Φ*、ν、κ和chart变量放入实际共同状态空间，定义单一低阶n_b。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：u−Φ*不乘q，避免q=0时失去状态控制。
- acceptance.02 [uncovered]：本条尚无对应实际输出：状态空间及slice使用真实W02和R12接口。

<a id="n01-02"></a>
### N01.02 一次选择点态安全邻域

**输出：** 用固定阶Sobolev嵌入选b₀,ε₀，使w/w*、Q/w、D同时落入论文闭区间。

**局部依赖：** N01.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“一次选择点态安全邻域”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 实际得到[1/2,2]、[7/8,9/8]、[1/2,3/2]。
- b₀、ε₀与输出阶s无关。

**本轮核对：** 未找到“一次选择点态安全邻域”对应的实际项目声明。未构造真实四未知量状态、共同低阶安全邻域或全组件变分界。

**未完成内容：**
- 尚待实际实现并证明：用固定阶Sobolev嵌入选b₀,ε₀，使w/w*、Q/w、D同时落入论文闭区间。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：实际得到[1/2,2]、[7/8,9/8]、[1/2,3/2]。
- acceptance.02 [uncovered]：本条尚无对应实际输出：b₀、ε₀与输出阶s无关。

<a id="n01-03"></a>
### N01.03 原profile的根germ保留

**输出：** 证明所有控制在根圈附近消失，且共同邻域保持其余区域符号及简单根。

**局部依赖：** N01.01, N01.02。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“原profile的根germ保留”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 证明根的位置与完整径向germ同参考。
- 不能预用N04的根正则坐标。

**本轮核对：** 未找到“原profile的根germ保留”对应的实际项目声明。未构造真实四未知量状态、共同低阶安全邻域或全组件变分界。

**未完成内容：**
- 尚待实际实现并证明：证明所有控制在根圈附近消失，且共同邻域保持其余区域符号及简单根。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：证明根的位置与完整径向germ同参考。
- acceptance.02 [uncovered]：本条尚无对应实际输出：不能预用N04的根正则坐标。

<a id="n01-04"></a>
### N01.04 原物理系数的高阶差界

**输出：** 从真实w,z残差系数公式证明各阶状态差和参数变分有H_m^βℰ_m^{C_s}界。

**局部依赖：** N01.02, N01.03。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“原物理系数的高阶差界”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 全部倒数由同一安全邻域支付。
- 完整系数乘积损失合并，不让base随s变化。

**本轮核对：** 未找到“原物理系数的高阶差界”对应的实际项目声明。未构造真实四未知量状态、共同低阶安全邻域或全组件变分界。

**未完成内容：**
- 尚待实际实现并证明：从真实w,z残差系数公式证明各阶状态差和参数变分有H_m^βℰ_m^{C_s}界。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：全部倒数由同一安全邻域支付。
- acceptance.02 [uncovered]：本条尚无对应实际输出：完整系数乘积损失合并，不让base随s变化。

<a id="n01-05"></a>
### N01.05 普通特征流的存在与单调

**输出：** 在未做根正则化的普通特征时间上构造同一两支流，证明角向导数严格正。

**局部依赖：** N01.02, N01.03, N01.04。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“普通特征流的存在与单调”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 给出全部组件和允许state统一的流存在区间。
- 角变量π-equivariance与奇偶对称由真实ODE传播。

**本轮核对：** 未找到“普通特征流的存在与单调”对应的实际项目声明。未构造真实四未知量状态、共同低阶安全邻域或全组件变分界。

**未完成内容：**
- 尚待实际实现并证明：在未做根正则化的普通特征时间上构造同一两支流，证明角向导数严格正。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：给出全部组件和允许state统一的流存在区间。
- acceptance.02 [uncovered]：本条尚无对应实际输出：角变量π-equivariance与奇偶对称由真实ODE传播。

<a id="n01-06"></a>
### N01.06 特征流状态微分方程

**输出：** 逐阶微分真实ODE得到流对状态和参数的变分方程。

**局部依赖：** N01.05。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“特征流状态微分方程”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 非线性系数方向微分按H01定义。
- 所有方程初值与周期条件明确。

**本轮核对：** 未找到“特征流状态微分方程”对应的实际项目声明。未构造真实四未知量状态、共同低阶安全邻域或全组件变分界。

**未完成内容：**
- 尚待实际实现并证明：逐阶微分真实ODE得到流对状态和参数的变分方程。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：非线性系数方向微分按H01定义。
- acceptance.02 [uncovered]：本条尚无对应实际输出：所有方程初值与周期条件明确。

<a id="n01-07"></a>
### N01.07 流及逆流的固定损失估计

**输出：** 用实际变分方程和逆映射等式证明普通流/逆的高阶差界及tame性。

**局部依赖：** N01.04, N01.05, N01.06。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“流及逆流的固定损失估计”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- ∀s存在C_s，但同一b₀,ε₀,d*保持不变。
- 不把N04三阶除后系数估计反向当作本项输入。

**本轮核对：** 未找到“流及逆流的固定损失估计”对应的实际项目声明。未构造真实四未知量状态、共同低阶安全邻域或全组件变分界。

**未完成内容：**
- 尚待实际实现并证明：用实际变分方程和逆映射等式证明普通流/逆的高阶差界及tame性。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：∀s存在C_s，但同一b₀,ε₀,d*保持不变。
- acceptance.02 [uncovered]：本条尚无对应实际输出：不把N04三阶除后系数估计反向当作本项输入。

<a id="n01-08"></a>
### N01.08 全组件统一的邻域量词

**输出：** 汇总所有原系数、普通流及根germ的常数允许依赖，证明单一邻域支持全部阶。

**局部依赖：** N01.02, N01.03, N01.04, N01.07。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“全组件统一的邻域量词”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 实际量词为∃b₀ ε₀ d* ∀s ∃C_s。
- 记录参考几何已经冻结，不因高阶要求重选N或单元。

**本轮核对：** 未找到“全组件统一的邻域量词”对应的实际项目声明。未构造真实四未知量状态、共同低阶安全邻域或全组件变分界。

**未完成内容：**
- 尚待实际实现并证明：汇总所有原系数、普通流及根germ的常数允许依赖，证明单一邻域支持全部阶。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：实际量词为∃b₀ ε₀ d* ∀s ∃C_s。
- acceptance.02 [uncovered]：本条尚无对应实际输出：记录参考几何已经冻结，不因高阶要求重选N或单元。

<a id="n01-09"></a>
### N01.09 组装：共同低阶几何邻域

**输出：** 存在固定b₀,ε₀,d*，使所有分量在n_{b₀}<ε₀上同时满足w/w*∈[1/2,2]、Q/w∈[7/8,9/8]、D∈[1/2,3/2]；根点germs不变，原物理系数及普通特征流的各阶变分/差具有H_m^βℰ_m^{C_s}界。根正则坐标及三阶除后系数的jet界另由N04证明。

**局部依赖：** N01.01, N01.02, N01.03, N01.04, N01.05, N01.06, N01.07, N01.08。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 100–250 行。已有子结论的接口组装与完整量词核对；不把尚未证明的子结论作为新假设。

**验收条件：**

- n_s包含未乘q的u−Φ*
- 量词∃b₀,ε₀,d*∀s∃C_s
- 不得每个s重选邻域半径
- 逐项调用以上子任务的实际结论；所有见证、范数、参数和允许依赖与原节点一致。

**本轮核对：** 未找到“组装：共同低阶几何邻域”对应的实际项目声明。未构造真实四未知量状态、共同低阶安全邻域或全组件变分界。

**未完成内容：**
- 尚待实际实现并证明：存在固定b₀,ε₀,d*，使所有分量在n_{b₀}<ε₀上同时满足w/w*∈[1/2,2]、Q/w∈[7/8,9/8]、D∈[1/2,3/2]；根点germs不变，原物理系数及普通特征流的各阶变分/差具有H_m^βℰ_m^{C_s}界。根正则坐标及三阶除后系数的jet界另由N04证明。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：n_s包含未乘q的u−Φ*
- acceptance.02 [uncovered]：本条尚无对应实际输出：量词∃b₀,ε₀,d*∀s∃C_s
- acceptance.03 [uncovered]：本条尚无对应实际输出：不得每个s重选邻域半径
- acceptance.04 [uncovered]：本条尚无对应实际输出：逐项调用以上子任务的实际结论；所有见证、范数、参数和允许依赖与原节点一致。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：存在固定b₀,ε₀,d*，使所有分量在n_{b₀}<ε₀上同时满足w/w*∈[1/2,2]、Q/w∈[7/8,9/8]、D∈[1/2,3/2]；根点germs不变，原物理系数及普通特征流的各阶变分/差具有H_m^βℰ_m^{C_s}界。根正则坐标及三阶除后系数的jet界另由N04证明。 | N01.09（组合全部子任务） |
| acceptance.01：n_s包含未乘q的u−Φ* | N01.01 |
| acceptance.02：量词∃b₀,ε₀,d*∀s∃C_s | N01.02, N01.04, N01.07, N01.08 |
| acceptance.03：不得每个s重选邻域半径 | N01.02, N01.07, N01.08 |

<a id="n02"></a>
## N02 圆返回残差与小除数逆

**原节点完整目标：** 从真实特征流构造边界chart和返回残差e；e=0等价于两支返回均为固定旋转。证明D_he=M_T+Q_h，及正偶频零均值sector上的M_T逆和固定损失估计。

**原上游里程碑：** R12, N01, W02

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [07-fixed-geometry.tex:341–389](../../paper/flexible-surface-rewrite/07-fixed-geometry.tex#L341)

<a id="n02-01"></a>
### N02.01 实际边界chart与两支返回

**输出：** 从N01同一特征流构造f_±、hL,hR及返回残差e。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“实际边界chart与两支返回”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 同时定义两支而非仅一支旋转。
- 所有chart保持增加、奇性与π-equivariance。

**本轮核对：** 未找到“实际边界chart与两支返回”对应的实际项目声明。未构造实际特征返回e、边界chart或M_T圆逆。

**未完成内容：**
- 尚待实际实现并证明：从N01同一特征流构造f_±、hL,hR及返回残差e。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：同时定义两支而非仅一支旋转。
- acceptance.02 [uncovered]：本条尚无对应实际输出：所有chart保持增加、奇性与π-equivariance。

<a id="n02-02"></a>
### N02.02 零残差与固定返回等价

**输出：** 证明e=0恰等价hR f_± hL⁻¹=R_{±T}的两条精确等式。

**局部依赖：** N02.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“零残差与固定返回等价”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- T使用R12同一真实旅行角。
- 没有只得到一阶近似的返回。

**本轮核对：** 未找到“零残差与固定返回等价”对应的实际项目声明。未构造实际特征返回e、边界chart或M_T圆逆。

**未完成内容：**
- 尚待实际实现并证明：证明e=0恰等价hR f_± hL⁻¹=R_{±T}的两条精确等式。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：T使用R12同一真实旅行角。
- acceptance.02 [uncovered]：本条尚无对应实际输出：没有只得到一阶近似的返回。

<a id="n02-03"></a>
### N02.03 角均值与非零频率分解

**输出：** 在圆序列空间定义均值/零均值连续tame投影，识别chart变分的sector。

**局部依赖：** N02.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“角均值与非零频率分解”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 常数频率留给径向控制变量。
- 实偶残差与奇chart增量的变换规则明确。

**本轮核对：** 未找到“角均值与非零频率分解”对应的实际项目声明。未构造实际特征返回e、边界chart或M_T圆逆。

**未完成内容：**
- 尚待实际实现并证明：在圆序列空间定义均值/零均值连续tame投影，识别chart变分的sector。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：常数频率留给径向控制变量。
- acceptance.02 [uncovered]：本条尚无对应实际输出：实偶残差与奇chart增量的变换规则明确。

<a id="n02-04"></a>
### N02.04 chart导数的真实展开

**输出：** 对实际组合路径求D_he，分解为固定M_T和显式残差因子的Q_h。

**局部依赖：** N02.01, N02.02。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“chart导数的真实展开”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- chart实际方向为v∘hL。
- 误差表达保留真实state路径，供独立残差替换。

**本轮核对：** 未找到“chart导数的真实展开”对应的实际项目声明。未构造实际特征返回e、边界chart或M_T圆逆。

**未完成内容：**
- 尚待实际实现并证明：对实际组合路径求D_he，分解为固定M_T和显式残差因子的Q_h。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：chart实际方向为v∘hL。
- acceptance.02 [uncovered]：本条尚无对应实际输出：误差表达保留真实state路径，供独立残差替换。

<a id="n02-05"></a>
### N02.05 旋转差算子的频率符号

**输出：** 计算M_T在每个正偶频率上的实际Fourier乘子和相应核。

**局部依赖：** N02.03, N02.04。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“旋转差算子的频率符号”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 零频率从定义域剔除。
- 符号归一化和两支旋转的正负号核对。

**本轮核对：** 未找到“旋转差算子的频率符号”对应的实际项目声明。未构造实际特征返回e、边界chart或M_T圆逆。

**未完成内容：**
- 尚待实际实现并证明：计算M_T在每个正偶频率上的实际Fourier乘子和相应核。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：零频率从定义域剔除。
- acceptance.02 [uncovered]：本条尚无对应实际输出：符号归一化和两支旋转的正负号核对。

<a id="n02-06"></a>
### N02.06 小除数逆的固定损失界

**输出：** 使用真实T的小除数下界构造M_T⁻¹并证明圆序列各阶固定损失估计。

**局部依赖：** N02.03, N02.05。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“小除数逆的固定损失界”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 全部正偶频率同时受同一参考几何控制。
- 无限Fourier级数在实际加权空间收敛。

**本轮核对：** 未找到“小除数逆的固定损失界”对应的实际项目声明。未构造实际特征返回e、边界chart或M_T圆逆。

**未完成内容：**
- 尚待实际实现并证明：使用真实T的小除数下界构造M_T⁻¹并证明圆序列各阶固定损失估计。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：全部正偶频率同时受同一参考几何控制。
- acceptance.02 [uncovered]：本条尚无对应实际输出：无限Fourier级数在实际加权空间收敛。

<a id="n02-07"></a>
### N02.07 双侧逆与实际圆方程

**输出：** 证明M_T M_T⁻¹和M_T⁻¹ M_T在指定零均值sector为恒等映射。

**局部依赖：** N02.06。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“双侧逆与实际圆方程”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 从Fourier系数相等回到真实圆函数相等。
- 输出chart的奇性及π-equivariance保留。

**本轮核对：** 未找到“双侧逆与实际圆方程”对应的实际项目声明。未构造实际特征返回e、边界chart或M_T圆逆。

**未完成内容：**
- 尚待实际实现并证明：证明M_T M_T⁻¹和M_T⁻¹ M_T在指定零均值sector为恒等映射。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：从Fourier系数相等回到真实圆函数相等。
- acceptance.02 [uncovered]：本条尚无对应实际输出：输出chart的奇性及π-equivariance保留。

<a id="n02-08"></a>
### N02.08 chart组合路径smooth tame

**输出：** 证明边界chart、返回残差及Q_h所用固定路径在共同低阶邻域smooth tame。

**局部依赖：** N02.01, N02.04, N02.06, N02.07。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“chart组合路径smooth tame”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 所有逆chart分母由固定低阶增加性控制。
- 邻域不因输出阶变化而缩小。

**本轮核对：** 未找到“chart组合路径smooth tame”对应的实际项目声明。未构造实际特征返回e、边界chart或M_T圆逆。

**未完成内容：**
- 尚待实际实现并证明：证明边界chart、返回残差及Q_h所用固定路径在共同低阶邻域smooth tame。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：所有逆chart分母由固定低阶增加性控制。
- acceptance.02 [uncovered]：本条尚无对应实际输出：邻域不因输出阶变化而缩小。

<a id="n02-09"></a>
### N02.09 组装：圆返回残差与小除数逆

**输出：** 从真实特征流构造边界chart和返回残差e；e=0等价于两支返回均为固定旋转。证明D_he=M_T+Q_h，及正偶频零均值sector上的M_T逆和固定损失估计。

**局部依赖：** N02.01, N02.02, N02.03, N02.04, N02.05, N02.06, N02.07, N02.08。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 100–250 行。已有子结论的接口组装与完整量词核对；不把尚未证明的子结论作为新假设。

**验收条件：**

- 常数频率由径向控制处理
- 返回等式包含两支特征
- chart增加性及组合路径的smooth tame性
- 逐项调用以上子任务的实际结论；所有见证、范数、参数和允许依赖与原节点一致。

**本轮核对：** 未找到“组装：圆返回残差与小除数逆”对应的实际项目声明。未构造实际特征返回e、边界chart或M_T圆逆。

**未完成内容：**
- 尚待实际实现并证明：从真实特征流构造边界chart和返回残差e；e=0等价于两支返回均为固定旋转。证明D_he=M_T+Q_h，及正偶频零均值sector上的M_T逆和固定损失估计。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：常数频率由径向控制处理
- acceptance.02 [uncovered]：本条尚无对应实际输出：返回等式包含两支特征
- acceptance.03 [uncovered]：本条尚无对应实际输出：chart增加性及组合路径的smooth tame性
- acceptance.04 [uncovered]：本条尚无对应实际输出：逐项调用以上子任务的实际结论；所有见证、范数、参数和允许依赖与原节点一致。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：从真实特征流构造边界chart和返回残差e；e=0等价于两支返回均为固定旋转。证明D_he=M_T+Q_h，及正偶频零均值sector上的M_T逆和固定损失估计。 | N02.09（组合全部子任务） |
| acceptance.01：常数频率由径向控制处理 | N02.03, N02.05, N02.06 |
| acceptance.02：返回等式包含两支特征 | N02.01, N02.02 |
| acceptance.03：chart增加性及组合路径的smooth tame性 | N02.01, N02.08 |

<a id="n03"></a>
## N03 固定特征返回的残差修正

**原节点完整目标：** 构造对称散度算子L̂，与L̄同法向主系数a、同根点germs及界面通量，正区间不变，返回精确固定。内部混合系数b一般改变，不声称全局法向通量相同。L̄−L̂=E_x(e)，对独立(e,η)为smooth tame双线性映射且输出兼容源。

**原上游里程碑：** N01, N02, W02, S05

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [07-fixed-geometry.tex:391–458](../../paper/flexible-surface-rewrite/07-fixed-geometry.tex#L391)

<a id="n03-01"></a>
### N03.01 独立返回残差的修正公式

**输出：** 固定实际state的流和复合路径，定义对独立圆残差e线性的系数修正。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“独立返回残差的修正公式”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 替换的只有显式e/e′因素。
- 公式在任意独立e上有定义，不限e=e(state)。

**本轮核对：** 未找到“独立返回残差的修正公式”对应的实际项目声明。未构造返回修正L̂或独立返回残差双线性E_x。

**未完成内容：**
- 尚待实际实现并证明：固定实际state的流和复合路径，定义对独立圆残差e线性的系数修正。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：替换的只有显式e/e′因素。
- acceptance.02 [uncovered]：本条尚无对应实际输出：公式在任意独立e上有定义，不限e=e(state)。

<a id="n03-02"></a>
### N03.02 修正支持与正区间不变

**输出：** 证明修正局限于指定负分量内部，并在根collar及正分量严格为零。

**局部依赖：** N03.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“修正支持与正区间不变”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 对两支特征的同一个修正定义检查支持。
- 全部根germ与原参考相合。

**本轮核对：** 未找到“修正支持与正区间不变”对应的实际项目声明。未构造返回修正L̂或独立返回残差双线性E_x。

**未完成内容：**
- 尚待实际实现并证明：证明修正局限于指定负分量内部，并在根collar及正分量严格为零。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：对两支特征的同一个修正定义检查支持。
- acceptance.02 [uncovered]：本条尚无对应实际输出：全部根germ与原参考相合。

<a id="n03-03"></a>
### N03.03 法向主系数保持

**输出：** 由修正公式证明â=a，写出混合系数b̂和角系数ĉ的实际变化。

**局部依赖：** N03.01, N03.02。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“法向主系数保持”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 明确b一般改变。
- 不把界面相同通量误写为全域相同通量。

**本轮核对：** 未找到“法向主系数保持”对应的实际项目声明。未构造返回修正L̂或独立返回残差双线性E_x。

**未完成内容：**
- 尚待实际实现并证明：由修正公式证明â=a，写出混合系数b̂和角系数ĉ的实际变化。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：明确b一般改变。
- acceptance.02 [uncovered]：本条尚无对应实际输出：不把界面相同通量误写为全域相同通量。

<a id="n03-04"></a>
### N03.04 精确固定返回

**输出：** 代入修正后的实际特征方程证明其返回严格等于指定旋转。

**局部依赖：** N03.01, N03.02, N03.03。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“精确固定返回”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 两支返回都成立。
- 结论是精确恒等式，非线性余项没有省略。

**本轮核对：** 未找到“精确固定返回”对应的实际项目声明。未构造返回修正L̂或独立返回残差双线性E_x。

**未完成内容：**
- 尚待实际实现并证明：代入修正后的实际特征方程证明其返回严格等于指定旋转。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：两支返回都成立。
- acceptance.02 [uncovered]：本条尚无对应实际输出：结论是精确恒等式，非线性余项没有省略。

<a id="n03-05"></a>
### N03.05 对称散度及界面通量

**输出：** 证明L̂为真实对称散度算子，且修正支持外及各界面保持原conormal通量。

**局部依赖：** N03.02, N03.03。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“对称散度及界面通量”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 对角变量和径向变量的积分分部定义一致。
- 界面通量与N04将采用的传递配对匹配。

**本轮核对：** 未找到“对称散度及界面通量”对应的实际项目声明。未构造返回修正L̂或独立返回残差双线性E_x。

**未完成内容：**
- 尚待实际实现并证明：证明L̂为真实对称散度算子，且修正支持外及各界面保持原conormal通量。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：对角变量和径向变量的积分分部定义一致。
- acceptance.02 [uncovered]：本条尚无对应实际输出：界面通量与N04将采用的传递配对匹配。

<a id="n03-06"></a>
### N03.06 独立双线性误差算子

**输出：** 定义E_x(e)η=L̄η−L̂η的独立残差线性扩展，并证明对(e,η)双线性。

**局部依赖：** N03.01, N03.03, N03.05。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“独立双线性误差算子”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 原恒等式在e=e(state)处真实成立。
- 不以范数O(||e||||η||)替代双线性恒等式。

**本轮核对：** 未找到“独立双线性误差算子”对应的实际项目声明。未构造返回修正L̂或独立返回残差双线性E_x。

**未完成内容：**
- 尚待实际实现并证明：定义E_x(e)η=L̄η−L̂η的独立残差线性扩展，并证明对(e,η)双线性。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：原恒等式在e=e(state)处真实成立。
- acceptance.02 [uncovered]：本条尚无对应实际输出：不以范数O(||e||||η||)替代双线性恒等式。

<a id="n03-07"></a>
### N03.07 修正误差的源兼容

**输出：** 证明E_x(e)η的物理积分为零且保持实偶半周期sector。

**局部依赖：** N03.02, N03.05, N03.06。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“修正误差的源兼容”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 全部端点通量因支持/平坦性真实消失。
- Jacobian和dr dθ测度未在换元中遗漏。

**本轮核对：** 未找到“修正误差的源兼容”对应的实际项目声明。未构造返回修正L̂或独立返回残差双线性E_x。

**未完成内容：**
- 尚待实际实现并证明：证明E_x(e)η的物理积分为零且保持实偶半周期sector。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：全部端点通量因支持/平坦性真实消失。
- acceptance.02 [uncovered]：本条尚无对应实际输出：Jacobian和dr dθ测度未在换元中遗漏。

<a id="n03-08"></a>
### N03.08 修正族的固定损失tame界

**输出：** 对独立e和η以及全部state方向导数证明E_x smooth tame双线性。

**局部依赖：** N03.01, N03.06, N03.07。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“修正族的固定损失tame界”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 每个输出阶至多一个高阶因子。
- 使用同一个N01低阶邻域及固定loss预算。

**本轮核对：** 未找到“修正族的固定损失tame界”对应的实际项目声明。未构造返回修正L̂或独立返回残差双线性E_x。

**未完成内容：**
- 尚待实际实现并证明：对独立e和η以及全部state方向导数证明E_x smooth tame双线性。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：每个输出阶至多一个高阶因子。
- acceptance.02 [uncovered]：本条尚无对应实际输出：使用同一个N01低阶邻域及固定loss预算。

<a id="n03-09"></a>
### N03.09 组装：固定特征返回的残差修正

**输出：** 构造对称散度算子L̂，与L̄同法向主系数a、同根点germs及界面通量，正区间不变，返回精确固定。内部混合系数b一般改变，不声称全局法向通量相同。L̄−L̂=E_x(e)，对独立(e,η)为smooth tame双线性映射且输出兼容源。

**局部依赖：** N03.01, N03.02, N03.03, N03.04, N03.05, N03.06, N03.07, N03.08。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 100–250 行。已有子结论的接口组装与完整量词核对；不把尚未证明的子结论作为新假设。

**验收条件：**

- 独立残差变量的线性不是只在e=e(state)成立
- 正区间及根germ不动
- 返回精确固定而非仅一阶近似
- 逐项调用以上子任务的实际结论；所有见证、范数、参数和允许依赖与原节点一致。

**本轮核对：** 未找到“组装：固定特征返回的残差修正”对应的实际项目声明。未构造返回修正L̂或独立返回残差双线性E_x。

**未完成内容：**
- 尚待实际实现并证明：构造对称散度算子L̂，与L̄同法向主系数a、同根点germs及界面通量，正区间不变，返回精确固定。内部混合系数b一般改变，不声称全局法向通量相同。L̄−L̂=E_x(e)，对独立(e,η)为smooth tame双线性映射且输出兼容源。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：独立残差变量的线性不是只在e=e(state)成立
- acceptance.02 [uncovered]：本条尚无对应实际输出：正区间及根germ不动
- acceptance.03 [uncovered]：本条尚无对应实际输出：返回精确固定而非仅一阶近似
- acceptance.04 [uncovered]：本条尚无对应实际输出：逐项调用以上子任务的实际结论；所有见证、范数、参数和允许依赖与原节点一致。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：构造对称散度算子L̂，与L̄同法向主系数a、同根点germs及界面通量，正区间不变，返回精确固定。内部混合系数b一般改变，不声称全局法向通量相同。L̄−L̂=E_x(e)，对独立(e,η)为smooth tame双线性映射且输出兼容源。 | N03.09（组合全部子任务） |
| acceptance.01：独立残差变量的线性不是只在e=e(state)成立 | N03.01, N03.06 |
| acceptance.02：正区间及根germ不动 | N03.02, N03.03, N03.05 |
| acceptance.03：返回精确固定而非仅一阶近似 | N03.04 |

<a id="n04"></a>
## N04 根坐标、正区间拼接与固定transmission

**原节点完整目标：** 证明根点x^(3/2)的even/odd合成固定损失，得到光滑非退化根坐标、同一strip的可逆chart、配对保持；正区间主密度差可除y³(1−y)³，所有算子共享传递条件。对满足分片规范方程、物理源在缝口光滑匹配且满足value/conormal传递的分片光滑解，由方程递推得到全部物理jets匹配。

**原上游里程碑：** N01, N03, W01, W02

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [07-fixed-geometry.tex:462–715](../../paper/flexible-surface-rewrite/07-fixed-geometry.tex#L462)

<a id="n04-01"></a>
### N04.01 根even合成的有限阶Taylor预算

**输出：** 对G(x,λ,θ)的λ-even部分，在x₀>0处写出代入λ=x^{3/2}的Taylor多项式与余项。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“根even合成的有限阶Taylor预算”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 逐项核对x₀幂非负及最高阶余项趋零。
- mixed θ导数扣除相应输入导数预算。

**本轮核对：** 未找到“根even合成的有限阶Taylor预算”对应的实际项目声明。未构造x^(3/2)根合成、固定strip、canonical transmission或三阶除后系数理论。

**未完成内容：**
- 尚待实际实现并证明：对G(x,λ,θ)的λ-even部分，在x₀>0处写出代入λ=x^{3/2}的Taylor多项式与余项。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：逐项核对x₀幂非负及最高阶余项趋零。
- acceptance.02 [uncovered]：本条尚无对应实际输出：mixed θ导数扣除相应输入导数预算。

<a id="n04-02"></a>
### N04.02 even合成的端点延拓及零损失界

**输出：** 证明EG在x=0光滑延拓，且||EG||_{Cˢ}≤C_s||G||_{Cˢ}。

**局部依赖：** N04.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“even合成的端点延拓及零损失界”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 全部固定参数微分与该线性操作交换。
- 实际端点jets由Taylor系数识别。

**本轮核对：** 未找到“even合成的端点延拓及零损失界”对应的实际项目声明。未构造x^(3/2)根合成、固定strip、canonical transmission或三阶除后系数理论。

**未完成内容：**
- 尚待实际实现并证明：证明EG在x=0光滑延拓，且||EG||_{Cˢ}≤C_s||G||_{Cˢ}。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：全部固定参数微分与该线性操作交换。
- acceptance.02 [uncovered]：本条尚无对应实际输出：实际端点jets由Taylor系数识别。

<a id="n04-03"></a>
### N04.03 odd除差积分表达及一阶损失

**输出：** 用K=1/2∫_{−1}¹∂λG(x,tλ,θ)dt表示OG，证明端点值和Cˢ←C^{s+1}界。

**局部依赖：** N04.02。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“odd除差积分表达及一阶损失”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- x=0值为∂λG(0,0,θ)。
- 不把OG当作未定义的x^{−3/2}函数。

**本轮核对：** 未找到“odd除差积分表达及一阶损失”对应的实际项目声明。未构造x^(3/2)根合成、固定strip、canonical transmission或三阶除后系数理论。

**未完成内容：**
- 尚待实际实现并证明：用K=1/2∫_{−1}¹∂λG(x,tλ,θ)dt表示OG，证明端点值和Cˢ←C^{s+1}界。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：x=0值为∂λG(0,0,θ)。
- acceptance.02 [uncovered]：本条尚无对应实际输出：不把OG当作未定义的x^{−3/2}函数。

<a id="n04-04"></a>
### N04.04 两变量根流的共同构造

**输出：** 在独立x,λ上构造固定时间ODE流G，再由±x^{3/2}得到同一边界chart下两支流。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“两变量根流的共同构造”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 原流和独立变量流的时间重标定精确相等。
- 共同boundary chart是even/odd抵消的同一个对象。

**本轮核对：** 未找到“两变量根流的共同构造”对应的实际项目声明。未构造x^(3/2)根合成、固定strip、canonical transmission或三阶除后系数理论。

**未完成内容：**
- 尚待实际实现并证明：在独立x,λ上构造固定时间ODE流G，再由±x^{3/2}得到同一边界chart下两支流。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：原流和独立变量流的时间重标定精确相等。
- acceptance.02 [uncovered]：本条尚无对应实际输出：共同boundary chart是even/odd抵消的同一个对象。

<a id="n04-05"></a>
### N04.05 根坐标的光滑非退化

**输出：** 证明σ=x^{3/2}χ₀、χ₀(0)>0及ξ=x(3χ₀/2)^{2/3}光滑且径向导数非零。

**局部依赖：** N04.02, N04.03, N04.04。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“根坐标的光滑非退化”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 左右根分别处理并保留方向符号。
- 输出使用ContDiff ℝ ∞及统一正下界。

**本轮核对：** 未找到“根坐标的光滑非退化”对应的实际项目声明。未构造x^(3/2)根合成、固定strip、canonical transmission或三阶除后系数理论。

**未完成内容：**
- 尚待实际实现并证明：证明σ=x^{3/2}χ₀、χ₀(0)>0及ξ=x(3χ₀/2)^{2/3}光滑且径向导数非零。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：左右根分别处理并保留方向符号。
- acceptance.02 [uncovered]：本条尚无对应实际输出：输出使用ContDiff ℝ ∞及统一正下界。

<a id="n04-06"></a>
### N04.06 固定strip的全局逆

**输出：** 由Uθ,Vθ>0和det D(σ,φ)>0，证明同一负柱到固定strip的全局光滑双射。

**局部依赖：** N04.04, N04.05。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“固定strip的全局逆”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- σ在固定φ时由0严格增至同一T。
- 局部逆不能替代整柱满射与单射。

**本轮核对：** 未找到“固定strip的全局逆”对应的实际项目声明。未构造x^(3/2)根合成、固定strip、canonical transmission或三阶除后系数理论。

**未完成内容：**
- 尚待实际实现并证明：由Uθ,Vθ>0和det D(σ,φ)>0，证明同一负柱到固定strip的全局光滑双射。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：σ在固定φ时由0严格增至同一T。
- acceptance.02 [uncovered]：本条尚无对应实际输出：局部逆不能替代整柱满射与单射。

<a id="n04-07"></a>
### N04.07 主密度的真实换元

**输出：** 计算散度二次型经Ψ变换后的α diag(1,−ξ)，证明α在根光滑正。

**局部依赖：** N04.05, N04.06。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“主密度的真实换元”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 使用绝对Jacobian及真实坐标导数。
- α=a|detDΨ|/(UθVθ)的根点解释完整。

**本轮核对：** 未找到“主密度的真实换元”对应的实际项目声明。未构造x^(3/2)根合成、固定strip、canonical transmission或三阶除后系数理论。

**未完成内容：**
- 尚待实际实现并证明：计算散度二次型经Ψ变换后的α diag(1,−ξ)，证明α在根光滑正。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：使用绝对Jacobian及真实坐标导数。
- acceptance.02 [uncovered]：本条尚无对应实际输出：α=a|detDΨ|/(UθVθ)的根点解释完整。

<a id="n04-08"></a>
### N04.08 Airy高度共轭与源配对

**输出：** 令h=α^{−1/2}，证明共轭后为∂ξ²−ξ∂φ²+V并给出真实F及积分配对恒等式。

**局部依赖：** N04.07。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“Airy高度共轭与源配对”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 高度因子一阶项真实消去。
- 源F=h(f/|detDΨ|)∘Ψ⁻¹及符号明确。

**本轮核对：** 未找到“Airy高度共轭与源配对”对应的实际项目声明。未构造x^(3/2)根合成、固定strip、canonical transmission或三阶除后系数理论。

**未完成内容：**
- 尚待实际实现并证明：令h=α^{−1/2}，证明共轭后为∂ξ²−ξ∂φ²+V并给出真实F及积分配对恒等式。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：高度因子一阶项真实消去。
- acceptance.02 [uncovered]：本条尚无对应实际输出：源F=h(f/|detDΨ|)∘Ψ⁻¹及符号明确。

<a id="n04-09"></a>
### N04.09 中央切口固定矩阵

**输出：** 计算左右高度因子的值和导数差，得到论文固定2×2中央传递矩阵。

**局部依赖：** N04.06, N04.07, N04.08。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“中央切口固定矩阵”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 矩阵不依赖state。
- ξ_R方向反转导致的符号保留。

**本轮核对：** 未找到“中央切口固定矩阵”对应的实际项目声明。未构造x^(3/2)根合成、固定strip、canonical transmission或三阶除后系数理论。

**未完成内容：**
- 尚待实际实现并证明：计算左右高度因子的值和导数差，得到论文固定2×2中央传递矩阵。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：矩阵不依赖state。
- acceptance.02 [uncovered]：本条尚无对应实际输出：ξ_R方向反转导致的符号保留。

<a id="n04-10"></a>
### N04.10 根圈物理value/conormal识别

**输出：** 证明canonical根值/导数与物理(u,p_in)的精确关系及切向shear消去。

**局部依赖：** N04.05, N04.07, N04.08。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“根圈物理value/conormal识别”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 全Green配对和零模均保留。
- 相邻正负坐标产生同一个物理一阶jet。

**本轮核对：** 未找到“根圈物理value/conormal识别”对应的实际项目声明。未构造x^(3/2)根合成、固定strip、canonical transmission或三阶除后系数理论。

**未完成内容：**
- 尚待实际实现并证明：证明canonical根值/导数与物理(u,p_in)的精确关系及切向shear消去。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：全Green配对和零模均保留。
- acceptance.02 [uncovered]：本条尚无对应实际输出：相邻正负坐标产生同一个物理一阶jet。

<a id="n04-11"></a>
### N04.11 参考chart及逆的全部系数界

**输出：** 对ξ、Ψ⁻¹、α、h、V与源因子证明ℰ_m^{C_s}界及必要下界。

**局部依赖：** N04.05, N04.06, N04.07, N04.08。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“参考chart及逆的全部系数界”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 根collar用显式积分公式，外部用Morse/transition真实下界。
- 全部参数依赖服从已经冻结的参考几何。

**本轮核对：** 未找到“参考chart及逆的全部系数界”对应的实际项目声明。未构造x^(3/2)根合成、固定strip、canonical transmission或三阶除后系数理论。

**未完成内容：**
- 尚待实际实现并证明：对ξ、Ψ⁻¹、α、h、V与源因子证明ℰ_m^{C_s}界及必要下界。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：根collar用显式积分公式，外部用Morse/transition真实下界。
- acceptance.02 [uncovered]：本条尚无对应实际输出：全部参数依赖服从已经冻结的参考几何。

<a id="n04-12"></a>
### N04.12 扰动根chart的固定损失估计

**输出：** 由N01普通流估计和even/odd精确损失，得到根chart及逆全部state导数的tame界。

**局部依赖：** N04.02, N04.03, N04.04, N04.05, N04.06, N04.11。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“扰动根chart的固定损失估计”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 完整系数乘积只成本一个额外M阶。
- 此项实际提供N01未包含的根正则化估计。

**本轮核对：** 未找到“扰动根chart的固定损失估计”对应的实际项目声明。未构造x^(3/2)根合成、固定strip、canonical transmission或三阶除后系数理论。

**未完成内容：**
- 尚待实际实现并证明：由N01普通流估计和even/odd精确损失，得到根chart及逆全部state导数的tame界。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：完整系数乘积只成本一个额外M阶。
- acceptance.02 [uncovered]：本条尚无对应实际输出：此项实际提供N01未包含的根正则化估计。

<a id="n04-13"></a>
### N04.13 正分量参考坐标及高度拼接

**输出：** 构造y∈[0,1]的严格正导数，匹配两端根坐标及高度因子。

**局部依赖：** N04.10, N04.11。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“正分量参考坐标及高度拼接”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 指定root collar总坐标增量<1/4。
- 中间正导数常数及其倒数有ℰ_m幂界。

**本轮核对：** 未找到“正分量参考坐标及高度拼接”对应的实际项目声明。未构造x^(3/2)根合成、固定strip、canonical transmission或三阶除后系数理论。

**未完成内容：**
- 尚待实际实现并证明：构造y∈[0,1]的严格正导数，匹配两端根坐标及高度因子。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：指定root collar总坐标增量<1/4。
- acceptance.02 [uncovered]：本条尚无对应实际输出：中间正导数常数及其倒数有ℰ_m幂界。

<a id="n04-14"></a>
### N04.14 扰动边界jets的cutoff延拓

**输出：** 延拓坐标差的四阶jets及log高度差的三阶jets，并在J*上保持参考不动。

**局部依赖：** N04.12, N04.13。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“扰动边界jets的cutoff延拓”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 使用真实cutoff Taylor多项式。
- 证明相对微分接近、proper和边界degree1给出同一全局diffeomorphism。

**本轮核对：** 未找到“扰动边界jets的cutoff延拓”对应的实际项目声明。未构造x^(3/2)根合成、固定strip、canonical transmission或三阶除后系数理论。

**未完成内容：**
- 尚待实际实现并证明：延拓坐标差的四阶jets及log高度差的三阶jets，并在J*上保持参考不动。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：使用真实cutoff Taylor多项式。
- acceptance.02 [uncovered]：本条尚无对应实际输出：证明相对微分接近、proper和边界degree1给出同一全局diffeomorphism。

<a id="n04-15"></a>
### N04.15 三阶Hadamard除法的真实估计

**输出：** 由F,F′,F″在端点为零证明F/y³的积分表达及固定三阶Sobolev损失界。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“三阶Hadamard除法的真实估计”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- L² rescaling的t^{−1/2}可积性实际证明。
- 左右两端顺次除后仍有统一固定loss。

**本轮核对：** 未找到“三阶Hadamard除法的真实估计”对应的实际项目声明。未构造x^(3/2)根合成、固定strip、canonical transmission或三阶除后系数理论。

**未完成内容：**
- 尚待实际实现并证明：由F,F′,F″在端点为零证明F/y³的积分表达及固定三阶Sobolev损失界。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：L² rescaling的t^{−1/2}可积性实际证明。
- acceptance.02 [uncovered]：本条尚无对应实际输出：左右两端顺次除后仍有统一固定loss。

<a id="n04-16"></a>
### N04.16 正主密度差的三阶消失

**输出：** 核对拼接jets使主密度差到二阶为零，并写P_x−P*=−∂a(d³e^{ab}∂b)+δV。

**局部依赖：** N04.08, N04.13, N04.14, N04.15。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“正主密度差的三阶消失”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- d=y(1−y)，δV不附加无根据的端点消失条件。
- 正算子采用−L̂的物理符号与canonical源。

**本轮核对：** 未找到“正主密度差的三阶消失”对应的实际项目声明。未构造x^(3/2)根合成、固定strip、canonical transmission或三阶除后系数理论。

**未完成内容：**
- 尚待实际实现并证明：核对拼接jets使主密度差到二阶为零，并写P_x−P*=−∂a(d³e^{ab}∂b)+δV。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：d=y(1−y)，δV不附加无根据的端点消失条件。
- acceptance.02 [uncovered]：本条尚无对应实际输出：正算子采用−L̂的物理符号与canonical源。

<a id="n04-17"></a>
### N04.17 除后系数的固定损失及正下界

**输出：** 证明e^{ab}、δV的全部state/tangential jets界和参考a≥ℰ_m^{−C}、c≥ℰ_m^{−C}d。

**局部依赖：** N04.11, N04.12, N04.14, N04.15, N04.16。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“除后系数的固定损失及正下界”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 近根精确a=1,c=y_i；外部用实际参考profile下界。
- 计入四阶trace、三次除法等全部固定d*。

**本轮核对：** 未找到“除后系数的固定损失及正下界”对应的实际项目声明。未构造x^(3/2)根合成、固定strip、canonical transmission或三阶除后系数理论。

**未完成内容：**
- 尚待实际实现并证明：证明e^{ab}、δV的全部state/tangential jets界和参考a≥ℰ_m^{−C}、c≥ℰ_m^{−C}d。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：近根精确a=1,c=y_i；外部用实际参考profile下界。
- acceptance.02 [uncovered]：本条尚无对应实际输出：计入四阶trace、三次除法等全部固定d*。

<a id="n04-18"></a>
### N04.18 固定传递条件的一阶闭合

**输出：** 统一中央切口与类型根的value/conormal条件，证明与物理一阶匹配等价。

**局部依赖：** N04.09, N04.10, N04.14。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“固定传递条件的一阶闭合”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 所有state共享同一canonical传递矩阵。
- 这一步只声称一阶匹配，不从其单独推出全阶光滑。

**本轮核对：** 未找到“固定传递条件的一阶闭合”对应的实际项目声明。未构造x^(3/2)根合成、固定strip、canonical transmission或三阶除后系数理论。

**未完成内容：**
- 尚待实际实现并证明：统一中央切口与类型根的value/conormal条件，证明与物理一阶匹配等价。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：所有state共享同一canonical传递矩阵。
- acceptance.02 [uncovered]：本条尚无对应实际输出：这一步只声称一阶匹配，不从其单独推出全阶光滑。

<a id="n04-19"></a>
### N04.19 从方程递推全部物理jets

**输出：** 对分片光滑、源物理光滑匹配且满足共同传递的解，由a>0的方程递推所有法向和mixed jets。

**局部依赖：** N04.16, N04.17, N04.18。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“从方程递推全部物理jets”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 每次法向微分后源及系数的匹配前提明确。
- 由全jets匹配证明真实物理C∞拼接。

**本轮核对：** 未找到“从方程递推全部物理jets”对应的实际项目声明。未构造x^(3/2)根合成、固定strip、canonical transmission或三阶除后系数理论。

**未完成内容：**
- 尚待实际实现并证明：对分片光滑、源物理光滑匹配且满足共同传递的解，由a>0的方程递推所有法向和mixed jets。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：每次法向微分后源及系数的匹配前提明确。
- acceptance.02 [uncovered]：本条尚无对应实际输出：由全jets匹配证明真实物理C∞拼接。

<a id="n04-20"></a>
### N04.20 组装：根坐标、正区间拼接与固定transmission

**输出：** 证明根点x^(3/2)的even/odd合成固定损失，得到光滑非退化根坐标、同一strip的可逆chart、配对保持；正区间主密度差可除y³(1−y)³，所有算子共享传递条件。对满足分片规范方程、物理源在缝口光滑匹配且满足value/conormal传递的分片光滑解，由方程递推得到全部物理jets匹配。

**局部依赖：** N04.01, N04.02, N04.03, N04.04, N04.05, N04.06, N04.07, N04.08, N04.09, N04.10, N04.11, N04.12, N04.13, N04.14, N04.15, N04.16, N04.17, N04.18, N04.19。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 100–250 行。已有子结论的接口组装与完整量词核对；不把尚未证明的子结论作为新假设。

**验收条件：**

- even/odd损失分别按原文精确计数
- 三阶零点除法的连续映射实际证明
- source Jacobian与符号不丢失
- 任意仅满足value/conormal条件的分片field不自动具有高阶jet匹配
- 在此节点证明根正则坐标和三阶除后系数的高阶界，避免N01隐式引用本节点
- 逐项调用以上子任务的实际结论；所有见证、范数、参数和允许依赖与原节点一致。

**本轮核对：** 未找到“组装：根坐标、正区间拼接与固定transmission”对应的实际项目声明。未构造x^(3/2)根合成、固定strip、canonical transmission或三阶除后系数理论。

**未完成内容：**
- 尚待实际实现并证明：证明根点x^(3/2)的even/odd合成固定损失，得到光滑非退化根坐标、同一strip的可逆chart、配对保持；正区间主密度差可除y³(1−y)³，所有算子共享传递条件。对满足分片规范方程、物理源在缝口光滑匹配且满足value/conormal传递的分片光滑解，由方程递推得到全部物理jets匹配。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：even/odd损失分别按原文精确计数
- acceptance.02 [uncovered]：本条尚无对应实际输出：三阶零点除法的连续映射实际证明
- acceptance.03 [uncovered]：本条尚无对应实际输出：source Jacobian与符号不丢失
- acceptance.04 [uncovered]：本条尚无对应实际输出：任意仅满足value/conormal条件的分片field不自动具有高阶jet匹配
- acceptance.05 [uncovered]：本条尚无对应实际输出：在此节点证明根正则坐标和三阶除后系数的高阶界，避免N01隐式引用本节点
- acceptance.06 [uncovered]：本条尚无对应实际输出：逐项调用以上子任务的实际结论；所有见证、范数、参数和允许依赖与原节点一致。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：证明根点x^(3/2)的even/odd合成固定损失，得到光滑非退化根坐标、同一strip的可逆chart、配对保持；正区间主密度差可除y³(1−y)³，所有算子共享传递条件。对满足分片规范方程、物理源在缝口光滑匹配且满足value/conormal传递的分片光滑解，由方程递推得到全部物理jets匹配。 | N04.20（组合全部子任务） |
| acceptance.01：even/odd损失分别按原文精确计数 | N04.01, N04.02, N04.03, N04.12 |
| acceptance.02：三阶零点除法的连续映射实际证明 | N04.15, N04.16, N04.17 |
| acceptance.03：source Jacobian与符号不丢失 | N04.07, N04.08, N04.10, N04.16 |
| acceptance.04：任意仅满足value/conormal条件的分片field不自动具有高阶jet匹配 | N04.18, N04.19 |
| acceptance.05：在此节点证明根正则坐标和三阶除后系数的高阶界，避免N01隐式引用本节点 | N04.11, N04.12, N04.15, N04.17 |

<a id="n05"></a>
## N05 增广参考逆和共同闭图域

**原节点完整目标：** 在固定canonical cylinders定义V_{t,s}和aL,μ,λ三个标量，构造任意源上的双侧逆G*；同一个G*的β±ε估计给固定M损失。D*=G*(V_{0,b})完备图闭，且识别分布transmission、trace并穷尽admissible smooth fields。

**原上游里程碑：** R12, N04, W02

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [08-stable-inverse.tex:14–171](../../paper/flexible-surface-rewrite/08-stable-inverse.tex#L14)

<a id="n05-01"></a>
### N05.01 canonical源Banach空间

**输出：** 在固定两半负柱和正柱上构造V_{t,s}及其加权直和完备拓扑。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“canonical源Banach空间”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 源不附加界面matching和积分条件。
- 每个索引m的测度和物理算子符号冻结。

**本轮核对：** 未找到“canonical源Banach空间”对应的实际项目声明。未有R12全局参考逆、canonical源及共同闭图域；中央单独谱图不等同此参考逆。

**未完成内容：**
- 尚待实际实现并证明：在固定两半负柱和正柱上构造V_{t,s}及其加权直和完备拓扑。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：源不附加界面matching和积分条件。
- acceptance.02 [uncovered]：本条尚无对应实际输出：每个索引m的测度和物理算子符号冻结。

<a id="n05-02"></a>
### N05.02 增广三scalar及算子列

**输出：** 定义(W,aL,μ,λ)、固定二模slice、s_x,k_x^c,c*并证明真实增广算子公式。

**局部依赖：** N05.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“增广三scalar及算子列”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- aL记录左端常数，右端归零。
- k_x使用真正Dν残差，包含参考高度变化。

**本轮核对：** 未找到“增广三scalar及算子列”对应的实际项目声明。未有R12全局参考逆、canonical源及共同闭图域；中央单独谱图不等同此参考逆。

**未完成内容：**
- 尚待实际实现并证明：定义(W,aL,μ,λ)、固定二模slice、s_x,k_x^c,c*并证明真实增广算子公式。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：aL记录左端常数，右端归零。
- acceptance.02 [uncovered]：本条尚无对应实际输出：k_x使用真正Dν残差，包含参考高度变化。

<a id="n05-03"></a>
### N05.03 源兼容投影与λ恢复

**输出：** 构造连续Q*，证明Q*c*=1并令λ=Q*F把任意源投影成兼容源。

**局部依赖：** N05.01, N05.02。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“源兼容投影与λ恢复”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- Q*与物理Q经实际源变换相合。
- λ不是隐式留作额外方程。

**本轮核对：** 未找到“源兼容投影与λ恢复”对应的实际项目声明。未有R12全局参考逆、canonical源及共同闭图域；中央单独谱图不等同此参考逆。

**未完成内容：**
- 尚待实际实现并证明：构造连续Q*，证明Q*c*=1并令λ=Q*F把任意源投影成兼容源。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：Q*与物理Q经实际源变换相合。
- acceptance.02 [uncovered]：本条尚无对应实际输出：λ不是隐式留作额外方程。

<a id="n05-04"></a>
### N05.04 零模primitive及端点scalar

**输出：** 用两次实际primitive构造零模解，证明除w*不损失端点指数及左端常数恢复。

**局部依赖：** N05.01, N05.02, N05.03。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“零模primitive及端点scalar”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 兼容源总积分为零使两端primitive一致。
- 右端归零、左端aL自由且唯一。

**本轮核对：** 未找到“零模primitive及端点scalar”对应的实际项目声明。未有R12全局参考逆、canonical源及共同闭图域；中央单独谱图不等同此参考逆。

**未完成内容：**
- 尚待实际实现并证明：用两次实际primitive构造零模解，证明除w*不损失端点指数及左端常数恢复。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：兼容源总积分为零使两端primitive一致。
- acceptance.02 [uncovered]：本条尚无对应实际输出：右端归零、左端aL自由且唯一。

<a id="n05-05"></a>
### N05.05 增广参考逆双侧恒等式

**输出：** 用R12兼容逆及零模公式构造G*，证明P*G*=I和G*P*=I。

**局部依赖：** N05.02, N05.03, N05.04。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“增广参考逆双侧恒等式”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 第二个恒等式在真实normalized natural endpoint域成立。
- μ与二模slice一并唯一。

**本轮核对：** 未找到“增广参考逆双侧恒等式”对应的实际项目声明。未有R12全局参考逆、canonical源及共同闭图域；中央单独谱图不等同此参考逆。

**未完成内容：**
- 尚待实际实现并证明：用R12兼容逆及零模公式构造G*，证明P*G*=I和G*P*=I。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：第二个恒等式在真实normalized natural endpoint域成立。
- acceptance.02 [uncovered]：本条尚无对应实际输出：μ与二模slice一并唯一。

<a id="n05-06"></a>
### N05.06 邻近两指数的同一逆

**输出：** 证明β−ε与β+ε逆在共同紧支光滑源上相等，再延拓到所需交叠。

**局部依赖：** N05.05。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“邻近两指数的同一逆”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 使用同一个R12几何、边框及端点条件。
- 差解的normalized齐次唯一性与零模常数均处理。

**本轮核对：** 未找到“邻近两指数的同一逆”对应的实际项目声明。未有R12全局参考逆、canonical源及共同闭图域；中央单独谱图不等同此参考逆。

**未完成内容：**
- 尚待实际实现并证明：证明β−ε与β+ε逆在共同紧支光滑源上相等，再延拓到所需交叠。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：使用同一个R12几何、边框及端点条件。
- acceptance.02 [uncovered]：本条尚无对应实际输出：差解的normalized齐次唯一性与零模常数均处理。

<a id="n05-07"></a>
### N05.07 双权block的定向选择

**输出：** 对π_kG*ι_m按输出/输入S差符号选γ=β±ε，证明共轭后e^{−ε|S_k−S_m|}界。

**局部依赖：** N05.06。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“双权block的定向选择”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 每项ℰ_k^{C_s}ℰ_m^{C_s}保留。
- 两个γ估计作用于前项同一算子。

**本轮核对：** 未找到“双权block的定向选择”对应的实际项目声明。未有R12全局参考逆、canonical源及共同闭图域；中央单独谱图不等同此参考逆。

**未完成内容：**
- 尚待实际实现并证明：对π_kG*ι_m按输出/输入S差符号选γ=β±ε，证明共轭后e^{−ε|S_k−S_m|}界。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：每项ℰ_k^{C_s}ℰ_m^{C_s}保留。
- acceptance.02 [uncovered]：本条尚无对应实际输出：两个γ估计作用于前项同一算子。

<a id="n05-08"></a>
### N05.08 材料权比的指数控制

**输出：** 证明|logM_k−logM_m|≤δ|S_k−S_m|+Cδ，并用固定L吸收全部系数幂。

**局部依赖：** N05.07。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“材料权比的指数控制”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 任意固定实t的权比M_k^{t−L}/M_m^t可控。
- L不随输出角阶s变化。

**本轮核对：** 未找到“材料权比的指数控制”对应的实际项目声明。未有R12全局参考逆、canonical源及共同闭图域；中央单独谱图不等同此参考逆。

**未完成内容：**
- 尚待实际实现并证明：证明|logM_k−logM_m|≤δ|S_k−S_m|+Cδ，并用固定L吸收全部系数幂。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：任意固定实t的权比M_k^{t−L}/M_m^t可控。
- acceptance.02 [uncovered]：本条尚无对应实际输出：L不随输出角阶s变化。

<a id="n05-09"></a>
### N05.09 Schur求和及volume逆界

**输出：** 证明指数block矩阵行列和统一有界，得到全V_{t,s}上G*固定M损失估计。

**局部依赖：** N05.01, N05.07, N05.08。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“Schur求和及volume逆界”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 使用S_n均匀分离及每索引有限pieces。
- 不引入额外角阶损失。

**本轮核对：** 未找到“Schur求和及volume逆界”对应的实际项目声明。未有R12全局参考逆、canonical源及共同闭图域；中央单独谱图不等同此参考逆。

**未完成内容：**
- 尚待实际实现并证明：证明指数block矩阵行列和统一有界，得到全V_{t,s}上G*固定M损失估计。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：使用S_n均匀分离及每索引有限pieces。
- acceptance.02 [uncovered]：本条尚无对应实际输出：不引入额外角阶损失。

<a id="n05-10"></a>
### N05.10 第一normal导数volume估计

**输出：** 结合局部径向方程和相同block求和证明一阶normal估计。

**局部依赖：** N05.04, N05.07, N05.08, N05.09。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“第一normal导数volume估计”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 至多多用一个角向源导数。
- 给出后续weak traces需要的实际局部Sobolev控制。

**本轮核对：** 未找到“第一normal导数volume估计”对应的实际项目声明。未有R12全局参考逆、canonical源及共同闭图域；中央单独谱图不等同此参考逆。

**未完成内容：**
- 尚待实际实现并证明：结合局部径向方程和相同block求和证明一阶normal估计。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：至多多用一个角向源导数。
- acceptance.02 [uncovered]：本条尚无对应实际输出：给出后续weak traces需要的实际局部Sobolev控制。

<a id="n05-11"></a>
### N05.11 图范数域的完备与闭图

**输出：** 定义D*=G*(V_{0,b})及图范数，证明完备并在实际ambient volume空间中闭图。

**局部依赖：** N05.05, N05.09。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“图范数域的完备与闭图”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 图闭使用G*连续与双侧恒等式。
- 本项不把像域完备等同于物理域识别。

**本轮核对：** 未找到“图范数域的完备与闭图”对应的实际项目声明。未有R12全局参考逆、canonical源及共同闭图域；中央单独谱图不等同此参考逆。

**未完成内容：**
- 尚待实际实现并证明：定义D*=G*(V_{0,b})及图范数，证明完备并在实际ambient volume空间中闭图。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：图闭使用G*连续与双侧恒等式。
- acceptance.02 [uncovered]：本条尚无对应实际输出：本项不把像域完备等同于物理域识别。

<a id="n05-12"></a>
### N05.12 紧支光滑源逼近及分布方程

**输出：** 在基本源空间构造实际稠密逼近，并把参考方程传到分布极限。

**局部依赖：** N05.09, N05.10, N05.11。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“紧支光滑源逼近及分布方程”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 极限的source、ambient field和每片分布方程一致。
- canonical源Jacobian未在极限中丢掉。

**本轮核对：** 未找到“紧支光滑源逼近及分布方程”对应的实际项目声明。未有R12全局参考逆、canonical源及共同闭图域；中央单独谱图不等同此参考逆。

**未完成内容：**
- 尚待实际实现并证明：在基本源空间构造实际稠密逼近，并把参考方程传到分布极限。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：极限的source、ambient field和每片分布方程一致。
- acceptance.02 [uncovered]：本条尚无对应实际输出：canonical源Jacobian未在极限中丢掉。

<a id="n05-13"></a>
### N05.13 弱trace与固定transmission识别

**输出：** 用first-normal控制识别D*元素的界面weak traces及全部固定传递。

**局部依赖：** N05.10, N05.12。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“弱trace与固定transmission识别”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 根与中央cut分别检验。
- natural endpoint和二模slice随极限闭合。

**本轮核对：** 未找到“弱trace与固定transmission识别”对应的实际项目声明。未有R12全局参考逆、canonical源及共同闭图域；中央单独谱图不等同此参考逆。

**未完成内容：**
- 尚待实际实现并证明：用first-normal控制识别D*元素的界面weak traces及全部固定传递。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：根与中央cut分别检验。
- acceptance.02 [uncovered]：本条尚无对应实际输出：natural endpoint和二模slice随极限闭合。

<a id="n05-14"></a>
### N05.14 admissible光滑场穷尽

**输出：** 对任意物理admissible光滑场y及source F∈V_{0,b}，证明y−G*F为零齐次场。

**局部依赖：** N05.05, N05.12, N05.13。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“admissible光滑场穷尽”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 使用R12唯一性而非把域定义成像后循环论证。
- 包含全部允许左端常数及normalize约束。

**本轮核对：** 未找到“admissible光滑场穷尽”对应的实际项目声明。未有R12全局参考逆、canonical源及共同闭图域；中央单独谱图不等同此参考逆。

**未完成内容：**
- 尚待实际实现并证明：对任意物理admissible光滑场y及source F∈V_{0,b}，证明y−G*F为零齐次场。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：使用R12唯一性而非把域定义成像后循环论证。
- acceptance.02 [uncovered]：本条尚无对应实际输出：包含全部允许左端常数及normalize约束。

<a id="n05-15"></a>
### N05.15 组装：增广参考逆和共同闭图域

**输出：** 在固定canonical cylinders定义V_{t,s}和aL,μ,λ三个标量，构造任意源上的双侧逆G*；同一个G*的β±ε估计给固定M损失。D*=G*(V_{0,b})完备图闭，且识别分布transmission、trace并穷尽admissible smooth fields。

**局部依赖：** N05.01, N05.02, N05.03, N05.04, N05.05, N05.06, N05.07, N05.08, N05.09, N05.10, N05.11, N05.12, N05.13, N05.14。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 100–250 行。已有子结论的接口组装与完整量词核对；不把尚未证明的子结论作为新假设。

**验收条件：**

- 逆在两指数交叠上确为同一个
- image-domain完备性不替代分布域识别
- 全部光滑admissible fields都在域中
- 逐项调用以上子任务的实际结论；所有见证、范数、参数和允许依赖与原节点一致。

**本轮核对：** 未找到“组装：增广参考逆和共同闭图域”对应的实际项目声明。未有R12全局参考逆、canonical源及共同闭图域；中央单独谱图不等同此参考逆。

**未完成内容：**
- 尚待实际实现并证明：在固定canonical cylinders定义V_{t,s}和aL,μ,λ三个标量，构造任意源上的双侧逆G*；同一个G*的β±ε估计给固定M损失。D*=G*(V_{0,b})完备图闭，且识别分布transmission、trace并穷尽admissible smooth fields。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：逆在两指数交叠上确为同一个
- acceptance.02 [uncovered]：本条尚无对应实际输出：image-domain完备性不替代分布域识别
- acceptance.03 [uncovered]：本条尚无对应实际输出：全部光滑admissible fields都在域中
- acceptance.04 [uncovered]：本条尚无对应实际输出：逐项调用以上子任务的实际结论；所有见证、范数、参数和允许依赖与原节点一致。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：在固定canonical cylinders定义V_{t,s}和aL,μ,λ三个标量，构造任意源上的双侧逆G*；同一个G*的β±ε估计给固定M损失。D*=G*(V_{0,b})完备图闭，且识别分布transmission、trace并穷尽admissible smooth fields。 | N05.15（组合全部子任务） |
| acceptance.01：逆在两指数交叠上确为同一个 | N05.06, N05.07 |
| acceptance.02：image-domain完备性不替代分布域识别 | N05.11, N05.12, N05.13 |
| acceptance.03：全部光滑admissible fields都在域中 | N05.14 |

<a id="n06"></a>
## N06 同一Banach空间的相对小扰动

**原节点完整目标：** R_x=(P_x−P*)G*是同一个V_{0,b}上的有界自同态，范数<1/2；在D*上有分布意义的P_x=(I+R_x)P*。

**原上游里程碑：** N01, N04, N05, W01

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [08-stable-inverse.tex:194–340](../../paper/flexible-surface-rewrite/08-stable-inverse.tex#L194)

<a id="n06-01"></a>
### N06.01 正柱分布解的初步H²正则

**输出：** 对每固定频率的L²解及L² source，由实际常微分方程得到端点H²代表。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“正柱分布解的初步H²正则”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 只为积分分部合法性使用此项。
- 频率一致常数留给后续加权能量估计。

**本轮核对：** 未找到“正柱分布解的初步H²正则”对应的实际项目声明。未有实际P_x、G*、V_{0,b}及同域R_x；普通Banach库结果不构成此项。

**未完成内容：**
- 尚待实际实现并证明：对每固定频率的L²解及L² source，由实际常微分方程得到端点H²代表。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：只为积分分部合法性使用此项。
- acceptance.02 [uncovered]：本条尚无对应实际输出：频率一致常数留给后续加权能量估计。

<a id="n06-02"></a>
### N06.02 任意边界的一阶加权能量

**输出：** 以d²u测试正柱方程，证明||du′||与||j d^{3/2}u||受||F||+||u||控制。

**局部依赖：** N06.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“任意边界的一阶加权能量”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- d=y(1−y)消去边界项，不假定u边界为0。
- 系数上下界和能量实部保留。

**本轮核对：** 未找到“任意边界的一阶加权能量”对应的实际项目声明。未有实际P_x、G*、V_{0,b}及同域R_x；普通Banach库结果不构成此项。

**未完成内容：**
- 尚待实际实现并证明：以d²u测试正柱方程，证明||du′||与||j d^{3/2}u||受||F||+||u||控制。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：d=y(1−y)消去边界项，不假定u边界为0。
- acceptance.02 [uncovered]：本条尚无对应实际输出：系数上下界和能量实部保留。

<a id="n06-03"></a>
### N06.03 d²u的二阶平方恒等式

**输出：** 令v=d²u，用两次分部积分得到v″、j²(c/a)v及j√(c/a)v′的平方估计。

**局部依赖：** N06.01, N06.02。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“d²u的二阶平方恒等式”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- c/a的二阶导数误差由前项统一控制。
- 实际v零trace来自d²而非对u附加边界条件。

**本轮核对：** 未找到“d²u的二阶平方恒等式”对应的实际项目声明。未有实际P_x、G*、V_{0,b}及同域R_x；普通Banach库结果不构成此项。

**未完成内容：**
- 尚待实际实现并证明：令v=d²u，用两次分部积分得到v″、j²(c/a)v及j√(c/a)v′的平方估计。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：c/a的二阶导数误差由前项统一控制。
- acceptance.02 [uncovered]：本条尚无对应实际输出：实际v零trace来自d²而非对u附加边界条件。

<a id="n06-04"></a>
### N06.04 全部cubic扰动项的graph控制

**输出：** 展开v′,v″并证明d³u_yy、d³u_yφ、d³u_φφ及系数导数项均可控。

**局部依赖：** N06.02, N06.03。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“全部cubic扰动项的graph控制”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 交叉normal/angular项用带j的真实范数。
- c≥ℰ_m^{−C}d的退化下界精确计入。

**本轮核对：** 未找到“全部cubic扰动项的graph控制”对应的实际项目声明。未有实际P_x、G*、V_{0,b}及同域R_x；普通Banach库结果不构成此项。

**未完成内容：**
- 尚待实际实现并证明：展开v′,v″并证明d³u_yy、d³u_yφ、d³u_φφ及系数导数项均可控。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：交叉normal/angular项用带j的真实范数。
- acceptance.02 [uncovered]：本条尚无对应实际输出：c≥ℰ_m^{−C}d的退化下界精确计入。

<a id="n06-05"></a>
### N06.05 角向Fourier卷积的相对界

**输出：** 对非径向扰动系数证明论文positive relative bound，保留一高state因子。

**局部依赖：** N06.04。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“角向Fourier卷积的相对界”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 源与高度高低阶分别列出。
- 不得把角向变量可分离误用于非径向系数。

**本轮核对：** 未找到“角向Fourier卷积的相对界”对应的实际项目声明。未有实际P_x、G*、V_{0,b}及同域R_x；普通Banach库结果不构成此项。

**未完成内容：**
- 尚待实际实现并证明：对非径向扰动系数证明论文positive relative bound，保留一高state因子。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：源与高度高低阶分别列出。
- acceptance.02 [uncovered]：本条尚无对应实际输出：不得把角向变量可分离误用于非径向系数。

<a id="n06-06"></a>
### N06.06 负柱相对扰动控制

**输出：** 用固定Airy型规范式及第一normal估计证明负柱扰动对参考graph的同类界。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“负柱相对扰动控制”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 用N04同一canonical chart和固定transmission。
- potential与主项的实际符号一致。

**本轮核对：** 未找到“负柱相对扰动控制”对应的实际项目声明。未有实际P_x、G*、V_{0,b}及同域R_x；普通Banach库结果不构成此项。

**未完成内容：**
- 尚待实际实现并证明：用固定Airy型规范式及第一normal估计证明负柱扰动对参考graph的同类界。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：用N04同一canonical chart和固定transmission。
- acceptance.02 [uncovered]：本条尚无对应实际输出：potential与主项的实际符号一致。

<a id="n06-07"></a>
### N06.07 额外弱权支付固定M损失

**输出：** 把δP系数H_m^βℰ_m^{C_s}与G*固定M损失组合，证明全组件可求和。

**局部依赖：** N06.05, N06.06。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“额外弱权支付固定M损失”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 使用H^βM^A有界和趋零；先冻结loss再选tail。
- 不能因s增长重选已固定参考几何。

**本轮核对：** 未找到“额外弱权支付固定M损失”对应的实际项目声明。未有实际P_x、G*、V_{0,b}及同域R_x；普通Banach库结果不构成此项。

**未完成内容：**
- 尚待实际实现并证明：把δP系数H_m^βℰ_m^{C_s}与G*固定M损失组合，证明全组件可求和。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：使用H^βM^A有界和趋零；先冻结loss再选tail。
- acceptance.02 [uncovered]：本条尚无对应实际输出：不能因s增长重选已固定参考几何。

<a id="n06-08"></a>
### N06.08 同一基本空间有界自同态

**输出：** 证明R_x=(P_x−P*)G*是V_{0,b}→V_{0,b}真实有界线性算子。

**局部依赖：** N06.07。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“同一基本空间有界自同态”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 定义域和值域确为同一个Banach空间。
- 不以带导数损失的scale估计替代本项。

**本轮核对：** 未找到“同一基本空间有界自同态”对应的实际项目声明。未有实际P_x、G*、V_{0,b}及同域R_x；普通Banach库结果不构成此项。

**未完成内容：**
- 尚待实际实现并证明：证明R_x=(P_x−P*)G*是V_{0,b}→V_{0,b}真实有界线性算子。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：定义域和值域确为同一个Banach空间。
- acceptance.02 [uncovered]：本条尚无对应实际输出：不以带导数损失的scale估计替代本项。

<a id="n06-09"></a>
### N06.09 共同低阶邻域的小范数

**输出：** 一次缩小允许的固定低阶state邻域，证明||R_x||<1/2。

**局部依赖：** N06.08。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“共同低阶邻域的小范数”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 缩小只依赖有限阶state范数。
- 所有输出高阶估计继续使用同一个邻域。

**本轮核对：** 未找到“共同低阶邻域的小范数”对应的实际项目声明。未有实际P_x、G*、V_{0,b}及同域R_x；普通Banach库结果不构成此项。

**未完成内容：**
- 尚待实际实现并证明：一次缩小允许的固定低阶state邻域，证明||R_x||<1/2。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：缩小只依赖有限阶state范数。
- acceptance.02 [uncovered]：本条尚无对应实际输出：所有输出高阶估计继续使用同一个邻域。

<a id="n06-10"></a>
### N06.10 Neumann逆的实际构造

**输出：** 在V_{0,b}上由有界小范数构造(I+R_x)⁻¹并证明双侧逆与范数≤2。

**局部依赖：** N06.08, N06.09。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“Neumann逆的实际构造”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- Neumann级数在算子范数实际收敛。
- 逆不作用于不同阶空间之间的导数损失映射。

**本轮核对：** 未找到“Neumann逆的实际构造”对应的实际项目声明。未有实际P_x、G*、V_{0,b}及同域R_x；普通Banach库结果不构成此项。

**未完成内容：**
- 尚待实际实现并证明：在V_{0,b}上由有界小范数构造(I+R_x)⁻¹并证明双侧逆与范数≤2。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：Neumann级数在算子范数实际收敛。
- acceptance.02 [uncovered]：本条尚无对应实际输出：逆不作用于不同阶空间之间的导数损失映射。

<a id="n06-11"></a>
### N06.11 共同域分布因式分解

**输出：** 对全部v∈D*证明P_xv=(I+R_x)P*v，并核对trace和每片分布方程。

**局部依赖：** N06.07, N06.08。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“共同域分布因式分解”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 先在稠密光滑场成立再按共同graph域闭合。
- 因式分解不改动transmission或natural endpoint条件。

**本轮核对：** 未找到“共同域分布因式分解”对应的实际项目声明。未有实际P_x、G*、V_{0,b}及同域R_x；普通Banach库结果不构成此项。

**未完成内容：**
- 尚待实际实现并证明：对全部v∈D*证明P_xv=(I+R_x)P*v，并核对trace和每片分布方程。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：先在稠密光滑场成立再按共同graph域闭合。
- acceptance.02 [uncovered]：本条尚无对应实际输出：因式分解不改动transmission或natural endpoint条件。

<a id="n06-12"></a>
### N06.12 组装：同一Banach空间的相对小扰动

**输出：** R_x=(P_x−P*)G*是同一个V_{0,b}上的有界自同态，范数<1/2；在D*上有分布意义的P_x=(I+R_x)P*。

**局部依赖：** N06.01, N06.02, N06.03, N06.04, N06.05, N06.06, N06.07, N06.08, N06.09, N06.10, N06.11。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 100–250 行。已有子结论的接口组装与完整量词核对；不把尚未证明的子结论作为新假设。

**验收条件：**

- 不得直接对带导数损失的逆用Neumann级数
- 因式分解在共同域上成立
- 低阶邻域不随输出阶数缩小
- 逐项调用以上子任务的实际结论；所有见证、范数、参数和允许依赖与原节点一致。

**本轮核对：** 未找到“组装：同一Banach空间的相对小扰动”对应的实际项目声明。未有实际P_x、G*、V_{0,b}及同域R_x；普通Banach库结果不构成此项。

**未完成内容：**
- 尚待实际实现并证明：R_x=(P_x−P*)G*是同一个V_{0,b}上的有界自同态，范数<1/2；在D*上有分布意义的P_x=(I+R_x)P*。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：不得直接对带导数损失的逆用Neumann级数
- acceptance.02 [uncovered]：本条尚无对应实际输出：因式分解在共同域上成立
- acceptance.03 [uncovered]：本条尚无对应实际输出：低阶邻域不随输出阶数缩小
- acceptance.04 [uncovered]：本条尚无对应实际输出：逐项调用以上子任务的实际结论；所有见证、范数、参数和允许依赖与原节点一致。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：R_x=(P_x−P*)G*是同一个V_{0,b}上的有界自同态，范数<1/2；在D*上有分布意义的P_x=(I+R_x)P*。 | N06.12（组合全部子任务） |
| acceptance.01：不得直接对带导数损失的逆用Neumann级数 | N06.08, N06.09, N06.10 |
| acceptance.02：因式分解在共同域上成立 | N06.11 |
| acceptance.03：低阶邻域不随输出阶数缩小 | N06.07, N06.09 |

<a id="h02"></a>
## H02 逆族smooth tame定理

**原节点完整目标：** 对smooth tame线性族L_x，若每个源有唯一解且逆族已连续、tame，则逆族smooth tame。

**原上游里程碑：** H01

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [08-stable-inverse.tex:523–550](../../paper/flexible-surface-rewrite/08-stable-inverse.tex#L523)

<a id="h02-01"></a>
### H02.01 逆族定理的真实接口

**输出：** 固定H01方向微积分及linear smooth tame L(x)y的精确空间、开集、唯一可解和逆估计假设。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“逆族定理的真实接口”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 逆族连续及tame是待由应用端验证的前提。
- 接口不把逆族smooth作为定义或假设。

**本轮核对：** 未找到“逆族定理的真实接口”对应的实际项目声明。未见固定loss Fréchet尺度的实际逆族smooth tame及导数族；有限维或几何逆不替代本项。

**未完成内容：**
- 尚待实际实现并证明：固定H01方向微积分及linear smooth tame L(x)y的精确空间、开集、唯一可解和逆估计假设。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：逆族连续及tame是待由应用端验证的前提。
- acceptance.02 [uncovered]：本条尚无对应实际输出：接口不把逆族smooth作为定义或假设。

<a id="h02-02"></a>
### H02.02 resolvent差分恒等式

**输出：** 由L(x)V(x)=I和V(x)L(x)=I证明V(x+h)−V(x)=−V(x+h)(L(x+h)−L(x))V(x)。

**局部依赖：** H02.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“resolvent差分恒等式”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 恒等式在全部允许源上成立。
- 检查每次复合的空间与固定阶损失。

**本轮核对：** 未找到“resolvent差分恒等式”对应的实际项目声明。未见固定loss Fréchet尺度的实际逆族smooth tame及导数族；有限维或几何逆不替代本项。

**未完成内容：**
- 尚待实际实现并证明：由L(x)V(x)=I和V(x)L(x)=I证明V(x+h)−V(x)=−V(x+h)(L(x+h)−L(x))V(x)。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：恒等式在全部允许源上成立。
- acceptance.02 [uncovered]：本条尚无对应实际输出：检查每次复合的空间与固定阶损失。

<a id="h02-03"></a>
### H02.03 逆族一阶导数公式

**输出：** 用差商及实际连续性证明DV(x)[h]y=−V(x)(DL(x)[h](V(x)y))。

**局部依赖：** H02.01, H02.02。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“逆族一阶导数公式”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 给出余项在每一所需seminorm中趋零。
- 联合依赖(x,h,y)的连续性由实际估计推出。

**本轮核对：** 未找到“逆族一阶导数公式”对应的实际项目声明。未见固定loss Fréchet尺度的实际逆族smooth tame及导数族；有限维或几何逆不替代本项。

**未完成内容：**
- 尚待实际实现并证明：用差商及实际连续性证明DV(x)[h]y=−V(x)(DL(x)[h](V(x)y))。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：给出余项在每一所需seminorm中趋零。
- acceptance.02 [uncovered]：本条尚无对应实际输出：联合依赖(x,h,y)的连续性由实际估计推出。

<a id="h02-04"></a>
### H02.04 一阶导数的tame界

**输出：** 对一阶导数公式证明固定loss的一高因子tame估计。

**局部依赖：** H02.03。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“一阶导数的tame界”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 应用端原逆估计的低阶项和高阶项均保留。
- 输出阶变化不缩小x邻域。

**本轮核对：** 未找到“一阶导数的tame界”对应的实际项目声明。未见固定loss Fréchet尺度的实际逆族smooth tame及导数族；有限维或几何逆不替代本项。

**未完成内容：**
- 尚待实际实现并证明：对一阶导数公式证明固定loss的一高因子tame估计。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：应用端原逆估计的低阶项和高阶项均保留。
- acceptance.02 [uncovered]：本条尚无对应实际输出：输出阶变化不缩小x邻域。

<a id="h02-05"></a>
### H02.05 高阶逆微分的有限展开

**输出：** 按导数阶归纳得到DᵏV的真实有限和公式，每项交替含V和L的正阶导数。

**局部依赖：** H02.03。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“高阶逆微分的有限展开”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 参数方向的全部排列项均计入。
- 多线性及对称性与H01实际导数一致。

**本轮核对：** 未找到“高阶逆微分的有限展开”对应的实际项目声明。未见固定loss Fréchet尺度的实际逆族smooth tame及导数族；有限维或几何逆不替代本项。

**未完成内容：**
- 尚待实际实现并证明：按导数阶归纳得到DᵏV的真实有限和公式，每项交替含V和L的正阶导数。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：参数方向的全部排列项均计入。
- acceptance.02 [uncovered]：本条尚无对应实际输出：多线性及对称性与H01实际导数一致。

<a id="h02-06"></a>
### H02.06 高阶估计与连续性归纳

**输出：** 用插值和一高因子估计证明每个DᵏV连续tame，损失对输出阶固定。

**局部依赖：** H02.04, H02.05。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“高阶估计与连续性归纳”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 每个固定k可有自己的loss；同一输出阶族邻域不变。
- 不能只形式微分后省略高阶连续性。

**本轮核对：** 未找到“高阶估计与连续性归纳”对应的实际项目声明。未见固定loss Fréchet尺度的实际逆族smooth tame及导数族；有限维或几何逆不替代本项。

**未完成内容：**
- 尚待实际实现并证明：用插值和一高因子估计证明每个DᵏV连续tame，损失对输出阶固定。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：每个固定k可有自己的loss；同一输出阶族邻域不变。
- acceptance.02 [uncovered]：本条尚无对应实际输出：不能只形式微分后省略高阶连续性。

<a id="h02-07"></a>
### H02.07 源参数联合平滑

**输出：** 把V(x)y对y的线性结构与x高阶导数合并，证明(x,y)↦V(x)y smooth tame。

**局部依赖：** H02.06。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“源参数联合平滑”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 混合源导数为0或对应V导数的精确公式。
- 输出依然是原来由唯一性确定的同一逆族。

**本轮核对：** 未找到“源参数联合平滑”对应的实际项目声明。未见固定loss Fréchet尺度的实际逆族smooth tame及导数族；有限维或几何逆不替代本项。

**未完成内容：**
- 尚待实际实现并证明：把V(x)y对y的线性结构与x高阶导数合并，证明(x,y)↦V(x)y smooth tame。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：混合源导数为0或对应V导数的精确公式。
- acceptance.02 [uncovered]：本条尚无对应实际输出：输出依然是原来由唯一性确定的同一逆族。

<a id="h02-08"></a>
### H02.08 组装：逆族smooth tame定理

**输出：** 对smooth tame线性族L_x，若每个源有唯一解且逆族已连续、tame，则逆族smooth tame。

**局部依赖：** H02.01, H02.02, H02.03, H02.04, H02.05, H02.06, H02.07。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 100–250 行。已有子结论的接口组装与完整量词核对；不把尚未证明的子结论作为新假设。

**验收条件：**

- 连续性和tame界是须验证的前提
- 无新公理
- 实际采用的方向微积分与H01一致
- 逐项调用以上子任务的实际结论；所有见证、范数、参数和允许依赖与原节点一致。

**本轮核对：** 未找到“组装：逆族smooth tame定理”对应的实际项目声明。未见固定loss Fréchet尺度的实际逆族smooth tame及导数族；有限维或几何逆不替代本项。

**未完成内容：**
- 尚待实际实现并证明：对smooth tame线性族L_x，若每个源有唯一解且逆族已连续、tame，则逆族smooth tame。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：连续性和tame界是须验证的前提
- acceptance.02 [uncovered]：本条尚无对应实际输出：无新公理
- acceptance.03 [uncovered]：本条尚无对应实际输出：实际采用的方向微积分与H01一致
- acceptance.04 [uncovered]：本条尚无对应实际输出：逐项调用以上子任务的实际结论；所有见证、范数、参数和允许依赖与原节点一致。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：对smooth tame线性族L_x，若每个源有唯一解且逆族已连续、tame，则逆族smooth tame。 | H02.08（组合全部子任务） |
| acceptance.01：连续性和tame界是须验证的前提 | H02.01, H02.03, H02.04, H02.06 |
| acceptance.02：无新公理 | H02.02, H02.03, H02.05, H02.06, H02.07 |
| acceptance.03：实际采用的方向微积分与H01一致 | H02.01, H02.03, H02.05, H02.07 |

<a id="n07"></a>
## N07 扰动标量逆及高阶恢复

**原节点完整目标：** 先在基本Banach空间反演，再从方程恢复全部角向/法向混合正则性，得到固定损失tame逆G_xf=(η,μ)，η∈Xβ∩kerℓ*；兼容源上λ=0，右端归零、左端常数自由。

**原上游里程碑：** N05, N06, H02, W02

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [08-stable-inverse.tex:342–550](../../paper/flexible-surface-rewrite/08-stable-inverse.tex#L342)

<a id="n07-01"></a>
### N07.01 基本Banach解的实际构造

**输出：** 用G*(I+R_x)⁻¹构造增广方程在D*上的唯一基本解。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“基本Banach解的实际构造”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 固定同一D*及V_{0,b}。
- 证明P_xG_x=I和同域唯一性。

**本轮核对：** 未找到“基本Banach解的实际构造”对应的实际项目声明。未有同一基本Banach逆及高阶恢复或兼容源消λ输出。

**未完成内容：**
- 尚待实际实现并证明：用G*(I+R_x)⁻¹构造增广方程在D*上的唯一基本解。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：固定同一D*及V_{0,b}。
- acceptance.02 [uncovered]：本条尚无对应实际输出：证明P_xG_x=I和同域唯一性。

<a id="n07-02"></a>
### N07.02 兼容源消去λ

**输出：** 积分真实物理方程并使用端点通量，证明Qf=0时λ=0。

**局部依赖：** N07.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“兼容源消去λ”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- c*归一化及源Jacobian与N05一致。
- μ列及χL列的积分贡献逐项核对。

**本轮核对：** 未找到“兼容源消去λ”对应的实际项目声明。未有同一基本Banach逆及高阶恢复或兼容源消λ输出。

**未完成内容：**
- 尚待实际实现并证明：积分真实物理方程并使用端点通量，证明Qf=0时λ=0。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：c*归一化及源Jacobian与N05一致。
- acceptance.02 [uncovered]：本条尚无对应实际输出：μ列及χL列的积分贡献逐项核对。

<a id="n07-03"></a>
### N07.03 角向高阶commutator估计

**输出：** 对已构造基本解与∂θᵏ求交换，得到一高state因子的高阶角正则估计。

**局部依赖：** N07.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“角向高阶commutator估计”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 每次应用的是同一基本解及同一逆。
- 全部系数高阶代价纳入固定loss。

**本轮核对：** 未找到“角向高阶commutator估计”对应的实际项目声明。未有同一基本Banach逆及高阶恢复或兼容源消λ输出。

**未完成内容：**
- 尚待实际实现并证明：对已构造基本解与∂θᵏ求交换，得到一高state因子的高阶角正则估计。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：每次应用的是同一基本解及同一逆。
- acceptance.02 [uncovered]：本条尚无对应实际输出：全部系数高阶代价纳入固定loss。

<a id="n07-04"></a>
### N07.04 法向正则逐阶恢复

**输出：** 由各canonical片方程递推normal导数并与angular估计合并。

**局部依赖：** N07.03。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“法向正则逐阶恢复”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 根与cut使用N04全jet匹配而非任意拼接场。
- mixed normal/angular全部阶覆盖。

**本轮核对：** 未找到“法向正则逐阶恢复”对应的实际项目声明。未有同一基本Banach逆及高阶恢复或兼容源消λ输出。

**未完成内容：**
- 尚待实际实现并证明：由各canonical片方程递推normal导数并与angular估计合并。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：根与cut使用N04全jet匹配而非任意拼接场。
- acceptance.02 [uncovered]：本条尚无对应实际输出：mixed normal/angular全部阶覆盖。

<a id="n07-05"></a>
### N07.05 同一解的全部高度范数

**输出：** 由volume与坐标转换把基本解提升到Xβ，给出η、μ的固定loss tame界。

**局部依赖：** N07.02, N07.03, N07.04。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“同一解的全部高度范数”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 输出η属于kerℓ*，右端0、左端常数自由。
- 高阶常数可变但状态邻域不变。

**本轮核对：** 未找到“同一解的全部高度范数”对应的实际项目声明。未有同一基本Banach逆及高阶恢复或兼容源消λ输出。

**未完成内容：**
- 尚待实际实现并证明：由volume与坐标转换把基本解提升到Xβ，给出η、μ的固定loss tame界。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：输出η属于kerℓ*，右端0、左端常数自由。
- acceptance.02 [uncovered]：本条尚无对应实际输出：高阶常数可变但状态邻域不变。

<a id="n07-06"></a>
### N07.06 逆族基本连续性

**输出：** 由resolvent差分及N06相对界证明state到基本逆的连续性。

**局部依赖：** N07.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“逆族基本连续性”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 连续性在实际source/graph Banach范数成立。
- 不是先假设smooth逆再推连续。

**本轮核对：** 未找到“逆族基本连续性”对应的实际项目声明。未有同一基本Banach逆及高阶恢复或兼容源消λ输出。

**未完成内容：**
- 尚待实际实现并证明：由resolvent差分及N06相对界证明state到基本逆的连续性。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：连续性在实际source/graph Banach范数成立。
- acceptance.02 [uncovered]：本条尚无对应实际输出：不是先假设smooth逆再推连续。

<a id="n07-07"></a>
### N07.07 全部阶逆族连续性

**输出：** 用高阶恢复估计与差分方程证明每个输出阶上的联合连续性。

**局部依赖：** N07.03, N07.04, N07.05, N07.06。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“全部阶逆族连续性”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 同一loss与固定低阶邻域。
- 源和state的混合依赖分别控制。

**本轮核对：** 未找到“全部阶逆族连续性”对应的实际项目声明。未有同一基本Banach逆及高阶恢复或兼容源消λ输出。

**未完成内容：**
- 尚待实际实现并证明：用高阶恢复估计与差分方程证明每个输出阶上的联合连续性。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：同一loss与固定低阶邻域。
- acceptance.02 [uncovered]：本条尚无对应实际输出：源和state的混合依赖分别控制。

<a id="n07-08"></a>
### N07.08 调用逆族定理得到smooth tame

**输出：** 逐项验证H02前提并导出G_xf=(η,μ)对state/source smooth tame且源线性。

**局部依赖：** N07.05, N07.06, N07.07。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“调用逆族定理得到smooth tame”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 调用H02前连续性与全部tame界已经实际证明。
- 最终输出引用同一个基本逆，不另选高阶解。

**本轮核对：** 未找到“调用逆族定理得到smooth tame”对应的实际项目声明。未有同一基本Banach逆及高阶恢复或兼容源消λ输出。

**未完成内容：**
- 尚待实际实现并证明：逐项验证H02前提并导出G_xf=(η,μ)对state/source smooth tame且源线性。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：调用H02前连续性与全部tame界已经实际证明。
- acceptance.02 [uncovered]：本条尚无对应实际输出：最终输出引用同一个基本逆，不另选高阶解。

<a id="n07-09"></a>
### N07.09 组装：扰动标量逆及高阶恢复

**输出：** 先在基本Banach空间反演，再从方程恢复全部角向/法向混合正则性，得到固定损失tame逆G_xf=(η,μ)，η∈Xβ∩kerℓ*；兼容源上λ=0，右端归零、左端常数自由。

**局部依赖：** N07.01, N07.02, N07.03, N07.04, N07.05, N07.06, N07.07, N07.08。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 100–250 行。已有子结论的接口组装与完整量词核对；不把尚未证明的子结论作为新假设。

**验收条件：**

- 高阶常数可变而邻域固定
- 积分守恒实际消去λ
- 逆族对state/source smooth tame
- 逐项调用以上子任务的实际结论；所有见证、范数、参数和允许依赖与原节点一致。

**本轮核对：** 未找到“组装：扰动标量逆及高阶恢复”对应的实际项目声明。未有同一基本Banach逆及高阶恢复或兼容源消λ输出。

**未完成内容：**
- 尚待实际实现并证明：先在基本Banach空间反演，再从方程恢复全部角向/法向混合正则性，得到固定损失tame逆G_xf=(η,μ)，η∈Xβ∩kerℓ*；兼容源上λ=0，右端归零、左端常数自由。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：高阶常数可变而邻域固定
- acceptance.02 [uncovered]：本条尚无对应实际输出：积分守恒实际消去λ
- acceptance.03 [uncovered]：本条尚无对应实际输出：逆族对state/source smooth tame
- acceptance.04 [uncovered]：本条尚无对应实际输出：逐项调用以上子任务的实际结论；所有见证、范数、参数和允许依赖与原节点一致。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：先在基本Banach空间反演，再从方程恢复全部角向/法向混合正则性，得到固定损失tame逆G_xf=(η,μ)，η∈Xβ∩kerℓ*；兼容源上λ=0，右端归零、左端常数自由。 | N07.09（组合全部子任务） |
| acceptance.01：高阶常数可变而邻域固定 | N07.03, N07.04, N07.05, N07.07 |
| acceptance.02：积分守恒实际消去λ | N07.02 |
| acceptance.03：逆族对state/source smooth tame | N07.06, N07.07, N07.08 |

<a id="n08"></a>
## N08 联合残差、真实控制列与smoothing

**原节点完整目标：** 构造R=(A,e):X×ℝ→Y、证明q=0可去且参考state为零；真实k=DνA、K=DκA包含h_w变化；J=⟨Dκe⟩对角一致可逆，K及GK取得所需控制权的smoothing。

**原上游里程碑：** S04, N01, N02, N07, W02

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [09-solving-the-equation.tex:13–137](../../paper/flexible-surface-rewrite/09-solving-the-equation.tex#L13)

<a id="n08-01"></a>
### N08.01 四未知量状态及切空间

**输出：** 构造(u,ν,κ,hL)的实际仿射slice及对应X,Y乘积空间。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“四未知量状态及切空间”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- q为独立实参数。
- 高度tangent为Xβ∩kerℓ*，圆残差含角均值。

**本轮核对：** 未找到“四未知量状态及切空间”对应的实际项目声明。未构造完整四未知量联合残差及控制列；点态scalar公式不替代函数空间输出。

**未完成内容：**
- 尚待实际实现并证明：构造(u,ν,κ,hL)的实际仿射slice及对应X,Y乘积空间。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：q为独立实参数。
- acceptance.02 [uncovered]：本条尚无对应实际输出：高度tangent为Xβ∩kerℓ*，圆残差含角均值。

<a id="n08-02"></a>
### N08.02 联合残差的可去定义

**输出：** 用真实归一化积分公式定义R=(A,e)，证明q=0处可去且source兼容。

**局部依赖：** N08.01。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 300–650 行。围绕“联合残差的可去定义”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- q=0处定义来自真实积分，不只分段命名。
- e采用N02两支返回的同一残差。

**本轮核对：** scalar A的可去归一化与兼容积分已证；四未知量实际联合R=(A,e)、返回e和weighted source映射没有实现。

**源码证据 `ContinuousFlexibility/Scalar/Normalization.lean`：** `ContinuousFlexibility.normalizedHeightResidual`, `ContinuousFlexibility.normalizedHeightResidual_zero`, `ContinuousFlexibility.normalizedHeightResidual_of_ne_zero`, `ContinuousFlexibility.normalizedHeightResidual_eq_factored`, `ContinuousFlexibility.contDiffAt_normalizedHeightResidual`, `ContinuousFlexibility.contDiffAt_normalizedHeightResidual_of_residual_zero`

实际scalar归一化残差在q=0可去，识别非零q比值和q=0线性化；只证明点态/有限维平滑。

**源码证据 `ContinuousFlexibility/Scalar/NormalizedConservation.lean`：** `ContinuousFlexibility.integral_mean_normalizedHeightResidual_eq_zero_of_ne_zero`, `ContinuousFlexibility.integral_mean_normalizedHeightResidual_radialHeight_eq_zero`

在明确光滑、周期和端点jets前提下，实际归一化scalar源物理积分为0。

**未完成内容：**
- 把A定义成实际X/Y上的smooth tame映射并构造同一两支返回e。
- 实现联合R及q=0处函数空间可去性和兼容性。

**逐条验收：**
- acceptance.01 [partial]：scalar q=0来自真实因式分解与ContDiffAt，整个函数空间R尚未建立。
- acceptance.02 [uncovered]：未找到N02两支返回残差e的实际声明。

<a id="n08-03"></a>
### N08.03 参考state确为零

**输出：** 由参考二模核与旋转返回证明R(Φ*,0,0,id;0)=0。

**局部依赖：** N08.01, N08.02。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“参考state确为零”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- Φ*与ℓ*规范化来自同一个R12见证。
- 两个残差都逐项为零。

**本轮核对：** 未找到“参考state确为零”对应的实际项目声明。未构造完整四未知量联合残差及控制列；点态scalar公式不替代函数空间输出。

**未完成内容：**
- 尚待实际实现并证明：由参考二模核与旋转返回证明R(Φ*,0,0,id;0)=0。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：Φ*与ℓ*规范化来自同一个R12见证。
- acceptance.02 [uncovered]：本条尚无对应实际输出：两个残差都逐项为零。

<a id="n08-04"></a>
### N08.04 真实控制列k和K

**输出：** 对实际A求Dν和Dκ，写出包含w及h_w全部变化的导数公式。

**局部依赖：** N08.02。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“真实控制列k和K”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 参考高度h_w随控制变化的项不得遗漏。
- 公式与N05增广k列一致。

**本轮核对：** 未找到“真实控制列k和K”对应的实际项目声明。未构造完整四未知量联合残差及控制列；点态scalar公式不替代函数空间输出。

**未完成内容：**
- 尚待实际实现并证明：对实际A求Dν和Dκ，写出包含w及h_w全部变化的导数公式。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：参考高度h_w随控制变化的项不得遗漏。
- acceptance.02 [uncovered]：本条尚无对应实际输出：公式与N05增广k列一致。

<a id="n08-05"></a>
### N08.05 圆控制均值J的实际对角性

**输出：** 计算Dκe的均值J，证明组件局部性、参考J₀=I和共同邻域统一可逆。

**局部依赖：** N08.01, N08.02。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“圆控制均值J的实际对角性”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- ν及端点scalar不在负分量产生正jets。
- 逐个对角元的统一正下界来自固定低阶范数。

**本轮核对：** 未找到“圆控制均值J的实际对角性”对应的实际项目声明。未构造完整四未知量联合残差及控制列；点态scalar公式不替代函数空间输出。

**未完成内容：**
- 尚待实际实现并证明：计算Dκe的均值J，证明组件局部性、参考J₀=I和共同邻域统一可逆。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：ν及端点scalar不在负分量产生正jets。
- acceptance.02 [uncovered]：本条尚无对应实际输出：逐个对角元的统一正下界来自固定低阶范数。

<a id="n08-06"></a>
### N08.06 参考圆均值行的精确公式

**输出：** 证明R₀°Z的径向积分公式并证明其杀掉非零角模和奇chart方向。

**局部依赖：** N08.02。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“参考圆均值行的精确公式”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 包含(1+w*²)/w*的真实系数。
- R₀°Φ*=0由真实二模结构推出。

**本轮核对：** 未找到“参考圆均值行的精确公式”对应的实际项目声明。未构造完整四未知量联合残差及控制列；点态scalar公式不替代函数空间输出。

**未完成内容：**
- 尚待实际实现并证明：证明R₀°Z的径向积分公式并证明其杀掉非零角模和奇chart方向。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：包含(1+w*²)/w*的真实系数。
- acceptance.02 [uncovered]：本条尚无对应实际输出：R₀°Φ*=0由真实二模结构推出。

<a id="n08-07"></a>
### N08.07 K的全部组件权平滑

**输出：** 对ξ∈Bβ证明Kξ在Yβ全部阶受C_s(1+n_{s+d*})||ξ||_{Bβ}控制。

**局部依赖：** N08.04。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“K的全部组件权平滑”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 每一项都有正height jet提供额外H_m^β。
- 端点scalar在控制支持上无height jet。

**本轮核对：** 未找到“K的全部组件权平滑”对应的实际项目声明。未构造完整四未知量联合残差及控制列；点态scalar公式不替代函数空间输出。

**未完成内容：**
- 尚待实际实现并证明：对ξ∈Bβ证明Kξ在Yβ全部阶受C_s(1+n_{s+d*})||ξ||_{Bβ}控制。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：每一项都有正height jet提供额外H_m^β。
- acceptance.02 [uncovered]：本条尚无对应实际输出：端点scalar在控制支持上无height jet。

<a id="n08-08"></a>
### N08.08 GK的高度及scalar平滑

**输出：** 把N07同一G与K组合，证明U=GK的高度和μ全部阶平滑估计。

**局部依赖：** N08.07。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“GK的高度及scalar平滑”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 只增加G的固定loss。
- 后续Bβ自同态的输入始终只需基本Bβ范数。

**本轮核对：** 未找到“GK的高度及scalar平滑”对应的实际项目声明。未构造完整四未知量联合残差及控制列；点态scalar公式不替代函数空间输出。

**未完成内容：**
- 尚待实际实现并证明：把N07同一G与K组合，证明U=GK的高度和μ全部阶平滑估计。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：只增加G的固定loss。
- acceptance.02 [uncovered]：本条尚无对应实际输出：后续Bβ自同态的输入始终只需基本Bβ范数。

<a id="n08-09"></a>
### N08.09 残差和控制族smooth tame

**输出：** 综合系数、flow、W02演算证明R,k,K,J⁻¹及U在同一低阶开集smooth tame。

**局部依赖：** N08.01, N08.02, N08.03, N08.04, N08.05, N08.06, N08.07, N08.08。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“残差和控制族smooth tame”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 所有映射共享同一实际state及参数域。
- 输出阶变化不改变邻域半径。

**本轮核对：** 未找到“残差和控制族smooth tame”对应的实际项目声明。未构造完整四未知量联合残差及控制列；点态scalar公式不替代函数空间输出。

**未完成内容：**
- 尚待实际实现并证明：综合系数、flow、W02演算证明R,k,K,J⁻¹及U在同一低阶开集smooth tame。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：所有映射共享同一实际state及参数域。
- acceptance.02 [uncovered]：本条尚无对应实际输出：输出阶变化不改变邻域半径。

<a id="n08-10"></a>
### N08.10 组装：联合残差、真实控制列与smoothing

**输出：** 构造R=(A,e):X×ℝ→Y、证明q=0可去且参考state为零；真实k=DνA、K=DκA包含h_w变化；J=⟨Dκe⟩对角一致可逆，K及GK取得所需控制权的smoothing。

**局部依赖：** N08.01, N08.02, N08.03, N08.04, N08.05, N08.06, N08.07, N08.08, N08.09。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 100–250 行。已有子结论的接口组装与完整量词核对；不把尚未证明的子结论作为新假设。

**验收条件：**

- state为(u,ν,κ,hL)，q为独立参数
- 不能忘记控制对h_w的贡献
- J和smoothing在同一Bβ上使用
- 逐项调用以上子任务的实际结论；所有见证、范数、参数和允许依赖与原节点一致。

**本轮核对：** 未找到“组装：联合残差、真实控制列与smoothing”对应的实际项目声明。未构造完整四未知量联合残差及控制列；点态scalar公式不替代函数空间输出。

**未完成内容：**
- 尚待实际实现并证明：构造R=(A,e):X×ℝ→Y、证明q=0可去且参考state为零；真实k=DνA、K=DκA包含h_w变化；J=⟨Dκe⟩对角一致可逆，K及GK取得所需控制权的smoothing。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：state为(u,ν,κ,hL)，q为独立参数
- acceptance.02 [uncovered]：本条尚无对应实际输出：不能忘记控制对h_w的贡献
- acceptance.03 [uncovered]：本条尚无对应实际输出：J和smoothing在同一Bβ上使用
- acceptance.04 [uncovered]：本条尚无对应实际输出：逐项调用以上子任务的实际结论；所有见证、范数、参数和允许依赖与原节点一致。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：构造R=(A,e):X×ℝ→Y、证明q=0可去且参考state为零；真实k=DνA、K=DκA包含h_w变化；J=⟨Dκe⟩对角一致可逆，K及GK取得所需控制权的smoothing。 | N08.10（组合全部子任务） |
| acceptance.01：state为(u,ν,κ,hL)，q为独立参数 | N08.01, N08.02 |
| acceptance.02：不能忘记控制对h_w的贡献 | N08.04, N08.07 |
| acceptance.03：J和smoothing在同一Bβ上使用 | N08.05, N08.07, N08.08 |

<a id="n09"></a>
## N09 耦合高度与圆方程的逆

**原节点完整目标：** 在同一个Bβ上证明qJ⁻¹R°GK的小范数，构造ξ、(η,μ)、v三条解公式；最终圆源零均值，使M_T逆合法，得到对源线性且对state smooth tame的V。

**原上游里程碑：** N02, N07, N08, H02

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [09-solving-the-equation.tex:139–181](../../paper/flexible-surface-rewrite/09-solving-the-equation.tex#L139)

<a id="n09-01"></a>
### N09.01 耦合两行的Schur消元

**输出：** 从修正线性系统严格导出高度y=Gf−Uξ及均值控制方程。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“耦合两行的Schur消元”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 取均值使用M_T的实际零均值性质。
- R°作用于G/U的高度分量。

**本轮核对：** 未找到“耦合两行的Schur消元”对应的实际项目声明。未构造耦合系统、同一Bβ上反馈有界算子/小范数逆及三条解公式。

**未完成内容：**
- 尚待实际实现并证明：从修正线性系统严格导出高度y=Gf−Uξ及均值控制方程。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：取均值使用M_T的实际零均值性质。
- acceptance.02 [uncovered]：本条尚无对应实际输出：R°作用于G/U的高度分量。

<a id="n09-02"></a>
### N09.02 基本控制Banach空间

**输出：** 冻结Bβ加权ℓ²空间及J⁻¹,R°U的定义域和值域。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“基本控制Banach空间”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- Bβ的测度、索引与H_m权同N08。
- 同一Bβ用于整个第二次Neumann过程。

**本轮核对：** 未找到“基本控制Banach空间”对应的实际项目声明。未构造耦合系统、同一Bβ上反馈有界算子/小范数逆及三条解公式。

**未完成内容：**
- 尚待实际实现并证明：冻结Bβ加权ℓ²空间及J⁻¹,R°U的定义域和值域。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：Bβ的测度、索引与H_m权同N08。
- acceptance.02 [uncovered]：本条尚无对应实际输出：同一Bβ用于整个第二次Neumann过程。

<a id="n09-03"></a>
### N09.03 反馈算子的有界性

**输出：** 使用U平滑证明J⁻¹R°U:Bβ→Bβ为真实有界线性映射。

**局部依赖：** N09.01, N09.02。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“反馈算子的有界性”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 所需state控制仅涉及有限阶范数。
- 没有用导数损失估计代替基本空间有界性。

**本轮核对：** 未找到“反馈算子的有界性”对应的实际项目声明。未构造耦合系统、同一Bβ上反馈有界算子/小范数逆及三条解公式。

**未完成内容：**
- 尚待实际实现并证明：使用U平滑证明J⁻¹R°U:Bβ→Bβ为真实有界线性映射。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：所需state控制仅涉及有限阶范数。
- acceptance.02 [uncovered]：本条尚无对应实际输出：没有用导数损失估计代替基本空间有界性。

<a id="n09-04"></a>
### N09.04 独立q小区间及反馈小范数

**输出：** 先冻结低阶state邻域，再选统一q区间使||qJ⁻¹R°U||<1/2。

**局部依赖：** N09.03。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“独立q小区间及反馈小范数”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- q区间不随输出阶变化。
- state与q的允许依赖顺序明确。

**本轮核对：** 未找到“独立q小区间及反馈小范数”对应的实际项目声明。未构造耦合系统、同一Bβ上反馈有界算子/小范数逆及三条解公式。

**未完成内容：**
- 尚待实际实现并证明：先冻结低阶state邻域，再选统一q区间使||qJ⁻¹R°U||<1/2。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：q区间不随输出阶变化。
- acceptance.02 [uncovered]：本条尚无对应实际输出：state与q的允许依赖顺序明确。

<a id="n09-05"></a>
### N09.05 控制逆及ξ的实际解公式

**输出：** 构造I−qJ⁻¹R°U的Banach双侧逆并定义论文ξ公式。

**局部依赖：** N09.01, N09.03, N09.04。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“控制逆及ξ的实际解公式”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 算子范数级数实际收敛。
- ξ对(f,g)线性，且满足均值控制方程。

**本轮核对：** 未找到“控制逆及ξ的实际解公式”对应的实际项目声明。未构造耦合系统、同一Bβ上反馈有界算子/小范数逆及三条解公式。

**未完成内容：**
- 尚待实际实现并证明：构造I−qJ⁻¹R°U的Banach双侧逆并定义论文ξ公式。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：算子范数级数实际收敛。
- acceptance.02 [uncovered]：本条尚无对应实际输出：ξ对(f,g)线性，且满足均值控制方程。

<a id="n09-06"></a>
### N09.06 高度及μ回代

**输出：** 定义(η,μ)=Gf−Uξ，证明第一行与height slice和端点条件。

**局部依赖：** N09.01, N09.05。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“高度及μ回代”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- η使用同一个G和U。
- 源兼容及λ=0前提真实满足。

**本轮核对：** 未找到“高度及μ回代”对应的实际项目声明。未构造耦合系统、同一Bβ上反馈有界算子/小范数逆及三条解公式。

**未完成内容：**
- 尚待实际实现并证明：定义(η,μ)=Gf−Uξ，证明第一行与height slice和端点条件。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：η使用同一个G和U。
- acceptance.02 [uncovered]：本条尚无对应实际输出：源兼容及λ=0前提真实满足。

<a id="n09-07"></a>
### N09.07 圆源均值恰为零

**输出：** 由已解均值控制方程证明g−qC°η−Dξ的角均值为零。

**局部依赖：** N09.05, N09.06。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“圆源均值恰为零”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 这是由方程推出的结论，不作为source新增假设。
- 每个组件均成立并保持实偶sector。

**本轮核对：** 未找到“圆源均值恰为零”对应的实际项目声明。未构造耦合系统、同一Bβ上反馈有界算子/小范数逆及三条解公式。

**未完成内容：**
- 尚待实际实现并证明：由已解均值控制方程证明g−qC°η−Dξ的角均值为零。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：这是由方程推出的结论，不作为source新增假设。
- acceptance.02 [uncovered]：本条尚无对应实际输出：每个组件均成立并保持实偶sector。

<a id="n09-08"></a>
### N09.08 chart解与全系统恒等式

**输出：** 应用M_T⁻¹求v并证明真实方向为v∘hL，完整修正两行系统成立。

**局部依赖：** N09.06, N09.07。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“chart解与全系统恒等式”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- chart奇性及π-equivariance保留。
- 返回两支的线性等式同时闭合。

**本轮核对：** 未找到“chart解与全系统恒等式”对应的实际项目声明。未构造耦合系统、同一Bβ上反馈有界算子/小范数逆及三条解公式。

**未完成内容：**
- 尚待实际实现并证明：应用M_T⁻¹求v并证明真实方向为v∘hL，完整修正两行系统成立。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：chart奇性及π-equivariance保留。
- acceptance.02 [uncovered]：本条尚无对应实际输出：返回两支的线性等式同时闭合。

<a id="n09-09"></a>
### N09.09 同一基本解的全部高阶界

**输出：** 从ξ=J⁻¹(g₀−qR°Gf)+qJ⁻¹R°Uξ恢复控制高阶，再得高度和chart高阶。

**局部依赖：** N09.05, N09.06, N09.08。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“同一基本解的全部高阶界”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 使用U全平滑让右端反馈只需||ξ||_{Bβ}。
- 固定loss与共同q区间不随阶变化。

**本轮核对：** 未找到“同一基本解的全部高阶界”对应的实际项目声明。未构造耦合系统、同一Bβ上反馈有界算子/小范数逆及三条解公式。

**未完成内容：**
- 尚待实际实现并证明：从ξ=J⁻¹(g₀−qR°Gf)+qJ⁻¹R°Uξ恢复控制高阶，再得高度和chart高阶。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：使用U全平滑让右端反馈只需||ξ||_{Bβ}。
- acceptance.02 [uncovered]：本条尚无对应实际输出：固定loss与共同q区间不随阶变化。

<a id="n09-10"></a>
### N09.10 逆族连续及smooth tame

**输出：** 由resolvent证明基本连续，再逐阶连续并验证H02，得到V(state,q)y smooth tame且对y线性。

**局部依赖：** N09.05, N09.08, N09.09。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“逆族连续及smooth tame”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- H02所有实际前提逐条核对。
- 得到同一V=(η,μ,ξ,v∘hL)，不换高阶解。

**本轮核对：** 未找到“逆族连续及smooth tame”对应的实际项目声明。未构造耦合系统、同一Bβ上反馈有界算子/小范数逆及三条解公式。

**未完成内容：**
- 尚待实际实现并证明：由resolvent证明基本连续，再逐阶连续并验证H02，得到V(state,q)y smooth tame且对y线性。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：H02所有实际前提逐条核对。
- acceptance.02 [uncovered]：本条尚无对应实际输出：得到同一V=(η,μ,ξ,v∘hL)，不换高阶解。

<a id="n09-11"></a>
### N09.11 组装：耦合高度与圆方程的逆

**输出：** 在同一个Bβ上证明qJ⁻¹R°GK的小范数，构造ξ、(η,μ)、v三条解公式；最终圆源零均值，使M_T逆合法，得到对源线性且对state smooth tame的V。

**局部依赖：** N09.01, N09.02, N09.03, N09.04, N09.05, N09.06, N09.07, N09.08, N09.09, N09.10。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 100–250 行。已有子结论的接口组装与完整量词核对；不把尚未证明的子结论作为新假设。

**验收条件：**

- 第二次Neumann仍是同空间有界逆
- 零均值须由方程证明
- 全部高阶估计对应同一基本解
- 逐项调用以上子任务的实际结论；所有见证、范数、参数和允许依赖与原节点一致。

**本轮核对：** 未找到“组装：耦合高度与圆方程的逆”对应的实际项目声明。未构造耦合系统、同一Bβ上反馈有界算子/小范数逆及三条解公式。

**未完成内容：**
- 尚待实际实现并证明：在同一个Bβ上证明qJ⁻¹R°GK的小范数，构造ξ、(η,μ)、v三条解公式；最终圆源零均值，使M_T逆合法，得到对源线性且对state smooth tame的V。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：第二次Neumann仍是同空间有界逆
- acceptance.02 [uncovered]：本条尚无对应实际输出：零均值须由方程证明
- acceptance.03 [uncovered]：本条尚无对应实际输出：全部高阶估计对应同一基本解
- acceptance.04 [uncovered]：本条尚无对应实际输出：逐项调用以上子任务的实际结论；所有见证、范数、参数和允许依赖与原节点一致。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：在同一个Bβ上证明qJ⁻¹R°GK的小范数，构造ξ、(η,μ)、v三条解公式；最终圆源零均值，使M_T逆合法，得到对源线性且对state smooth tame的V。 | N09.11（组合全部子任务） |
| acceptance.01：第二次Neumann仍是同空间有界逆 | N09.02, N09.03, N09.04, N09.05 |
| acceptance.02：零均值须由方程证明 | N09.07, N09.08 |
| acceptance.03：全部高阶估计对应同一基本解 | N09.05, N09.09, N09.10 |

<a id="n10"></a>
## N10 两个独立残差的精确二次误差

**原节点完整目标：** 构造对任意独立r=(r₁,r₂)、y=(f,g)双线性且smooth tame的Q_x,q(r,y)，证明D_xR·Vy=y+Q_x,q(R,y)，并证明输出源兼容。

**原上游里程碑：** N03, N08, N09, S05, W02

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [09-solving-the-equation.tex:183–227](../../paper/flexible-surface-rewrite/09-solving-the-equation.tex#L183)

<a id="n10-01"></a>
### N10.01 真实导数与修正系统的差

**输出：** 把S05、N03和N02 chart导数恒等式代入实际D_xR，写出全部残差误差项。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 300–650 行。围绕“真实导数与修正系统的差”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 两行误差的符号和q因子逐项核对。
- 控制方向包括真实h_w变化。

**本轮核对：** scalar高度导数与S05修正之差已精确展开；N03返回修正、chart行及完整联合导数均未实现。

**源码证据 `ContinuousFlexibility/Scalar/TypeCorrection.lean`：** `ContinuousFlexibility.heightLinearizedDivergence_eq_corrected_of_smooth`, `ContinuousFlexibility.parameter_mul_normalizedHeightResidual`, `ContinuousFlexibility.heightLinearizedDivergence_eq_corrected_normalized`

真实scalar高度线性化与corrected divergence之差是q乘残差角散度；未包括返回修正和chart行。

**未完成内容：**
- 补齐返回修正和chart行的真实导数。
- 将四未知量控制对h_w的全部变化纳入D_xR。

**逐条验收：**
- acceptance.01 [partial]：scalar q因子和残差角散度符号已证，第二行尚缺。
- acceptance.02 [uncovered]：未见四未知量真实控制对h_w变化的完整导数对接。

<a id="n10-02"></a>
### N10.02 任意独立残差的误差定义

**输出：** 对任意r=(r₁,r₂)和y=(f,g)定义Q：仅替换显式A,e,e′因子，保持真实state路径。

**局部依赖：** N10.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“任意独立残差的误差定义”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- η,v来自同一个V(state,q)y。
- 定义域是全部独立残差对，不限r=R。

**本轮核对：** 未找到“任意独立残差的误差定义”对应的实际项目声明。未构造独立二残差Q及全两行恒等式；scalar局部公式不替代本项。

**未完成内容：**
- 尚待实际实现并证明：对任意r=(r₁,r₂)和y=(f,g)定义Q：仅替换显式A,e,e′因子，保持真实state路径。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：η,v来自同一个V(state,q)y。
- acceptance.02 [uncovered]：本条尚无对应实际输出：定义域是全部独立残差对，不限r=R。

<a id="n10-03"></a>
### N10.03 Q对两个参数的真实双线性

**输出：** 分别证明Q在r和y的加法/数乘恒等式。

**局部依赖：** N10.02。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“Q对两个参数的真实双线性”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 使用V对y线性及E_x、Q_h对独立r₂线性。
- 不是仅有O(||r||||y||)的界。

**本轮核对：** 未找到“Q对两个参数的真实双线性”对应的实际项目声明。未构造独立二残差Q及全两行恒等式；scalar局部公式不替代本项。

**未完成内容：**
- 尚待实际实现并证明：分别证明Q在r和y的加法/数乘恒等式。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：使用V对y线性及E_x、Q_h对独立r₂线性。
- acceptance.02 [uncovered]：本条尚无对应实际输出：不是仅有O(||r||||y||)的界。

<a id="n10-04"></a>
### N10.04 scalar误差的兼容积分

**输出：** 证明角向散度和内部修正散度两项的物理积分为零。

**局部依赖：** N10.02, N10.03。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 200–500 行。围绕“scalar误差的兼容积分”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 端点平坦通量的消失和角周期性真实核验。
- 源Jacobian与物理dr dθ一致。

**本轮核对：** 真实散度积分兼容机制已证，但独立Q的scalar两项未构造，其具体平坦通量与source身份未核验。

**源码证据 `ContinuousFlexibility/Scalar/Conservation.lean`：** `ContinuousFlexibility.integral_exteriorCoefficient_eq_zero`, `ContinuousFlexibility.integral_mean_heightResidual_eq_zero_of_boundary_jets`

矩形上真实周期/端边配对条件使散度物理dr dθ积分为0；尚未构造独立Q两项。

**未完成内容：**
- 定义独立r,y下Q scalar角散度与内部修正散度。
- 验证实际周期/平坦通量及source Jacobian。

**逐条验收：**
- acceptance.01 [partial]：一般周期/端边条件推出积分零已证；Q实际端点通量未核验。
- acceptance.02 [partial]：一般公式使用真实dr dθ；Q/canonical源实际Jacobian仍缺。

<a id="n10-05"></a>
### N10.05 圆误差的奇偶sector

**输出：** 证明Q_h(r₂,v)落入指定实偶半周期圆残差空间。

**局部依赖：** N10.02, N10.03。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“圆误差的奇偶sector”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 实际组合路径保留π-equivariance。
- 均值项允许存在，不误投影掉圆控制行。

**本轮核对：** 未找到“圆误差的奇偶sector”对应的实际项目声明。未构造独立二残差Q及全两行恒等式；scalar局部公式不替代本项。

**未完成内容：**
- 尚待实际实现并证明：证明Q_h(r₂,v)落入指定实偶半周期圆残差空间。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：实际组合路径保留π-equivariance。
- acceptance.02 [uncovered]：本条尚无对应实际输出：均值项允许存在，不误投影掉圆控制行。

<a id="n10-06"></a>
### N10.06 二弱因子的固定损失tame估计

**输出：** 证明Q及全部state方向导数是独立双线性smooth tame映射到实际Y。

**局部依赖：** N10.02, N10.03, N10.04, N10.05。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“二弱因子的固定损失tame估计”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 每项的两个弱端点因子实际识别。
- 所有输出阶共用固定低阶邻域。

**本轮核对：** 未找到“二弱因子的固定损失tame估计”对应的实际项目声明。未构造独立二残差Q及全两行恒等式；scalar局部公式不替代本项。

**未完成内容：**
- 尚待实际实现并证明：证明Q及全部state方向导数是独立双线性smooth tame映射到实际Y。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：每项的两个弱端点因子实际识别。
- acceptance.02 [uncovered]：本条尚无对应实际输出：所有输出阶共用固定低阶邻域。

<a id="n10-07"></a>
### N10.07 精确二次误差恒等式

**输出：** 证明D_xR V y=y+Q(state,q)[R(state,q),y]，并覆盖q=0可去点。

**局部依赖：** N10.01, N10.02, N10.03, N10.04, N10.05, N10.06。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“精确二次误差恒等式”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 等式在实际函数空间中成立，非只逐点形式计算。
- 与H03采用的接口逐字段相合。

**本轮核对：** 未找到“精确二次误差恒等式”对应的实际项目声明。未构造独立二残差Q及全两行恒等式；scalar局部公式不替代本项。

**未完成内容：**
- 尚待实际实现并证明：证明D_xR V y=y+Q(state,q)[R(state,q),y]，并覆盖q=0可去点。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：等式在实际函数空间中成立，非只逐点形式计算。
- acceptance.02 [uncovered]：本条尚无对应实际输出：与H03采用的接口逐字段相合。

<a id="n10-08"></a>
### N10.08 组装：两个独立残差的精确二次误差

**输出：** 构造对任意独立r=(r₁,r₂)、y=(f,g)双线性且smooth tame的Q_x,q(r,y)，证明D_xR·Vy=y+Q_x,q(R,y)，并证明输出源兼容。

**局部依赖：** N10.01, N10.02, N10.03, N10.04, N10.05, N10.06, N10.07。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 100–250 行。已有子结论的接口组装与完整量词核对；不把尚未证明的子结论作为新假设。

**验收条件：**

- 不能用O(‖R‖‖y‖)估计替代精确恒等式
- 真正双线性且定义在全部独立残差上
- source积分和奇偶条件闭合
- 逐项调用以上子任务的实际结论；所有见证、范数、参数和允许依赖与原节点一致。

**本轮核对：** 未找到“组装：两个独立残差的精确二次误差”对应的实际项目声明。未构造独立二残差Q及全两行恒等式；scalar局部公式不替代本项。

**未完成内容：**
- 尚待实际实现并证明：构造对任意独立r=(r₁,r₂)、y=(f,g)双线性且smooth tame的Q_x,q(r,y)，证明D_xR·Vy=y+Q_x,q(R,y)，并证明输出源兼容。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：不能用O(‖R‖‖y‖)估计替代精确恒等式
- acceptance.02 [uncovered]：本条尚无对应实际输出：真正双线性且定义在全部独立残差上
- acceptance.03 [uncovered]：本条尚无对应实际输出：source积分和奇偶条件闭合
- acceptance.04 [uncovered]：本条尚无对应实际输出：逐项调用以上子任务的实际结论；所有见证、范数、参数和允许依赖与原节点一致。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：构造对任意独立r=(r₁,r₂)、y=(f,g)双线性且smooth tame的Q_x,q(r,y)，证明D_xR·Vy=y+Q_x,q(R,y)，并证明输出源兼容。 | N10.08（组合全部子任务） |
| acceptance.01：不能用O(‖R‖‖y‖)估计替代精确恒等式 | N10.01, N10.07 |
| acceptance.02：真正双线性且定义在全部独立残差上 | N10.02, N10.03 |
| acceptance.03：source积分和奇偶条件闭合 | N10.04, N10.05, N10.06 |

<a id="h03"></a>
## H03 带二次误差的Nash–Moser隐函数定理

**原节点完整目标：** 在真实tame空间开集上，smooth tame的R,V,Q满足上述精确二次误差恒等式且初值为零，则存在同一参数开邻域上的解；须得到本工程需要的正则性和参数依赖。

**原上游里程碑：** H01

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [09-solving-the-equation.tex:183–196](../../paper/flexible-surface-rewrite/09-solving-the-equation.tex#L183)

<a id="h03-01"></a>
### H03.01 二次误差IFT的精确适用接口

**输出：** 固定实际tame空间开集、参数空间、初始零点和R,V,Q的全量词假设。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“二次误差IFT的精确适用接口”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- V对源线性、Q对两个独立残差双线性。
- 不得把待证存在结论作为结构字段或新公理。

**本轮核对：** 未找到“二次误差IFT的精确适用接口”对应的实际项目声明。未定义实际平滑Newton迭代、预算或共同参数域的Nash–Moser存在证明；模型smoothing不替代它。

**未完成内容：**
- 尚待实际实现并证明：固定实际tame空间开集、参数空间、初始零点和R,V,Q的全量词假设。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：V对源线性、Q对两个独立残差双线性。
- acceptance.02 [uncovered]：本条尚无对应实际输出：不得把待证存在结论作为结构字段或新公理。

<a id="h03-02"></a>
### H03.02 统一邻域与有限损失预算

**输出：** 从R,V,Q真实tame界抽取一次性的基阶、loss、低阶半径和迭代所需有限阶常数。

**局部依赖：** H03.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“统一邻域与有限损失预算”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 输出阶增长不重选基邻域。
- 保留参数开集及初始零点的实际开性。

**本轮核对：** 未找到“统一邻域与有限损失预算”对应的实际项目声明。未定义实际平滑Newton迭代、预算或共同参数域的Nash–Moser存在证明；模型smoothing不替代它。

**未完成内容：**
- 尚待实际实现并证明：从R,V,Q真实tame界抽取一次性的基阶、loss、低阶半径和迭代所需有限阶常数。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：输出阶增长不重选基邻域。
- acceptance.02 [uncovered]：本条尚无对应实际输出：保留参数开集及初始零点的实际开性。

<a id="h03-03"></a>
### H03.03 平滑尺度序列及离散求和

**输出：** 选定θ_n的明确增长律，证明迭代将用到的幂衰减与可求和不等式。

**局部依赖：** H03.02。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“平滑尺度序列及离散求和”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 指数选择与全部固定loss预算相容。
- 离散起始尺度的允许依赖明确。

**本轮核对：** 未找到“平滑尺度序列及离散求和”对应的实际项目声明。未定义实际平滑Newton迭代、预算或共同参数域的Nash–Moser存在证明；模型smoothing不替代它。

**未完成内容：**
- 尚待实际实现并证明：选定θ_n的明确增长律，证明迭代将用到的幂衰减与可求和不等式。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：指数选择与全部固定loss预算相容。
- acceptance.02 [uncovered]：本条尚无对应实际输出：离散起始尺度的允许依赖明确。

<a id="h03-04"></a>
### H03.04 平滑、余项及插值的定量包

**输出：** 把H01实际Sθ估计整理为同一迭代算法可调用的高低阶与I−Sθ界。

**局部依赖：** H03.01, H03.02。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“平滑、余项及插值的定量包”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 所有阶移常数完整保留。
- 不能用抽象任意SmoothTame谓词跳过真实算子。

**本轮核对：** 未找到“平滑、余项及插值的定量包”对应的实际项目声明。未定义实际平滑Newton迭代、预算或共同参数域的Nash–Moser存在证明；模型smoothing不替代它。

**未完成内容：**
- 尚待实际实现并证明：把H01实际Sθ估计整理为同一迭代算法可调用的高低阶与I−Sθ界。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：所有阶移常数完整保留。
- acceptance.02 [uncovered]：本条尚无对应实际输出：不能用抽象任意SmoothTame谓词跳过真实算子。

<a id="h03-05"></a>
### H03.05 迭代修正算法的实际定义

**输出：** 选定适用于二次误差恒等式的平滑Newton算法，定义state、修正、残差及累计平滑缺陷。

**局部依赖：** H03.01, H03.02, H03.03, H03.04。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“迭代修正算法的实际定义”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 每个量都是实际空间元素与实际函数。
- 算法是否为Hamilton版或专用版明确，不能混用两套预算。

**本轮核对：** 未找到“迭代修正算法的实际定义”对应的实际项目声明。未定义实际平滑Newton迭代、预算或共同参数域的Nash–Moser存在证明；模型smoothing不替代它。

**未完成内容：**
- 尚待实际实现并证明：选定适用于二次误差恒等式的平滑Newton算法，定义state、修正、残差及累计平滑缺陷。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：每个量都是实际空间元素与实际函数。
- acceptance.02 [uncovered]：本条尚无对应实际输出：算法是否为Hamilton版或专用版明确，不能混用两套预算。

<a id="h03-06"></a>
### H03.06 单步修正的良定义与平滑

**输出：** 证明只要state在固定邻域，平滑修正和全部辅助量良定义并对参数光滑。

**局部依赖：** H03.05。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“单步修正的良定义与平滑”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- V与R的作用域及各阶损失匹配。
- 每一步保持实际线性约束slice。

**本轮核对：** 未找到“单步修正的良定义与平滑”对应的实际项目声明。未定义实际平滑Newton迭代、预算或共同参数域的Nash–Moser存在证明；模型smoothing不替代它。

**未完成内容：**
- 尚待实际实现并证明：证明只要state在固定邻域，平滑修正和全部辅助量良定义并对参数光滑。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：V与R的作用域及各阶损失匹配。
- acceptance.02 [uncovered]：本条尚无对应实际输出：每一步保持实际线性约束slice。

<a id="h03-07"></a>
### H03.07 单步残差的精确分解

**输出：** 用Taylor积分余项和D R V=I+Q(R,·)证明新残差=平滑误差+二次误差+累计缺陷。

**局部依赖：** H03.05, H03.06。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 350–750 行。围绕“单步残差的精确分解”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 每项为真实恒等式，不能仅写预计二次收敛。
- Q两个独立变量的用法与N10接口一致。

**本轮核对：** 未找到“单步残差的精确分解”对应的实际项目声明。未定义实际平滑Newton迭代、预算或共同参数域的Nash–Moser存在证明；模型smoothing不替代它。

**未完成内容：**
- 尚待实际实现并证明：用Taylor积分余项和D R V=I+Q(R,·)证明新残差=平滑误差+二次误差+累计缺陷。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：每项为真实恒等式，不能仅写预计二次收敛。
- acceptance.02 [uncovered]：本条尚无对应实际输出：Q两个独立变量的用法与N10接口一致。

<a id="h03-08"></a>
### H03.08 低阶Taylor二次余项界

**输出：** 在固定低阶邻域证明R(x+Δ)−R(x)−DR(x)Δ的二次范数界。

**局部依赖：** H03.02, H03.07。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“低阶Taylor二次余项界”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 积分路径留在同一开集。
- 参数常数及所需高阶state输入明确。

**本轮核对：** 未找到“低阶Taylor二次余项界”对应的实际项目声明。未定义实际平滑Newton迭代、预算或共同参数域的Nash–Moser存在证明；模型smoothing不替代它。

**未完成内容：**
- 尚待实际实现并证明：在固定低阶邻域证明R(x+Δ)−R(x)−DR(x)Δ的二次范数界。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：积分路径留在同一开集。
- acceptance.02 [uncovered]：本条尚无对应实际输出：参数常数及所需高阶state输入明确。

<a id="h03-09"></a>
### H03.09 误差Q的定量二次控制

**输出：** 从真实双线性tame界控制Q(R,y)，配合平滑阶选择给出低阶衰减。

**局部依赖：** H03.02, H03.04, H03.07。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“误差Q的定量二次控制”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 两个弱因子及高低阶分配分别列出。
- 不能把二次误差当作精确右逆。

**本轮核对：** 未找到“误差Q的定量二次控制”对应的实际项目声明。未定义实际平滑Newton迭代、预算或共同参数域的Nash–Moser存在证明；模型smoothing不替代它。

**未完成内容：**
- 尚待实际实现并证明：从真实双线性tame界控制Q(R,y)，配合平滑阶选择给出低阶衰减。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：两个弱因子及高低阶分配分别列出。
- acceptance.02 [uncovered]：本条尚无对应实际输出：不能把二次误差当作精确右逆。

<a id="h03-10"></a>
### H03.10 平滑缺陷和交换误差控制

**输出：** 控制(I−Sθ)残差以及算法实际产生的平滑/微分交换项和累计缺陷。

**局部依赖：** H03.03, H03.04, H03.07。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“平滑缺陷和交换误差控制”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 逐项包含所选算法全部误差项。
- 任何不能闭合的损失必须回到预算节点修改而非省略。

**本轮核对：** 未找到“平滑缺陷和交换误差控制”对应的实际项目声明。未定义实际平滑Newton迭代、预算或共同参数域的Nash–Moser存在证明；模型smoothing不替代它。

**未完成内容：**
- 尚待实际实现并证明：控制(I−Sθ)残差以及算法实际产生的平滑/微分交换项和累计缺陷。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：逐项包含所选算法全部误差项。
- acceptance.02 [uncovered]：本条尚无对应实际输出：任何不能闭合的损失必须回到预算节点修改而非省略。

<a id="h03-11"></a>
### H03.11 修正在低阶范数的收缩界

**输出：** 由V固定loss和平滑增益证明Δ_n的低阶可求和上界。

**局部依赖：** H03.06, H03.08, H03.09, H03.10。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“修正在低阶范数的收缩界”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 衰减指数严格足以求和。
- 同一初始尺度兼容全部低阶条件。

**本轮核对：** 未找到“修正在低阶范数的收缩界”对应的实际项目声明。未定义实际平滑Newton迭代、预算或共同参数域的Nash–Moser存在证明；模型smoothing不替代它。

**未完成内容：**
- 尚待实际实现并证明：由V固定loss和平滑增益证明Δ_n的低阶可求和上界。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：衰减指数严格足以求和。
- acceptance.02 [uncovered]：本条尚无对应实际输出：同一初始尺度兼容全部低阶条件。

<a id="h03-12"></a>
### H03.12 高阶state增长的归纳界

**输出：** 证明迭代state在每个高阶seminorm有明确θ_n幂增长，而只以低阶小量控制域。

**局部依赖：** H03.02, H03.04, H03.06, H03.08, H03.09, H03.10。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 350–750 行。围绕“高阶state增长的归纳界”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 允许C_s随s变化。
- 高阶增长不触发重新缩小参数或state邻域。

**本轮核对：** 未找到“高阶state增长的归纳界”对应的实际项目声明。未定义实际平滑Newton迭代、预算或共同参数域的Nash–Moser存在证明；模型smoothing不替代它。

**未完成内容：**
- 尚待实际实现并证明：证明迭代state在每个高阶seminorm有明确θ_n幂增长，而只以低阶小量控制域。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：允许C_s随s变化。
- acceptance.02 [uncovered]：本条尚无对应实际输出：高阶增长不触发重新缩小参数或state邻域。

<a id="h03-13"></a>
### H03.13 残差衰减的闭合归纳

**输出：** 同时闭合低阶残差、累计缺陷及修正界的全部归纳不等式。

**局部依赖：** H03.03, H03.08, H03.09, H03.10, H03.11, H03.12。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 350–750 行。围绕“残差衰减的闭合归纳”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 初始步从初始零点及参数小量实际验证。
- 所有指数不等式和常数选择次序明写。

**本轮核对：** 未找到“残差衰减的闭合归纳”对应的实际项目声明。未定义实际平滑Newton迭代、预算或共同参数域的Nash–Moser存在证明；模型smoothing不替代它。

**未完成内容：**
- 尚待实际实现并证明：同时闭合低阶残差、累计缺陷及修正界的全部归纳不等式。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：初始步从初始零点及参数小量实际验证。
- acceptance.02 [uncovered]：本条尚无对应实际输出：所有指数不等式和常数选择次序明写。

<a id="h03-14"></a>
### H03.14 全部迭代留在共同开集

**输出：** 由低阶修正和的上界证明每个state及Taylor连接段都在固定低阶邻域。

**局部依赖：** H03.11, H03.13。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“全部迭代留在共同开集”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 选择一次参数半径与初始尺度。
- 不以尚待证明的极限存在反证迭代合法。

**本轮核对：** 未找到“全部迭代留在共同开集”对应的实际项目声明。未定义实际平滑Newton迭代、预算或共同参数域的Nash–Moser存在证明；模型smoothing不替代它。

**未完成内容：**
- 尚待实际实现并证明：由低阶修正和的上界证明每个state及Taylor连接段都在固定低阶邻域。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：选择一次参数半径与初始尺度。
- acceptance.02 [uncovered]：本条尚无对应实际输出：不以尚待证明的极限存在反证迭代合法。

<a id="h03-15"></a>
### H03.15 任意阶修正的可求和恢复

**输出：** 结合低阶衰减、高阶增长和插值，证明每个固定s下Σ||Δ_n||_s收敛。

**局部依赖：** H03.04, H03.11, H03.12, H03.13, H03.14。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 350–750 行。围绕“任意阶修正的可求和恢复”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 每阶常数可变，但θ_n、初始尺度及参数域同一。
- 不能仅得到有限某一阶收敛。

**本轮核对：** 未找到“任意阶修正的可求和恢复”对应的实际项目声明。未定义实际平滑Newton迭代、预算或共同参数域的Nash–Moser存在证明；模型smoothing不替代它。

**未完成内容：**
- 尚待实际实现并证明：结合低阶衰减、高阶增长和插值，证明每个固定s下Σ||Δ_n||_s收敛。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：每阶常数可变，但θ_n、初始尺度及参数域同一。
- acceptance.02 [uncovered]：本条尚无对应实际输出：不能仅得到有限某一阶收敛。

<a id="h03-16"></a>
### H03.16 Fréchet极限的实际构造

**输出：** 由每级Cauchy和相容完备性构造单一极限x(q)，并保留slice和参考初值。

**局部依赖：** H03.15。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“Fréchet极限的实际构造”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 所有级上的极限是同一相容对象。
- 极限没有携带新的存在性假设。

**本轮核对：** 未找到“Fréchet极限的实际构造”对应的实际项目声明。未定义实际平滑Newton迭代、预算或共同参数域的Nash–Moser存在证明；模型smoothing不替代它。

**未完成内容：**
- 尚待实际实现并证明：由每级Cauchy和相容完备性构造单一极限x(q)，并保留slice和参考初值。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：所有级上的极限是同一相容对象。
- acceptance.02 [uncovered]：本条尚无对应实际输出：极限没有携带新的存在性假设。

<a id="h03-17"></a>
### H03.17 极限残差严格为零

**输出：** 用R的实际连续性、state收敛和残差衰减证明R(x(q),q)=0。

**局部依赖：** H03.13, H03.16。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“极限残差严格为零”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 等式在全部目标空间成立。
- 初始q=0时返回指定参考state。

**本轮核对：** 未找到“极限残差严格为零”对应的实际项目声明。未定义实际平滑Newton迭代、预算或共同参数域的Nash–Moser存在证明；模型smoothing不替代它。

**未完成内容：**
- 尚待实际实现并证明：用R的实际连续性、state收敛和残差衰减证明R(x(q),q)=0。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：等式在全部目标空间成立。
- acceptance.02 [uncovered]：本条尚无对应实际输出：初始q=0时返回指定参考state。

<a id="h03-18"></a>
### H03.18 参数紧子集上的统一收敛

**输出：** 把前述估计统一到一次选定参数区间的紧子集，证明x_n→x的局部一致逐阶收敛。

**局部依赖：** H03.14, H03.15, H03.16。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“参数紧子集上的统一收敛”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 整个参数开区间不随输出阶变化。
- 所有参数sup由实际有限阶tame估计支付。

**本轮核对：** 未找到“参数紧子集上的统一收敛”对应的实际项目声明。未定义实际平滑Newton迭代、预算或共同参数域的Nash–Moser存在证明；模型smoothing不替代它。

**未完成内容：**
- 尚待实际实现并证明：把前述估计统一到一次选定参数区间的紧子集，证明x_n→x的局部一致逐阶收敛。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：整个参数开区间不随输出阶变化。
- acceptance.02 [uncovered]：本条尚无对应实际输出：所有参数sup由实际有限阶tame估计支付。

<a id="h03-19"></a>
### H03.19 参数一阶导数的迭代方程

**输出：** 逐步微分实际迭代定义，给出D_qx_n及辅助误差的一阶递推。

**局部依赖：** H03.06, H03.07, H03.18。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“参数一阶导数的迭代方程”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 包含Sθ与实际state依赖引起的全部项。
- 不直接以对极限方程形式微分代替存在导数。

**本轮核对：** 未找到“参数一阶导数的迭代方程”对应的实际项目声明。未定义实际平滑Newton迭代、预算或共同参数域的Nash–Moser存在证明；模型smoothing不替代它。

**未完成内容：**
- 尚待实际实现并证明：逐步微分实际迭代定义，给出D_qx_n及辅助误差的一阶递推。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：包含Sθ与实际state依赖引起的全部项。
- acceptance.02 [uncovered]：本条尚无对应实际输出：不直接以对极限方程形式微分代替存在导数。

<a id="h03-20"></a>
### H03.20 参数一阶导数的统一Cauchy界

**输出：** 对已写一阶递推闭合导数误差归纳，证明D_qx_n在每seminorm局部一致收敛。

**局部依赖：** H03.11, H03.12, H03.13, H03.15, H03.19。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 350–750 行。围绕“参数一阶导数的统一Cauchy界”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 导数loss由同一平滑预算吸收。
- 参数区间仍为同一个既定区间。

**本轮核对：** 未找到“参数一阶导数的统一Cauchy界”对应的实际项目声明。未定义实际平滑Newton迭代、预算或共同参数域的Nash–Moser存在证明；模型smoothing不替代它。

**未完成内容：**
- 尚待实际实现并证明：对已写一阶递推闭合导数误差归纳，证明D_qx_n在每seminorm局部一致收敛。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：导数loss由同一平滑预算吸收。
- acceptance.02 [uncovered]：本条尚无对应实际输出：参数区间仍为同一个既定区间。

<a id="h03-21"></a>
### H03.21 任意参数阶的递推与估计

**输出：** 对k归纳写出D_qᵏ迭代公式，证明导数增量在每个目标seminorm可求和。

**局部依赖：** H03.04, H03.07, H03.18, H03.19, H03.20。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 350–750 行。围绕“任意参数阶的递推与估计”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 所有低阶导数乘积使用一高因子tame/interpolation估计。
- 固定k可改变常数但不改变初始参数域。

**本轮核对：** 未找到“任意参数阶的递推与估计”对应的实际项目声明。未定义实际平滑Newton迭代、预算或共同参数域的Nash–Moser存在证明；模型smoothing不替代它。

**未完成内容：**
- 尚待实际实现并证明：对k归纳写出D_qᵏ迭代公式，证明导数增量在每个目标seminorm可求和。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：所有低阶导数乘积使用一高因子tame/interpolation估计。
- acceptance.02 [uncovered]：本条尚无对应实际输出：固定k可改变常数但不改变初始参数域。

<a id="h03-22"></a>
### H03.22 极限与各阶参数微分交换

**输出：** 由实际局部一致导数收敛证明x为C∞参数映射，并识别各阶极限为D_qᵏx。

**局部依赖：** H03.18, H03.20, H03.21。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“极限与各阶参数微分交换”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 使用H01同一方向微积分与具体参数ContDiff桥接。
- 不能只断言逐阶解存在即联合光滑。

**本轮核对：** 未找到“极限与各阶参数微分交换”对应的实际项目声明。未定义实际平滑Newton迭代、预算或共同参数域的Nash–Moser存在证明；模型smoothing不替代它。

**未完成内容：**
- 尚待实际实现并证明：由实际局部一致导数收敛证明x为C∞参数映射，并识别各阶极限为D_qᵏx。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：使用H01同一方向微积分与具体参数ContDiff桥接。
- acceptance.02 [uncovered]：本条尚无对应实际输出：不能只断言逐阶解存在即联合光滑。

<a id="h03-23"></a>
### H03.23 所需tame参数估计与定理组装

**输出：** 把解的全部阶估计写成适用版本的smooth/tame分支结论，保持同一个开邻域。

**局部依赖：** H03.16, H03.17, H03.18, H03.22。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“所需tame参数估计与定理组装”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 准确说明所证Hamilton适用版本的全部输出。
- 普通Banach隐函数定理不能替代上述导数损失证明。

**本轮核对：** 未找到“所需tame参数估计与定理组装”对应的实际项目声明。未定义实际平滑Newton迭代、预算或共同参数域的Nash–Moser存在证明；模型smoothing不替代它。

**未完成内容：**
- 尚待实际实现并证明：把解的全部阶估计写成适用版本的smooth/tame分支结论，保持同一个开邻域。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：准确说明所证Hamilton适用版本的全部输出。
- acceptance.02 [uncovered]：本条尚无对应实际输出：普通Banach隐函数定理不能替代上述导数损失证明。

<a id="h03-24"></a>
### H03.24 组装：带二次误差的Nash–Moser隐函数定理

**输出：** 在真实tame空间开集上，smooth tame的R,V,Q满足上述精确二次误差恒等式且初值为零，则存在同一参数开邻域上的解；须得到本工程需要的正则性和参数依赖。

**局部依赖：** H03.01, H03.02, H03.03, H03.04, H03.05, H03.06, H03.07, H03.08, H03.09, H03.10, H03.11, H03.12, H03.13, H03.14, H03.15, H03.16, H03.17, H03.18, H03.19, H03.20, H03.21, H03.22, H03.23。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 100–250 行。已有子结论的接口组装与完整量词核对；不把尚未证明的子结论作为新假设。

**验收条件：**

- 不能用普通Banach隐函数定理代替
- 不能只把Hamilton结论作为假设/公理
- 换实现路线前必须保留相同的解存在结论
- 逐项调用以上子任务的实际结论；所有见证、范数、参数和允许依赖与原节点一致。

**本轮核对：** 未找到“组装：带二次误差的Nash–Moser隐函数定理”对应的实际项目声明。未定义实际平滑Newton迭代、预算或共同参数域的Nash–Moser存在证明；模型smoothing不替代它。

**未完成内容：**
- 尚待实际实现并证明：在真实tame空间开集上，smooth tame的R,V,Q满足上述精确二次误差恒等式且初值为零，则存在同一参数开邻域上的解；须得到本工程需要的正则性和参数依赖。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：不能用普通Banach隐函数定理代替
- acceptance.02 [uncovered]：本条尚无对应实际输出：不能只把Hamilton结论作为假设/公理
- acceptance.03 [uncovered]：本条尚无对应实际输出：换实现路线前必须保留相同的解存在结论
- acceptance.04 [uncovered]：本条尚无对应实际输出：逐项调用以上子任务的实际结论；所有见证、范数、参数和允许依赖与原节点一致。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：在真实tame空间开集上，smooth tame的R,V,Q满足上述精确二次误差恒等式且初值为零，则存在同一参数开邻域上的解；须得到本工程需要的正则性和参数依赖。 | H03.24（组合全部子任务） |
| acceptance.01：不能用普通Banach隐函数定理代替 | H03.02, H03.03, H03.04, H03.05, H03.07, H03.13, H03.15, H03.23 |
| acceptance.02：不能只把Hamilton结论作为假设/公理 | H03.01, H03.05, H03.13, H03.16, H03.17, H03.22 |
| acceptance.03：换实现路线前必须保留相同的解存在结论 | H03.01, H03.05, H03.17, H03.23 |

<a id="n11"></a>
## N11 弱权非线性解支

**原节点完整目标：** 得到一个共同q₀>0及|q|<q₀上的解x(q)，满足R=0、ℓ*u_q=1、u_q=Φ*+O(q)，全部阶seminorm在同一个区间受控。

**原上游里程碑：** H03, N08, N09, N10

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [09-solving-the-equation.tex:229–238](../../paper/flexible-surface-rewrite/09-solving-the-equation.tex#L229)

<a id="n11-01"></a>
### N11.01 实际空间与IFT接口对接

**输出：** 把H03每个空间、tame retraction、slice和开集字段实例化为本项目X/Y。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“实际空间与IFT接口对接”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 全部输入为W02与N08实际构造。
- 不把抽象结构的存在性留作最终假设。

**本轮核对：** 未找到“实际空间与IFT接口对接”对应的实际项目声明。尚无Nash–Moser实例化产生的同区间实际弱分支。

**未完成内容：**
- 尚待实际实现并证明：把H03每个空间、tame retraction、slice和开集字段实例化为本项目X/Y。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：全部输入为W02与N08实际构造。
- acceptance.02 [uncovered]：本条尚无对应实际输出：不把抽象结构的存在性留作最终假设。

<a id="n11-02"></a>
### N11.02 残差与参考零点假设核验

**输出：** 验证R的smooth tame、q可去点及参考state零。

**局部依赖：** N11.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“残差与参考零点假设核验”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- N08同一R和同一Φ*。
- 参考零点覆盖两行残差。

**本轮核对：** 未找到“残差与参考零点假设核验”对应的实际项目声明。尚无Nash–Moser实例化产生的同区间实际弱分支。

**未完成内容：**
- 尚待实际实现并证明：验证R的smooth tame、q可去点及参考state零。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：N08同一R和同一Φ*。
- acceptance.02 [uncovered]：本条尚无对应实际输出：参考零点覆盖两行残差。

<a id="n11-03"></a>
### N11.03 逆与独立二次误差假设核验

**输出：** 逐项把N09的V及N10的Q代入H03恒等式和tame假设。

**局部依赖：** N11.01, N11.02。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“逆与独立二次误差假设核验”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- Q定义在全部独立残差上。
- 所有映射使用共同低阶邻域及独立q。

**本轮核对：** 未找到“逆与独立二次误差假设核验”对应的实际项目声明。尚无Nash–Moser实例化产生的同区间实际弱分支。

**未完成内容：**
- 尚待实际实现并证明：逐项把N09的V及N10的Q代入H03恒等式和tame假设。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：Q定义在全部独立残差上。
- acceptance.02 [uncovered]：本条尚无对应实际输出：所有映射使用共同低阶邻域及独立q。

<a id="n11-04"></a>
### N11.04 同一参数开区间的分支

**输出：** 实际应用已证明H03得到q₀>0及|q|<q₀上的单一光滑state分支。

**局部依赖：** N11.01, N11.02, N11.03。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“同一参数开区间的分支”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- q₀不随输出阶改变。
- 所有状态分量来自同一选择。

**本轮核对：** 未找到“同一参数开区间的分支”对应的实际项目声明。尚无Nash–Moser实例化产生的同区间实际弱分支。

**未完成内容：**
- 尚待实际实现并证明：实际应用已证明H03得到q₀>0及|q|<q₀上的单一光滑state分支。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：q₀不随输出阶改变。
- acceptance.02 [uncovered]：本条尚无对应实际输出：所有状态分量来自同一选择。

<a id="n11-05"></a>
### N11.05 归一化及参考一阶接近

**输出：** 证明ℓ*u_q=1以及u_q−Φ*=O(q)在每个Xβ阶的真实估计。

**局部依赖：** N11.04。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“归一化及参考一阶接近”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 利用同一区间上的参数导数界。
- q是构造参数，不是最终弯曲相位τ。

**本轮核对：** 未找到“归一化及参考一阶接近”对应的实际项目声明。尚无Nash–Moser实例化产生的同区间实际弱分支。

**未完成内容：**
- 尚待实际实现并证明：证明ℓ*u_q=1以及u_q−Φ*=O(q)在每个Xβ阶的真实估计。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：利用同一区间上的参数导数界。
- acceptance.02 [uncovered]：本条尚无对应实际输出：q是构造参数，不是最终弯曲相位τ。

<a id="n11-06"></a>
### N11.06 共同紧参数区间上的全阶控制

**输出：** 一次选择闭子区间，证明每阶seminorm及所需参数导数在该区间有界。

**局部依赖：** N11.04, N11.05。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“共同紧参数区间上的全阶控制”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 实际量词为∃q₀>0 ∀s ∃C_s。
- 不能改成∀s∃q_s。

**本轮核对：** 未找到“共同紧参数区间上的全阶控制”对应的实际项目声明。尚无Nash–Moser实例化产生的同区间实际弱分支。

**未完成内容：**
- 尚待实际实现并证明：一次选择闭子区间，证明每阶seminorm及所需参数导数在该区间有界。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：实际量词为∃q₀>0 ∀s ∃C_s。
- acceptance.02 [uncovered]：本条尚无对应实际输出：不能改成∀s∃q_s。

<a id="n11-07"></a>
### N11.07 组装：弱权非线性解支

**输出：** 得到一个共同q₀>0及|q|<q₀上的解x(q)，满足R=0、ℓ*u_q=1、u_q=Φ*+O(q)，全部阶seminorm在同一个区间受控。

**局部依赖：** N11.01, N11.02, N11.03, N11.04, N11.05, N11.06。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 100–250 行。已有子结论的接口组装与完整量词核对；不把尚未证明的子结论作为新假设。

**验收条件：**

- 不得每个阶数各得一个q_s
- q是构造参数，尚非弯曲相位τ
- 最终必须实际实例化所有分析前提
- 逐项调用以上子任务的实际结论；所有见证、范数、参数和允许依赖与原节点一致。

**本轮核对：** 未找到“组装：弱权非线性解支”对应的实际项目声明。尚无Nash–Moser实例化产生的同区间实际弱分支。

**未完成内容：**
- 尚待实际实现并证明：得到一个共同q₀>0及|q|<q₀上的解x(q)，满足R=0、ℓ*u_q=1、u_q=Φ*+O(q)，全部阶seminorm在同一个区间受控。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：不得每个阶数各得一个q_s
- acceptance.02 [uncovered]：本条尚无对应实际输出：q是构造参数，尚非弯曲相位τ
- acceptance.03 [uncovered]：本条尚无对应实际输出：最终必须实际实例化所有分析前提
- acceptance.04 [uncovered]：本条尚无对应实际输出：逐项调用以上子任务的实际结论；所有见证、范数、参数和允许依赖与原节点一致。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：得到一个共同q₀>0及 / q / <q₀上的解x(q)，满足R=0、ℓ*u_q=1、u_q=Φ*+O(q)，全部阶seminorm在同一个区间受控。 | N11.07（组合全部子任务） |
| acceptance.01：不得每个阶数各得一个q_s | N11.04, N11.06 |
| acceptance.02：q是构造参数，尚非弯曲相位τ | N11.04, N11.05 |
| acceptance.03：最终必须实际实例化所有分析前提 | N11.01, N11.02, N11.03 |

<a id="n12"></a>
## N12 最小平坦环带核心

**原节点完整目标：** 取固定0<|q|<q₀，构造w_q,z_q，证明Nres=0、余度量正定且局部欧氏、半转对称和非径向；w_q各阶零延拓、z_q两端分别常值平坦延拓。

**原上游里程碑：** N11, W03, N01, R12, S03

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [10-endpoint-and-sphere.tex:250–317](../../paper/flexible-surface-rewrite/10-endpoint-and-sphere.tex#L250)

<a id="n12-01"></a>
### N12.01 固定非零构造参数

**输出：** 从N11同一q₀区间选择0<|q|<q₀并冻结state、实际参考几何及规范。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“固定非零构造参数”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 后续所有结论使用同一q。
- 选择不依赖高阶输出或弯曲相位。

**本轮核对：** 未找到“固定非零构造参数”对应的实际项目声明。尚无非零q实际分支及w_q/z_q/Core构造；Core条件接口不证明输入存在。

**未完成内容：**
- 尚待实际实现并证明：从N11同一q₀区间选择0<|q|<q₀并冻结state、实际参考几何及规范。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：后续所有结论使用同一q。
- acceptance.02 [uncovered]：本条尚无对应实际输出：选择不依赖高阶输出或弯曲相位。

<a id="n12-02"></a>
### N12.02 实际profile及高度的构造

**输出：** 定义w_q=w*exp(νχ*+Σκ_mχ_m)，再积分得到h_{w_q}并令z_q=h_{w_q}+qu_q。

**局部依赖：** N12.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“实际profile及高度的构造”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 控制和在实际空间及局部函数意义收敛。
- h的加法规范固定，不能改变两端高差。

**本轮核对：** 未找到“实际profile及高度的构造”对应的实际项目声明。尚无非零q实际分支及w_q/z_q/Core构造；Core条件接口不证明输入存在。

**未完成内容：**
- 尚待实际实现并证明：定义w_q=w*exp(νχ*+Σκ_mχ_m)，再积分得到h_{w_q}并令z_q=h_{w_q}+qu_q。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：控制和在实际空间及局部函数意义收敛。
- acceptance.02 [uncovered]：本条尚无对应实际输出：h的加法规范固定，不能改变两端高差。

<a id="n12-03"></a>
### N12.03 profile内部正性与根germ

**输出：** 由指数正性和N01安全邻域证明w_q>0、同参考根位置及根germ。

**局部依赖：** N12.02。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“profile内部正性与根germ”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 内部严格正与端点零延拓分开表达。
- 不把扩大开collar上错误要求为正。

**本轮核对：** 未找到“profile内部正性与根germ”对应的实际项目声明。尚无非零q实际分支及w_q/z_q/Core构造；Core条件接口不证明输入存在。

**未完成内容：**
- 尚待实际实现并证明：由指数正性和N01安全邻域证明w_q>0、同参考根位置及根germ。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：内部严格正与端点零延拓分开表达。
- acceptance.02 [uncovered]：本条尚无对应实际输出：不把扩大开collar上错误要求为正。

<a id="n12-04"></a>
### N12.04 弱控制足够的profile全阶零延拓

**输出：** 仅用弱β控制、参考profile jets及材料包络，证明w_q全部普通径向导数两端趋0。

**局部依赖：** N12.02, N12.03。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“弱控制足够的profile全阶零延拓”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 不能依赖后置X02的2β或O(q²)加强。
- 用实际Banach值/端点延拓定理得到同一w_q的C∞零延拓。

**本轮核对：** 未找到“弱控制足够的profile全阶零延拓”对应的实际项目声明。尚无非零q实际分支及w_q/z_q/Core构造；Core条件接口不证明输入存在。

**未完成内容：**
- 尚待实际实现并证明：仅用弱β控制、参考profile jets及材料包络，证明w_q全部普通径向导数两端趋0。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：不能依赖后置X02的2β或O(q²)加强。
- acceptance.02 [uncovered]：本条尚无对应实际输出：用实际Banach值/端点延拓定理得到同一w_q的C∞零延拓。

<a id="n12-05"></a>
### N12.05 高度两端常值联合延拓

**输出：** 应用W03到qu_q并结合h_{w_q}证明z_q在两端分别常值C∞延拓。

**局部依赖：** N12.02, N12.04。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“高度两端常值联合延拓”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 允许左右常数不同。
- r/θ混合jets及所需q参数导数均覆盖同一域。

**本轮核对：** 未找到“高度两端常值联合延拓”对应的实际项目声明。尚无非零q实际分支及w_q/z_q/Core构造；Core条件接口不证明输入存在。

**未完成内容：**
- 尚待实际实现并证明：应用W03到qu_q并结合h_{w_q}证明z_q在两端分别常值C∞延拓。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：允许左右常数不同。
- acceptance.02 [uncovered]：本条尚无对应实际输出：r/θ混合jets及所需q参数导数均覆盖同一域。

<a id="n12-06"></a>
### N12.06 真实残差零与余度量正定

**输出：** 由R=0在q≠0处还原真实Nres=0，并从D>0得到g−dz_q²正定。

**局部依赖：** N12.02, N12.03。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 200–500 行。围绕“真实残差零与余度量正定”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 明确归一化残差与真实残差的非零q关系。
- 正定性按显式coordinate pairings证明。

**本轮核对：** 非零q归一化公式及D>0推出真实余度量正定的通用代数结果已证；实际分支和w_q,z_q未构造。

**源码证据 `ContinuousFlexibility/Scalar/Normalization.lean`：** `ContinuousFlexibility.normalizedHeightResidual`, `ContinuousFlexibility.normalizedHeightResidual_zero`, `ContinuousFlexibility.normalizedHeightResidual_of_ne_zero`, `ContinuousFlexibility.normalizedHeightResidual_eq_factored`, `ContinuousFlexibility.contDiffAt_normalizedHeightResidual`, `ContinuousFlexibility.contDiffAt_normalizedHeightResidual_of_residual_zero`

实际scalar归一化残差在q=0可去，识别非零q比值和q=0线性化；只证明点态/有限维平滑。

**源码证据 `ContinuousFlexibility/Scalar/TypeCorrection.lean`：** `ContinuousFlexibility.heightLinearizedDivergence_eq_corrected_of_smooth`, `ContinuousFlexibility.parameter_mul_normalizedHeightResidual`, `ContinuousFlexibility.heightLinearizedDivergence_eq_corrected_normalized`

真实scalar高度线性化与corrected divergence之差是q乘残差角散度；未包括返回修正和chart行。

**源码证据 `ContinuousFlexibility/Scalar/Positivity.lean`：** `ContinuousFlexibility.remainderPositive_of_discriminant_pos`, `ContinuousFlexibility.remainderPositive_iff_discriminant_pos`, `ContinuousFlexibility.radial_remainderPositive_iff_discriminant_pos`, `ContinuousFlexibility.discriminant_pos_iff_height_norm_sq_lt_one`

D>0与真实坐标余度量二次型正定/高度范数<1的实际代数证明，未作用到不存在的实际弱分支。

**未完成内容：**
- 在同一实际分支识别A=0并还原Nres(w_q,z_q)=0。
- 在实际构造的同一w_q,z_q上验证D>0后调用正定性。

**逐条验收：**
- acceptance.01 [partial]：q乘归一化残差=r乘真实残差的公式已证，但R和实际q分支未有。
- acceptance.02 [covered]：正定性用真实显式坐标二次型，不偷用PolarPoint max norm的欧氏恒等式。

<a id="n12-07"></a>
### N12.07 真实Cartan连接及局部欧氏

**输出：** 用S03实际导数/Cartan公式把Nres=0识别为闭连接并得到所需局部欧氏结构。

**局部依赖：** N12.05, N12.06。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 300–650 行。围绕“真实Cartan连接及局部欧氏”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 不能把flat命名为未经识别的任意谓词。
- 不假设环带上全局实primitive。

**本轮核对：** 本项是Nres=0推出真实闭连接与局部欧氏的通用子定理；现有真实Cartan和局部发展结果完整覆盖，不构造Core或声明其非空。

**源码证据 `ContinuousFlexibility/Geometry/HeightCoframe.lean`：** `ContinuousFlexibility.heightCoframe_square_sum`, `ContinuousFlexibility.heightCoframe_cartan`, `ContinuousFlexibility.heightConnection_exterior_eq_residual`, `ContinuousFlexibility.heightConnection_closed_of_residual_zero`

实际coframe平方和识别余度量、真实Cartan结构方程及真实连接外导数=r·Nres，故Nres=0推出闭连接。

**源码证据 `ContinuousFlexibility/Geometry/FlatDevelopment.lean`：** `ContinuousFlexibility.exists_smooth_remainder_development`, `ContinuousFlexibility.exists_locally_invertible_remainder_development`, `ContinuousFlexibility.coordinate_pair_eq_remainder_of_square_sum`, `ContinuousFlexibility.development_pullback_bilinear`

给定光滑、正定、Nres=0的高度，在凸开局部U构造实际C∞平面发展、正确余度量拉回和光滑局部逆；未假设环带全局primitive。

**逐条验收：**
- acceptance.01 [covered]：真实Cartan/连接外导数及发展拉回余度量识别flatness，不是任意谓词。
- acceptance.02 [covered]：发展仅在凸开局部U构造，没有假设环带全局实primitive。

<a id="n12-08"></a>
### N12.08 半周期实偶性与非径向见证

**输出：** 证明z_q保留实偶π周期；由ℓ*u_q=1且q≠0得到两个角值不同。

**局部依赖：** N12.02, N12.05。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 300–650 行。围绕“半周期实偶性与非径向见证”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 非径向从真实函数值推出，不仅抽象系数不零。
- h_{w_q}径向项不影响角差。

**本轮核对：** 未找到“半周期实偶性与非径向见证”对应的实际项目声明。尚无非零q实际分支及w_q/z_q/Core构造；Core条件接口不证明输入存在。

**未完成内容：**
- 尚待实际实现并证明：证明z_q保留实偶π周期；由ℓ*u_q=1且q≠0得到两个角值不同。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：非径向从真实函数值推出，不仅抽象系数不零。
- acceptance.02 [uncovered]：本条尚无对应实际输出：h_{w_q}径向项不影响角差。

<a id="n12-09"></a>
### N12.09 无附加存在性假设的Core输出

**输出：** 把同一a,b,w_q,z_q及所有全局延拓字段装入实际FlatAnnularCore。

**局部依赖：** N12.01, N12.02, N12.03, N12.04, N12.05, N12.06, N12.07, N12.08。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。围绕“无附加存在性假设的Core输出”的单一输出估计；已有库桥接或证明展开超出上界时继续细分。

**验收条件：**

- 调用Contracts/Annular当前接口，不添加P或Cartesian-flatness为输入。
- Core非空由本构造推出，不保留RadialReference或Hamilton结论假设。

**本轮核对：** 未找到“无附加存在性假设的Core输出”对应的实际项目声明。尚无非零q实际分支及w_q/z_q/Core构造；Core条件接口不证明输入存在。

**未完成内容：**
- 尚待实际实现并证明：把同一a,b,w_q,z_q及所有全局延拓字段装入实际FlatAnnularCore。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：调用Contracts/Annular当前接口，不添加P或Cartesian-flatness为输入。
- acceptance.02 [uncovered]：本条尚无对应实际输出：Core非空由本构造推出，不保留RadialReference或Hamilton结论假设。

<a id="n12-10"></a>
### N12.10 组装：最小平坦环带核心

**输出：** 取固定0<|q|<q₀，构造w_q,z_q，证明Nres=0、余度量正定且局部欧氏、半转对称和非径向；w_q各阶零延拓、z_q两端分别常值平坦延拓。

**局部依赖：** N12.01, N12.02, N12.03, N12.04, N12.05, N12.06, N12.07, N12.08, N12.09。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 100–250 行。已有子结论的接口组装与完整量词核对；不把尚未证明的子结论作为新假设。

**验收条件：**

- 不能因强估计后置而省掉w_q的延拓证明
- 左右常数允许不同
- 输出不携带未证明的存在性前提
- 逐项调用以上子任务的实际结论；所有见证、范数、参数和允许依赖与原节点一致。

**本轮核对：** 未找到“组装：最小平坦环带核心”对应的实际项目声明。尚无非零q实际分支及w_q/z_q/Core构造；Core条件接口不证明输入存在。

**未完成内容：**
- 尚待实际实现并证明：取固定0<|q|<q₀，构造w_q,z_q，证明Nres=0、余度量正定且局部欧氏、半转对称和非径向；w_q各阶零延拓、z_q两端分别常值平坦延拓。

**逐条验收：**
- acceptance.01 [uncovered]：本条尚无对应实际输出：不能因强估计后置而省掉w_q的延拓证明
- acceptance.02 [uncovered]：本条尚无对应实际输出：左右常数允许不同
- acceptance.03 [uncovered]：本条尚无对应实际输出：输出不携带未证明的存在性前提
- acceptance.04 [uncovered]：本条尚无对应实际输出：逐项调用以上子任务的实际结论；所有见证、范数、参数和允许依赖与原节点一致。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：取固定0< / q / <q₀，构造w_q,z_q，证明Nres=0、余度量正定且局部欧氏、半转对称和非径向；w_q各阶零延拓、z_q两端分别常值平坦延拓。 | N12.10（组合全部子任务） |
| acceptance.01：不能因强估计后置而省掉w_q的延拓证明 | N12.04 |
| acceptance.02：左右常数允许不同 | N12.02, N12.05 |
| acceptance.03：输出不携带未证明的存在性前提 | N12.01, N12.02, N12.03, N12.04, N12.05, N12.06, N12.07, N12.08, N12.09 |

<a id="d01"></a>
## D01 曲面二阶几何与刚体运动自然性

**原节点完整目标：** 对实际光滑曲面嵌入定义诱导度量、单位法向、第二基本形式、形算子、Gaussian曲率及H=tr(S)/2；证明图公式和在欧氏仿射等距/重参数化下的变换律。

**原上游里程碑：** C00

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [01-introduction.tex:33–39](../../paper/flexible-surface-rewrite/01-introduction.tex#L33)；[02-geometry.tex:146–190](../../paper/flexible-surface-rewrite/02-geometry.tex#L146)

<a id="d01-01"></a>
### D01.01 局部第一与第二基本形式核验

**输出：** 对实际 C∞ immersion f 及光滑单位法向 n，核对 I(v,w)=⟪Df v,Df w⟫、II(v,w)=⟪D²f(v,w),n⟫ 与 Gram/shape 定义及 Weingarten 符号的一致性。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 60–180 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 所有双线性等式使用实际 fderiv。
- I 正定由实际 immersion 推出，法向符号在接口中固定。

**可复用基础：** Geometry/SurfaceGeometry.lean 的 I/II、Gram 与 Weingarten 局部定理。

**本轮核对：** 实际 Frechet 一二阶导已定义 I/II、Gram、shape；immersion 下 Gram 正定、shape 关系唯一及 Weingarten 符号已证明。

**源码证据 `ContinuousFlexibility/Geometry/SurfaceGeometry.lean`：** `ContinuousFlexibility.surfaceFirstForm`, `ContinuousFlexibility.surfaceSecondForm`, `ContinuousFlexibility.surfaceGram`, `ContinuousFlexibility.surfaceShapeMatrix`, `ContinuousFlexibility.surfaceGram_posDef`, `ContinuousFlexibility.surfaceGram_mul_shape`, `ContinuousFlexibility.surfaceShapeMatrix_unique`, `ContinuousFlexibility.surfaceSecondForm_eq_neg_normal_derivative`

I/II 为实际 fderiv 双线性式，微分法向正交得 II=-<Df,DN>。

**逐条验收：**
- acceptance.01 [covered]：定义及 shape 关系使用实际 fderiv。
- acceptance.02 [covered]：Gram 正定由实际 fderiv 单射推出，Weingarten 固定法向符号。

<a id="d01-02"></a>
### D01.02 二阶重参数化链式法则

**输出：** 对平面局部微分同胚 φ 证明 D²(f∘φ)=D²f(Dφ,Dφ)+Df(D²φ)，并由实际法向正交消去第二项在 II 中的贡献。

**局部依赖：** D01.01。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 160–400 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- φ 的局部逆和二阶导假设明确。
- 法向项消去由正交证明，不将其作为输入。

**可复用基础：** Geometry/SurfaceReparametrization.lean 已有候选证明；只作复用线索。

**本轮核对：** 实际二阶链式法则及法向额外项消去已证明；定理对任意 C² φ 成立，特别覆盖局部微分同胚。

**源码证据 `ContinuousFlexibility/Geometry/SurfaceReparametrization.lean`：** `ContinuousFlexibility.secondFDeriv_surface_comp`, `ContinuousFlexibility.surfaceSecondForm_comp`, `ContinuousFlexibility.IsUnitSurfaceNormal.comp`

二阶链式法则显式含 Df(D²φ)，II 变换由真实法向切向正交消去该项。

**逐条验收：**
- acceptance.01 [covered]：φ 的实际 C² 假设明确；该更一般结论不需要局部逆假设。
- acceptance.02 [covered]：法向项由 IsUnitSurfaceNormal 的实际正交性质消去，不作为输入。

<a id="d01-03"></a>
### D01.03 形算子共轭与曲率重参数化

**输出：** 从 I/II 的变换式证明 S(f∘φ)=(Dφ)⁻¹S(f)Dφ，推出 K=det S 和 H=tr S/2 在相同运输法向下不变。

**局部依赖：** D01.01, D01.02。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 180–450 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 逆矩阵来自实际局部微分同胚。
- H 的 1/2 和法向方向贯穿等式。

**本轮核对：** 实际 Gram/II 矩阵变换、Jacobian 可逆、shape 共轭及 K/H 重参数化全已证明。

**源码证据 `ContinuousFlexibility/Geometry/SurfaceReparametrization.lean`：** `ContinuousFlexibility.surfaceJacobian_isUnit`, `ContinuousFlexibility.surfaceJacobian_det_ne_zero`, `ContinuousFlexibility.surfaceGram_comp`, `ContinuousFlexibility.surfaceSecondMatrix_comp`, `ContinuousFlexibility.surfaceShapeMatrix_comp`, `ContinuousFlexibility.surfaceGaussianCurvature_comp`, `ContinuousFlexibility.surfaceMeanCurvature_comp`

由真实 Dφ 单射得到逆矩阵，再共轭 shape；det 与 trace/2 保持。

**逐条验收：**
- acceptance.01 [covered]：Jacobian unit 由实际 fderiv φ 单射证明，局部微分同胚为其特例。
- acceptance.02 [covered]：H 的 trace/2 与同一运输法向贯穿最终等式，没有取绝对值。

<a id="d01-04"></a>
### D01.04 坐标形算子成为切空间算子

**输出：** 将局部矩阵 S 经 Df 转为实际曲面切空间上的自伴算子，证明不同曲面图坐标给出同一切空间算子。

**局部依赖：** D01.01, D01.03。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 250–650 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 必须构造切空间上的线性算子和基变换。
- 坐标无关性为等式证明而非定义命名。

**本轮核对：** 局部 shape 和矩阵共轭已证，尚未构造实际曲面切空间的坐标无关自伴算子。

**源码证据 `ContinuousFlexibility/Geometry/SurfaceGeometry.lean`：** `ContinuousFlexibility.surfaceShapeMatrix`, `ContinuousFlexibility.surfaceGram_mul_shape`, `ContinuousFlexibility.surfaceShapeMatrix_unique`

当前只识别局部2×2矩阵。

**源码证据 `ContinuousFlexibility/Geometry/SurfaceReparametrization.lean`：** `ContinuousFlexibility.surfaceShapeMatrix_comp`

矩阵基变换提供下降前提。

**未完成内容：**
- 实际切空间线性算子、自伴性与经 Df 的坐标无关识别。

**逐条验收：**
- acceptance.01 [partial]：目前局部支持未覆盖全部验收；尚缺：实际切空间线性算子、自伴性与经 Df 的坐标无关识别。
- acceptance.02 [partial]：目前局部支持未覆盖全部验收；尚缺：实际切空间线性算子、自伴性与经 Df 的坐标无关识别。

<a id="d01-05"></a>
### D01.05 全局 K 与有向 H 的光滑性

**输出：** 对有限光滑图册中的相容局部法向，用重叠区变换律粘合 K 和 H；证明所得全局函数光滑且限制等于已有图公式。

**局部依赖：** D01.03, D01.04。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 250–650 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- K 独立于法向反号，H 按所选法向变号。
- 实际 ContMDiff/图内 ContDiff 桥接明确。

**本轮核对：** 图的光滑法向、真实局部曲率和图族曲率运输已证；尚无有限曲面图册粘合和全局流形曲率。

**源码证据 `ContinuousFlexibility/Geometry/SurfaceGeometry.lean`：** `ContinuousFlexibility.surfaceGaussianCurvature_neg_normal`, `ContinuousFlexibility.surfaceMeanCurvature_neg_normal`

K 反号不变、H 反号变号已证。

**源码证据 `ContinuousFlexibility/Geometry/GraphSurfaceGeometry.lean`：** `ContinuousFlexibility.contDiff_graphUpwardNormal`, `ContinuousFlexibility.surfaceGaussianCurvature_heightGraph`, `ContinuousFlexibility.surfaceMeanCurvature_heightGraph`

真实局部图公式。

**源码证据 `ContinuousFlexibility/Contracts/GraphFamilyCurvature.lean`：** `ContinuousFlexibility.IsometricGraphDevelopment.rotationNormal_joint_smooth`, `ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_gaussianCurvature`, `ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_meanCurvature`

同一图族的真实法向与 K/H 运输，不是全局图册。

**未完成内容：**
- 有限图册 K/H 的实际粘合与 ContMDiff 桥接。

**逐条验收：**
- acceptance.01 [covered]：图的光滑法向、真实局部曲率和图族曲率运输已证；尚无有限曲面图册粘合和全局流形曲率。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：实际 ContMDiff/图内 ContDiff 桥接明确。

<a id="d01-06"></a>
### D01.06 主方向线与切空间特征线

**输出：** 对自伴形算子的两个不同特征值，证明两条实际主方向线由切空间特征空间给出；识别 marker 中坐标特征向量的 Df 像。

**局部依赖：** D01.04。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 220–550 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 两条线正交且张成切平面。
- 坐标 Hessian 不等不能直接作为主曲率不等结论。

**本轮核对：** marker 实际坐标 shape 特征向量/特征值已证，未识别实际切空间主方向线。

**源码证据 `ContinuousFlexibility/Geometry/MarkedCap.lean`：** `ContinuousFlexibility.surfaceShapeMatrix_markerBump_zero`, `ContinuousFlexibility.surfaceShapeMatrix_markerBump_center_eigenvectors`

得到坐标矩阵 diag(-kA,-kB) 及两特征向量。

**源码证据 `ContinuousFlexibility/Geometry/MarkerStabilizer.lean`：** `ContinuousFlexibility.marker_mem_line_of_eigenvector`, `ContinuousFlexibility.marker_line_preserved_of_commute`

抽象 E3 线代数，未转成实际曲面主线。

**未完成内容：**
- 实际切空间的两条正交主线和张成证明。
- 坐标向量的 Df 像与主方向的对应。

**逐条验收：**
- acceptance.01 [partial]：目前局部支持未覆盖全部验收；尚缺：实际切空间的两条正交主线和张成证明。；坐标向量的 Df 像与主方向的对应。
- acceptance.02 [partial]：目前局部支持未覆盖全部验收；尚缺：实际切空间的两条正交主线和张成证明。；坐标向量的 Df 像与主方向的对应。

<a id="d01-07"></a>
### D01.07 所有环境等距的曲率自然性

**输出：** 把局部仿射等距自然性提升到曲面像与切空间；对任意含反射的 AffineIsometryEquiv，运输法向后保持 K/H，并共轭实际形算子。

**局部依赖：** D01.03, D01.04, D01.05。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 180–480 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 量化所有仿射等距，不预设行列式为正。
- 结论以实际运输法向表述；向外法向的区域识别留给 G15。

**可复用基础：** Geometry/SurfaceGeometry.lean 已有局部 affineIsometry K/H 自然性。

**本轮核对：** 任意含反射仿射等距的局部实际 shape/K/H 自然性已证，但缺任务要求的实际曲面像/切空间全局提升。

**源码证据 `ContinuousFlexibility/Geometry/SurfaceGeometry.lean`：** `ContinuousFlexibility.affineSurfaceMap_eq_rigidSurfaceMap`, `ContinuousFlexibility.surfaceShapeMatrix_affineIsometry`, `ContinuousFlexibility.surfaceGaussianCurvature_affineIsometry`, `ContinuousFlexibility.surfaceMeanCurvature_affineIsometry`, `ContinuousFlexibility.IsUnitSurfaceNormal.rigidSurfaceMap`

量化所有 AffineIsometryEquiv 并以线性部运输法向，当前仍是参数图内声明。

**未完成内容：**
- 曲面像与实际切空间 shape 的全局自然性。

**逐条验收：**
- acceptance.01 [covered]：任意含反射仿射等距的局部实际 shape/K/H 自然性已证，但缺任务要求的实际曲面像/切空间全局提升。
- acceptance.02 [covered]：任意含反射仿射等距的局部实际 shape/K/H 自然性已证，但缺任务要求的实际曲面像/切空间全局提升。

<a id="d01-08"></a>
### D01.08 统一二阶曲面几何接口

**输出：** 对同一实际曲面嵌入和所选单位法向组装诱导度量、II、切空间 S、K/H、图公式、重参数化及任意环境等距自然性。

**局部依赖：** D01.01, D01.02, D01.03, D01.04, D01.05, D01.06, D01.07。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 80–220 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 接口的局部限制与原有编译声明逐项一致。
- 不增加未经证明的全局法向或主方向假设。

**本轮核对：** 局部二阶几何、图公式、重参数化和任意仿射等距自然性具备；实际切空间与全局曲面统一接口仍缺。

**源码证据 `ContinuousFlexibility/Geometry/SurfaceGeometry.lean`：** `ContinuousFlexibility.surfaceShapeMatrix_unique`, `ContinuousFlexibility.surfaceShapeMatrix_affineIsometry`

局部 shape 与环境自然性。

**源码证据 `ContinuousFlexibility/Geometry/SurfaceReparametrization.lean`：** `ContinuousFlexibility.surfaceShapeMatrix_comp`, `ContinuousFlexibility.surfaceMeanCurvature_comp`

局部重参数化。

**源码证据 `ContinuousFlexibility/Geometry/GraphSurfaceGeometry.lean`：** `ContinuousFlexibility.surfaceGaussianCurvature_heightGraph`, `ContinuousFlexibility.surfaceMeanCurvature_heightGraph`

真实图公式。

**未完成内容：**
- D01.04–06 所需切空间、图册独立性及全局光滑性接口。

**逐条验收：**
- acceptance.01 [partial]：目前局部支持未覆盖全部验收；尚缺：D01.04–06 所需切空间、图册独立性及全局光滑性接口。
- acceptance.02 [partial]：目前局部支持未覆盖全部验收；尚缺：D01.04–06 所需切空间、图册独立性及全局光滑性接口。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：对实际光滑曲面嵌入定义诱导度量、单位法向、第二基本形式、形算子、Gaussian曲率及H=tr(S)/2；证明图公式和在欧氏仿射等距/重参数化下的变换律。 | D01.08（组合全部子任务） |
| acceptance.01：曲率marker使用真正Gaussian曲率 | D01.01, D01.03, D01.05 |
| acceptance.02：覆盖环境反射及向外法向的运输 | D01.07 |
| acceptance.03：主方向线与形算子特征空间的对应 | D01.04, D01.06 |
| remaining.01：证明一般重参数化、坐标独立性和全局流形上的曲率接口 | D01.02, D01.03, D01.04, D01.05 |
| remaining.02：实际闭曲面的向外法向识别、principal tangent lines及全局曲面积分尚待完成 | D01.04, D01.06, D01.07, G15.09, G15.10, D02.04, D02.05, D02.10 |

**覆盖说明 D01.remaining.02：** D01.04/06负责实际切空间形算子及主方向线；具体闭曲面的向外法向必须在G15.09/10由实际围成区域识别，真正全局曲面积分由D02.04/05/10构造。D01通用带法向自然性不等于这些具体对象已实例化。该覆盖委托不是D01的反向证明依赖。

<a id="d02"></a>
## D02 曲面面积和有向积分接口

**原节点完整目标：** 建立参数化/像曲面面积对应、有限图册积分独立性、分块拼接及重参数/环境等距换元，并定义实际的∫H_out dA。

**原上游里程碑：** D01

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [02-geometry.tex:258–268](../../paper/flexible-surface-rewrite/02-geometry.tex#L258)；[01-introduction.tex:33–39](../../paper/flexible-surface-rewrite/01-introduction.tex#L33)

<a id="d02-01"></a>
### D02.01 局部面积密度与 Jacobian

**输出：** 对 immersion 图坐标证明 dA 的局部密度为 sqrt(det Gram)，并给出该密度在平面局部微分同胚下的绝对 Jacobian 变换式。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 220–550 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- Gram 正定保证平方根严格正。
- 换元使用 |det Dφ|，包括反向图坐标。

**本轮核对：** 真实局部面积平方根、正性及一般 φ 下 Gram det 的 Jacobian 平方变换已证；尚缺一般面积密度的绝对 Jacobian 变换声明。

**源码证据 `ContinuousFlexibility/Geometry/GraphSurfaceGeometry.lean`：** `ContinuousFlexibility.graphAreaDensity_pos`, `ContinuousFlexibility.graphAreaDensity_eq_sqrt_gram_det`

图密度正且等于 sqrt(det Gram)。

**源码证据 `ContinuousFlexibility/Geometry/SurfaceGeometry.lean`：** `ContinuousFlexibility.surfaceGram_det_pos`

一般 immersion 的 Gram det 正。

**源码证据 `ContinuousFlexibility/Geometry/SurfaceReparametrization.lean`：** `ContinuousFlexibility.surfaceGram_det_comp`

当前显式给 Gram det 乘 Jacobian det 平方。

**源码证据 `ContinuousFlexibility/Contracts/GraphDiskIntegrals.lean`：** `ContinuousFlexibility.surfaceParamAreaDensity`

真实一般参数密度定义存在。

**未完成内容：**
- 证明一般面积密度乘 |det Dφ| 的变换式，包含反向重参数化。

**逐条验收：**
- acceptance.01 [covered]：真实局部面积平方根、正性及一般 φ 下 Gram det 的 Jacobian 平方变换已证；尚缺一般面积密度的绝对 Jacobian 变换声明。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：换元使用 |det Dφ|，包括反向图坐标。

<a id="d02-02"></a>
### D02.02 图坐标上的面积测度

**输出：** 由实际 Lebesgue 测度及面积密度构造图像局部 Borel 测度，证明与图坐标参数积分的推前公式。

**局部依赖：** D02.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 220–550 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 测度载体是实际嵌入像的 Borel 子集。
- 推前公式包含可测性及局部可积性。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 未定义实际像上的局部 Borel 面积测度及参数积分推前。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：测度载体是实际嵌入像的 Borel 子集。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：推前公式包含可测性及局部可积性。

<a id="d02-03"></a>
### D02.03 重叠图上的测度相容

**输出：** 用实际 transition map 和面积密度 Jacobian 式，证明两图在共同像上的局部面积测度完全相等。

**局部依赖：** D02.01, D02.02。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 220–550 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 验证 transition 的双向光滑与可测性。
- 相等作用于任意共同像的可测子集。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 未构造重叠图面积测度相容及任意可测子集相等。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：验证 transition 的双向光滑与可测性。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：相等作用于任意共同像的可测子集。

<a id="d02-04"></a>
### D02.04 有限图册的全局面积测度

**输出：** 用可测不交化或等价的有限图册测度粘合构造全局像面积测度，并证明不依赖覆盖及不交化次序。

**局部依赖：** D02.02, D02.03。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 250–650 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 每个局部限制恢复原局部面积测度。
- 重叠部分仅计一次，不能简单将所有图积分相加。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 未构造有限图册粘合的全局像面积测度或覆盖独立性。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：每个局部限制恢复原局部面积测度。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：重叠部分仅计一次，不能简单将所有图积分相加。

<a id="d02-05"></a>
### D02.05 嵌入拉回面积的全局识别

**输出：** 证明全局像面积测度等于嵌入将诱导黎曼面积测度的推前，并建立可测函数的参数化积分等式。

**局部依赖：** D02.04。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 250–650 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 源面与实际 range 的载体和逆映射明确。
- 面积与参数积分为已证明等式，不用常值别名定义。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 未将实际像面积识别为诱导黎曼面积测度推前。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：源面与实际 range 的载体和逆映射明确。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：面积与参数积分为已证明等式，不用常值别名定义。

<a id="d02-06"></a>
### D02.06 紧曲面上的可积性

**输出：** 证明紧嵌入曲面的总面积有限，连续曲面函数对面积测度可积；特别处理实际光滑 K/H 的可测与可积。

**局部依赖：** D02.04, D02.05。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 180–450 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 有限性由有限图册密度界和紧性导出。
- H 为有符号实函数，不替换为绝对值。

**本轮核对：** 实际紧图盘的参数面积密度及 signed upward H 积分可积性已证；全局曲面面积测度尚缺。

**源码证据 `ContinuousFlexibility/Contracts/GraphDiskIntegrals.lean`：** `ContinuousFlexibility.IsometricGraphDevelopment.areaDensity_integrableOn_closedDisk`, `ContinuousFlexibility.IsometricGraphDevelopment.upwardMeanIntegrand_integrableOn_closedDisk`, `ContinuousFlexibility.IsometricGraphDevelopment.continuous_upwardMeanCurvature`

真正闭盘可积性，H 保留符号。

**未完成内容：**
- 有限图册的全局面积有限性。
- 实际像面积测度下连续函数及全局 K/H 可积。

**逐条验收：**
- acceptance.01 [partial]：目前局部支持未覆盖全部验收；尚缺：有限图册的全局面积有限性。；实际像面积测度下连续函数及全局 K/H 可积。
- acceptance.02 [partial]：目前局部支持未覆盖全部验收；尚缺：有限图册的全局面积有限性。；实际像面积测度下连续函数及全局 K/H 可积。

<a id="d02-07"></a>
### D02.07 环境等距的面积测度推前

**输出：** 对任意环境仿射等距证明其将像面积测度推到变换后曲面的面积测度，并给出带标量被积函数的换元式。

**局部依赖：** D02.03, D02.04。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 200–500 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 同时覆盖含反射的环境等距。
- 标量函数和测度推前方向明确。

**本轮核对：** 任意环境等距的 Gram 保持及实际平面旋转换元已证；尚无像面积测度推前和一般曲面标量换元。

**源码证据 `ContinuousFlexibility/Geometry/SurfaceGeometry.lean`：** `ContinuousFlexibility.surfaceGram_rigidSurfaceMap`, `ContinuousFlexibility.affineSurfaceMap_eq_rigidSurfaceMap`

局部密度不变性的基础。

**源码证据 `ContinuousFlexibility/Contracts/GraphDiskIntegrals.lean`：** `ContinuousFlexibility.measurePreserving_planarRotation`, `ContinuousFlexibility.integral_comp_planarRotation_closedDisk`

真实二维 Lebesgue 换元，不是任意曲面测度推前。

**未完成内容：**
- 实际像面积测度在任意仿射等距下的推前与一般标量积分换元。

**逐条验收：**
- acceptance.01 [partial]：目前局部支持未覆盖全部验收；尚缺：实际像面积测度在任意仿射等距下的推前与一般标量积分换元。
- acceptance.02 [partial]：目前局部支持未覆盖全部验收；尚缺：实际像面积测度在任意仿射等距下的推前与一般标量积分换元。

<a id="d02-08"></a>
### D02.08 曲面重参数化积分换元

**输出：** 对同一像的光滑重参数化证明曲面标量积分与参数积分一致，并与诱导黎曼测度的变化相容。

**局部依赖：** D02.03, D02.05。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 180–450 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 容许反向重参数化，面积密度仍为正。
- 不把参数像相同直接当作积分恒等式。

**本轮核对：** 图盘旋转的实际参数面积及 signed upward H 积分不变已证；一般光滑重参数化的像/诱导黎曼面积换元尚缺。

**源码证据 `ContinuousFlexibility/Contracts/GraphDiskIntegrals.lean`：** `ContinuousFlexibility.integral_comp_planarRotation_closedDisk`, `ContinuousFlexibility.IsometricGraphDevelopment.graphDiskArea_eq_zeroPhase`, `ContinuousFlexibility.IsometricGraphDevelopment.graphDiskUpwardMeanIntegral_eq_zeroPhase`

特定 det=1 旋转及参数积分；源声明明确不包含像面积桥接。

**未完成内容：**
- 包含反向情况的一般曲面重参数化积分换元。
- 诱导黎曼面积与真实像面积对应。

**逐条验收：**
- acceptance.01 [partial]：目前局部支持未覆盖全部验收；尚缺：包含反向情况的一般曲面重参数化积分换元。；诱导黎曼面积与真实像面积对应。
- acceptance.02 [partial]：目前局部支持未覆盖全部验收；尚缺：包含反向情况的一般曲面重参数化积分换元。；诱导黎曼面积与真实像面积对应。

<a id="d02-09"></a>
### D02.09 分块曲面积分及领圈去重

**输出：** 对图盘、固定帽及其共同领圈构造实际可测分割，证明曲面积分的分块加法；给出边界曲线面积零或直接不交分割的证明。

**局部依赖：** D02.04, D02.06。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 250–650 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 明确分块边界和重叠的处理方式。
- 领圈存在面积时通过分割去重，不能擅自认作零测。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 未构造实际图盘/帽的曲面可测不交分割和领圈去重。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：明确分块边界和重叠的处理方式。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：领圈存在面积时通过分割去重，不能擅自认作零测。

<a id="d02-10"></a>
### D02.10 向外有向平均曲率积分接口

**输出：** 对已经由实际区域识别的向外单位法向定义 ∫H_out dA，证明其在同时运输区域与法向的环境等距下自然。

**局部依赖：** D02.06, D02.07, D02.08。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 200–500 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- H=tr(S)/2，保留向外方向。
- 本通用接口不假设本项目具体 Ω 已存在；G15负责实例化。

**本轮核对：** 已定义真实图盘 signed upward H 参数积分并证明可积/不变；尚无 outward 或全局像测度的有向积分。

**源码证据 `ContinuousFlexibility/Contracts/GraphDiskIntegrals.lean`：** `ContinuousFlexibility.IsometricGraphDevelopment.graphDiskUpwardMeanIntegral`, `ContinuousFlexibility.IsometricGraphDevelopment.upwardMeanIntegrand_integrableOn_closedDisk`, `ContinuousFlexibility.IsometricGraphDevelopment.graphDiskUpwardMeanIntegral_eq_zeroPhase`

实际 trace/2 signed H，选择的是 upward 而非已识别的 outward。

**未完成内容：**
- 由实际区域识别 outward 与图法向。
- 全局像测度上的 ∫H_out dA 及环境自然性。

**逐条验收：**
- acceptance.01 [partial]：目前局部支持未覆盖全部验收；尚缺：由实际区域识别 outward 与图法向。；全局像测度上的 ∫H_out dA 及环境自然性。
- acceptance.02 [partial]：目前局部支持未覆盖全部验收；尚缺：由实际区域识别 outward 与图法向。；全局像测度上的 ∫H_out dA 及环境自然性。

<a id="d02-11"></a>
### D02.11 面积及有向积分完整接口

**输出：** 合并局部密度、像面积识别、图册无关性、分块及换元，给出后续闭球面面积和总向外 H 积分所需的全部通用定理。

**局部依赖：** D02.01, D02.02, D02.03, D02.04, D02.05, D02.06, D02.07, D02.08, D02.09, D02.10。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 80–220 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 全部测度和被积函数具有实际几何定义。
- G14/G16不再需要未证明的面积公式或换元黑箱。

**本轮核对：** 参数图盘密度及 signed H 积分部分已实现，完整通用像面积和图册无关积分接口尚缺。

**源码证据 `ContinuousFlexibility/Contracts/GraphDiskIntegrals.lean`：** `ContinuousFlexibility.surfaceParamAreaDensity`, `ContinuousFlexibility.IsometricGraphDevelopment.graphDiskArea`, `ContinuousFlexibility.IsometricGraphDevelopment.graphDiskUpwardMeanIntegral`

这些是具体参数积分对象，并非已构造闭球面像积分。

**未完成内容：**
- D02.02–05/07–10 的全局像面积、图册粘合及 outward 换元。

**逐条验收：**
- acceptance.01 [partial]：目前局部支持未覆盖全部验收；尚缺：D02.02–05/07–10 的全局像面积、图册粘合及 outward 换元。
- acceptance.02 [partial]：目前局部支持未覆盖全部验收；尚缺：D02.02–05/07–10 的全局像面积、图册粘合及 outward 换元。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：建立参数化/像曲面面积对应、有限图册积分独立性、分块拼接及重参数/环境等距换元，并定义实际的∫H_out dA。 | D02.11（组合全部子任务） |
| acceptance.01：面积不是任意常值别名 | D02.01, D02.02, D02.04, D02.05 |
| acceptance.02：有向平均曲率不是 / H /  | D02.06, D02.10 |
| acceptance.03：重叠/缝口不被重复计数 | D02.03, D02.04, D02.09 |

<a id="g01"></a>
## G01 平坦端点扩大为真实开领圈

**原节点完整目标：** 扩大环带，把w以零、z以各自端常数延拓，得到光滑半转对称数据，保留正定平坦余度量，并在两端实际开领圈上w=0,z=c_L/c_R。

**原上游里程碑：** N12, W03, S03

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [02-geometry.tex:9–17](../../paper/flexible-surface-rewrite/02-geometry.tex#L9)；[10-endpoint-and-sphere.tex:304–317](../../paper/flexible-surface-rewrite/10-endpoint-and-sphere.tex#L304)

<a id="g01-01"></a>
### G01.01 扩大半径与常值延拓数据

**输出：** 对同一 FlatAnnularCore 选明确扩大半径 a/2 与 b+1，延续同一 w,z，证明原环带保持及左右独立常数的开领圈等式。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 40–150 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 左右常数 cL、cR 不要求相等。
- 两端领圈是非空开集，非仅端点 jets。

**可复用基础：** Contracts/Annular.lean 的 enlarge_w/enlarge_z 与 collar 定理。

**本轮核对：** 同一 Core 的 enlarge 明确取 a/2、b+1，保留同一 w/z；左右独立常值开领圈与非空性均已证明。

**源码证据 `ContinuousFlexibility/Contracts/Annular.lean`：** `ContinuousFlexibility.FlatAnnularCore.enlarge`, `ContinuousFlexibility.FlatAnnularCore.enlarge_w`, `ContinuousFlexibility.FlatAnnularCore.enlarge_z`, `ContinuousFlexibility.AnnularSolution.left_collar`, `ContinuousFlexibility.AnnularSolution.right_collar`, `ContinuousFlexibility.AnnularSolution.left_collar_nonempty`, `ContinuousFlexibility.AnnularSolution.right_collar_nonempty`

enlarge 只改半径，两端 Ioo collar 真实非空，cLeft/cRight 分别保留。

**逐条验收：**
- acceptance.01 [covered]：没有要求 cLeft=cRight，enlarge 保留两个独立字段。
- acceptance.02 [covered]：明确 Ioo 领圈等式与 nonempty 声明给实际非空开集。

<a id="g01-02"></a>
### G01.02 全部混合导数的光滑延拓接口

**输出：** 核对 N12/W03 实际输出的全阶径向和角向混合导数足以使扩大数据联合 C∞，并在拼接点与给定全局延拓一致。

**局部依赖：** G01.01。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 160–420 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 所有所需 mixed jets 明确量化。
- 若仅给定条件性 Core，结论仍标为条件性而非 Core 非空。

**本轮核对：** 给定 Core 的 C∞ 与常值延拓字段已存在；没有 N12/W03 真实输出到全部 mixed jets 的实例化。

**源码证据 `ContinuousFlexibility/Contracts/Annular.lean`：** `ContinuousFlexibility.FlatAnnularCore`, `ContinuousFlexibility.FlatAnnularCore.enlarge`, `ContinuousFlexibility.FlatAnnularCore.left_flat_germs`, `ContinuousFlexibility.FlatAnnularCore.right_flat_germs`

Core 将全局光滑/端部常值作为输入，enlarge 保持。

**未完成内容：**
- 实际加权分析输出的全部 mixed jets 和联合 C∞ 延拓。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：所有所需 mixed jets 明确量化。
- acceptance.02 [covered]：给定 Core 的 C∞ 与常值延拓字段已存在；没有 N12/W03 真实输出到全部 mixed jets 的实例化。

<a id="g01-03"></a>
### G01.03 拼接点的正定与真实平坦性

**输出：** 证明扩大余度量在端点和开领圈均正定，连接残差为零；零 profile 和常高度确实给 Euclidean remainder。

**局部依赖：** G01.01, G01.02。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 60–180 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 原核心正性与开领圈 w=0 分别表述。
- 平坦来自实际连接残差等式。

**可复用基础：** Scalar/FlatCollar.lean 的真实 jets/D/residual 定理。

**本轮核对：** 扩大数据全域真实正判别式、真实残差零，以及 Cartesian 内外标准余度量和正定性均已证明。

**源码证据 `ContinuousFlexibility/Contracts/Annular.lean`：** `ContinuousFlexibility.FlatAnnularCore.discriminant_pos_global`, `ContinuousFlexibility.FlatAnnularCore.residual_zero_global`, `ContinuousFlexibility.FlatAnnularCore.enlarge`

原 Icc 核心与外区分情形，enlarge 使用全域结论。

**源码证据 `ContinuousFlexibility/Scalar/FlatCollar.lean`：** `ContinuousFlexibility.flat_germ_discriminant_eq_one`, `ContinuousFlexibility.flat_germ_residual_eq_zero`

真实常值 germs 导数推出 D=1/residual=0。

**源码证据 `ContinuousFlexibility/Contracts/CartesianMetricRegularity.lean`：** `ContinuousFlexibility.FlatAnnularCore.cartesianRemainder_left`, `ContinuousFlexibility.FlatAnnularCore.cartesianRemainder_right`, `ContinuousFlexibility.FlatAnnularCore.cartesianRemainder_pos`

实际 Euclidean pairing 和全域正定。

**逐条验收：**
- acceptance.01 [covered]：严格 w>0 只用于原核心；扩大 collar 使用 w_zero。
- acceptance.02 [covered]：平坦来自真实 coordinate residual 等式，非任意谓词。

<a id="g01-04"></a>
### G01.04 实例化同一 AnnularSolution

**输出：** 用分析链实际给出的 Core 实例组装 AnnularSolution，保留半转对称、非径向见证与所有开领圈性质。

**局部依赖：** G01.01, G01.02, G01.03。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 80–220 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 输入必须是已构造的 N12 见证，不用空结构条件定理代替。
- 输出同一 w,z 供全部几何节点复用。

**本轮核对：** 任意给定 Core 的真实 AnnularSolution 构造与非径向保持已证；分析链非空 Core 尚无，实际实例化不完整。

**源码证据 `ContinuousFlexibility/Contracts/Annular.lean`：** `ContinuousFlexibility.FlatAnnularCore.enlarge`, `ContinuousFlexibility.AnnularSolution.nonradial_on_annulus`

条件性构造以 A:FlatAnnularCore 为输入。

**未完成内容：**
- N12 真实非空 Core 及其在同一几何链的选择/实例化。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：输入必须是已构造的 N12 见证，不用空结构条件定理代替。
- acceptance.02 [covered]：任意给定 Core 的真实 AnnularSolution 构造与非径向保持已证；分析链非空 Core 尚无，实际实例化不完整。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：扩大环带，把w以零、z以各自端常数延拓，得到光滑半转对称数据，保留正定平坦余度量，并在两端实际开领圈上w=0,z=c_L/c_R。 | G01.04（组合全部子任务） |
| acceptance.01：真实开集相等，不只是边界jets趋零 | G01.01 |
| acceptance.02：c_L与c_R独立 | G01.01 |
| acceptance.03：平坦和正性在拼接点也成立 | G01.02, G01.03 |
| remaining.01：由N12与加权空间实际产出这里所需的全局联合光滑Core延拓；Core存在性未证明 | W03.03, W03.04, W03.05, W03.06, W03.07, N12.04, N12.05, N12.09, G01.02, G01.04, MAIN.01 |

**覆盖说明 G01.remaining.01：** W03.03–07承担全阶mixed jets、参数一致性及联合延拓，N12.04/05/09实际构造w/z及非空Core；G01.02/04核对并扩大同一数据，MAIN.01选择实际存在见证。仅从给定Core的扩大定理不能消除原存在性义务。

<a id="g02"></a>
## G02 填盘后的归一化平面发展

**原节点完整目标：** 对任意AnnularSolution A，填内圈为平盘，在其光滑正定平坦余度量下构造定向局部等距P，外领圈P=id。后续几何节点共享同一A及其选择的P、cap、Fτ。

**原上游里程碑：** C00, S03

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [02-geometry.tex:69–94](../../paper/flexible-surface-rewrite/02-geometry.tex#L69)

<a id="g02-01"></a>
### G02.01 Cartesian 填盘高度的全局光滑性

**输出：** 从同一 AnnularSolution 的 π 周期高度构造 Cartesian 高度，证明支割线相容与原点常值邻域的真实 C∞。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 40–140 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 原点光滑由常值邻域证明。
- 非径向高度见证保持在同一半径。

**可复用基础：** Contracts/CartesianHeight.lean 已有高度与非径向支持。

**本轮核对：** Cartesian 高度已实际构造，支割线相容、原点常值光滑及同半径非径向见证均已证明。

**源码证据 `ContinuousFlexibility/Contracts/CartesianHeight.lean`：** `ContinuousFlexibility.FlatAnnularCore.cartesianHeight`, `ContinuousFlexibility.contDiffAt_polarHeightOnComplex_slit`, `ContinuousFlexibility.contDiffAt_polarHeightOnComplex_of_ne_zero`, `ContinuousFlexibility.FlatAnnularCore.contDiff_cartesianHeight`, `ContinuousFlexibility.FlatAnnularCore.cartesianHeight_left`, `ContinuousFlexibility.FlatAnnularCore.cartesianHeight_polarPosition`, `ContinuousFlexibility.FlatAnnularCore.cartesianHeight_nonradial`

π 周期处理支割线，内常值邻域处理原点，同半径 polarPosition 保留非径向 witness。

**逐条验收：**
- acceptance.01 [covered]：cartesianHeight_left 给原点实际常值邻域，光滑定理原点分支据此证明。
- acceptance.02 [covered]：cartesianHeight_nonradial 保留同半径两角不同高度。

<a id="g02-02"></a>
### G02.02 Cartesian 余度量的正定与标准区域

**输出：** 构造与同一高度匹配的 Cartesian 余度量矩阵，证明全域光滑正定，内外开域为 Euclidean，且 polar pullback 为原 g-dz²。

**局部依赖：** G02.01。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 60–180 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 坐标配对明确使用 Euclidean 双线性式。
- 不使用 ℝ×ℝ max norm 代替 Euclidean metric。

**可复用基础：** Contracts/CartesianMetric.lean 与 CartesianMetricRegularity.lean。

**本轮核对：** 同一高度/profile 的 Cartesian 余度量全域 C∞ 正定、内外标准及真实 polar 拉回全部已证。

**源码证据 `ContinuousFlexibility/Contracts/CartesianMetric.lean`：** `ContinuousFlexibility.cartesianMetric_polar_pullback`, `ContinuousFlexibility.FlatAnnularCore.cartesianRemainder_polar_pullback`

真实 polarJacobian 与 coordinateEuclideanPair 拉回。

**源码证据 `ContinuousFlexibility/Contracts/CartesianMetricRegularity.lean`：** `ContinuousFlexibility.FlatAnnularCore.cartesianRemainder_pos`, `ContinuousFlexibility.FlatAnnularCore.contDiff_cartesianRemainder_entries`, `ContinuousFlexibility.FlatAnnularCore.cartesianRemainder_standard_left`, `ContinuousFlexibility.FlatAnnularCore.cartesianRemainder_standard_right`

实际矩阵条目 C∞、全域正定和内外单位矩阵。

**逐条验收：**
- acceptance.01 [covered]：polar 拉回明确以 coordinateEuclideanPair 表述。
- acceptance.02 [covered]：使用真实坐标 Euclidean 双线性式，无 product max norm 替代。

<a id="g02-03"></a>
### G02.03 实际全局余标架及连接

**输出：** 由正定矩阵取光滑定向 Cholesky coframe，构造满足 Cartan 方程的真实光滑连接，并证明外域 coframe 标准、连接为零。

**局部依赖：** G02.02。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 60–180 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- coframe 平方和等于实际余度量。
- 定向楔积严格为正。

**可复用基础：** Geometry/CartesianMetricCoframe.lean。

**本轮核对：** Cholesky 实际 coframe、Cartan 连接、光滑和标准外域性质已证明。

**源码证据 `ContinuousFlexibility/Geometry/CartesianMetricCoframe.lean`：** `ContinuousFlexibility.matrixCoframe_square_sum`, `ContinuousFlexibility.matrixCoframe_wedge_pos`, `ContinuousFlexibility.contDiffAt_matrixCoframe`, `ContinuousFlexibility.matrixCoframe_cartan`, `ContinuousFlexibility.contDiffAt_matrixCoframeConnection`, `ContinuousFlexibility.matrixCoframe_standard`, `ContinuousFlexibility.matrixCoframeConnection_zero_of_eventually_standard`

实际正矩阵给正定向光滑 coframe 与连接。

**源码证据 `ContinuousFlexibility/Contracts/CartesianFlatness.lean`：** `ContinuousFlexibility.FlatAnnularCore.contDiff_cartesianRemainderCoframe`, `ContinuousFlexibility.FlatAnnularCore.contDiff_cartesianRemainderConnection`

对同一实际 Core 余度量实例化。

**逐条验收：**
- acceptance.01 [covered]：matrixCoframe_square_sum 给真实余度量平方和。
- acceptance.02 [covered]：matrixCoframe_wedge_pos 给严格正定向楔积。

<a id="g02-04"></a>
### G02.04 从原残差到闭连接

**输出：** 用实际 polar 拉回和同度量 coframe 变换，证明 Cartesian 连接闭；在填盘中心通过标准度量邻域处理。

**局部依赖：** G02.02, G02.03。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 60–200 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 闭性来自原真实残差零。
- 不新增 Cartesian flatness 输入字段。

**可复用基础：** Contracts/CartesianFlatness.lean 与 Geometry/PullbackCurvature.lean。

**本轮核对：** 真实 scalar residual 通过同 metric/polar 拉回证明 Cartesian 闭连接，中心用标准 germs 单独处理。

**源码证据 `ContinuousFlexibility/Contracts/CartesianFlatness.lean`：** `ContinuousFlexibility.FlatAnnularCore.cartesianCoframe_polar_same_metric`, `ContinuousFlexibility.FlatAnnularCore.cartesianRemainderConnection_closed_left`, `ContinuousFlexibility.FlatAnnularCore.cartesianRemainderConnection_closed_polar`, `ContinuousFlexibility.FlatAnnularCore.cartesianRemainderConnection_closed`

仅依 Core 的真实 residual 零，没有新增 Cartesian flatness 字段。

**源码证据 `ContinuousFlexibility/Geometry/PullbackCurvature.lean`：** `ContinuousFlexibility.cartan_curvature_pullback_eq_of_same_metric`

真实同 metric coframe 的曲率拉回识别。

**逐条验收：**
- acceptance.01 [covered]：closed_polar 从真实 Core residual 与实际 Cartan/polar 导数得到。
- acceptance.02 [covered]：全域 closed 结合中心标准邻域与非零极坐标区域，无新 flatness 前提。

<a id="g02-05"></a>
### G02.05 填盘后的全局归一化 primitive

**输出：** 在填盘形成的凸平面域对闭连接构造光滑 primitive，并利用连通外域把 primitive 归一化为零。

**局部依赖：** G02.03, G02.04。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 60–200 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 凸填盘消除 annulus holonomy。
- 不假设 annulus 上存在全局实 primitive。

**可复用基础：** Geometry/CartesianDevelopment.lean 与 Primitive.lean。

**本轮核对：** 全平面闭连接的真实光滑 primitive 已构造，并由实际连通开外域归一化为零。

**源码证据 `ContinuousFlexibility/Geometry/CartesianDevelopment.lean`：** `ContinuousFlexibility.exists_global_smooth_primitive`, `ContinuousFlexibility.exists_global_smooth_primitive_zero_on_exterior`

全平面闭一形式给 ψ 与 HasFDerivAt，实际外域归一化。

**源码证据 `ContinuousFlexibility/Geometry/CartesianExterior.lean`：** `ContinuousFlexibility.isPreconnected_complex_radius_exterior`, `ContinuousFlexibility.isOpen_complex_radius_exterior`

外域的真实连通和开放性。

**逐条验收：**
- acceptance.01 [covered]：primitive 在填盘后的全平面构造，消去 annulus holonomy。
- acceptance.02 [covered]：没有假设 annulus 本身存在全局实 primitive。

<a id="g02-06"></a>
### G02.06 闭余标架积分为归一化发展

**输出：** 用连接 primitive 旋转 coframe 为闭 coframe，再逐分量积分成同一个 P，证明外领圈 P=id 及完整双线性拉回等式。

**局部依赖：** G02.03, G02.05。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 80–220 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 所有常数选择共同满足外域归一化。
- 拉回覆盖两个独立切向量。

**可复用基础：** Geometry/MatrixDevelopment.lean 与 Contracts/PlanarDevelopment.lean。

**本轮核对：** primitive 旋转 coframe 后积分同一外域恒等 P，完整双线性拉回已证明。

**源码证据 `ContinuousFlexibility/Geometry/CartesianDevelopment.lean`：** `ContinuousFlexibility.exists_normalized_development_of_closed_cartesian_coframe`, `ContinuousFlexibility.exists_global_development_of_flat_cartesian_coframe`

同一存在元中 ψ 外域零、P 外域 id。

**源码证据 `ContinuousFlexibility/Contracts/PlanarDevelopment.lean`：** `ContinuousFlexibility.coordinate_pair_eq_matrix_of_square_sum`, `ContinuousFlexibility.FlatAnnularCore.exists_planarDevelopment`

真实 Core 输出后由极化得所有 x,u,v 的 metric 等式。

**逐条验收：**
- acceptance.01 [covered]：实际存在元共同携带 ψ 与 P 的外域归一化。
- acceptance.02 [covered]：exists_planarDevelopment 明确量化两个独立切向量。

<a id="g02-07"></a>
### G02.07 真实微分可逆与定向

**输出：** 从 coframe 楔积正性证明 DP 处处双射和 Jacobian 正，构造局部 C∞ 逆。

**局部依赖：** G02.02, G02.06。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 60–180 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 局部逆来自实际 fderiv。
- 定向不是仅在一个点陈述。

**可复用基础：** Geometry/LocalInverse.lean 与 PlanarOrientation.lean。

**本轮核对：** 实际发展微分双射、C∞ 局部逆以及处处严格正 Jacobian 均已证明。

**源码证据 `ContinuousFlexibility/Geometry/LocalInverse.lean`：** `ContinuousFlexibility.fderiv_bijective_of_remainder_metric`, `ContinuousFlexibility.exists_smooth_localInverse_of_remainder_metric`

实际余度量正性给 fderiv 双射和真实局部逆。

**源码证据 `ContinuousFlexibility/Geometry/PlanarOrientation.lean`：** `ContinuousFlexibility.planeJacobian_pos_of_normalized_homeomorph`, `ContinuousFlexibility.IsometricGraphDevelopment.planar_orientation`

同一归一化光滑双向发展给全域严格正 Jacobian。

**逐条验收：**
- acceptance.01 [covered]：局部逆取自实际 fderiv 双射。
- acceptance.02 [covered]：planar_orientation 对每个实际 x 给严格正 Jacobian。

<a id="g02-08"></a>
### G02.08 冻结共享归一化发展见证

**输出：** 对给定环带数据输出同一个归一化 P、高度、余度量及其全部局部性质，供后续唯一性、全局逆、帽及相位族引用。

**局部依赖：** G02.01, G02.02, G02.03, G02.04, G02.05, G02.06, G02.07。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 80–220 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 条件性构造不宣称 analytic Core 已存在。
- 后续不得各自重新选择无法统一的 P。

**本轮核对：** 给定同一 Core 已真正构造 IsometricGraphDevelopment，并固定 graphDevelopment 供后续共同引用。

**源码证据 `ContinuousFlexibility/Contracts/IsometricGraph.lean`：** `ContinuousFlexibility.IsometricGraphDevelopment`, `ContinuousFlexibility.FlatAnnularCore.exists_isometricGraphDevelopment`, `ContinuousFlexibility.FlatAnnularCore.graphDevelopment`

所有 P/height/metric 字段出自同一存在元，实际 choice 固定共同发展。

**逐条验收：**
- acceptance.01 [covered]：本任务是给定环带数据的条件构造，不计 Core 非空。
- acceptance.02 [covered]：graphDevelopment 和 D 的类型固定同一 A、同一 P 的选择。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：对任意AnnularSolution A，填内圈为平盘，在其光滑正定平坦余度量下构造定向局部等距P，外领圈P=id。后续几何节点共享同一A及其选择的P、cap、Fτ。 | G02.08（组合全部子任务） |
| acceptance.01：中心处光滑性不以极坐标公式冒充 | G02.01, G02.02 |
| acceptance.02：global coframe与外圈归一化实际证明 | G02.03, G02.05, G02.06 |
| acceptance.03：闭连接到全局primitive没有残留holonomy | G02.04, G02.05 |
| remaining.01：尚未在已构造的analytic Core见证上实例化，因为Core存在性属于N12未完成 | N12.09, G01.04, G02.08, MAIN.01 |

**覆盖说明 G02.remaining.01：** N12.09负责实际非空Core，G01.04输出其扩大环带，MAIN.01统一实例化G02.08的条件性归一化发展。这里记录最终使用时的存在性义务，不向通用G02证明添加N12依赖。

<a id="g03"></a>
## G03 发展唯一性和内盘中心定位

**原节点完整目标：** 归一化平面发展唯一；半转对称推出P为奇映射，因此内平盘上P是绕原点旋转，无平移项。

**原上游里程碑：** G02

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [02-geometry.tex:96–102](../../paper/flexible-surface-rewrite/02-geometry.tex#L96)

<a id="g03-01"></a>
### G03.01 相对 Euclidean 微分的刚性

**输出：** 对两个同度量的定向发展，经同一局部逆比较导数，证明其相对映射是固定正交线性部加平移。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 50–170 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 固定线性部来自实际混合偏导。
- 使用 Euclidean 坐标配对而非 product norm。

**可复用基础：** Geometry/EuclideanRigidity.lean 与 EuclideanRigidityCoordinates.lean。

**本轮核对：** 真实 Euclidean metric 导数经混合偏导推导固定 SO2 线性部和平移，足以比较相对发展。

**源码证据 `ContinuousFlexibility/Geometry/EuclideanRigidityCoordinates.lean`：** `ContinuousFlexibility.derivative_rotation_of_metric`, `ContinuousFlexibility.fderiv_eq_planeRotation_of_metric`, `ContinuousFlexibility.derivative_rotation_fderiv_zero`

实际混合二阶导消去旋转系数变化。

**源码证据 `ContinuousFlexibility/Geometry/EuclideanRigidity.lean`：** `ContinuousFlexibility.exists_rotation_affine_of_euclidean_derivative`, `ContinuousFlexibility.normalized_developments_unique`

相对发展经实际光滑逆成为 Euclidean derivative map。

**逐条验收：**
- acceptance.01 [covered]：固定线性部由 derivative_rotation_fderiv_zero 与实际 affine 结论证明。
- acceptance.02 [covered]：所用 metric 为显式 Euclidean 坐标配对。

<a id="g03-02"></a>
### G03.02 外域归一化消去相对刚体运动

**输出：** 证明两个归一化发展在非空外领圈相同，迫使其固定旋转和平移均为恒等，得到全局唯一性。

**局部依赖：** G03.01。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 40–140 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 归一化域是实际非空开集。
- 结论比较同一余度量的全部归一化发展。

**可复用基础：** Contracts/CenteredDevelopment.lean 的 planar_unique。

**本轮核对：** 同 metric 归一化发展的全局唯一性已证明，并对同一 Core 的任意 D/E 实例化。

**源码证据 `ContinuousFlexibility/Geometry/EuclideanRigidity.lean`：** `ContinuousFlexibility.normalized_developments_unique`

非空开放归一化域消去相对 Euclidean 运动。

**源码证据 `ContinuousFlexibility/Contracts/CenteredDevelopment.lean`：** `ContinuousFlexibility.IsometricGraphDevelopment.planar_unique`

实际构造 b+1 外域点并核验全部 metric/normalization。

**逐条验收：**
- acceptance.01 [covered]：planar_unique 的证明选 b+1 半径外域点，真实归一化域非空开放。
- acceptance.02 [covered]：D/E 为同一 A 上的任意发展，结论比较全局 planar 映射。

<a id="g03-03"></a>
### G03.03 半转对称产生发展奇性

**输出：** 构造实际反射发展 -P(-x)，验证其余度量与归一化和 P 相同，再由唯一性得 P(-x)=-P(x)、P(0)=0。

**局部依赖：** G03.02。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 40–150 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 高度偶性通过实际导数进入余度量等式。
- 不能直接把 P 奇性作为输入。

**可复用基础：** Contracts/DevelopmentSymmetry.lean 与 CenteredDevelopment.lean。

**本轮核对：** 反射发展 -P(-x) 已真实构造，实际高度偶性导数验证同 metric；唯一性得到 P 奇性及中心固定。

**源码证据 `ContinuousFlexibility/Contracts/DevelopmentSymmetry.lean`：** `ContinuousFlexibility.fderiv_even_apply_neg`, `ContinuousFlexibility.FlatAnnularCore.cartesianRemainder_neg_neg`, `ContinuousFlexibility.IsometricGraphDevelopment.reflected`, `ContinuousFlexibility.IsometricGraphDevelopment.reflected_planar_apply`

构造真实反射发展并核对字段。

**源码证据 `ContinuousFlexibility/Contracts/CenteredDevelopment.lean`：** `ContinuousFlexibility.IsometricGraphDevelopment.planar_odd`, `ContinuousFlexibility.IsometricGraphDevelopment.planar_zero`

通过实际发展唯一性推出奇性与 P0=0。

**逐条验收：**
- acceptance.01 [covered]：高度偶性由 fderiv_even_apply_neg 接入实际余度量。
- acceptance.02 [covered]：planar_odd/zero 为推论，不是输入字段。

<a id="g03-04"></a>
### G03.04 内闭盘中心旋转及完整唯一性

**输出：** 在内 Euclidean 开盘利用刚性与 P(0)=0 消去平移，并由连续性延到内闭盘，输出同一 P 的中心旋转公式及唯一性。

**局部依赖：** G03.01, G03.02, G03.03。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 50–160 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 得到绕原点旋转而非任意 Euclidean 运动。
- 内盘闭边界包含在实际等式中。

**本轮核对：** 内闭盘无平移中心旋转已证，闭边界由连续性与真实开盘闭包识别处理。

**源码证据 `ContinuousFlexibility/Contracts/CenteredDevelopment.lean`：** `ContinuousFlexibility.closure_cartesianDisk`, `ContinuousFlexibility.IsometricGraphDevelopment.exists_centered_inner_rotation`

先开盘 affine rotation，再由 P0=0 消平移，最后延至闭盘。

**逐条验收：**
- acceptance.01 [covered]：输出 c²+s²=1 与实际中心旋转，无平移项。
- acceptance.02 [covered]：最终等式明确覆盖 cartesianRadius≤a 的闭盘边界。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：归一化平面发展唯一；半转对称推出P为奇映射，因此内平盘上P是绕原点旋转，无平移项。 | G03.04（组合全部子任务） |
| acceptance.01：不得只证明内盘是某个欧氏运动 | G03.01, G03.03, G03.04 |
| acceptance.02：半转对称落实到实际P | G03.02, G03.03 |
| remaining.01：给定Core的发展唯一性/奇性/中心旋转已全部证明；主链尚待N12构造实际非空Core并用于同一球面组装 | N12.09, G01.04, MAIN.01, G03.02, G03.03, G03.04, G07.05, G07.10, MAIN.02, MAIN.03 |

**覆盖说明 G03.remaining.01：** G03.02–04只证明给定同一Core的发展唯一性和中心旋转；真实见证来自N12.09/G01.04并由MAIN.01实例化，同一球面实际组装由G07.05/10及MAIN.02/03承担。不能把条件性唯一性等同于实际闭球面存在。

<a id="g04"></a>
## G04 局部发展成为全局微分同胚

**原节点完整目标：** P恒等延拓为R²上的proper local diffeomorphism，由有限纤维covering和外部单层推出全局双射，限制为圆盘自微分同胚。

**原上游里程碑：** G02

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [02-geometry.tex:104–108](../../paper/flexible-surface-rewrite/02-geometry.tex#L104)

<a id="g04-01"></a>
### G04.01 外域恒等延拓的光滑局部逆

**输出：** 将同一归一化 P 在真实外领圈延拓为全平面恒等，证明全平面 C∞ 且微分处处双射。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 60–180 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 公共领圈上两定义实际相等。
- 中心、领圈和外域分别核对。

**本轮核对：** 当前发展直接在全平面构造，C∞、外域恒等及处处微分双射均已证明，比另作恒等延拓更强并保持同一 P。

**源码证据 `ContinuousFlexibility/Contracts/PlanarDevelopment.lean`：** `ContinuousFlexibility.FlatAnnularCore.exists_planarDevelopment`

同一全平面 homeomorphism 具有双向 C∞、外域恒等及真实 metric。

**源码证据 `ContinuousFlexibility/Geometry/LocalInverse.lean`：** `ContinuousFlexibility.fderiv_bijective_of_remainder_metric`

实际正余度量给全域真实微分双射。

**逐条验收：**
- acceptance.01 [covered]：同一全平面定义在开外域已经是 id，无另一个有缝选择。
- acceptance.02 [covered]：中心、外域标准余度量和全域正性均已在存在构造中实例化。

<a id="g04-02"></a>
### G04.02 proper 性与有限纤维

**输出：** 由紧集外恒等证明 P proper，结合局部 homeomorphism 得紧离散纤维有限。

**局部依赖：** G04.01。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 50–160 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- proper 使用实际逆像紧性。
- 有限纤维不凭图像直觉假设。

**可复用基础：** Geometry/GlobalInverse.lean 与 GlobalCovering.lean。

**本轮核对：** 紧集外恒等的 proper 性、紧纤维和 proper local homeomorphism 的有限纤维已经证明。

**源码证据 `ContinuousFlexibility/Geometry/GlobalInverse.lean`：** `ContinuousFlexibility.isCompact_preimage_of_eq_id_outside_compact`, `ContinuousFlexibility.isProperMap_of_eq_id_outside_compact`, `ContinuousFlexibility.isCompact_fiber_of_eq_id_outside_compact`

直接构造实际紧逆像/proper/紧纤维。

**源码证据 `ContinuousFlexibility/Geometry/GlobalCovering.lean`：** `ContinuousFlexibility.finite_fiber_of_proper_localHomeomorph`

局部 homeomorphism 给离散纤维，再由紧性得有限。

**逐条验收：**
- acceptance.01 [covered]：proper 由每个紧集的真实逆像紧性推出。
- acceptance.02 [covered]：有限纤维来自实际紧离散集合定理，无图像直觉假设。

<a id="g04-03"></a>
### G04.03 covering 与单层全局逆

**输出：** 把 proper local homeomorphism 提升为 covering，再用外部单层和基空间连通性构造全局双射及 homeomorphism。

**局部依赖：** G04.01, G04.02。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 70–220 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- surjective 和 injective 均有真实证明。
- 外部单层与覆盖层数关系明确。

**可复用基础：** Geometry/GlobalCovering.lean。

**本轮核对：** proper→covering 及平面 covering 的真实双侧连续逆已证；实现采用平面覆盖提升直接证明更强的单层结论。

**源码证据 `ContinuousFlexibility/Geometry/GlobalCovering.lean`：** `ContinuousFlexibility.isCoveringMap_of_proper_localHomeomorph`, `ContinuousFlexibility.exists_globalInverse_of_plane_covering`, `ContinuousFlexibility.isHomeomorph_of_plane_covering`, `ContinuousFlexibility.isHomeomorph_of_eq_id_outside_compact`

通过恒等图提升构造 Q，证明 LeftInverse/RightInverse；外部恒等归一化场合是直接特例。

**逐条验收：**
- acceptance.01 [covered]：真实声明同时给 LeftInverse Q P 与 RightInverse Q P，分别产生单射和满射。
- acceptance.02 [covered]：平面单连通覆盖提升直接得全局一层，比原外部单层路线更强；eq_id_outside_compact 明确实例化外部归一化情形。

<a id="g04-04"></a>
### G04.04 全局逆的 C∞

**输出：** 将全局 homeomorphism 逆与局部光滑逆逐点识别，证明其全域 C∞。

**局部依赖：** G04.01, G04.03。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 50–170 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 双向逆等式确实成立。
- 逐点 ContDiffAt 提升为完整全局光滑接口。

**本轮核对：** 全局逆通过实际微分可逆与局部逆逐点 C∞，Core 输出再将其提升为全局 ContDiff。

**源码证据 `ContinuousFlexibility/Geometry/GlobalCovering.lean`：** `ContinuousFlexibility.contDiffAt_homeomorph_symm_of_fderiv_bijective`, `ContinuousFlexibility.exists_smooth_homeomorph_of_eq_id_outside_compact`

同一 homeomorphism 的实际逆光滑。

**源码证据 `ContinuousFlexibility/Contracts/PlanarDevelopment.lean`：** `ContinuousFlexibility.FlatAnnularCore.exists_planarDevelopment`

最终同时给全局 ContDiff e 与 ContDiff e.symm。

**逐条验收：**
- acceptance.01 [covered]：逆就是同一 Homeomorph.symm，类型携带双侧逆等式。
- acceptance.02 [covered]：Core 构造用 contDiff_iff_contDiffAt 将逐点结论提升为全局 C∞。

<a id="g04-05"></a>
### G04.05 同一圆盘的自微分同胚

**输出：** 利用外域恒等与全局双射证明 P 把目标开盘及闭盘分别恰映到自身，并组装同一高度与后续图族所用的光滑圆盘逆。

**局部依赖：** G04.01, G04.02, G04.03, G04.04。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 70–200 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 圆盘像相等而非仅像包含。
- 不另外挑选与 G02 不同的发展见证。

**本轮核对：** 闭盘像保持和双向 C∞ 已证；任务同时要求的同一开盘像等式尚无专门实例化声明。

**源码证据 `ContinuousFlexibility/Contracts/PlanarDevelopment.lean`：** `ContinuousFlexibility.FlatAnnularCore.exists_planarDevelopment`, `ContinuousFlexibility.image_larger_disk_of_normalized_homeomorph`

实际专门声明均为≤R闭盘像。

**源码证据 `ContinuousFlexibility/Geometry/GlobalInverse.lean`：** `ContinuousFlexibility.image_eq_self_of_bijective_eq_id_outside`

任意集合通用引理可供后续开盘证明，但开盘外含边界的恒等前提尚未实例化。

**未完成内容：**
- 对同一发展证明开盘像等于自身，并统一开/闭盘光滑逆输出。

**逐条验收：**
- acceptance.01 [partial]：目前局部支持未覆盖全部验收；尚缺：对同一发展证明开盘像等于自身，并统一开/闭盘光滑逆输出。
- acceptance.02 [covered]：闭盘像保持和双向 C∞ 已证；任务同时要求的同一开盘像等式尚无专门实例化声明。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：P恒等延拓为R²上的proper local diffeomorphism，由有限纤维covering和外部单层推出全局双射，限制为圆盘自微分同胚。 | G04.05（组合全部子任务） |
| acceptance.01：局部等距不直接等于嵌入 | G04.02, G04.03, G04.04 |
| acceptance.02：证明像圆盘恰为同一圆盘 | G04.01, G04.03, G04.05 |
| acceptance.03：边界附近的恒等延拓光滑 | G04.01 |
| remaining.01：G02实际构造的归一化发展必须扩成全平面映射并核对所有前提 | G04.01, G04.03, G04.04 |
| remaining.02：与同一个填盘高度、标记补帽及后续相位族统一见证 | G02.08, G04.05, G06.14, G07.05, G08.03, MAIN.02, MAIN.03 |

**覆盖说明 G04.remaining.02：** G02.08/G04.05保留同一高度和发展，G06.14给出真正标记帽，G07.05及G08.03用这些同一见证拼出球面及相位族，MAIN.02/03统一实例化。各节点单独存在性不自动保证见证相容。

**覆盖说明 G04.acceptance.02：** 圆盘像恰为同一圆盘的证明实际使用G04.01的紧集外恒等延拓、G04.03的全局双射，最后在G04.05完成内外像分离的集合论识别；不是仅凭局部等距推出圆盘像相等。

<a id="g05"></a>
## G05 等距图盘

**原节点完整目标：** F=(P,z)是光滑嵌入圆盘且F*δ=g；外领圈为水平恒等盘，内盘为水平中心旋转盘。

**原上游里程碑：** G03, G04

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [02-geometry.tex:69–81](../../paper/flexible-surface-rewrite/02-geometry.tex#L69)；[02-geometry.tex:107–108](../../paper/flexible-surface-rewrite/02-geometry.tex#L107)

<a id="g05-01"></a>
### G05.01 图映射与完整拉回度量

**输出：** 对同一 P,z 构造真正 E3 中的 F=(P,z)，证明联合坐标导数及 F*δ=(g-dz²)+dz²=g。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 50–170 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- E3 使用 EuclideanSpace ℝ (Fin 3)。
- 度量等式对任意两个切向量成立。

**可复用基础：** Geometry/GraphEmbedding.lean 与 Contracts/IsometricGraph.lean。

**本轮核对：** 真实 E3 graphMap 的坐标、微分及完整拉回 metric 已证，同一 Core 输出实际 graph_metric。

**源码证据 `ContinuousFlexibility/Geometry/GraphEmbedding.lean`：** `ContinuousFlexibility.graphMap`, `ContinuousFlexibility.hasFDerivAt_graphMap`, `ContinuousFlexibility.fderiv_graphMap`, `ContinuousFlexibility.inner_graphDifferential`, `ContinuousFlexibility.graphMap_pullback_metric`

目标真实 EuclideanSpace ℝ(Fin3)，实际微分内积等式。

**源码证据 `ContinuousFlexibility/Contracts/IsometricGraph.lean`：** `ContinuousFlexibility.FlatAnnularCore.exists_isometricGraphDevelopment`

同一 P,z 输出∀x u v graph_metric。

**逐条验收：**
- acceptance.01 [covered]：graphMap 的实际目标为 E3=EuclideanSpace ℝ(Fin3)。
- acceptance.02 [covered]：完整 graph_metric 对两个独立切向量成立，等于 remainder+dz²。

<a id="g05-02"></a>
### G05.02 图盘的全局嵌入与微分单射

**输出：** 以 P 的实际光滑全局逆构造图像逆投影，证明图盘 topological embedding，并由正定拉回度量证明微分单射。

**局部依赖：** G05.01。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 60–200 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 全局 injective 和连续逆分别落实。
- immersion 与 embedding 不能相互替代。

**本轮核对：** 真实 P homeomorphism 与基底投影给全局图 embedding，实际正定 metric 给微分单射。

**源码证据 `ContinuousFlexibility/Geometry/GraphEmbedding.lean`：** `ContinuousFlexibility.isEmbedding_graphMap`, `ContinuousFlexibility.graphMap_fderiv_injective_of_metric`, `ContinuousFlexibility.graphMap_fderiv_injective_of_smooth_inverse`, `ContinuousFlexibility.graphMap_smooth_embedding_with_metric`

连续图逆与微分单射分别证明。

**源码证据 `ContinuousFlexibility/Contracts/IsometricGraph.lean`：** `ContinuousFlexibility.IsometricGraphDevelopment.embedding_restrict`, `ContinuousFlexibility.AnnularSolution.exists_isometricGraphDisk`

实际限制到扩大闭盘仍 embedding。

**逐条验收：**
- acceptance.01 [covered]：isEmbedding_graphMap 用真实 P 逆和基底投影给连续逆。
- acceptance.02 [covered]：immersion 的 fderiv 单射与 topological embedding 是分别证明的不同结论。

<a id="g05-03"></a>
### G05.03 内外领圈的精确图公式

**输出：** 证明 F 在外领圈为水平恒等图，在内闭盘为同一中心旋转加常高度，保留独立端高度常数。

**局部依赖：** G05.01。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 40–140 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 内盘旋转不含平移。
- 外领圈是开区域，为后续拼帽提供余量。

**可复用基础：** Contracts/IsometricGraph.lean 与 CenteredDevelopment.lean。

**本轮核对：** 外开领圈水平恒等、内闭盘中心旋转及左右独立常高度公式已全部给出。

**源码证据 `ContinuousFlexibility/Contracts/IsometricGraph.lean`：** `ContinuousFlexibility.IsometricGraphDevelopment.map_standard_outside`, `ContinuousFlexibility.AnnularSolution.exists_isometricGraphDisk`

外域水平恒等图，扩大 outerRadius>b 供真实内侧领圈。

**源码证据 `ContinuousFlexibility/Contracts/CenteredDevelopment.lean`：** `ContinuousFlexibility.IsometricGraphDevelopment.exists_centered_inner_rotation`

内闭盘中心旋转。

**源码证据 `ContinuousFlexibility/Contracts/CartesianHeight.lean`：** `ContinuousFlexibility.FlatAnnularCore.cartesianHeight_left`, `ContinuousFlexibility.FlatAnnularCore.cartesianHeight_right`

两端独立常值高度。

**逐条验收：**
- acceptance.01 [covered]：内盘公式明确无平移。
- acceptance.02 [covered]：扩大闭盘边界内的 Ioo b outerRadius 是非空开领圈。

<a id="g05-04"></a>
### G05.04 共享等距图盘接口

**输出：** 把同一 P,z 的光滑、嵌入、拉回度量及领圈公式组装为可限制到扩大闭盘的图盘见证。

**局部依赖：** G05.01, G05.02, G05.03。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 60–180 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 结论只在给定 Core 条件下使用，不宣称闭球面完成。
- 后续帽及相位族使用完全相同见证。

**本轮核对：** 同一 P,z 的光滑、embedding、微分单射、metric 及扩大盘领圈通过真实结构和存在声明统一输出。

**源码证据 `ContinuousFlexibility/Contracts/IsometricGraph.lean`：** `ContinuousFlexibility.IsometricGraphDevelopment`, `ContinuousFlexibility.FlatAnnularCore.exists_isometricGraphDevelopment`, `ContinuousFlexibility.FlatAnnularCore.graphDevelopment`, `ContinuousFlexibility.AnnularSolution.exists_isometricGraphDisk`

字段出自同一实际存在元，后续取同一 A,D。

**逐条验收：**
- acceptance.01 [covered]：前提是给定 Core，不计闭球面或 analytic Core 存在。
- acceptance.02 [covered]：graphDevelopment 固定实际共同选择，扩大盘只是同一 D 的限制。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：F=(P,z)是光滑嵌入圆盘且F*δ=g；外领圈为水平恒等盘，内盘为水平中心旋转盘。 | G05.04（组合全部子任务） |
| acceptance.01：smooth immersion和topological embedding均证明 | G05.01, G05.02 |
| acceptance.02：保持内外领圈的精确公式 | G05.03 |
| remaining.01：同一标记帽及球面组装尚未构造；图盘结论不含闭球面族或非全等 | G05.04, G06.08, G06.12, G06.14, G07.05, G07.07, G07.08, G07.10, G08.03, G09.04, G09.05, G13.07, MAIN.02, MAIN.03, MAIN.04 |
| remaining.02：尚未证明analytic Core存在 | N12.09, G01.04, G05.04, MAIN.01 |

**覆盖说明 G05.remaining.01：** G05.04的等距图盘不包含帽/闭球面/非全等；真正帽及分离由G06.08/12/14给出，球面构造和嵌入由G07.05/07/08/10、G08.03、G09.04/05承担，闭像非全等由G13.07证明，MAIN.02–04选同一见证组合。此处是原剩余义务的跨节点定位，不是把后续结论假设进G05。

**覆盖说明 G05.remaining.02：** Core非空由N12.09实际构造，经G01.04扩大后由MAIN.01实例化G05.04。图盘通用构造不能被当作analytic Core存在性证明。

<a id="g06"></a>
## G06 隔离的固定标记补帽

**原节点完整目标：** 对给定图盘构造光滑嵌入补帽，与该图盘的全部轴向旋转像除公共领圈外分离；在中央圆柱内补帽仅为底平盘c_B且c_B<min Z。补帽含唯一全局Gaussian曲率最大点p，其两主曲率不同。

**原上游里程碑：** G05, D01

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [02-geometry.tex:146–190](../../paper/flexible-surface-rewrite/02-geometry.tex#L146)

<a id="g06-01"></a>
### G06.01 全相位图盘的统一高度与曲率界

**输出：** 对同一闭图盘及其全部轴旋转像，证明高度具有共同上下界，Gaussian 曲率绝对值具有统一有限上界。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 160–420 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 高度界作用于所有实相位。
- 曲率界来自真实曲率的紧性及环境旋转自然性。

**可复用基础：** Contracts/GraphFamilyImage.lean 已有共同高度界。

**本轮核对：** 所有实相位的统一真实高度界已证，尚无同一闭盘真实 K 绝对值统一界的项目声明。

**源码证据 `ContinuousFlexibility/Contracts/GraphFamilyImage.lean`：** `ContinuousFlexibility.IsometricGraphDevelopment.exists_rotationFamily_height_bounds`

完整量化所有 t 与闭盘点。

**源码证据 `ContinuousFlexibility/Contracts/GraphFamilyCurvature.lean`：** `ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_gaussianCurvature`

真实 K 运输可用于后续界，但该界未声明。

**未完成内容：**
- 真实 K 的连续性、紧盘绝对值界及全相位统一上界。

**逐条验收：**
- acceptance.01 [covered]：所有实相位的统一真实高度界已证，尚无同一闭盘真实 K 绝对值统一界的项目声明。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：曲率界来自真实曲率的紧性及环境旋转自然性。

<a id="g06-02"></a>
### G06.02 对称平坦转角函数

**输出：** 构造实际 C∞ 非减 χ:[0,1]→[0,1]，在两端开邻域恒为 0/1，且 χ(1-t)=1-χ(t)。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 200–500 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 两端 plateau 有明确正宽度。
- 对称性、取值界及中部严格变化分别证明。

**可复用基础：** Geometry/CapMeridian.lean 有进行中的实际积分构造，需按交付复核。

**本轮核对：** 实际 capTurn 为 C∞ 非减对称函数，两端 plateau、[0,1] 界和中部0<χ<1全已证明。

**源码证据 `ContinuousFlexibility/Geometry/CapMeridian.lean`：** `ContinuousFlexibility.capTurn`, `ContinuousFlexibility.contDiff_capTurn`, `ContinuousFlexibility.capTurn_nonneg`, `ContinuousFlexibility.capTurn_le_one`, `ContinuousFlexibility.monotone_capTurn`, `ContinuousFlexibility.capTurn_eq_zero`, `ContinuousFlexibility.capTurn_eq_one`, `ContinuousFlexibility.capTurn_reflection`, `ContinuousFlexibility.capTurn_pos`, `ContinuousFlexibility.capTurn_lt_one`

真实 χ 函数与全部指定性质。

**逐条验收：**
- acceptance.01 [covered]：明确 t≤1/4 与 t≥3/4 上恒为0/1，plateau宽度正。
- acceptance.02 [covered]：单独声明证明单调、取值界、对称及中部正性/小于1。

<a id="g06-03"></a>
### G06.03 积分径线与单位速度

**输出：** 以 r′=cos(πχ(s/L))、z′=-sin(πχ(s/L)) 定义实际积分径线，证明 C∞、导数及单位速度。

**局部依赖：** G06.02。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 180–450 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 导数由实际积分基本定理得到。
- 初值为同一附着半径 R 与边界高度。

**本轮核对：** 实际积分定义径线，C∞、真实速度、单位速度及初值已证。

**源码证据 `ContinuousFlexibility/Geometry/CapMeridian.lean`：** `ContinuousFlexibility.capRadialOffset`, `ContinuousFlexibility.capHeightDrop`, `ContinuousFlexibility.capMeridian`, `ContinuousFlexibility.contDiff_capMeridian`, `ContinuousFlexibility.hasDerivAt_capRadialOffset`, `ContinuousFlexibility.hasDerivAt_capHeightDrop`, `ContinuousFlexibility.hasDerivAt_capMeridian`, `ContinuousFlexibility.capMeridian_unit_speed`, `ContinuousFlexibility.capMeridian_zero`

实际积分基本定理给 cos/sin 速度，初值(R,h)。

**逐条验收：**
- acceptance.01 [covered]：速度确由实际积分函数 HasDerivAt 得到。
- acceptance.02 [covered]：capMeridian_zero 精确给 (R,h)，h可取同一图边界高度。

<a id="g06-04"></a>
### G06.04 径线径向约束与单射

**输出：** 由 χ 对称性证明末端返回相同半径、全程 r≥R；利用严格下降的中段高度与端部直段证明完整径线无自交。

**局部依赖：** G06.02, G06.03。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 250–650 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 水平端部高度常值不能用于严格单调证明。
- 端部/中部不同参数的可能碰撞逐类排除。

**本轮核对：** 径线返回半径、全程r≥R以及完整参数单射已证明，水平端段与严格下降中段分开处理。

**源码证据 `ContinuousFlexibility/Geometry/CapMeridian.lean`：** `ContinuousFlexibility.capRadialOffset_reflection`, `ContinuousFlexibility.capMeridian_length`, `ContinuousFlexibility.capMeridianRadius_core_le`, `ContinuousFlexibility.capMeridianRadius_core_lt`, `ContinuousFlexibility.capMeridianHeight_strict`, `ContinuousFlexibility.capNormalizedMeridian_injective`, `ContinuousFlexibility.capMeridian_injective`

规范化分区单射再缩放；内段r>R、两端r=R。

**逐条验收：**
- acceptance.01 [covered]：未错误地以全域高度严格单调处理水平端段。
- acceptance.02 [covered]：实际单射证明排除端段/中段不同参数碰撞。

<a id="g06-05"></a>
### G06.05 选择足够深的底盘高度

**输出：** 证明总下降为 L 乘一个固定正常数，选同一个 L 使底高 cB 严格低于全部相位图盘；给出端部直线段的精确公式。

**局部依赖：** G06.01, G06.03, G06.04。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 180–450 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 正常数独立于 L 和相位。
- 后续 marker 尺度尚未影响此选择。

**本轮核对：** capDrop 为固定正数，总下降 L*capDrop，明确 capLength 选择及同图族统一附着已证。

**源码证据 `ContinuousFlexibility/Geometry/CapMeridian.lean`：** `ContinuousFlexibility.capDrop_pos`, `ContinuousFlexibility.capMeridianHeight_eq_left`, `ContinuousFlexibility.capMeridianHeight_eq_right`, `ContinuousFlexibility.capLength_pos`, `ContinuousFlexibility.capLength_bottom_lt`

实际 L 缩放给底盘低于指定 lo，端部精确水平。

**源码证据 `ContinuousFlexibility/Geometry/CapDisk.lean`：** `ContinuousFlexibility.IsometricGraphDevelopment.exists_fixed_cap_attachment`

实际共同图族中由全相位高度界选同一 L。

**逐条验收：**
- acceptance.01 [covered]：capDrop 是固定正常数，与 L/τ 无关。
- acceptance.02 [covered]：capLength 选择只依赖 h、lo、ε，不含后选 marker 参数。

<a id="g06-06"></a>
### G06.06 旋转径线的环面部分

**输出：** 旋转 r>0 的实际径线得到光滑旋转曲面，证明其二维微分单射和参数除圆周等价之外无重复。

**局部依赖：** G06.03, G06.04, G06.05。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 250–650 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 角变量圆周商与参数重复明确处理。
- 微分单射使用 r>0 及单位速度。

**本轮核对：** 真实旋转曲面、metric 和 r>0 微分单射已证；Circle 参数圆柱的全局单射/embedding 也已证。

**源码证据 `ContinuousFlexibility/Geometry/CapRevolution.lean`：** `ContinuousFlexibility.capRevolution`, `ContinuousFlexibility.contDiff_capRevolution`, `ContinuousFlexibility.capRevolution_pullback_metric`, `ContinuousFlexibility.capRevolution_fderiv_injective`, `ContinuousFlexibility.capCylinderMap`, `ContinuousFlexibility.capCylinderMap_injOn`, `ContinuousFlexibility.isEmbedding_capClosedCylinderMap`

Circle处理角参数重复；实际 ds²+r²dθ² 给 immersion。

**逐条验收：**
- acceptance.01 [covered]：全局圆柱对象采用 Circle 角变量，按圆周等价去重。
- acceptance.02 [covered]：实际微分单射由 L>0、r≠0 和单位速度正定 metric 得到。

<a id="g06-07"></a>
### G06.07 轴端平盘的真实光滑性

**输出：** 用底部真实水平直段接平盘至轴，给出 Cartesian 图坐标并证明轴处 C∞、微分单射及与旋转参数的重叠一致。

**局部依赖：** G06.05, G06.06。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 220–550 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 不能在 r=0 直接套退化极坐标 immersion。
- 轴邻域确实为水平平面图。

**本轮核对：** 真实 capDiskMap 在轴邻域为严格线性水平图，C∞、轴微分单射及非轴 polar 重叠公式均已证明。

**源码证据 `ContinuousFlexibility/Geometry/CapDisk.lean`：** `ContinuousFlexibility.capDisk_axis_formula`, `ContinuousFlexibility.capDisk_axis_germ`, `ContinuousFlexibility.contDiff_capDiskMap`, `ContinuousFlexibility.hasFDerivAt_capDiskMap_axis`, `ContinuousFlexibility.capDiskMap_axis_fderiv_injective`, `ContinuousFlexibility.capDiskMap_polarMap`, `ContinuousFlexibility.capDiskMap_polar_germ`, `ContinuousFlexibility.capDiskMap_fderiv_injective_nonaxis`

轴用 Cartesian 线性 germ；非轴用真实 polarJacobian，未微分 arg。

**逐条验收：**
- acceptance.01 [covered]：轴处用非退化 Cartesian 线性水平 germ，不套退化极坐标。
- acceptance.02 [covered]：实际 polarMap/germ 给与旋转参数的重叠一致，全部点C∞。

<a id="g06-08"></a>
### G06.08 附着 rim 的光滑及无交

**输出：** 用顶部真实水平直段与扩大图盘的同一开领圈匹配，证明拼接无折角、C∞，且除公共领圈外与所有相位图盘分离。

**局部依赖：** G06.01, G06.05, G06.06, G06.07。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 250–650 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 共同领圈参数方向与坐标转移明确。
- 分离量化所有实相位，不只初始图盘。

**本轮核对：** rim chart、开邻域水平等式、rim微分单射及同图族全相位分离/附着已完整证明。

**源码证据 `ContinuousFlexibility/Geometry/CapDisk.lean`：** `ContinuousFlexibility.capDiskRimChart`, `ContinuousFlexibility.capDiskMap_rimChart`, `ContinuousFlexibility.capDiskMap_rim_germ`, `ContinuousFlexibility.contDiffAt_capDiskRimChart`, `ContinuousFlexibility.capDiskRimChart_fderiv_injective`, `ContinuousFlexibility.IsometricGraphDevelopment.graph_cap_intersection`, `ContinuousFlexibility.IsometricGraphDevelopment.graph_cap_open_collar`, `ContinuousFlexibility.IsometricGraphDevelopment.exists_fixed_cap_attachment`

闭像只交共同 attaching rim，实际延拓在非空开领圈精确相同。

**逐条验收：**
- acceptance.01 [covered]：capDiskRimChart 给实际反向径向转换、光滑及非退化。
- acceptance.02 [covered]：graph_cap_intersection/open_collar 和存在附着声明覆盖全部实相位。

<a id="g06-09"></a>
### G06.09 无 marker 帽的全局嵌入和曲率界

**输出：** 组装旋转环段与轴平盘为同一完整帽，证明其全局嵌入、与图盘相容，并取得待放 marker 之外整个闭面的曲率上界。

**局部依赖：** G06.06, G06.07, G06.08。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 250–650 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 紧性界不依赖尚未选的 marker k、ρ。
- 预留水平环带必须是实际非空开区。

**本轮核对：** 无marker真实完整 cap disk 的光滑嵌入、底盘与全族附着已构造；未取得全曲面其余部分曲率上界及实际预留marker环带接口。

**源码证据 `ContinuousFlexibility/Geometry/CapDisk.lean`：** `ContinuousFlexibility.capDiskMap_smooth_embedding`, `ContinuousFlexibility.capDisk_inside_cylinder_bottom`, `ContinuousFlexibility.IsometricGraphDevelopment.exists_fixed_cap_attachment`

真实闭参数盘嵌入帽并与同图族统一分离/开领圈附着。

**未完成内容：**
- 与后选 k、ρ 无关的帽/图参数片曲率上界。
- 实际可放marker支持的非空水平开环带。

**逐条验收：**
- acceptance.01 [partial]：目前局部支持未覆盖全部验收；尚缺：与后选 k、ρ 无关的帽/图参数片曲率上界。；实际可放marker支持的非空水平开环带。
- acceptance.02 [partial]：目前局部支持未覆盖全部验收；尚缺：与后选 k、ρ 无关的帽/图参数片曲率上界。；实际可放marker支持的非空水平开环带。

<a id="g06-10"></a>
### G06.10 marker 支撑放入预留环带

**输出：** 在预留水平环带选择实际中心及平面坐标，将紧支撑椭圆 bump 平移放入；证明支持边界全阶匹配和真实图曲率公式。

**局部依赖：** G06.09。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 180–480 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 支撑闭包严格包含于预留环带。
- 现有 marker 公式经平移/坐标转换后仍是实际曲率。

**可复用基础：** Geometry/MarkerBump.lean 与 MarkedCap.lean 已有局部真实 bump/K 公式。

**本轮核对：** 独立 marker 的紧支撑C∞、支持边界及真实K公式已证，未实际平移放入当前cap预留环带。

**源码证据 `ContinuousFlexibility/Geometry/MarkerBump.lean`：** `ContinuousFlexibility.contDiff_markerBump`, `ContinuousFlexibility.hasCompactSupport_markerBump`, `ContinuousFlexibility.markerBump_secondDerivative_eq_zero`

真实局部bump支持与边界二阶平坦。

**源码证据 `ContinuousFlexibility/Geometry/MarkedCap.lean`：** `ContinuousFlexibility.surfaceGaussianCurvature_markerBump`

其原坐标下的真实图K公式。

**未完成内容：**
- 实际环带内中心/坐标及支持闭包严格包含选择。
- 平移/帽坐标后的曲率与粘合识别。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：支撑闭包严格包含于预留环带。
- acceptance.02 [partial]：目前局部支持未覆盖全部验收；尚缺：实际环带内中心/坐标及支持闭包严格包含选择。；平移/帽坐标后的曲率与粘合识别。

<a id="g06-11"></a>
### G06.11 按顺序冻结 k 再选择 ρ

**输出：** 先用已有非 marker 曲率上界选 k 使 ABk² 更大，再选同一 ρ 使支撑适配且高度 kρ²/2 保持与底帽和移动图盘分离。

**局部依赖：** G06.01, G06.09, G06.10。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 220–550 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- ρ 不得反向改变已冻结的 L 和非 marker 上界。
- 高度、支撑和全族分离条件由同一参数同时满足。

**本轮核对：** 实际 marker 高度上界及中心峰值公式存在，尚未用其余全曲面曲率界按 k→ρ 次序同时选参数。

**源码证据 `ContinuousFlexibility/Geometry/MarkerBump.lean`：** `ContinuousFlexibility.markerBump_bounds`, `ContinuousFlexibility.hasCompactSupport_markerBump`

局部真实高度≤kρ²/2及支持。

**源码证据 `ContinuousFlexibility/Geometry/MarkedCap.lean`：** `ContinuousFlexibility.surfaceGaussianCurvature_markerBump_zero`

真实中心K=ABk²。

**未完成内容：**
- 实际全曲面其余曲率界后选择 k。
- 再选同一ρ同时满足环带支持和全族分离，不改变冻结几何。

**逐条验收：**
- acceptance.01 [partial]：目前局部支持未覆盖全部验收；尚缺：实际全曲面其余曲率界后选择 k。；再选同一ρ同时满足环带支持和全族分离，不改变冻结几何。
- acceptance.02 [partial]：目前局部支持未覆盖全部验收；尚缺：实际全曲面其余曲率界后选择 k。；再选同一ρ同时满足环带支持和全族分离，不改变冻结几何。

<a id="g06-12"></a>
### G06.12 插入 marker 后的帽光滑嵌入

**输出：** 将 marker 图粘到预留水平帽区域，证明新帽 C∞、全局嵌入和与全部相位图盘的分离性质仍成立。

**局部依赖：** G06.08, G06.10, G06.11。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 250–650 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 不因 bump 的向上高度引入新的交点。
- 拼接与底帽的参数化保持同一帽见证。

**本轮核对：** 无marker帽嵌入与独立bump光滑已证，但没有实际插入marker后的新帽定义及其全族无交。

**源码证据 `ContinuousFlexibility/Geometry/CapDisk.lean`：** `ContinuousFlexibility.capDiskMap_smooth_embedding`, `ContinuousFlexibility.IsometricGraphDevelopment.exists_fixed_cap_attachment`

无marker帽。

**源码证据 `ContinuousFlexibility/Geometry/MarkerBump.lean`：** `ContinuousFlexibility.contDiff_markerBump`, `ContinuousFlexibility.hasCompactSupport_markerBump`

独立marker可供局部替换。

**未完成内容：**
- 实际插入同一cap的映射与C∞粘合。
- 新帽全局嵌入、对全部移动图盘分离。

**逐条验收：**
- acceptance.01 [partial]：目前局部支持未覆盖全部验收；尚缺：实际插入同一cap的映射与C∞粘合。；新帽全局嵌入、对全部移动图盘分离。
- acceptance.02 [partial]：目前局部支持未覆盖全部验收；尚缺：实际插入同一cap的映射与C∞粘合。；新帽全局嵌入、对全部移动图盘分离。

<a id="g06-13"></a>
### G06.13 唯一全局曲率峰与不同主曲率

**输出：** 证明 marker 中心是整个闭曲面的唯一 K 最大点，且该点实际切空间形算子有两个不同主曲率及主方向线。

**局部依赖：** G06.09, G06.10, G06.11, G06.12。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 220–550 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 严格峰值同时与 marker 内其它点和全曲面其它块比较。
- 主方向由 D01 的切空间桥接而非坐标 Hessian 命名。

**本轮核对：** 独立marker图的唯一严格K峰与中心坐标shape不同特征值已证；完整闭面峰值比较和实际切空间主方向尚缺。

**源码证据 `ContinuousFlexibility/Geometry/MarkedCap.lean`：** `ContinuousFlexibility.surfaceGaussianCurvature_markerBump_lt_peak`, `ContinuousFlexibility.surfaceGaussianCurvature_markerBump_eq_peak_iff`, `ContinuousFlexibility.surfaceShapeMatrix_markerBump_zero`, `ContinuousFlexibility.surfaceShapeMatrix_markerBump_center_eigenvectors`

只关于独立marker图，不是已插入的完整闭面。

**未完成内容：**
- 与同一图盘/帽的其它所有点比较真实K。
- 实际切空间主曲率和主方向线识别。

**逐条验收：**
- acceptance.01 [partial]：目前局部支持未覆盖全部验收；尚缺：与同一图盘/帽的其它所有点比较真实K。；实际切空间主曲率和主方向线识别。
- acceptance.02 [partial]：目前局部支持未覆盖全部验收；尚缺：与同一图盘/帽的其它所有点比较真实K。；实际切空间主曲率和主方向线识别。

<a id="g06-14"></a>
### G06.14 完整固定标记帽见证

**输出：** 输出同一固定帽、底盘、标记点及主方向，对全部相位量化分离并保留 axis/rim 的真实光滑性与唯一全局曲率峰。

**局部依赖：** G06.01, G06.02, G06.03, G06.04, G06.05, G06.06, G06.07, G06.08, G06.09, G06.10, G06.11, G06.12, G06.13。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 120–300 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 所有参数已按统一顺序选定。
- 结论包含实际 cap 存在，不只给定 cap 的条件命题。

**本轮核对：** 真实无marker固定帽及图族附着已构造；同一标记帽仍缺实际marker插入、全局峰和主方向。

**源码证据 `ContinuousFlexibility/Geometry/CapDisk.lean`：** `ContinuousFlexibility.IsometricGraphDevelopment.exists_fixed_cap_attachment`

真实帽、全族交集、开领圈、C∞/embedding/immersion。

**源码证据 `ContinuousFlexibility/Geometry/MarkedCap.lean`：** `ContinuousFlexibility.surfaceGaussianCurvature_markerBump_eq_peak_iff`

只有独立marker峰值支持。

**未完成内容：**
- 按统一参数次序给同一标记帽与全闭面唯一峰、实际主方向的完整见证。

**逐条验收：**
- acceptance.01 [partial]：目前局部支持未覆盖全部验收；尚缺：按统一参数次序给同一标记帽与全闭面唯一峰、实际主方向的完整见证。
- acceptance.02 [partial]：目前局部支持未覆盖全部验收；尚缺：按统一参数次序给同一标记帽与全闭面唯一峰、实际主方向的完整见证。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：对给定图盘构造光滑嵌入补帽，与该图盘的全部轴向旋转像除公共领圈外分离；在中央圆柱内补帽仅为底平盘c_B且c_B<min Z。补帽含唯一全局Gaussian曲率最大点p，其两主曲率不同。 | G06.14（组合全部子任务） |
| acceptance.01：对整个相位族的统一分离 | G06.01, G06.05, G06.08, G06.11, G06.12 |
| acceptance.02：最大点是整个闭曲面的唯一最大点 | G06.09, G06.11, G06.13 |
| acceptance.03：主曲率不等，不仅坐标Hessian不等 | G06.13 |
| remaining.01：尚未构造完整cap的实际积分径线、axis/rim光滑、底盘和全族分离 | G06.02, G06.03, G06.04, G06.05, G06.06, G06.07, G06.08, G06.09 |
| remaining.02：尚需把marker实际放入预留环带并与整个闭曲面的其它曲率比较、按顺序选择k和ρ | G06.09, G06.10, G06.11, G06.12, G06.13 |
| remaining.03：坐标shape eigenvectors到principal tangent lines以及G12有限stabilizer仍待证明；MarkedCap文件名不表示补帽存在 | D01.04, D01.06, G06.13, G06.14, G12.04, G12.05, G12.06, G12.07 |

**覆盖说明 G06.remaining.03：** D01.04/06将坐标shape eigenvectors变为实际切空间主方向，G06.13落实到所造帽的标记点；G12.04–07进一步证明全部环境仿射等距的有限稳定子。G06.14组装不能替代这些具体证明，也不将G12设为G06反向依赖。

<a id="g07"></a>
## G07 标准球面参数化和固定度量

**原节点完整目标：** 在标准S²上拼出光滑嵌入F₀，北侧为图盘、南侧为补帽，并定义光滑正定gΣ=F₀*δ。

**原上游里程碑：** G05, G06, D01

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [02-geometry.tex:146–168](../../paper/flexible-surface-rewrite/02-geometry.tex#L146)；[02-geometry.tex:230–239](../../paper/flexible-surface-rewrite/02-geometry.tex#L230)

<a id="g07-01"></a>
### G07.01 标准球面的具体图坐标

**输出：** 固定 mathlib 标准单位 S² 的立体投影图册，选覆盖北图盘、南帽和共同领圈的具体开域与半径。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 定义域直接为标准光滑 S²。
- 不用 equator 处径向导数退化的 xy 投影。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 没有标准S²的实际立体投影覆盖、图域及半径选择。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：定义域直接为标准光滑 S²。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：不用 equator 处径向导数退化的 xy 投影。

<a id="g07-02"></a>
### G07.02 北侧图盘的球面坐标表达

**输出：** 构造北侧球面开域与实际扩大圆盘之间的光滑坐标识别，将同一等距图盘写成球面图内映射。

**局部依赖：** G07.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 220–550 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 坐标识别在盘边界外保留开领圈。
- 实际导数/逆的光滑性明确。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 没有北侧标准球面图与实际扩大图盘的光滑坐标识别。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：坐标识别在盘边界外保留开领圈。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：实际导数/逆的光滑性明确。

<a id="g07-03"></a>
### G07.03 南侧帽的球面坐标表达

**输出：** 将同一完整帽经其径线与底盘参数写入南侧球面图，证明轴邻域和 rim 邻域的真实光滑坐标表达。

**局部依赖：** G07.01。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 250–650 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 轴端使用非退化 Cartesian 局部表达。
- 匹配实际 cap 而非另选拓扑等价帽。

**本轮核对：** 实际cap的轴端、非轴和rim Cartesian参数表达已证明，尚未写入标准S²南侧图。

**源码证据 `ContinuousFlexibility/Geometry/CapDisk.lean`：** `ContinuousFlexibility.contDiff_capDiskMap`, `ContinuousFlexibility.capDisk_axis_germ`, `ContinuousFlexibility.capDiskMap_polar_germ`, `ContinuousFlexibility.capDiskMap_rim_germ`

cap自身的真实光滑参数片与重叠。

**未完成内容：**
- 标准S²南侧chart到同一capDiskMap的实际光滑转换。

**逐条验收：**
- acceptance.01 [partial]：目前局部支持未覆盖全部验收；尚缺：标准S²南侧chart到同一capDiskMap的实际光滑转换。
- acceptance.02 [partial]：目前局部支持未覆盖全部验收；尚缺：标准S²南侧chart到同一capDiskMap的实际光滑转换。

<a id="g07-04"></a>
### G07.04 共同领圈上的坐标过渡

**输出：** 选择领圈参数化，使南北定义在实际非空开重叠上相等，证明 transition 为光滑微分同胚且导数非退化。

**局部依赖：** G07.02, G07.03。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 250–650 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 相等在整个开重叠成立。
- 径向方向、角向方向及重叠范围均明确。

**本轮核对：** 图盘与cap真实rim chart、开邻域等式及rim微分单射已证，尚无标准S²南北chart过渡双向微分同胚。

**源码证据 `ContinuousFlexibility/Geometry/CapDisk.lean`：** `ContinuousFlexibility.capDiskRimChart`, `ContinuousFlexibility.contDiffAt_capDiskRimChart`, `ContinuousFlexibility.capDiskRimChart_fderiv_injective`, `ContinuousFlexibility.IsometricGraphDevelopment.graph_cap_open_collar`

已有实际平面领圈对应，但没有球面图册对象。

**未完成内容：**
- 同一标准S²南北图域、transition逆、光滑和非退化桥接。

**逐条验收：**
- acceptance.01 [partial]：目前局部支持未覆盖全部验收；尚缺：同一标准S²南北图域、transition逆、光滑和非退化桥接。
- acceptance.02 [partial]：目前局部支持未覆盖全部验收；尚缺：同一标准S²南北图域、transition逆、光滑和非退化桥接。

<a id="g07-05"></a>
### G07.05 标准球面上的全局 F₀

**输出：** 用相容局部定义粘合 F₀:S²→E3，证明其在各图内分别等于同一图盘和同一帽。

**局部依赖：** G07.02, G07.03, G07.04。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 180–450 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 覆盖全部 S²，定义无选择歧义。
- range 精确为预定图盘与帽之并。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 未定义标准S²上的全局F₀及其实际range。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：覆盖全部 S²，定义无选择歧义。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：range 精确为预定图盘与帽之并。

<a id="g07-06"></a>
### G07.06 F₀ 的全局流形光滑性

**输出：** 由具体图坐标表达证明 F₀ 是实际流形意义的 C∞ 映射，处理北端、南轴及整个领圈。

**局部依赖：** G07.04, G07.05。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 220–550 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 用 ContMDiff 与局部 ContDiff 的真实桥接。
- 不能仅给每块 Euclidean 公式而跳过图册适配。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- F₀未定义，没有真实ContMDiff F₀的全局图册验证。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：用 ContMDiff 与局部 ContDiff 的真实桥接。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：不能仅给每块 Euclidean 公式而跳过图册适配。

<a id="g07-07"></a>
### G07.07 F₀ 的全局单射

**输出：** 由每块单射和图帽分离，逐类处理同块、不同块及公共领圈的点对，证明 F₀ 在 S² 上单射。

**局部依赖：** G07.04, G07.05。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 重叠图坐标的同一球面点不重复当作不同点。
- 图帽公共像必须恰由共同领圈识别。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 没有标准S²上的实际F₀，尚无其全局单射声明。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：重叠图坐标的同一球面点不重复当作不同点。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：图帽公共像必须恰由共同领圈识别。

<a id="g07-08"></a>
### G07.08 F₀ 的切空间微分单射

**输出：** 把实际图盘和帽的 Euclidean immersion 经球面坐标转移到切空间，证明 F₀ 的全域 IsImmersion。

**局部依赖：** G07.02, G07.03, G07.04, G07.06。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 250–650 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 必须应用真实流形切映射链式法则。
- axis、rim 和图盘内部全部覆盖。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 没有标准球面切空间上F₀的IsImmersion证明。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：必须应用真实流形切映射链式法则。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：axis、rim 和图盘内部全部覆盖。

<a id="g07-09"></a>
### G07.09 实际拉回黎曼度量

**输出：** 在 S² 切丛定义 gΣ=F₀*δ，由实际微分单射证明正定，由全局光滑性证明 ContMDiffRiemannianMetric。

**局部依赖：** G07.06, G07.08。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 250–650 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 度量是实际切空间内积拉回。
- 不以 ambient Isometry 代替拉回 tensor。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 没有实际标准S²切丛上的gΣ=F₀*δ或ContMDiffRiemannianMetric。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：度量是实际切空间内积拉回。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：不以 ambient Isometry 代替拉回 tensor。

<a id="g07-10"></a>
### G07.10 球面嵌入及固定盘帽拓扑

**输出：** 由紧性与单射得到 F₀ 的全局 topological embedding，组装光滑嵌入和度量；同时给出内盘及补帽在标准 S² 上的实际圆盘拓扑与非空内部。

**局部依赖：** G07.01, G07.02, G07.03, G07.04, G07.05, G07.06, G07.07, G07.08, G07.09。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 固定区域与后续相位族使用同一北盘/南帽分割。
- 闭曲面紧且无边界，完整输出属于标准 S²。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 没有标准S²的实际闭面嵌入及固定盘帽拓扑分割。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：固定区域与后续相位族使用同一北盘/南帽分割。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：闭曲面紧且无边界，完整输出属于标准 S²。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：在标准S²上拼出光滑嵌入F₀，北侧为图盘、南侧为补帽，并定义光滑正定gΣ=F₀*δ。 | G07.10（组合全部子任务） |
| acceptance.01：不用equator处退化的xy半球投影 | G07.01, G07.02, G07.03, G07.04 |
| acceptance.02：直接标准S²避免另造曲面后偷用分类定理 | G07.01, G07.05, G07.06 |
| acceptance.03：metric是实际F₀的拉回 | G07.08, G07.09 |

<a id="g08"></a>
## G08 相位族联合光滑、周期与固定区域

**原节点完整目标：** 图盘上Fτ=R_(-2πτ)F₀R_(2πτ)，补帽固定；证明联合光滑、Fτ+1=Fτ，以及内盘和补帽逐点固定。

**原上游里程碑：** G03, G07

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [01-introduction.tex:172–174](../../paper/flexible-surface-rewrite/01-introduction.tex#L172)；[02-geometry.tex:230–239](../../paper/flexible-surface-rewrite/02-geometry.tex#L230)

<a id="g08-01"></a>
### G08.01 图盘旋转共轭的联合光滑性

**输出：** 对同一 D 的图映射定义 Fτ=R(-2πτ)F₀R(2πτ)，证明在盘点和实参数上联合 C∞，并保留同一盘域。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 60–180 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- q 已固定，τ 为独立相位。
- 角旋转使用真实 Euclidean 正交作用。

**可复用基础：** Geometry/GraphRotationFamily.lean 与 PlanarRotations.lean 已有局部联合证明。

**本轮核对：** 同一D的盘内旋转共轭及真实E3轴旋转形式已证联合C∞，任意实相位有效并保持同一圆盘。

**源码证据 `ContinuousFlexibility/Geometry/GraphRotationFamily.lean`：** `ContinuousFlexibility.rotationConjugate`, `ContinuousFlexibility.contDiff_rotationConjugate_joint`, `ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_joint_smooth`

真实联合光滑。

**源码证据 `ContinuousFlexibility/Contracts/GraphFamilyImage.lean`：** `ContinuousFlexibility.axialRotation`, `ContinuousFlexibility.contDiff_axialRotation_joint`, `ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_eq_axialRotation`, `ContinuousFlexibility.planarRotation_image_closedCartesianDisk`

真实Euclidean LinearIsometryEquiv及同盘旋转公式。

**逐条验收：**
- acceptance.01 [covered]：A、D固定后构造参数不变，τ为独立实相位。
- acceptance.02 [covered]：真实Euclidean轴线性等距与点/参数联合ContDiff均已证明。

<a id="g08-02"></a>
### G08.02 球面图内的固定帽族

**输出：** 在 G07 的同一球面图册上，将北侧旋转共轭与南侧常值帽定义成局部联合光滑族。

**局部依赖：** G08.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 固定帽与初始 F₀ 使用同一见证。
- 联合光滑覆盖参数全实轴，不只有限区间。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 尚无G07同一标准球面图册中的北旋转族/南固定帽联合局部映射。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：固定帽与初始 F₀ 使用同一见证。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：联合光滑覆盖参数全实轴，不只有限区间。

<a id="g08-03"></a>
### G08.03 开领圈上旋转精确抵消

**输出：** 用 P 的中心旋转及外域恒等公式证明两变量局部定义在共同开领圈相等，从而粘合为 S²×ℝ 上联合光滑 F。

**局部依赖：** G08.01, G08.02。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 220–550 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 恒等在开领圈逐点、逐参数成立。
- 不由逐参数光滑直接推断联合光滑。

**本轮核对：** 图盘内外逐点固定和真实图/cap开领圈等式已证；尚无S²×ℝ全局两变量粘合映射。

**源码证据 `ContinuousFlexibility/Geometry/GraphRotationFamily.lean`：** `ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_fixed_outside`, `ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_fixed_inside`, `ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_joint_smooth`

真实图族固定等式及联合光滑。

**源码证据 `ContinuousFlexibility/Geometry/CapDisk.lean`：** `ContinuousFlexibility.IsometricGraphDevelopment.graph_cap_open_collar`

同一无marker帽与图族的真实开领圈相等。

**未完成内容：**
- 在实际标准S²图册上粘成全局联合C∞ F。

**逐条验收：**
- acceptance.01 [covered]：图盘内外逐点固定和真实图/cap开领圈等式已证；尚无S²×ℝ全局两变量粘合映射。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：不由逐参数光滑直接推断联合光滑。

<a id="g08-04"></a>
### G08.04 一周期与初始成员

**输出：** 在同一全局 F 上证明 F(x,τ+1)=F(x,τ) 和 F(x,0)=F₀(x)，涵盖图盘、帽及领圈。

**局部依赖：** G08.03。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 100–280 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 周期针对所有 x、τ。
- 使用同一初始嵌入，不另选基准。

**本轮核对：** 图盘族周期和初始成员已证，全局球面F尚未定义。

**源码证据 `ContinuousFlexibility/Geometry/GraphRotationFamily.lean`：** `ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_periodic`, `ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_zero`

所有盘点、实参数上的周期及t=0。

**未完成内容：**
- 同一标准S²全局族周期与初始等式，包含帽及领圈。

**逐条验收：**
- acceptance.01 [partial]：目前局部支持未覆盖全部验收；尚缺：同一标准S²全局族周期与初始等式，包含帽及领圈。
- acceptance.02 [partial]：目前局部支持未覆盖全部验收；尚缺：同一标准S²全局族周期与初始等式，包含帽及领圈。

<a id="g08-05"></a>
### G08.05 两固定区域的逐点公式

**输出：** 证明 G07 的非退化内闭盘和互补帽上 Fτ=F₀，并保留两区域的规定圆盘拓扑与非空内部。

**局部依赖：** G08.03。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 160–420 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 固定的是材料点的像，不仅固定区域的像集。
- 内盘位于移动图盘内部，帽为预定互补区域。

**本轮核对：** 图族内闭盘和外域逐点固定已证；标准S²互补帽/内盘的实际拓扑和材料点区域尚缺。

**源码证据 `ContinuousFlexibility/Geometry/GraphRotationFamily.lean`：** `ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_fixed_inside`, `ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_fixed_outside`

真正逐点公式，不仅固定像集。

**未完成内容：**
- 标准S²的两个实际固定区域、规定圆盘拓扑、非空内部与互补关系。

**逐条验收：**
- acceptance.01 [covered]：图族内闭盘和外域逐点固定已证；标准S²互补帽/内盘的实际拓扑和材料点区域尚缺。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：内盘位于移动图盘内部，帽为预定互补区域。

<a id="g08-06"></a>
### G08.06 同一球面上的完整周期族

**输出：** 组装同一 Core、P、帽、F₀ 和全局 F 的联合 C∞、一周期、初始成员及固定区域结论。

**局部依赖：** G08.01, G08.02, G08.03, G08.04, G08.05。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 80–220 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 条件性几何族与分析存在性实例化分清。
- 不以图盘族替代完整闭球面族。

**本轮核对：** 给定Core的图盘周期等距族完整，但无同一标准球面、标记帽与全局F的完整组装。

**源码证据 `ContinuousFlexibility/Geometry/GraphRotationFamily.lean`：** `ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_joint_smooth`, `ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_periodic`, `ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_fixed_inside`, `ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_fixed_outside`

仅图盘族，源声明不作球面闭合结论。

**未完成内容：**
- 实际标准S²全局F、同一标记帽及固定区域的组装。

**逐条验收：**
- acceptance.01 [covered]：给定Core的图盘周期等距族完整，但无同一标准球面、标记帽与全局F的完整组装。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：不以图盘族替代完整闭球面族。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：图盘上Fτ=R_(-2πτ)F₀R_(2πτ)，补帽固定；证明联合光滑、Fτ+1=Fτ，以及内盘和补帽逐点固定。 | G08.06（组合全部子任务） |
| acceptance.01：逐参数光滑不替代联合光滑 | G08.01, G08.02, G08.03 |
| acceptance.02：两个固定区域具有非空内部和规定圆盘拓扑 | G08.05 |
| acceptance.03：q已固定，τ是独立相位 | G08.01, G08.06 |
| remaining.01：尚未构造G06/G07同一固定帽和标准S²上的真实联合光滑拼接 | G06.08, G06.12, G06.14, G07.03, G07.04, G07.05, G07.06, G08.02, G08.03, G08.05 |
| remaining.02：尚需在真实Core见证上实例化；图盘族不等于闭球面族 | N12.09, G01.04, MAIN.01, G07.05, G08.03, G08.06, MAIN.03 |

**覆盖说明 G08.remaining.01：** 同一固定帽的实际存在与分离在G06.08/12/14，标准S²和真实图册过渡由G07.03–06构造，G08.02/03/05在此基础上完成双变量光滑拼接及固定区域。单独图盘族不能完成此义务。

**覆盖说明 G08.remaining.02：** 实际Core由N12.09/G01.04供给并经MAIN.01选定；G07.05和G08.03给出完整闭球面族，G08.06及MAIN.03在同一见证上组装。条件性图族结论不提升为实际Core或球面存在性。

<a id="g09"></a>
## G09 每一相位均为同度量嵌入

**原节点完整目标：** 每个Fτ是光滑嵌入且Fτ*δ=gΣ。

**原上游里程碑：** G05, G06, G08

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [02-geometry.tex:230–239](../../paper/flexible-surface-rewrite/02-geometry.tex#L230)

<a id="g09-01"></a>
### G09.01 全部相位图盘的同一度量

**输出：** 由径向内禀旋转保持 g，证明每个实 τ 的图盘族实际拉回 Euclidean 度量等于初始 g。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 80–240 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- tensor 等式量化两独立切向量。
- τ 无额外小参数限制。

**可复用基础：** Geometry/GraphRotationFamily.lean 已有实际 metric/immersion 支持。

**本轮核对：** 图族全部实相位的真实Euclidean拉回metric已直接证明为同一cartesianMetric。

**源码证据 `ContinuousFlexibility/Geometry/GraphRotationFamily.lean`：** `ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_remainder_metric`, `ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_metric`

最终量化t,x,u,v，使用真实fderiv与Euclidean inner。

**逐条验收：**
- acceptance.01 [covered]：最终metric等式明确量化两个独立切向量。
- acceptance.02 [covered]：t为任意实数，无小参数限制。

<a id="g09-02"></a>
### G09.02 帽与领圈上的度量一致性

**输出：** 证明固定帽的拉回度量恒为 F₀ 的度量，利用共同领圈的映射相等将北侧 tensor 等式与南侧 tensor 等式相容。

**局部依赖：** G09.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 180–450 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 等式作为标准 S² 切空间 tensor 表述。
- 领圈交叠不能遗漏或重复定义度量。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 没有标准S²全局Fτ/gΣ及帽与领圈的切空间tensor拼接。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：等式作为标准 S² 切空间 tensor 表述。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：领圈交叠不能遗漏或重复定义度量。

<a id="g09-03"></a>
### G09.03 相位族的流形 immersion

**输出：** 用正定拉回度量或具体坐标正规形证明每个 Fτ 的实际流形 IsImmersion，包含轴端与 rim。

**局部依赖：** G09.01, G09.02。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 220–550 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 应用真实切映射，不止 Euclidean fderiv 单射。
- 所有局部图的假设逐项实例化。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 没有标准S² Fτ的实际流形IsImmersion；当前只有Euclidean图盘fderiv单射。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：应用真实切映射，不止 Euclidean fderiv 单射。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：所有局部图的假设逐项实例化。

<a id="g09-04"></a>
### G09.04 全部相位的全局单射

**输出：** 用实际图盘像是轴旋转图、固定帽统一分离及共同领圈的唯一识别，证明每个 Fτ 在标准 S² 上单射。

**局部依赖：** G09.01, G09.02。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 220–550 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 逐类排除图内、帽内和跨块交点。
- 证明覆盖全部 τ 的统一分离。

**本轮核对：** 每相位图盘embedding、同一无marker帽embedding与交集恰为attaching rim已证；尚无标准S²粘合后的全局单射。

**源码证据 `ContinuousFlexibility/Geometry/GraphRotationFamily.lean`：** `ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_embedding_restrict`

每个图盘自身的全局embedding。

**源码证据 `ContinuousFlexibility/Geometry/CapDisk.lean`：** `ContinuousFlexibility.isEmbedding_capDiskEmbeddingMap`, `ContinuousFlexibility.IsometricGraphDevelopment.graph_cap_intersection`, `ContinuousFlexibility.IsometricGraphDevelopment.exists_fixed_cap_attachment`

真实帽embedding及全相位跨块分离。

**未完成内容：**
- 实际标准S²拼接和共同领圈点识别，从而得到Fτ全局单射。

**逐条验收：**
- acceptance.01 [partial]：目前局部支持未覆盖全部验收；尚缺：实际标准S²拼接和共同领圈点识别，从而得到Fτ全局单射。
- acceptance.02 [partial]：目前局部支持未覆盖全部验收；尚缺：实际标准S²拼接和共同领圈点识别，从而得到Fτ全局单射。

<a id="g09-05"></a>
### G09.05 紧球面给全局 topological embedding

**输出：** 对各 τ 将连续单射与标准 S² 紧性结合，证明 Fτ 到 E3 的 topological embedding 并识别实际闭像。

**局部依赖：** G09.03, G09.04。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 120–330 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 闭像确为 range Fτ。
- 不把 immersion 或局部单射称为全局 embedding。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 没有标准S²上的实际连续单射Fτ与其range的紧球面embedding。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：闭像确为 range Fτ。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：不把 immersion 或局部单射称为全局 embedding。

<a id="g09-06"></a>
### G09.06 全相位同度量光滑嵌入

**输出：** 合并联合光滑、实际 IsImmersion、topological embedding 及全局 Fτ*δ=gΣ，输出完整等距嵌入族。

**局部依赖：** G09.01, G09.02, G09.03, G09.04, G09.05。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 80–220 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- gΣ 必须是 G07 同一 F₀ 的拉回度量。
- 所有实 τ 的量词位于最终结论。

**本轮核对：** 图族Euclidean metric、immersion与embedding已全证；完整标准球面smooth embedding及gΣ尚缺。

**源码证据 `ContinuousFlexibility/Geometry/GraphRotationFamily.lean`：** `ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_embedding`, `ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_metric`, `ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_immersion`

仅全平面/圆盘图族三项。

**未完成内容：**
- 标准S²实际Fτ、流形IsImmersion、全局embedding与同一gΣ的tensor等式。

**逐条验收：**
- acceptance.01 [partial]：目前局部支持未覆盖全部验收；尚缺：标准S²实际Fτ、流形IsImmersion、全局embedding与同一gΣ的tensor等式。
- acceptance.02 [partial]：目前局部支持未覆盖全部验收；尚缺：标准S²实际Fτ、流形IsImmersion、全局embedding与同一gΣ的tensor等式。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：每个Fτ是光滑嵌入且Fτ*δ=gΣ。 | G09.06（组合全部子任务） |
| acceptance.01：覆盖所有实τ | G09.01, G09.04, G09.06 |
| acceptance.02：不能仅证明immersion或局部单射 | G09.03, G09.04, G09.05 |
| acceptance.03：嵌入是全球结论 | G09.04, G09.05 |
| remaining.01：隔离补帽/球面拼接和所有相位全球嵌入尚未证明 | G06.08, G06.12, G06.14, G07.05, G07.07, G07.08, G07.10, G08.03, G09.02, G09.04, G09.05 |
| remaining.02：标准球面流形上的smooth embedding/IsImmersion需实际图坐标正规形桥接，不能直接把现有微分单射当作库中的IsImmersion | G07.02, G07.03, G07.04, G07.06, G07.08, G09.03, G09.05, G09.06 |

**覆盖说明 G09.remaining.01：** G06.08/12/14承担与全相位图盘统一分离的实际帽；G07.05/07/08/10及G08.03承担标准球面拼接；G09.02/04/05才证明这些实际成员的同度量和全球嵌入。覆盖列出构造环节而非只引用最终组装。

**覆盖说明 G09.remaining.02：** G07.02/03/04/06/08给出标准球面真实图坐标和切空间微分桥接，G09.03在每个相位证明实际IsImmersion，G09.05/06再与全局topological embedding组合。已有Euclidean微分单射不能直接称为流形smooth embedding。

<a id="g10"></a>
## G10 径向盘的边界等距刚性

**原节点完整目标：** 对本构造的径向盘度量，光滑内禀等距自微分同胚H若在外领圈等于Rθ，则全盘等于Rθ。

**原上游里程碑：** C00

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [02-geometry.tex:241–248](../../paper/flexible-surface-rewrite/02-geometry.tex#L241)

<a id="g10-01"></a>
### G10.01 径向度量的 Cartesian 正则性

**输出：** 对本构造径向盘度量写出 Cartesian 系数、光滑逆矩阵及中心 Euclidean 邻域，证明在整个开盘 C∞ 正定。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 200–500 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 不在极坐标中心除以零。
- 系数来自实际径向 profile。

**本轮核对：** 真实径向profile因子的原点光滑/标准邻域及一般metric逆已具备；未将实际cartesianMetric打包为全局C∞且det非零的PlaneMetricField。

**源码证据 `ContinuousFlexibility/Contracts/CartesianMetricRegularity.lean`：** `ContinuousFlexibility.FlatAnnularCore.contDiff_cartesianProfileFactor`, `ContinuousFlexibility.FlatAnnularCore.cartesianRemainder_standard_left`

profile原点光滑及标准邻域基础；注意remainder不是完整radial metric。

**源码证据 `ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean`：** `ContinuousFlexibility.planeMetricInverse`, `ContinuousFlexibility.planeMetricInverse_pairing`, `ContinuousFlexibility.contDiffAt_planeMetricInverse_apply`

一般实际CLM metric场逆与光滑性，尚非当前径向场实例。

**未完成内容：**
- 真实cartesianMetric的PlaneMetricField构造、全局C∞/det≠0及中心Euclidean验证。

**逐条验收：**
- acceptance.01 [partial]：目前局部支持未覆盖全部验收；尚缺：真实cartesianMetric的PlaneMetricField构造、全局C∞/det≠0及中心Euclidean验证。
- acceptance.02 [partial]：目前局部支持未覆盖全部验收；尚缺：真实cartesianMetric的PlaneMetricField构造、全局C∞/det≠0及中心Euclidean验证。

<a id="g10-02"></a>
### G10.02 真实 Christoffel 系数及光滑性

**输出：** 用实际 g、g⁻¹ 和一阶导定义 Christoffel 符号，证明坐标 Koszul 恒等式与系数 C∞。

**局部依赖：** G10.01。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 220–550 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 公式使用实际系数导数。
- 不新增任意连接保持假设。

**本轮核对：** 实际metric系数、逆、Koszul值、Christoffel及其pairing和C∞已完成，适用于任意满足假设的真实metric场。

**源码证据 `ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean`：** `ContinuousFlexibility.planeMetricInverse`, `ContinuousFlexibility.planeMetricInverse_pairing`, `ContinuousFlexibility.metricKoszulValue`, `ContinuousFlexibility.metricChristoffel`, `ContinuousFlexibility.metricChristoffel_pairing`, `ContinuousFlexibility.contDiffAt_metricKoszulValue`, `ContinuousFlexibility.contDiffAt_metricChristoffel`, `ContinuousFlexibility.contDiffAt_metricChristoffelLinear`

从实际fderiv g与真实逆构造Christoffel，无任意connection保持输入。

**逐条验收：**
- acceptance.01 [covered]：metricKoszulValue用实际fderiv g，pairing验证Koszul恒等式。
- acceptance.02 [covered]：只有实际g光滑/对称/det非零，无新增connection保持前提。

<a id="g10-03"></a>
### G10.03 微分等距方程的一阶微分

**输出：** 对实际光滑内禀等距自微分同胚 H，从 g(Hx)(DHv,DHw)=g(x)(v,w) 求导，写出含 D²H 的精确坐标恒等式。

**局部依赖：** G10.01。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 250–650 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- H 的实际二阶导参与公式。
- 仅以 metric identity 和光滑性为输入。

**本轮核对：** 真实metric identity的一阶微分公式独立已证，包含全部实际D²H项。

**源码证据 `ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean`：** `ContinuousFlexibility.fderiv_metric_pullback_apply`, `ContinuousFlexibility.fderiv_metric_evaluation_apply`, `ContinuousFlexibility.differentiated_metric_identity`

从邻域metric等式取实际fderiv，不假设连接变换。

**逐条验收：**
- acceptance.01 [covered]：公式显式包含fderiv(fderiv H)的两项。
- acceptance.02 [covered]：仅实际可微性、H的C²及邻域metric identity为输入。

<a id="g10-04"></a>
### G10.04 混合偏导与 Hessian 变换

**输出：** 结合 D²H 的对称性及 Koszul 恒等式，消元证明 D²H 与两端 Christoffel 系数的完整变换式。

**局部依赖：** G10.02, G10.03。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 300–700 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 连接保持由证明推出。
- Hessian 变换式对任意两个坐标向量成立。

**本轮核对：** 实际Hessian/Koszul三项消元及完整Christoffel变换式已证，实际metric还可推出微分双射。

**源码证据 `ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean`：** `ContinuousFlexibility.metric_hessian_koszul`, `ContinuousFlexibility.metric_hessian_transformation`, `ContinuousFlexibility.metric_derivative_bijective`

混合偏导对称结合真实metric逆识别向量Hessian。

**逐条验收：**
- acceptance.01 [covered]：连接/Hessian变换从metric identity推出，非输入假设。
- acceptance.02 [covered]：结论量化任意u,v，给完整向量式。

<a id="g10-05"></a>
### G10.05 旋转归一化与领圈一阶 jet

**输出：** 将领圈等于 Rθ 的 H 组合为领圈恒等的 K，证明 K 仍保持同一径向度量，且某个真实内点上 K=id、DK=Id。

**局部依赖：** G10.01, G10.03。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 180–450 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 内禀旋转保持真实径向 tensor。
- 领圈导数恒等来自开集相等。

**本轮核对：** 内禀旋转保持真实cartesianMetric与identity germ微分支持具备；未对当前H构造旋转归一化K。

**源码证据 `ContinuousFlexibility/Geometry/PlanarRotations.lean`：** `ContinuousFlexibility.cartesianMetric_planarRotation`

真实径向tensor旋转保持。

**源码证据 `ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean`：** `ContinuousFlexibility.metric_isometry_eq_id_of_identity_germ_on_convex`

从identity germ取真实导数的通用定理，但没有当前K的构造。

**未完成内容：**
- 实际定义K=R(-θ)∘H并证明其metric identity。
- 选真实非空领圈点并输出共同初始value/derivative jet。

**逐条验收：**
- acceptance.01 [covered]：内禀旋转保持真实cartesianMetric与identity germ微分支持具备；未对当前H构造旋转归一化K。
- acceptance.02 [partial]：目前局部支持未覆盖全部验收；尚缺：实际定义K=R(-θ)∘H并证明其metric identity。；选真实非空领圈点并输出共同初始value/derivative jet。

<a id="g10-06"></a>
### G10.06 从领圈内点到任意点的线段

**输出：** 对任意目标开盘点构造始于领圈点的实际直线 γ:[0,1]→D，证明其全程包含于开盘且具有正紧邻域余量。

**局部依赖：** G10.05。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 180–450 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 不能让起点只位于边界。
- 线段与周围紧管道均留在实际定义域。

**本轮核对：** 实际直线和凸域内完整线段包含性在通用刚性证明中已实现；尚未实例化当前领圈起点和开盘正余量。

**源码证据 `ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean`：** `ContinuousFlexibility.metricLine`, `ContinuousFlexibility.hasDerivAt_metricLine`, `ContinuousFlexibility.metric_isometry_oneJet_rigidity_on_convex`

证明体hline覆盖完整Icc0 1。

**源码证据 `ContinuousFlexibility/Contracts/CenteredDevelopment.lean`：** `ContinuousFlexibility.convex_cartesianDisk`

真实目标开盘凸性。

**未完成内容：**
- 从当前真实非空领圈选起点。
- 实例化紧线段到开盘边界的正余量。

**逐条验收：**
- acceptance.01 [partial]：目前局部支持未覆盖全部验收；尚缺：从当前真实非空领圈选起点。；实例化紧线段到开盘边界的正余量。
- acceptance.02 [partial]：目前局部支持未覆盖全部验收；尚缺：从当前真实非空领圈选起点。；实例化紧线段到开盘边界的正余量。

<a id="g10-07"></a>
### G10.07 沿线段的一阶 jet 实际 ODE

**输出：** 由 Hessian 变换式证明 Y(t)=(K(γ(t)),DK(γ(t))) 满足明确的一阶非自治 ODE，写出完整向量场及作用空间。

**局部依赖：** G10.02, G10.04, G10.06。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 250–650 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 解的导数由链式法则和 Hessian 式算出。
- 场在位置与矩阵状态上有实际定义。

**本轮核对：** 真实first-jet场及沿直线的实际ODE已从Hessian变换证明，无预设connection/jet transport。

**源码证据 `ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean`：** `ContinuousFlexibility.metricJetRHS`, `ContinuousFlexibility.contDiff_metricJetRHS`, `ContinuousFlexibility.hasDerivAt_metricJet_along_line`

真实状态空间point×CLM；由链式法则计算两分量导数。

**逐条验收：**
- acceptance.01 [covered]：HasDerivAt的证明明确用真实Hessian变换与链式法则。
- acceptance.02 [covered]：RHS在位置及矩阵状态上真实定义并证明联合C∞。

<a id="g10-08"></a>
### G10.08 恒等 jet 解与共同初值

**输出：** 证明参考曲线 Y₀(t)=(γ(t),Id) 满足同一个 ODE，并且与 Y 在 t=0 的初始数据相同。

**局部依赖：** G10.05, G10.07。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 160–420 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 两曲线的方程、参数与初始时刻完全一致。
- 参考解不是不同归一化下另一个场的解。

**本轮核对：** 恒等jet是同一实际ODE的解，通用刚性证明真实构造两曲线并由初始value/derivative给共同初值。

**源码证据 `ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean`：** `ContinuousFlexibility.hasDerivAt_identityMetricJet`, `ContinuousFlexibility.metric_isometry_oneJet_rigidity_on_convex`

参考曲线(γ,Id)使用同一metricJetRHS，证明体hzero明确来自hvalue/hder。

**逐条验收：**
- acceptance.01 [covered]：同一g,a,d,RHS与时间0用于两条实际解。
- acceptance.02 [covered]：参考解满足同一场，不是另一个归一化场。

<a id="g10-09"></a>
### G10.09 紧管道上的统一 Lipschitz 界

**输出：** 在包含两条实际 jet 曲线的共同紧管道上，由场状态导数的界证明同一个 Lipschitz 常数；保证管道位置分量处于开盘。

**局部依赖：** G10.01, G10.02, G10.06, G10.07, G10.08。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 250–650 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 常数对整个待比较时间区间有效。
- 验证实际 ODE 唯一性定理的全部局部域假设。

**本轮核对：** 包含两条真实轨迹的紧球及统一Lipschitz常数已构造并用于唯一性；未严格证明原任务指定的管道位置仍在开盘。

**源码证据 `ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean`：** `ContinuousFlexibility.smooth_ode_unique_on_unit_interval`, `ContinuousFlexibility.contDiff_metricJetRHS`

真实紧轨迹并包于闭球，紧凸乘积上获同一K；当前metric在全平面C∞/det≠0，球可跨盘外。

**未完成内容：**
- 按任务证明管道位置在实际开盘，或由总控核准使用全平面非退化metric这一已证替代接口。

**逐条验收：**
- acceptance.01 [covered]：包含两条真实轨迹的紧球及统一Lipschitz常数已构造并用于唯一性；未严格证明原任务指定的管道位置仍在开盘。
- acceptance.02 [partial]：目前局部支持未覆盖全部验收；尚缺：按任务证明管道位置在实际开盘，或由总控核准使用全平面非退化metric这一已证替代接口。

<a id="g10-10"></a>
### G10.10 ODE 唯一性传播到开盘

**输出：** 应用实际 ODE 唯一性及必要的区间延续，推出 Y=Y₀，进而对任意开盘目标点有 K(x)=x、DK(x)=Id。

**局部依赖：** G10.07, G10.08, G10.09。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 220–550 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 唯一性调用基于实际已证明的两个解。
- 覆盖完整 [0,1]，非仅起点邻域。

**本轮核对：** 任意凸开域上真实metric identity与一个真实jet给H=id、DH=Id，完整[0,1]实际ODE比较已证明。

**源码证据 `ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean`：** `ContinuousFlexibility.smooth_ode_unique_on_unit_interval`, `ContinuousFlexibility.metric_isometry_oneJet_rigidity_on_convex`

实际f/k两解、continuousOn、HasDerivWithinAt、共同初值全部核验，取t=1到任意目标。

**逐条验收：**
- acceptance.01 [covered]：唯一性调用基于实际已计算的两解和同一RHS。
- acceptance.02 [covered]：hfg作用于整个Icc0 1，t=1输出任意目标点。

<a id="g10-11"></a>
### G10.11 闭盘延拓与旋转还原

**输出：** 由连续性把 K=id 延拓至闭盘边界，并还原原 H=Rθ；量化任意允许的 θ 和光滑等距自微分同胚。

**局部依赖：** G10.05, G10.10。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 160–420 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 边界结论从实际稠密性/闭包推出。
- 不限制环境旋转角范围。

**本轮核对：** 真实开闭盘闭包及通用identity-germ刚性已有；尚无原H=Rθ的闭盘连续延拓和旋转还原定理。

**源码证据 `ContinuousFlexibility/Contracts/CenteredDevelopment.lean`：** `ContinuousFlexibility.closure_cartesianDisk`

真实开盘闭包等于闭盘。

**源码证据 `ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean`：** `ContinuousFlexibility.metric_isometry_eq_id_of_identity_germ_on_convex`

通用开域identity germ刚性。

**未完成内容：**
- 旋转归一化K与原H的实际关系。
- 原H的闭盘延拓及全部θ还原。

**逐条验收：**
- acceptance.01 [partial]：目前局部支持未覆盖全部验收；尚缺：旋转归一化K与原H的实际关系。；原H的闭盘延拓及全部θ还原。
- acceptance.02 [partial]：目前局部支持未覆盖全部验收；尚缺：旋转归一化K与原H的实际关系。；原H的闭盘延拓及全部θ还原。

<a id="g10-12"></a>
### G10.12 径向盘边界等距刚性完整定理

**输出：** 组装仅以真实径向 metric identity、光滑自微分同胚及外领圈旋转为前提的全盘刚性。

**局部依赖：** G10.01, G10.02, G10.03, G10.04, G10.05, G10.06, G10.07, G10.08, G10.09, G10.10, G10.11。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 80–220 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 最终声明没有连接保持、jet刚性或ODE唯一解作为新假设。
- 路径、解、Lipschitz 界均由本节点实际构造。

**本轮核对：** 真实metric Hessian、jet ODE和通用凸开域1jet刚性已证；本构造径向metric实例化、旋转归一化及闭边界仍缺。

**源码证据 `ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean`：** `ContinuousFlexibility.metric_hessian_transformation`, `ContinuousFlexibility.metric_isometry_oneJet_rigidity_on_convex`, `ContinuousFlexibility.metric_isometry_eq_id_of_identity_germ_on_convex`

通用定理没有新connection/jet假设，但需要实际全平面C∞非退化metric，尚未接当前径向场。

**未完成内容：**
- G10.01/05/06/11 的径向metric、外领圈旋转归一化及闭盘结论。

**逐条验收：**
- acceptance.01 [partial]：目前局部支持未覆盖全部验收；尚缺：G10.01/05/06/11 的径向metric、外领圈旋转归一化及闭盘结论。
- acceptance.02 [partial]：目前局部支持未覆盖全部验收；尚缺：G10.01/05/06/11 的径向metric、外领圈旋转归一化及闭盘结论。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：对本构造的径向盘度量，光滑内禀等距自微分同胚H若在外领圈等于Rθ，则全盘等于Rθ。 | G10.12（组合全部子任务） |
| acceptance.01：实际微分等距方程，不能把连接保持或1jet刚性作为新前提 | G10.03, G10.04 |
| acceptance.02：严格构造光滑Christoffel系数、两条真实ODE解和同一紧管道Lipschitz界 | G10.01, G10.02, G10.07, G10.08, G10.09 |
| acceptance.03：开盘传播及闭盘连续延拓全部实际证明；不能暗用未经实现的测地线刚性 | G10.06, G10.10, G10.11, G10.12 |

<a id="g11"></a>
## G11 移动盘像不恒定

**原节点完整目标：** 非径向z蕴含存在两个相位使移动圆盘像不同。

**原上游里程碑：** G04, G05, G08, G10

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [02-geometry.tex:241–248](../../paper/flexible-surface-rewrite/02-geometry.tex#L241)

<a id="g11-01"></a>
### G11.01 图像的基底逆与高度恢复

**输出：** 用同一 P 的实际逆把图盘像写成 y↦(y,Z(y))，证明每个基底点唯一高度及图像逆公式。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** complete。**初始粒度：** 160–420 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 恢复的是实际图盘像。
- 基底圆盘在所有相位保持同一集合。

**本轮核对：** 实际physicalHeight=cartesianHeight∘P⁻¹已定义并C∞，同一图映射精确为物理高度图；真实基底逆和各相位满同盘具备。

**源码证据 `ContinuousFlexibility/Contracts/GraphFamilyCurvature.lean`：** `ContinuousFlexibility.IsometricGraphDevelopment.physicalHeight`, `ContinuousFlexibility.IsometricGraphDevelopment.contDiff_physicalHeight`, `ContinuousFlexibility.IsometricGraphDevelopment.map_eq_physical_graph`

真实D.map的高度图公式及同一P.symm恢复高度。

**源码证据 `ContinuousFlexibility/Geometry/GraphEmbedding.lean`：** `ContinuousFlexibility.graphMap_two`, `ContinuousFlexibility.graphBaseProjection_graphMap`

基底和第三坐标真实投影等式给唯一高度。

**源码证据 `ContinuousFlexibility/Contracts/GraphFamilyImage.lean`：** `ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_projects_onto_disk`

各相位基底为同一实际圆盘。

**逐条验收：**
- acceptance.01 [covered]：map_eq_physical_graph与实际D.map相等，坐标投影给真实图逆及唯一高度。
- acceptance.02 [covered]：rotationFamily_projects_onto_disk对每相位给相同闭盘基底。

<a id="g11-02"></a>
### G11.02 恒像假设下的共轭自微分同胚

**输出：** 假设所有旋转图盘像相同，对任意 θ 构造 Hθ=P⁻¹RθP，证明其在同一圆盘上是光滑自微分同胚。

**局部依赖：** G11.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 180–450 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 全局逆与盘像保持来自同一 P。
- Hθ 的定义域和像均为整个盘。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 未定义并证明恒像假设下Hθ=P⁻¹RθP为同盘自微分同胚；现有rotationConjugate是R⁻¹PR，不是本Hθ。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：全局逆与盘像保持来自同一 P。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：Hθ 的定义域和像均为整个盘。

<a id="g11-03"></a>
### G11.03 从恒像推出高度保持

**输出：** 由图像高度唯一性证明 z∘Hθ=z，且图嵌入满足实际 F∘Hθ=Rθ∘F。

**局部依赖：** G11.01, G11.02。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 160–420 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 等式来自实际像集相等。
- 不以参数化映射相同替代恒像假设。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 没有从恒像假设推出z∘Hθ=z及F∘Hθ=Rθ∘F的声明。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：等式来自实际像集相等。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：不以参数化映射相同替代恒像假设。

<a id="g11-04"></a>
### G11.04 共轭映射的度量与领圈

**输出：** 从 F∘Hθ 的实际等式及图盘拉回度量证明 Hθ 保持 g，并在外开领圈等于 Rθ。

**局部依赖：** G11.02, G11.03。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 180–450 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- metric identity 覆盖两个切向量。
- 外领圈等式用 P=id 及实际盘域。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 没有由恒像共轭Hθ导出真实metric identity及外领圈旋转。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：metric identity 覆盖两个切向量。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：外领圈等式用 P=id 及实际盘域。

<a id="g11-05"></a>
### G11.05 刚性迫使高度径向

**输出：** 应用 G10 得 Hθ=Rθ，对所有 θ 推出 z(r,α+θ)=z(r,α)，并将实角到同半径点的对应写清。

**局部依赖：** G11.03, G11.04。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 160–420 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 使用全部旋转而非仅 π 周期。
- θ 与实际 Cartesian/polar 位置关系明确。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 未对当前Hθ实例化径向刚性并推出全部旋转高度不变。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：使用全部旋转而非仅 π 周期。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：θ 与实际 Cartesian/polar 位置关系明确。

<a id="g11-06"></a>
### G11.06 两个移动盘像不同的见证

**输出：** 把全旋转高度不变与原 Core 同半径两个角值不同的见证矛盾，得存在两个相位使闭图盘像不同。

**局部依赖：** G11.01, G11.02, G11.03, G11.04, G11.05。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 140–360 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 输出比较 image/range 集合。
- 从角度到实相位的 2π 换算明确。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 没有两个真实移动盘像不同的相位存在见证。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：输出比较 image/range 集合。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：从角度到实相位的 2π 换算明确。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：非径向z蕴含存在两个相位使移动圆盘像不同。 | G11.06（组合全部子任务） |
| acceptance.01：比较像集而非参数化映射 | G11.01, G11.03, G11.06 |
| acceptance.02：Hθ确实是全盘等距自微分同胚 | G11.02, G11.04 |
| acceptance.03：非径向用存在两个角值不等的明确谓词 | G11.05, G11.06 |

<a id="g12"></a>
## G12 全等变换的有限候选集

**原节点完整目标：** 任意联系两个闭像的欧氏仿射等距变换，固定共同marker p、向外法向和两条不同主方向线，故候选至多四个。

**原上游里程碑：** G06, G09, G15, D01

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [02-geometry.tex:250–253](../../paper/flexible-surface-rewrite/02-geometry.tex#L250)

<a id="g12-01"></a>
### G12.01 全等变换运输真实内部区域

**输出：** 若 A 联系两个完整闭像，利用 G15 的补集连通分支识别证明 A(Ωτ)=Ωσ，并排除将有界内部送到无界外部。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 220–550 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- A 量化任意 AffineIsometryEquiv。
- 内部运输来自实际区域识别。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 没有真实Ωτ或其补集连通分支识别，不能证明全等运输内部。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：A 量化任意 AffineIsometryEquiv。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：内部运输来自实际区域识别。

<a id="g12-02"></a>
### G12.02 向外法向的正确运输

**输出：** 由局部边界/内部侧关系及 A(Ωτ)=Ωσ，证明 A 的线性部把向外单位法向送为向外单位法向，含 det=-1 情形。

**局部依赖：** G12.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 220–550 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 不使用参数叉积方向推断 outward。
- 环境反射不能额外反转已运输的 outward 选择。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 没有真实闭曲面的outward normal或内部侧运输证明。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：不使用参数叉积方向推断 outward。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：环境反射不能额外反转已运输的 outward 选择。

<a id="g12-03"></a>
### G12.03 唯一曲率标记迫使固定点

**输出：** 用实际 K 的环境等距自然性及同一帽中的唯一全局峰，证明每个闭像全等变换必须固定同一标记点 p。

**局部依赖：** G12.01。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 160–420 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 峰值比较覆盖整个闭像。
- p 与相位无关。

**本轮核对：** 独立marker图的真实唯一K峰及任意仿射等距的局部K自然性已证，但完整帽/闭面峰与闭像全等约束未建立。

**源码证据 `ContinuousFlexibility/Geometry/MarkedCap.lean`：** `ContinuousFlexibility.surfaceGaussianCurvature_markerBump_eq_peak_iff`

独立marker图唯一峰。

**源码证据 `ContinuousFlexibility/Geometry/SurfaceGeometry.lean`：** `ContinuousFlexibility.surfaceGaussianCurvature_affineIsometry`

任意仿射等距局部K自然性。

**未完成内容：**
- 实际已插入同一帽的全闭面唯一峰。
- 由任意闭像全等证明A p=p。

**逐条验收：**
- acceptance.01 [partial]：目前局部支持未覆盖全部验收；尚缺：实际已插入同一帽的全闭面唯一峰。；由任意闭像全等证明A p=p。
- acceptance.02 [partial]：目前局部支持未覆盖全部验收；尚缺：实际已插入同一帽的全闭面唯一峰。；由任意闭像全等证明A p=p。

<a id="g12-04"></a>
### G12.04 形算子运输固定两条主线

**输出：** 用向外法向和形算子自然性证明 A 的线性部保持标记点两条不同特征值对应的实际主方向线。

**局部依赖：** G12.02, G12.03。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 220–550 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 两条线分别保持，不能任意交换不同特征值。
- 使用实际切空间主方向桥接。

**本轮核对：** 给定E3算子不同特征值的特征线保持已证，尚未把实际曲面outward shape及主方向接入。

**源码证据 `ContinuousFlexibility/Geometry/MarkerStabilizer.lean`：** `ContinuousFlexibility.marker_line_preserved_of_commute`, `ContinuousFlexibility.marker_center_eigenvalues_injective`

以给定对角算子/commutation为前提的真实线代数。

**源码证据 `ContinuousFlexibility/Geometry/SurfaceGeometry.lean`：** `ContinuousFlexibility.surfaceShapeMatrix_affineIsometry`

局部shape自然性。

**未完成内容：**
- 真实切空间主线与outward shape。
- 任意闭像全等的实际线性部commutation/线保持。

**逐条验收：**
- acceptance.01 [partial]：目前局部支持未覆盖全部验收；尚缺：真实切空间主线与outward shape。；任意闭像全等的实际线性部commutation/线保持。
- acceptance.02 [partial]：目前局部支持未覆盖全部验收；尚缺：真实切空间主线与outward shape。；任意闭像全等的实际线性部commutation/线保持。

<a id="g12-05"></a>
### G12.05 固定法向和主线的正交基

**输出：** 在标记点把两条主方向线的单位向量与向外法向组成实际 E3 正交基，证明任意候选线性部在该基中形如 diag(ε₁,ε₂,1)。

**局部依赖：** G12.02, G12.04。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 200–500 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- ε₁、ε₂ 各自只能为 ±1。
- 正交基的选择全程与相位无关。

**本轮核对：** 给定非零线向量的等距作用为±v及给定E3基的四种编码已证；未构造实际marker主线/outward正交基。

**源码证据 `ContinuousFlexibility/Geometry/MarkerStabilizer.lean`：** `ContinuousFlexibility.linearIsometry_eq_or_eq_neg_of_mem_span`, `ContinuousFlexibility.markerStabilizerEncoding_mapsTo`, `ContinuousFlexibility.markerStabilizerEncoding_injOn`

抽象给定Basis的有限编码，不是当前曲面的真实主方向基。

**未完成内容：**
- 同一marker的实际主线与outward normal正交基。
- 真实全等变换在该基中diag(±1,±1,1)。

**逐条验收：**
- acceptance.01 [partial]：目前局部支持未覆盖全部验收；尚缺：同一marker的实际主线与outward normal正交基。；真实全等变换在该基中diag(±1,±1,1)。
- acceptance.02 [partial]：目前局部支持未覆盖全部验收；尚缺：同一marker的实际主线与outward normal正交基。；真实全等变换在该基中diag(±1,±1,1)。

<a id="g12-06"></a>
### G12.06 四个仿射候选的实际构造

**输出：** 为四种符号选择构造完整仿射等距 Aε，以固定 p 决定平移；证明任意允许全等变换等于其中一个。

**局部依赖：** G12.03, G12.05。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 220–550 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 仿射部分不能只证明线性部有限。
- 候选可以包含反射，数量上界为四。

**可复用基础：** Geometry/MarkerStabilizer.lean 有进行中的稳定子构造，须复核具体前提。

**本轮核对：** 给定p/Basis的真实affine stabilizer有限且encard≤4，固定点确定平移的注入已证；未显式构造四个符号Aε或接入当前marker。

**源码证据 `ContinuousFlexibility/Geometry/MarkerStabilizer.lean`：** `ContinuousFlexibility.markerStabilizers`, `ContinuousFlexibility.markerStabilizerEncoding_injOn`, `ContinuousFlexibility.markerStabilizerEncoding_mapsTo`, `ContinuousFlexibility.markerStabilizers_encard_le_four`, `ContinuousFlexibility.markerStabilizers_finite`

对象确为AffineIsometryEquiv集合，固定p及基上作用确定完整仿射映射。

**未完成内容：**
- 实际marker点、两主方向及法向基。
- 按当前任务显式构造四种符号Aε，并证明全部闭像全等属于其中。

**逐条验收：**
- acceptance.01 [partial]：目前局部支持未覆盖全部验收；尚缺：实际marker点、两主方向及法向基。；按当前任务显式构造四种符号Aε，并证明全部闭像全等属于其中。
- acceptance.02 [partial]：目前局部支持未覆盖全部验收；尚缺：实际marker点、两主方向及法向基。；按当前任务显式构造四种符号Aε，并证明全部闭像全等属于其中。

<a id="g12-07"></a>
### G12.07 相位无关的有限全等候选

**输出：** 输出同一至多四元素集合 C，证明任意 τ、σ 以及联系两闭像的 A 均属于 C。

**局部依赖：** G12.01, G12.02, G12.03, G12.04, G12.05, G12.06。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 120–320 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 集合只依赖共同 marker 的点/法向/主线。
- 量化全部 Euclidean affine isometries。

**本轮核对：** 给定marker基/算子条件的affine候选集至多四且有限已证；尚无当前闭像全等的统一候选归属。

**源码证据 `ContinuousFlexibility/Geometry/MarkerStabilizer.lean`：** `ContinuousFlexibility.markerStabilizers_encard_le_four`, `ContinuousFlexibility.markerOperatorStabilizers_subset`, `ContinuousFlexibility.markerOperatorStabilizers_encard_le_four`

真实通用代数定理，不包含闭像几何约束。

**未完成内容：**
- 真实闭像全等固定点/outward/两主线证明。
- 实际固定C之后量化所有τ、σ的全等归属。

**逐条验收：**
- acceptance.01 [partial]：目前局部支持未覆盖全部验收；尚缺：真实闭像全等固定点/outward/两主线证明。；实际固定C之后量化所有τ、σ的全等归属。
- acceptance.02 [partial]：目前局部支持未覆盖全部验收；尚缺：真实闭像全等固定点/outward/两主线证明。；实际固定C之后量化所有τ、σ的全等归属。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：任意联系两个闭像的欧氏仿射等距变换，固定共同marker p、向外法向和两条不同主方向线，故候选至多四个。 | G12.07（组合全部子任务） |
| acceptance.01：量化所有仿射等距，包括环境反射 | G12.01, G12.02, G12.06, G12.07 |
| acceptance.02：有限集合与相位无关 | G12.03, G12.05, G12.06 |
| acceptance.03：不得只证明orientation-preserving congruence有限 | G12.02, G12.05, G12.06 |

<a id="g13"></a>
## G13 闭球面像确实非全等

**原节点完整目标：** 存在τ₁,τ₂，对任意欧氏仿射等距A，A''range(Fτ₁)≠range(Fτ₂)。

**原上游里程碑：** G08, G11, G12

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [02-geometry.tex:250–256](../../paper/flexible-surface-rewrite/02-geometry.tex#L250)

<a id="g13-01"></a>
### G13.01 实际相位图高度函数

**输出：** 用同一 P 的逆定义 Zτ 在固定闭圆盘上的真实高度，证明其图恰为移动盘像，并给出与旋转的精确组合公式。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 160–420 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 实际图高度唯一性来自 G11 使用的同一图。
- 所有 τ 的定义域是相同闭盘。

**本轮核对：** 初始物理高度与移动盘像真实轴旋转已证；尚无相位高度Zτ的实际定义及完整graph/旋转组合公式。

**源码证据 `ContinuousFlexibility/Contracts/GraphFamilyCurvature.lean`：** `ContinuousFlexibility.IsometricGraphDevelopment.physicalHeight`, `ContinuousFlexibility.IsometricGraphDevelopment.map_eq_physical_graph`

初始真实物理高度图。

**源码证据 `ContinuousFlexibility/Contracts/GraphFamilyImage.lean`：** `ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_image_closedDisk`, `ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_projects_onto_disk`

真实移动盘像与同基底，足以支持后续Zτ构造。

**未完成内容：**
- 同一闭盘实际Zτ定义、graph识别和Zτ=Z₀∘Rτ的声明。

**逐条验收：**
- acceptance.01 [partial]：目前局部支持未覆盖全部验收；尚缺：同一闭盘实际Zτ定义、graph识别和Zτ=Z₀∘Rτ的声明。
- acceptance.02 [partial]：目前局部支持未覆盖全部验收；尚缺：同一闭盘实际Zτ定义、graph识别和Zτ=Z₀∘Rτ的声明。

<a id="g13-02"></a>
### G13.02 高度族在一致拓扑连续

**输出：** 由 (y,τ) 的联合连续性和闭盘紧性，证明 τ↦Zτ 是到 C(D) 一致范数拓扑的连续映射。

**局部依赖：** G13.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 不能用逐点连续代替一致拓扑连续。
- 实际 sup 范数及连续函数空间结构明确。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 没有实际τ↦Zτ:C(D)的一致范数连续性。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：不能用逐点连续代替一致拓扑连续。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：实际 sup 范数及连续函数空间结构明确。

<a id="g13-03"></a>
### G13.03 从完整闭像恢复顶部图

**输出：** 在中央圆柱内用上图与底盘严格分离，证明从完整闭像唯一恢复 Zτ，特别是闭像相同蕴含顶部图和盘像相同。

**局部依赖：** G13.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 220–550 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 不把底帽误识别为上图。
- 柱边界和共同领圈的恢复规则明确。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 没有完整闭像与真实底帽/顶部恢复函数，无法从闭像恢复Zτ。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：不把底帽误识别为上图。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：柱边界和共同领圈的恢复规则明确。

<a id="g13-04"></a>
### G13.04 全等性假设给出有限高度像

**输出：** 若所有闭像均与某一基准闭像全等，应用 G12 同一有限候选集，证明可能的闭像有限，进而可能的 Zτ 有限。

**局部依赖：** G13.01, G13.03。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 180–450 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 有限集合不依赖 τ。
- 从有限闭像到有限高度使用已证明的恢复映射。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 没有所有闭像全等时有限闭像/有限高度像的推论。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：有限集合不依赖 τ。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：从有限闭像到有限高度使用已证明的恢复映射。

<a id="g13-05"></a>
### G13.05 连通参数的有限连续像恒定

**输出：** 在真实 Hausdorff 函数空间 C(D) 中证明实参数连通连续像若有限则为单点，应用到 τ↦Zτ。

**局部依赖：** G13.02, G13.04。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 140–380 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 使用实轴整体或明确连通参数区间。
- 有限性与离散性结论作用于实际函数空间。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 没有将实参数到实际C(D)的连续像实例化为有限连通像并证明恒定。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：使用实轴整体或明确连通参数区间。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：有限性与离散性结论作用于实际函数空间。

<a id="g13-06"></a>
### G13.06 恒高度与移动盘像矛盾

**输出：** 把高度族恒定转为所有移动盘像相同，与 G11 的两个不同盘像见证矛盾。

**局部依赖：** G13.01, G13.03, G13.05。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 120–330 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 矛盾比较真实像集。
- 两个盘像见证属于当前同一球面族。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 没有同一球面族恒高度与不同盘像的真实见证矛盾。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：矛盾比较真实像集。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：两个盘像见证属于当前同一球面族。

<a id="g13-07"></a>
### G13.07 完整闭像非全等见证

**输出：** 导出存在 τ₁、τ₂，使对任意 Euclidean AffineIsometryEquiv A 都有 A  range Fτ₁ ≠ range Fτ₂。

**局部依赖：** G13.01, G13.02, G13.03, G13.04, G13.05, G13.06。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 120–300 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 最终量词覆盖含反射的全部 A。
- 不是仅证明参数映射不同或排除绕轴旋转。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 没有两个实际闭球面像对所有环境仿射等距非全等的存在声明。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：最终量词覆盖含反射的全部 A。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：不是仅证明参数映射不同或排除绕轴旋转。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：存在τ₁,τ₂，对任意欧氏仿射等距A，A''range(Fτ₁)≠range(Fτ₂)。 | G13.07（组合全部子任务） |
| acceptance.01：连续性载体和从闭像恢复顶部图均明确 | G13.01, G13.02, G13.03 |
| acceptance.02：不是仅排除绕轴旋转 | G13.04, G13.07 |
| acceptance.03：从不恒定到非全等的有限候选论证完整 | G13.04, G13.05, G13.06 |

<a id="g14"></a>
## G14 面积不变

**原节点完整目标：** 实际闭像曲面面积Area(Fτ(S²))与τ无关。

**原上游里程碑：** G09, D02

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [02-geometry.tex:258–260](../../paper/flexible-surface-rewrite/02-geometry.tex#L258)

<a id="g14-01"></a>
### G14.01 实际像面积的拉回公式实例化

**输出：** 对每个 Fτ 的实际标准球面嵌入应用 D02，证明闭像面积等于其真实诱导面积密度的球面积分。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 120–330 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 需用 G09 已证明的全局 embedding。
- 像面积为实际几何面积测度的总质量。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 没有实际标准S²嵌入族或像面积测度，参数图盘面积不满足该桥接。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：需用 G09 已证明的全局 embedding。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：像面积为实际几何面积测度的总质量。

<a id="g14-02"></a>
### G14.02 同一度量给同一面积密度

**输出：** 由 Fτ*δ=gΣ 证明全部相位的诱导面积测度一致，进而总面积相等。

**局部依赖：** G14.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 120–330 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 比较实际密度/测度而非定义成同一常数。
- 包含整个闭球面及交接区域。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 没有标准球面同一gΣ的实际诱导面积测度，当前仅盘内密度不变。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：比较实际密度/测度而非定义成同一常数。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：包含整个闭球面及交接区域。

<a id="g14-03"></a>
### G14.03 有限实际闭像面积不变

**输出：** 组装所有 τ 的有限像面积及与 τ=0 的相等式，完成主定理中的面积不变量。

**局部依赖：** G14.01, G14.02。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 80–220 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 有限性来自实际紧曲面积分。
- 不残留未经识别的形式面积名称。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 没有实际闭像有限面积不变量；graphDiskArea是参数图盘积分。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：有限性来自实际紧曲面积分。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：不残留未经识别的形式面积名称。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：实际闭像曲面面积Area(Fτ(S²))与τ无关。 | G14.03（组合全部子任务） |
| acceptance.01：像面积与参数化积分有已证桥接 | G14.01 |
| acceptance.02：不是只把同一gΣ的形式面积记作结论 | G14.02, G14.03 |

<a id="g15"></a>
## G15 显式围成区域及体积不变

**原节点完整目标：** 构造有界开内部区域Ωτ，证明边界恰为闭像、内外连通关系足以识别其围成区域，并证明Lebesgue体积恒定。

**原上游里程碑：** G06, G08, G09

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [02-geometry.tex:260–268](../../paper/flexible-surface-rewrite/02-geometry.tex#L260)

<a id="g15-01"></a>
### G15.01 侧帽内部的显式截面描述

**输出：** 从同一实际径线的中部严格下降及端部水平直段构造水平截面半径/等价显式内部不等式，证明侧帽内外的对应关系。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 250–650 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 逆高度仅在真实严格下降段取逆，单独处理水平端段。
- 截面描述必须是构造结论而非新的 cap 内部假设。

**本轮核对：** 真实径线严格下降中段、水平端段及柱内帽为底盘已证；尚未构造侧域真实水平截面逆或内部不等式。

**源码证据 `ContinuousFlexibility/Geometry/CapMeridian.lean`：** `ContinuousFlexibility.strictMonoOn_capHeightDrop`, `ContinuousFlexibility.capMeridianHeight_strict`, `ContinuousFlexibility.capMeridian_left_collar`, `ContinuousFlexibility.capMeridian_right_collar`

实际中部严格单调与水平端段。

**源码证据 `ContinuousFlexibility/Geometry/CapDisk.lean`：** `ContinuousFlexibility.capDisk_inside_cylinder_bottom`

实际帽柱内部分为底盘，不等于完整内部侧域。

**未完成内容：**
- 真实中部高度逆/水平截面函数和端部拼接。
- 所定义侧域的真实内外对应。

**逐条验收：**
- acceptance.01 [partial]：目前局部支持未覆盖全部验收；尚缺：真实中部高度逆/水平截面函数和端部拼接。；所定义侧域的真实内外对应。
- acceptance.02 [partial]：目前局部支持未覆盖全部验收；尚缺：真实中部高度逆/水平截面函数和端部拼接。；所定义侧域的真实内外对应。

<a id="g15-02"></a>
### G15.02 全相位显式开放内部集合

**输出：** 用侧帽截面、同一底高 cB 与实际顶部 Zτ 定义 Ωτ，证明在中央柱内恰为 cB<z<Zτ(y)，柱外为固定侧域。

**局部依赖：** G15.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 250–650 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 集合由实际坐标不等式给出。
- 顶图可能低于附着高度，定义仍须正确截断侧域。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 未定义真实全相位Ωτ或中央/柱外切片等式。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：集合由实际坐标不等式给出。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：顶图可能低于附着高度，定义仍须正确截断侧域。

<a id="g15-03"></a>
### G15.03 内部开放有界与可测

**输出：** 证明每个 Ωτ 非空、开放、有界且 Lebesgue 可测，给出同一统一包围盒。

**局部依赖：** G15.01, G15.02。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 非空来自统一严格图底间隙。
- 开放性包含侧帽与中央柱交接点。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 真实Ωτ未定义，无开放/有界/可测及统一包围盒。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：非空来自统一严格图底间隙。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：开放性包含侧帽与中央柱交接点。

<a id="g15-04"></a>
### G15.04 中央柱内边界逐点识别

**输出：** 利用严格图底间隙与连续高度，证明中央柱内 Ωτ 的边界恰为顶部图和底平盘，并给出其内部侧。

**局部依赖：** G15.02, G15.03。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 250–650 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 上下图同时处理。
- 不把柱侧边误认成额外闭曲面边界。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 未建立真实Ωτ的顶部/底盘边界逐点识别。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：上下图同时处理。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：不把柱侧边误认成额外闭曲面边界。

<a id="g15-05"></a>
### G15.05 侧帽及缝口边界识别

**输出：** 在柱外识别 Ωτ 边界为固定帽，逐一核对 rim、水平直段、marker 支撑边界和柱缝，证明边界没有额外分支。

**局部依赖：** G15.01, G15.02, G15.03, G15.04。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 250–650 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 实际共同领圈消去人为分块边界。
- marker 插入后的真实顶部也包含在识别中。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 未建立真实Ωτ的侧帽、marker、缝口完整边界识别。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：实际共同领圈消去人为分块边界。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：marker 插入后的真实顶部也包含在识别中。

<a id="g15-06"></a>
### G15.06 内部的路径连通性

**输出：** 在低于所有顶部的共同高度构造横向通道，再用垂直或侧截面路径把任意内部点连到该通道，证明 Ωτ 路径连通。

**局部依赖：** G15.01, G15.02, G15.03。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 220–550 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 路径始终满足实际区域不等式。
- 使用同一 cB<共同高度<全部顶部 的严格间隙。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 没有真实Ωτ内部路径连通和统一低通道构造。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：路径始终满足实际区域不等式。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：使用同一 cB<共同高度<全部顶部 的严格间隙。

<a id="g15-07"></a>
### G15.07 外部的路径连通与无界性

**输出：** 对 E3\closure Ωτ 的任意点构造通往固定远处的路径，分别处理上图上方、底盘下方和侧帽外侧。

**局部依赖：** G15.01, G15.02, G15.03, G15.05。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 250–650 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 路径避开全部闭像及 marker。
- 外部确实无界，不能仅由补集非空推出。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 没有真实Ωτ外部路径连通和无界性。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：路径避开全部闭像及 marker。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：外部确实无界，不能仅由补集非空推出。

<a id="g15-08"></a>
### G15.08 围成区域的唯一识别

**输出：** 将边界等于 range Fτ、内部连通和外部连通结合，证明 Ωτ 是闭像补集唯一有界连通分支，即该闭曲面的真实围成区域。

**局部依赖：** G15.03, G15.04, G15.05, G15.06, G15.07。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 220–550 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 先完成区域识别，再把体积称为 enclosed volume。
- 不将 Jordan 分离结论作为未经实例化黑箱。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 没有实际闭像补集唯一有界连通分支识别。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：先完成区域识别，再把体积称为 enclosed volume。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：不将 Jordan 分离结论作为未经实例化黑箱。

<a id="g15-09"></a>
### G15.09 顶部图的向外法向

**输出：** 由 Ωτ 在顶部的真实下图局部表达证明现有向上图单位法向就是向外法向，并给出所有相位的运输公式。

**局部依赖：** G15.04, G15.08。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 220–550 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 向外方向通过内部侧不等式判定。
- 不由随意参数法向的符号推断。

**本轮核对：** 实际图族上向单位法向、第三坐标正与旋转运输已证，尚未从实际Ωτ下图侧识别为outward。

**源码证据 `ContinuousFlexibility/Contracts/GraphFamilyCurvature.lean`：** `ContinuousFlexibility.IsometricGraphDevelopment.upwardGraphNormal_isUnitSurfaceNormal`, `ContinuousFlexibility.IsometricGraphDevelopment.upwardGraphNormal_height_pos`, `ContinuousFlexibility.IsometricGraphDevelopment.rotationNormal_isUnitSurfaceNormal`, `ContinuousFlexibility.IsometricGraphDevelopment.rotationNormal_height_pos`

真实upward法向，源声明明确没有闭曲面outward识别。

**未完成内容：**
- 真实Ωτ局部下图表达/内部侧，证明upward=outward。

**逐条验收：**
- acceptance.01 [partial]：目前局部支持未覆盖全部验收；尚缺：真实Ωτ局部下图表达/内部侧，证明upward=outward。
- acceptance.02 [partial]：目前局部支持未覆盖全部验收；尚缺：真实Ωτ局部下图表达/内部侧，证明upward=outward。

<a id="g15-10"></a>
### G15.10 帽与领圈的向外法向相容

**输出：** 从实际侧域/底盘内部侧识别帽的向外单位法向，在共同领圈证明与顶部所选向外法向相容，得到全闭面的光滑 outward normal。

**局部依赖：** G15.05, G15.08, G15.09。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 250–650 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 底盘方向与顶图方向分别识别。
- 含反射时运输区域给正确法向，不额外取负。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 没有由侧帽/底盘真实内部侧识别的全局outward normal与领圈相容。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：底盘方向与顶图方向分别识别。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：含反射时运输区域给正确法向，不额外取负。

<a id="g15-11"></a>
### G15.11 实际体积的 Fubini 分解

**输出：** 对 Ωτ 的实际指标函数应用 Fubini/Tonelli，把中央柱部分 Lebesgue 体积识别为 ∫(Zτ-cB)，把柱外部分识别为同一固定量。

**局部依赖：** G15.02, G15.03, G15.08。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 250–650 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 实际垂直切片和可测性逐项核对。
- 柱缝用不交可测分割或零测论证正确去重。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 没有对真实Ωτ指标函数的Fubini/Lebesgue体积分解。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：实际垂直切片和可测性逐项核对。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：柱缝用不交可测分割或零测论证正确去重。

<a id="g15-12"></a>
### G15.12 旋转换元与体积恒定

**输出：** 以真实 planar rotation 的测度保持及同一圆盘像保持证明 ∫(Zτ-cB)=∫(Z₀-cB)，结合固定柱外体积得到 volume Ωτ 恒定。

**局部依赖：** G15.11。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 220–550 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 基底测度是真实二维 Lebesgue 面积。
- 旋转 Jacobian/measure preserving 与高度公式均明确实例化。

**本轮核对：** 真实二维Lebesgue旋转measure preserving与任意闭盘积分换元已证，但没有真实Ωτ体积或相位高度的Fubini分解。

**源码证据 `ContinuousFlexibility/Contracts/GraphDiskIntegrals.lean`：** `ContinuousFlexibility.measurePreserving_planarRotation`, `ContinuousFlexibility.integral_comp_planarRotation_closedDisk`

真实基底换元完整，但不是体积不变量。

**源码证据 `ContinuousFlexibility/Contracts/GraphFamilyImage.lean`：** `ContinuousFlexibility.planarRotation_image_closedCartesianDisk`

真实圆盘保持。

**未完成内容：**
- 同一Zτ公式和真实Ωτ的Fubini识别。
- 固定柱外体积并组装实际volume恒等。

**逐条验收：**
- acceptance.01 [covered]：真实二维Lebesgue旋转measure preserving与任意闭盘积分换元已证，但没有真实Ωτ体积或相位高度的Fubini分解。
- acceptance.02 [partial]：目前局部支持未覆盖全部验收；尚缺：同一Zτ公式和真实Ωτ的Fubini识别。；固定柱外体积并组装实际volume恒等。

<a id="g15-13"></a>
### G15.13 真实围成区域和体积完整输出

**输出：** 输出同一全族 Ωτ 的开放有界性、精确闭像边界、内外连通识别、实际向外法向及 Lebesgue 体积恒定，供非全等及总曲率引用。

**局部依赖：** G15.01, G15.02, G15.03, G15.04, G15.05, G15.06, G15.07, G15.08, G15.09, G15.10, G15.11, G15.12。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 140–360 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 不能仅输出一个积分表达式。
- 结论涉及同一帽、同一 Fτ 与同一实际内部。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 没有真实围成区域、边界、内外连通、outward与体积的统一输出。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：不能仅输出一个积分表达式。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：结论涉及同一帽、同一 Fτ 与同一实际内部。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：构造有界开内部区域Ωτ，证明边界恰为闭像、内外连通关系足以识别其围成区域，并证明Lebesgue体积恒定。 | G15.13（组合全部子任务） |
| acceptance.01：不能直接把∫(Zτ−cB)定义成围成体积而跳过区域识别 | G15.01, G15.02, G15.04, G15.05, G15.06, G15.07, G15.08 |
| acceptance.02：底帽与上图分离用于所有τ | G15.02, G15.03 |
| acceptance.03：为G12/G16给真实向外法向 | G15.09, G15.10 |

<a id="g16"></a>
## G16 总向外有向平均曲率不变

**原节点完整目标：** 向外法向、H=(k₁+k₂)/2约定下，∫_{Fτ(S²)}H_out dA与τ无关。

**原上游里程碑：** G06, G08, G09, G15, D02

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [02-geometry.tex:258–260](../../paper/flexible-surface-rewrite/02-geometry.tex#L258)；[01-introduction.tex:33–39](../../paper/flexible-surface-rewrite/01-introduction.tex#L33)

<a id="g16-01"></a>
### G16.01 全族真实 outward 曲率运输

**输出：** 将 G15 识别的顶部 outward normal 与图盘环境旋转运输相容，证明真实有向 H 与面积密度在同一旋转/重参数下的变换式。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 200–500 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- H 使用 (k₁+k₂)/2 和 outward 方向。
- 不把固定参数法向直接视为 outward。

**可复用基础：** Contracts/GraphFamilyCurvature.lean 有进行中的图族曲率运输，需核对其法向前提。

**本轮核对：** 图族真实单位法向、signed H及参数面积密度的旋转变换已证；尚无真实Ωτ识别upward=outward。

**源码证据 `ContinuousFlexibility/Contracts/GraphFamilyCurvature.lean`：** `ContinuousFlexibility.IsometricGraphDevelopment.rotationNormal_isUnitSurfaceNormal`, `ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_meanCurvature`

同一真实旋转/重参数下signed H运输。

**源码证据 `ContinuousFlexibility/Contracts/GraphDiskIntegrals.lean`：** `ContinuousFlexibility.IsometricGraphDevelopment.areaDensity_rotationFamily`, `ContinuousFlexibility.IsometricGraphDevelopment.areaDensity_planarRotation`

真实参数密度相容。

**未完成内容：**
- 由G15实际区域识别当前图normal为outward，并给真实像面积桥接。

**逐条验收：**
- acceptance.01 [partial]：目前局部支持未覆盖全部验收；尚缺：由G15实际区域识别当前图normal为outward，并给真实像面积桥接。
- acceptance.02 [partial]：目前局部支持未覆盖全部验收；尚缺：由G15实际区域识别当前图normal为outward，并给真实像面积桥接。

<a id="g16-02"></a>
### G16.02 固定帽及平领圈的曲率项

**输出：** 证明同一固定帽上的实际 outward H 和面积测度与 τ 无关，且真实水平领圈 H=0，明确共同分割。

**局部依赖：** G16.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 180–450 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 固定帽向外选择由同一 Ωτ 识别。
- 领圈有面积但被积函数为零，不能把领圈称为零测。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 没有实际标记帽的outward H/像面积测度和共同分割，尚无该帽/平领圈的真实有向积分项证明。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：固定帽向外选择由同一 Ωτ 识别。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：领圈有面积但被积函数为零，不能把领圈称为零测。

<a id="g16-03"></a>
### G16.03 移动图盘的有向积分换元

**输出：** 对移动图盘用 D02 实际环境等距及重参数换元，证明 ∫H_out dA 与初始盘相同。

**局部依赖：** G16.01。另继承上列原上游里程碑。

**状态：** partial。**初始粒度：** 220–550 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 先验证积分可积性和像面积桥接。
- 保留 H 的符号，不替换为 |H|。

**本轮核对：** 真实移动图盘的signed upward H参数积分可积并相位不变已证，任务要求的outward与像面积桥接尚缺。

**源码证据 `ContinuousFlexibility/Contracts/GraphDiskIntegrals.lean`：** `ContinuousFlexibility.IsometricGraphDevelopment.upwardMeanIntegrand_integrableOn_closedDisk`, `ContinuousFlexibility.IsometricGraphDevelopment.graphDiskUpwardMeanIntegral`, `ContinuousFlexibility.IsometricGraphDevelopment.graphDiskUpwardMeanIntegral_eq_zeroPhase`

实际signed H，真实平面Lebesgue旋转换元；源明确保留image/outward桥接。

**未完成内容：**
- 参数积分等于真实移动盘像的曲面积分。
- 真实内部判定该normal是outward。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：先验证积分可积性和像面积桥接。
- acceptance.02 [covered]：真实移动图盘的signed upward H参数积分可积并相位不变已证，任务要求的outward与像面积桥接尚缺。

<a id="g16-04"></a>
### G16.04 闭曲面积分的真实分块

**输出：** 用 D02 共同可测分割将整个闭像 ∫H_out dA 拆为移动盘、固定帽及必要领圈项，证明无重复计数和缝口遗漏。

**局部依赖：** G16.02, G16.03。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–500 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 分割对应实际闭像的全部点。
- 交叠通过明确分割处理，不依赖直观拼接。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 没有完整闭像面积测度及图盘/固定帽可测不交分割，未证明全曲面积分分块。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：分割对应实际闭像的全部点。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：交叠通过明确分割处理，不依赖直观拼接。

<a id="g16-05"></a>
### G16.05 总向外有向平均曲率不变

**输出：** 组装同一真实闭像、同一 outward normal 的有限 ∫H_out dA，证明对所有实 τ 与初始值相等。

**局部依赖：** G16.01, G16.02, G16.03, G16.04。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 120–300 行。以一个明确的构造、恒等式或估计为验收单位；达到区间上界仍未闭合时继续拆分。

**验收条件：**

- 最终声明的曲率与 D01 的真实形算子一致。
- 全部积分对象和方向来自当前同一球面族。

**本轮核对：** 冻结快照中尚无该子任务要求的实际对象或项目定理。

**未完成内容：**
- 没有真实闭球面outward mean-curvature积分或全族不变性，图盘upward参数积分不能替代。

**逐条验收：**
- acceptance.01 [uncovered]：冻结快照未见此验收的实际项目声明：最终声明的曲率与 D01 的真实形算子一致。
- acceptance.02 [uncovered]：冻结快照未见此验收的实际项目声明：全部积分对象和方向来自当前同一球面族。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：向外法向、H=(k₁+k₂)/2约定下，∫_{Fτ(S²)}H_out dA与τ无关。 | G16.05（组合全部子任务） |
| acceptance.01：明确向外方向而非任选参数法向 | G16.01, G16.02 |
| acceptance.02：不是∫ / H /  | G16.01, G16.03, G16.05 |
| acceptance.03：交接领圈和图册重叠积分无遗漏 | G16.02, G16.04 |

<a id="main"></a>
## MAIN 闭球面光滑周期等距弯曲主定理

**原节点完整目标：** 实例化C00的全部结论：标准S²上的一个固定光滑正定度量、联合光滑一周期等距嵌入族、两个非全等闭像、固定内盘及补帽，以及三项几何积分不变量。

**原上游里程碑：** G01, G07, G08, G09, G13, G14, G15, G16

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [01-introduction.tex:18–39](../../paper/flexible-surface-rewrite/01-introduction.tex#L18)；[10-endpoint-and-sphere.tex:320–339](../../paper/flexible-surface-rewrite/10-endpoint-and-sphere.tex#L320)

<a id="main-01"></a>
### MAIN.01 实际非空输入实例化

**输出：** 从N12/G01的已证明存在见证选择一个非零q和实际Core，统一其全部后续数据。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 最终定理无Core非空或环带解存在前提。
- q与弯曲参数τ区分。

**本轮核对：** 完整无条件Core/标准S2/闭嵌入族及三项不变量尚未构造，不能组装本项主定理结论。

**未完成内容：**
- 从N12/G01的已证明存在见证选择一个非零q和实际Core，统一其全部后续数据。

**逐条验收：**
- acceptance.01 [uncovered]：完整无条件Core/标准S2/闭嵌入族及三项不变量尚未构造，不能组装本项主定理结论。
- acceptance.02 [uncovered]：完整无条件Core/标准S2/闭嵌入族及三项不变量尚未构造，不能组装本项主定理结论。

<a id="main-02"></a>
### MAIN.02 同一标准球面与初始度量

**输出：** 实例化G07的标准S2、补帽及F0，固定gΣ=F0*δ。

**局部依赖：** MAIN.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- gΣ为实际光滑正定拉回度量。
- 后续所有成员使用这一gΣ。

**本轮核对：** 完整无条件Core/标准S2/闭嵌入族及三项不变量尚未构造，不能组装本项主定理结论。

**未完成内容：**
- 实例化G07的标准S2、补帽及F0，固定gΣ=F0*δ。

**逐条验收：**
- acceptance.01 [uncovered]：完整无条件Core/标准S2/闭嵌入族及三项不变量尚未构造，不能组装本项主定理结论。
- acceptance.02 [uncovered]：完整无条件Core/标准S2/闭嵌入族及三项不变量尚未构造，不能组装本项主定理结论。

<a id="main-03"></a>
### MAIN.03 共同周期嵌入族组合

**输出：** 以同一发展、帽和相位族组合联合光滑、所有实τ的嵌入、度量等式及一周期。

**局部依赖：** MAIN.01, MAIN.02。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 不是逐参数光滑代替联合光滑。
- 不是环境距离等距代替切向量度量。

**本轮核对：** 完整无条件Core/标准S2/闭嵌入族及三项不变量尚未构造，不能组装本项主定理结论。

**未完成内容：**
- 以同一发展、帽和相位族组合联合光滑、所有实τ的嵌入、度量等式及一周期。

**逐条验收：**
- acceptance.01 [uncovered]：完整无条件Core/标准S2/闭嵌入族及三项不变量尚未构造，不能组装本项主定理结论。
- acceptance.02 [uncovered]：完整无条件Core/标准S2/闭嵌入族及三项不变量尚未构造，不能组装本项主定理结论。

<a id="main-04"></a>
### MAIN.04 固定区域与非全等像组合

**输出：** 组合非退化固定内盘及补帽、两个闭像对全部环境仿射等距非全等。

**局部依赖：** MAIN.02, MAIN.03。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 固定区域有要求的拓扑和非空内部。
- 反射包括在全等量词内。

**本轮核对：** 完整无条件Core/标准S2/闭嵌入族及三项不变量尚未构造，不能组装本项主定理结论。

**未完成内容：**
- 组合非退化固定内盘及补帽、两个闭像对全部环境仿射等距非全等。

**逐条验收：**
- acceptance.01 [uncovered]：完整无条件Core/标准S2/闭嵌入族及三项不变量尚未构造，不能组装本项主定理结论。
- acceptance.02 [uncovered]：完整无条件Core/标准S2/闭嵌入族及三项不变量尚未构造，不能组装本项主定理结论。

<a id="main-05"></a>
### MAIN.05 三项真实几何不变量组合

**输出：** 对同一F调用G14/G15/G16，统一面积、实际围成区域体积及向外有向H积分。

**局部依赖：** MAIN.02, MAIN.03。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 不在三个结论中另选不同见证。
- 法向和H=(k1+k2)/2约定一致。

**本轮核对：** 完整无条件Core/标准S2/闭嵌入族及三项不变量尚未构造，不能组装本项主定理结论。

**未完成内容：**
- 对同一F调用G14/G15/G16，统一面积、实际围成区域体积及向外有向H积分。

**逐条验收：**
- acceptance.01 [uncovered]：完整无条件Core/标准S2/闭嵌入族及三项不变量尚未构造，不能组装本项主定理结论。
- acceptance.02 [uncovered]：完整无条件Core/标准S2/闭嵌入族及三项不变量尚未构造，不能组装本项主定理结论。

<a id="main-06"></a>
### MAIN.06 全部分析假设消除

**输出：** 检查径向参考、闭域逆、smooth tame及Hamilton存在结论均由实际证明实例化。

**局部依赖：** MAIN.01, MAIN.02, MAIN.03, MAIN.04, MAIN.05。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 最终存在定理无RadialReference或逆存在假设。
- 结构非空由构造给出而不是从空类型推出条件结论。

**本轮核对：** 完整无条件Core/标准S2/闭嵌入族及三项不变量尚未构造，不能组装本项主定理结论。

**未完成内容：**
- 检查径向参考、闭域逆、smooth tame及Hamilton存在结论均由实际证明实例化。

**逐条验收：**
- acceptance.01 [uncovered]：完整无条件Core/标准S2/闭嵌入族及三项不变量尚未构造，不能组装本项主定理结论。
- acceptance.02 [uncovered]：完整无条件Core/标准S2/闭嵌入族及三项不变量尚未构造，不能组装本项主定理结论。

<a id="main-07"></a>
### MAIN.07 主定理类型与内核审计

**输出：** 将论文thm:main逐条对应最终Lean存在定理的类型，运行所属模块及统一owner-based审计。

**局部依赖：** MAIN.01, MAIN.02, MAIN.03, MAIN.04, MAIN.05, MAIN.06。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 所有私有helper也在审计范围。
- 构建会话有明确终端exit status。

**本轮核对：** 完整无条件Core/标准S2/闭嵌入族及三项不变量尚未构造，不能组装本项主定理结论。

**未完成内容：**
- 将论文thm:main逐条对应最终Lean存在定理的类型，运行所属模块及统一owner-based审计。

**逐条验收：**
- acceptance.01 [uncovered]：完整无条件Core/标准S2/闭嵌入族及三项不变量尚未构造，不能组装本项主定理结论。
- acceptance.02 [uncovered]：完整无条件Core/标准S2/闭嵌入族及三项不变量尚未构造，不能组装本项主定理结论。

<a id="main-08"></a>
### MAIN.08 完整主定理交付

**输出：** 组合全部见证与结论，以最终Lean声明和实际构建输出交付无条件主定理。

**局部依赖：** MAIN.01, MAIN.02, MAIN.03, MAIN.04, MAIN.05, MAIN.06, MAIN.07。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 150–450 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 不得用蓝图结构通过代替内核证明。
- 完成声明仅在integration核对全部原始结论后给出。

**本轮核对：** 完整无条件Core/标准S2/闭嵌入族及三项不变量尚未构造，不能组装本项主定理结论。

**未完成内容：**
- 组合全部见证与结论，以最终Lean声明和实际构建输出交付无条件主定理。

**逐条验收：**
- acceptance.01 [uncovered]：完整无条件Core/标准S2/闭嵌入族及三项不变量尚未构造，不能组装本项主定理结论。
- acceptance.02 [uncovered]：完整无条件Core/标准S2/闭嵌入族及三项不变量尚未构造，不能组装本项主定理结论。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：实例化C00的全部结论：标准S²上的一个固定光滑正定度量、联合光滑一周期等距嵌入族、两个非全等闭像、固定内盘及补帽，以及三项几何积分不变量。 | MAIN.08（组合全部子任务） |
| acceptance.01：最终Lean声明类型逐条覆盖原thm:main | MAIN.02, MAIN.03, MAIN.04, MAIN.05, MAIN.07 |
| acceptance.02：全部主链节点有实际证明且主定理通过内核和公理审计 | MAIN.06, MAIN.07 |
| acceptance.03：不得以条件性闭合定理或蓝图验收器代替完成 | MAIN.01, MAIN.06, MAIN.07 |

<a id="x01"></a>
## X01 所有端点指数的同一几何加强

**原节点完整目标：** 将同一径向几何的逆估计加强到全部紧区间[γ₋,γ₊]⊂(0,1)，几何本身不随区间变化。

**原上游里程碑：** R05, R10, R11, R12

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [04-designing-the-profile.tex:99–106](../../paper/flexible-surface-rewrite/04-designing-the-profile.tex#L99)；[06-global-reference-inverse.tex:707–764](../../paper/flexible-surface-rewrite/06-global-reference-inverse.tex#L707)

<a id="x01-01"></a>
### X01.01 指数区间与固定几何量词

**输出：** 固定已经选定的一套几何，再引入任意紧指数区间[γ-,γ+]⊂(0,1)，列出可依赖区间的常数。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 几何选择在指数区间量词之前。
- 不得逐γ重选轮廓或边框。

**本轮核对：** 尚无实际全局固定径向参考及其指数区间统一Green逆，不能开展此加强。

**未完成内容：**
- 固定已经选定的一套几何，再引入任意紧指数区间[γ-,γ+]⊂(0,1)，列出可依赖区间的常数。

**逐条验收：**
- acceptance.01 [uncovered]：尚无实际全局固定径向参考及其指数区间统一Green逆，不能开展此加强。
- acceptance.02 [uncovered]：尚无实际全局固定径向参考及其指数区间统一Green逆，不能开展此加强。

<a id="x01-02"></a>
### X01.02 紧区间单元估计一致性

**输出：** 将R05单元估计的指数依赖压缩为紧区间上统一常数。

**局部依赖：** X01.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 尾部索引阈值的允许依赖明确。
- 保持原有同一自然端线。

**本轮核对：** 尚无实际全局固定径向参考及其指数区间统一Green逆，不能开展此加强。

**未完成内容：**
- 将R05单元估计的指数依赖压缩为紧区间上统一常数。

**逐条验收：**
- acceptance.01 [uncovered]：尚无实际全局固定径向参考及其指数区间统一Green逆，不能开展此加强。
- acceptance.02 [uncovered]：尚无实际全局固定径向参考及其指数区间统一Green逆，不能开展此加强。

<a id="x01-03"></a>
### X01.03 紧区间Green核与匹配界

**输出：** 在不改变几何的前提下推广Green核、匹配块和界面矩阵的指数一致估计。

**局部依赖：** X01.01, X01.02。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 同一个全局Green逆。
- 源配对测度不随指数变更而隐去。

**本轮核对：** 尚无实际全局固定径向参考及其指数区间统一Green逆，不能开展此加强。

**未完成内容：**
- 在不改变几何的前提下推广Green核、匹配块和界面矩阵的指数一致估计。

**逐条验收：**
- acceptance.01 [uncovered]：尚无实际全局固定径向参考及其指数区间统一Green逆，不能开展此加强。
- acceptance.02 [uncovered]：尚无实际全局固定径向参考及其指数区间统一Green逆，不能开展此加强。

<a id="x01-04"></a>
### X01.04 全指数尾部求和

**输出：** 证明紧区间上尾部级数的统一收敛、权交换及双侧逆估计。

**局部依赖：** X01.02, X01.03。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 不得交换未经控制的无限求和与supγ。
- 图域与自然端点解释保持一致。

**本轮核对：** 尚无实际全局固定径向参考及其指数区间统一Green逆，不能开展此加强。

**未完成内容：**
- 证明紧区间上尾部级数的统一收敛、权交换及双侧逆估计。

**逐条验收：**
- acceptance.01 [uncovered]：尚无实际全局固定径向参考及其指数区间统一Green逆，不能开展此加强。
- acceptance.02 [uncovered]：尚无实际全局固定径向参考及其指数区间统一Green逆，不能开展此加强。

<a id="x01-05"></a>
### X01.05 全指数加强组合

**输出：** 组合得到原X01的全部紧区间加强，维持几何与指数区间选择的量词顺序。

**局部依赖：** X01.01, X01.02, X01.03, X01.04。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 150–450 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 不新增MAIN前置依赖。
- 主定理所用固定β三指数是此加强的特例而非循环前提。

**本轮核对：** 尚无实际全局固定径向参考及其指数区间统一Green逆，不能开展此加强。

**未完成内容：**
- 组合得到原X01的全部紧区间加强，维持几何与指数区间选择的量词顺序。

**逐条验收：**
- acceptance.01 [uncovered]：尚无实际全局固定径向参考及其指数区间统一Green逆，不能开展此加强。
- acceptance.02 [uncovered]：尚无实际全局固定径向参考及其指数区间统一Green逆，不能开展此加强。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：将同一径向几何的逆估计加强到全部紧区间[γ₋,γ₊]⊂(0,1)，几何本身不随区间变化。 | X01.05（组合全部子任务） |
| acceptance.01：这是原参考命题的加强范围；主定理仅需固定β及邻近指数 | X01.01, X01.05 |
| acceptance.02：不能逐γ另造几何 | X01.01, X01.02, X01.03, X01.04 |

<a id="x02"></a>
## X02 双倍端点权和二次控制加强

**原节点完整目标：** 二次余项进入2β权；mean primitive不损失指数，恢复ν_q,κ_q=O(q²)、强拓扑光滑性及H^(1−ε)端点估计。

**原上游里程碑：** N11, S04, W02, W03, N01

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [10-endpoint-and-sphere.tex:19–299](../../paper/flexible-surface-rewrite/10-endpoint-and-sphere.tex#L19)

<a id="x02-01"></a>
### X02.01 两弱因子的双权乘积

**输出：** 在实际加权levels证明两个β弱因子的乘积落入2β权，并记录导数损失。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 估计对同一q区间成立。
- 角向和径向混合导数一并控制。

**本轮核对：** 实际弱权非线性解和具体加权levels尚未构造，本项双权/二阶恢复加强没有实现。

**未完成内容：**
- 在实际加权levels证明两个β弱因子的乘积落入2β权，并记录导数损失。

**逐条验收：**
- acceptance.01 [uncovered]：实际弱权非线性解和具体加权levels尚未构造，本项双权/二阶恢复加强没有实现。
- acceptance.02 [uncovered]：实际弱权非线性解和具体加权levels尚未构造，本项双权/二阶恢复加强没有实现。

<a id="x02-02"></a>
### X02.02 二次余项的双权识别

**输出：** 将真实非线性二次余项逐项分解，验证其2β权源估计。

**局部依赖：** X02.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 实际残差而非任意命名的二次项。
- 保留源兼容与奇偶条件。

**本轮核对：** 实际弱权非线性解和具体加权levels尚未构造，本项双权/二阶恢复加强没有实现。

**未完成内容：**
- 将真实非线性二次余项逐项分解，验证其2β权源估计。

**逐条验收：**
- acceptance.01 [uncovered]：实际弱权非线性解和具体加权levels尚未构造，本项双权/二阶恢复加强没有实现。
- acceptance.02 [uncovered]：实际弱权非线性解和具体加权levels尚未构造，本项双权/二阶恢复加强没有实现。

<a id="x02-03"></a>
### X02.03 平均primitive无指数损失

**输出：** 求解实际平均方程并证明primitive保持所需指数及端点常数自由。

**局部依赖：** X02.02。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 右端归零而左端常数可不同。
- 积分使用实际dr源测度。

**本轮核对：** 实际弱权非线性解和具体加权levels尚未构造，本项双权/二阶恢复加强没有实现。

**未完成内容：**
- 求解实际平均方程并证明primitive保持所需指数及端点常数自由。

**逐条验收：**
- acceptance.01 [uncovered]：实际弱权非线性解和具体加权levels尚未构造，本项双权/二阶恢复加强没有实现。
- acceptance.02 [uncovered]：实际弱权非线性解和具体加权levels尚未构造，本项双权/二阶恢复加强没有实现。

<a id="x02-04"></a>
### X02.04 高度和圆控制二阶恢复

**输出：** 从同一弱解恢复νq、κq并证明O(q²)的指定加权范数界。

**局部依赖：** X02.02, X02.03。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 控制来自原方程。
- 无需重新进行非线性迭代或缩小每阶参数区间。

**本轮核对：** 实际弱权非线性解和具体加权levels尚未构造，本项双权/二阶恢复加强没有实现。

**未完成内容：**
- 从同一弱解恢复νq、κq并证明O(q²)的指定加权范数界。

**逐条验收：**
- acceptance.01 [uncovered]：实际弱权非线性解和具体加权levels尚未构造，本项双权/二阶恢复加强没有实现。
- acceptance.02 [uncovered]：实际弱权非线性解和具体加权levels尚未构造，本项双权/二阶恢复加强没有实现。

<a id="x02-05"></a>
### X02.05 强拓扑参数光滑性

**输出：** 把二次恢复和双权估计提升为强拓扑中的实际参数方向导数及全阶连续性。

**局部依赖：** X02.01, X02.02, X02.03, X02.04。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 不能用各q分别有界代替参数光滑。
- 全部阶数保留同一q0。

**本轮核对：** 实际弱权非线性解和具体加权levels尚未构造，本项双权/二阶恢复加强没有实现。

**未完成内容：**
- 把二次恢复和双权估计提升为强拓扑中的实际参数方向导数及全阶连续性。

**逐条验收：**
- acceptance.01 [uncovered]：实际弱权非线性解和具体加权levels尚未构造，本项双权/二阶恢复加强没有实现。
- acceptance.02 [uncovered]：实际弱权非线性解和具体加权levels尚未构造，本项双权/二阶恢复加强没有实现。

<a id="x02-06"></a>
### X02.06 H的一减ε端点估计

**输出：** 在论文指定范围ε内证明H^(1-ε)端点估计并识别原高度/控制。

**局部依赖：** X02.02, X02.03, X02.04。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 范数和端点区域明确。
- 不替代N12必需的弱权全阶延拓。

**本轮核对：** 实际弱权非线性解和具体加权levels尚未构造，本项双权/二阶恢复加强没有实现。

**未完成内容：**
- 在论文指定范围ε内证明H^(1-ε)端点估计并识别原高度/控制。

**逐条验收：**
- acceptance.01 [uncovered]：实际弱权非线性解和具体加权levels尚未构造，本项双权/二阶恢复加强没有实现。
- acceptance.02 [uncovered]：实际弱权非线性解和具体加权levels尚未构造，本项双权/二阶恢复加强没有实现。

<a id="x02-07"></a>
### X02.07 双权加强组合

**输出：** 组合双权余项、平均primitive、二阶控制、强光滑性及端点估计。

**局部依赖：** X02.01, X02.02, X02.03, X02.04, X02.05, X02.06。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 150–450 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 首次MAIN闭合不依赖X02。
- N12弱空间延拓义务继续单独验收。

**本轮核对：** 实际弱权非线性解和具体加权levels尚未构造，本项双权/二阶恢复加强没有实现。

**未完成内容：**
- 组合双权余项、平均primitive、二阶控制、强光滑性及端点估计。

**逐条验收：**
- acceptance.01 [uncovered]：实际弱权非线性解和具体加权levels尚未构造，本项双权/二阶恢复加强没有实现。
- acceptance.02 [uncovered]：实际弱权非线性解和具体加权levels尚未构造，本项双权/二阶恢复加强没有实现。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：二次余项进入2β权；mean primitive不损失指数，恢复ν_q,κ_q=O(q²)、强拓扑光滑性及H^(1−ε)端点估计。 | X02.07（组合全部子任务） |
| acceptance.01：不阻挡首次MAIN闭合 | X02.06, X02.07 |
| acceptance.02：仍保留N12必需的弱空间延拓证明 | X02.03, X02.06, X02.07 |

<a id="x03"></a>
## X03 有限角向截断的障碍

**原节点完整目标：** 形式化附录prop:obs-finite-square的完整原陈述及其有限Fourier最高频、复平方根ODE和延拓论证。

**原上游里程碑：** S03

**现有证明：** 原节点证据见 [原权威清单](../manifest.json)，本轮逐项核对证据见下列任务及 [验收汇总](AUDIT.md)。

**论文定位：** [appendix-shortcuts.tex:11–109](../../paper/flexible-surface-rewrite/appendix-shortcuts.tex#L11)

<a id="x03-01"></a>
### X03.01 有限Fourier最高模抽取

**输出：** 在实际有限角向展开中抽取真实标量方程最高频系数。

**局部依赖：** 无。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 处理实值条件及最高非零模。
- 系数计算与S03实际微分相连。

**本轮核对：** 快照未实现附录有限Fourier最高模、复平方根ODE及零点延拓路线的这一具体步骤。

**未完成内容：**
- 在实际有限角向展开中抽取真实标量方程最高频系数。

**逐条验收：**
- acceptance.01 [uncovered]：快照未实现附录有限Fourier最高模、复平方根ODE及零点延拓路线的这一具体步骤。
- acceptance.02 [uncovered]：快照未实现附录有限Fourier最高模、复平方根ODE及零点延拓路线的这一具体步骤。

<a id="x03-02"></a>
### X03.02 非零区间的复平方根分支

**输出：** 对最高模相关复函数，在适当非零区间构造可微平方根分支。

**局部依赖：** X03.01。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 分支存在由局部非零与区间性质证明。
- 不假设跨零点全局平方根。

**本轮核对：** 快照未实现附录有限Fourier最高模、复平方根ODE及零点延拓路线的这一具体步骤。

**未完成内容：**
- 对最高模相关复函数，在适当非零区间构造可微平方根分支。

**逐条验收：**
- acceptance.01 [uncovered]：快照未实现附录有限Fourier最高模、复平方根ODE及零点延拓路线的这一具体步骤。
- acceptance.02 [uncovered]：快照未实现附录有限Fourier最高模、复平方根ODE及零点延拓路线的这一具体步骤。

<a id="x03-03"></a>
### X03.03 分支对应的一阶ODE

**输出：** 由最高模方程推导平方根的真实一阶ODE及系数可积性。

**局部依赖：** X03.01, X03.02。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 明确复导数解释为实参数导数。
- 所有除法在非零区间内部合法。

**本轮核对：** 快照未实现附录有限Fourier最高模、复平方根ODE及零点延拓路线的这一具体步骤。

**未完成内容：**
- 由最高模方程推导平方根的真实一阶ODE及系数可积性。

**逐条验收：**
- acceptance.01 [uncovered]：快照未实现附录有限Fourier最高模、复平方根ODE及零点延拓路线的这一具体步骤。
- acceptance.02 [uncovered]：快照未实现附录有限Fourier最高模、复平方根ODE及零点延拓路线的这一具体步骤。

<a id="x03-04"></a>
### X03.04 Gronwall与零点传播

**输出：** 用已满足系数条件的ODE/Gronwall证明局部分支的唯一性和到边界的控制。

**局部依赖：** X03.03。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 不是仅形式写出ODE后宣称唯一。
- 量化有限区间与端点极限。

**本轮核对：** 快照未实现附录有限Fourier最高模、复平方根ODE及零点延拓路线的这一具体步骤。

**未完成内容：**
- 用已满足系数条件的ODE/Gronwall证明局部分支的唯一性和到边界的控制。

**逐条验收：**
- acceptance.01 [uncovered]：快照未实现附录有限Fourier最高模、复平方根ODE及零点延拓路线的这一具体步骤。
- acceptance.02 [uncovered]：快照未实现附录有限Fourier最高模、复平方根ODE及零点延拓路线的这一具体步骤。

<a id="x03-05"></a>
### X03.05 孤立零点的两侧拼接

**输出：** 证明最高模在孤立零点两侧的分支约束可传递，恢复原函数一致性。

**局部依赖：** X03.02, X03.03, X03.04。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 不要求两侧平方根选取同一符号。
- 实际拼接对象为原最高模函数。

**本轮核对：** 快照未实现附录有限Fourier最高模、复平方根ODE及零点延拓路线的这一具体步骤。

**未完成内容：**
- 证明最高模在孤立零点两侧的分支约束可传递，恢复原函数一致性。

**逐条验收：**
- acceptance.01 [uncovered]：快照未实现附录有限Fourier最高模、复平方根ODE及零点延拓路线的这一具体步骤。
- acceptance.02 [uncovered]：快照未实现附录有限Fourier最高模、复平方根ODE及零点延拓路线的这一具体步骤。

<a id="x03-06"></a>
### X03.06 零点累积的延拓

**输出：** 处理零点非孤立及累积情形，利用连续性/ODE控制完成最高模消失结论。

**局部依赖：** X03.04, X03.05。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 显式覆盖零点累积情况。
- 不能以有限分片假设跳过该情形。

**本轮核对：** 快照未实现附录有限Fourier最高模、复平方根ODE及零点延拓路线的这一具体步骤。

**未完成内容：**
- 处理零点非孤立及累积情形，利用连续性/ODE控制完成最高模消失结论。

**逐条验收：**
- acceptance.01 [uncovered]：快照未实现附录有限Fourier最高模、复平方根ODE及零点延拓路线的这一具体步骤。
- acceptance.02 [uncovered]：快照未实现附录有限Fourier最高模、复平方根ODE及零点延拓路线的这一具体步骤。

<a id="x03-07"></a>
### X03.07 有限最高频降阶归纳

**输出：** 迭代最高模消失结果，完成有限Fourier次数的严格降阶。

**局部依赖：** X03.01, X03.06。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 200–600 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 次数归纳有终止基例。
- 结论保持附录命题的全部原假设。

**本轮核对：** 快照未实现附录有限Fourier最高模、复平方根ODE及零点延拓路线的这一具体步骤。

**未完成内容：**
- 迭代最高模消失结果，完成有限Fourier次数的严格降阶。

**逐条验收：**
- acceptance.01 [uncovered]：快照未实现附录有限Fourier最高模、复平方根ODE及零点延拓路线的这一具体步骤。
- acceptance.02 [uncovered]：快照未实现附录有限Fourier最高模、复平方根ODE及零点延拓路线的这一具体步骤。

<a id="x03-08"></a>
### X03.08 有限截断障碍组合

**输出：** 组合最高频、局部平方根、零点延拓及有限降阶，得到prop:obs-finite-square完整陈述。

**局部依赖：** X03.01, X03.02, X03.03, X03.04, X03.05, X03.06, X03.07。另继承上列原上游里程碑。

**状态：** planned。**初始粒度：** 150–450 行。先按单一输出组织；实际证明超过800行或含独立困难时再次拆分。

**验收条件：**

- 旁支不引入MAIN依赖。
- 复平方根及累积零点分别有实际证明。

**本轮核对：** 快照未实现附录有限Fourier最高模、复平方根ODE及零点延拓路线的这一具体步骤。

**未完成内容：**
- 组合最高频、局部平方根、零点延拓及有限降阶，得到prop:obs-finite-square完整陈述。

**逐条验收：**
- acceptance.01 [uncovered]：快照未实现附录有限Fourier最高模、复平方根ODE及零点延拓路线的这一具体步骤。
- acceptance.02 [uncovered]：快照未实现附录有限Fourier最高模、复平方根ODE及零点延拓路线的这一具体步骤。

**原义务覆盖表：**

| 原义务 | 承担子任务 |
| --- | --- |
| statement：形式化附录prop:obs-finite-square的完整原陈述及其有限Fourier最高频、复平方根ODE和延拓论证。 | X03.08（组合全部子任务） |
| acceptance.01：独立于主存在性链 | X03.01, X03.07, X03.08 |
| acceptance.02：复平方根和零点累积延拓不能只靠代数检查 | X03.02, X03.04, X03.05, X03.06 |
