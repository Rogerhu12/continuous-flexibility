# 主定理形式化节点清单

由 `manifest.json` 生成。修改清单后运行 `python scripts/check_blueprint.py --write`。

状态只对本节点的精确陈述有效。计划中的陈述和证明提纲尚未通过 Lean；依赖图通过检查不等于数学证明成立。

共 58 个节点，主链 55 个，旁支 3 个；3 个已完成局部节点，35 个部分实现节点，共同记录现有 3240 条公开显式定理。


证明源码范围固定于 `coordination/checkpoint-2026-11-11-radial-contract-wave.json`，逐文件核对当前哈希；另有 25 个已登记负责人的源码文件未计入本检查点（含并行草稿及后续交付）。

## 拓扑顺序索引

| 节点 | 状态 | 直接依赖 |
| --- | --- | --- |
| [C00 主定理语义与四个接口](#c00) | 已有部分已编译子结果 | — |
| [S01 余度量正定与余标架](#s01) | 已形式化的局部节点 | — |
| [S02 线性系数行列式与残差修正](#s02) | 已形式化的局部节点 | — |
| [R01 真实导数下的对数幂 gauge](#r01) | 已形式化的局部节点 | — |
| [H01 分次空间、方向微分与tame基础](#h01) | 已有部分已编译子结果 | — |
| [D01 曲面二阶几何与刚体运动自然性](#d01) | 已有部分已编译子结果 | C00 |
| [G10 径向盘的边界等距刚性](#g10) | 已有部分已编译子结果 | C00 |
| [S03 高度微分、Cartan连接与真实变分](#s03) | 已有部分已编译子结果 | C00, S01, S02 |
| [R02 Liouville变换与径向实现](#r02) | 已有部分已编译子结果 | R01 |
| [H02 逆族smooth tame定理](#h02) | 待形式化 | H01 |
| [H03 带二次误差的Nash–Moser隐函数定理](#h03) | 已有部分已编译子结果 | H01 |
| [D02 曲面面积和有向积分接口](#d02) | 已有部分已编译子结果 | D01 |
| [S04 归一化残差的可去延拓和守恒](#s04) | 已有部分已编译子结果 | S03 |
| [G02 填盘后的归一化平面发展](#g02) | 已有部分已编译子结果 | C00, S03 |
| [X03 有限角向截断的障碍](#x03) | 待形式化；加强旁支 | S03 |
| [R03 中央谐振子模型的完整实现](#r03) | 已有部分已编译子结果 | R02 |
| [R04 Morse模型的两类非共振](#r04) | 已有部分已编译子结果 | R02 |
| [S05 固定类型的真实修正算子](#s05) | 已有部分已编译子结果 | S02, S03, S04 |
| [G03 发展唯一性和内盘中心定位](#g03) | 已有部分已编译子结果 | G02 |
| [G04 局部发展成为全局微分同胚](#g04) | 已有部分已编译子结果 | G02 |
| [R05 真实单元、连接与累积平坦轮廓](#r05) | 已有部分已编译子结果 | R04, R01 |
| [R09 正buffer压缩与Poisson边界矩阵](#r09) | 待形式化 | R03, R04 |
| [G05 等距图盘](#g05) | 已有部分已编译子结果 | G03, G04 |
| [R06 深尾连续算子逆与唯一衰减线](#r06) | 已有部分已编译子结果 | R01, R05 |
| [W01 材料坐标与连续权函数](#w01) | 已有部分已编译子结果 | R05 |
| [G06 隔离的固定标记补帽](#g06) | 已有部分已编译子结果 | G05, D01 |
| [R07 过渡区与所有频率同时选高](#r07) | 待形式化 | R04, R05, R06 |
| [W02 加权高度、源与圆序列空间](#w02) | 已有部分已编译子结果 | W01, H01 |
| [G07 标准球面参数化和固定度量](#g07) | 已有部分已编译子结果 | G05, G06, D01 |
| [R08 保留二模的中央目标连接](#r08) | 待形式化 | R03, R07 |
| [W03 正指数弱空间的全阶平坦延拓](#w03) | 已有部分已编译子结果 | W01, W02 |
| [G08 相位族联合光滑、周期与固定区域](#g08) | 已有部分已编译子结果 | G03, G07 |
| [R10 全局匹配Green逆](#r10) | 待形式化 | R06, R07, R08, R09 |
| [G09 每一相位均为同度量嵌入](#g09) | 已有部分已编译子结果 | G05, G06, G08 |
| [G11 移动盘像不恒定](#g11) | 已有部分已编译子结果 | G04, G05, G08, G10 |
| [R11 同一几何上的双权全局估计](#r11) | 待形式化 | R05, R10 |
| [G14 面积不变](#g14) | 已有部分已编译子结果 | G09, D02 |
| [G15 显式围成区域及体积不变](#g15) | 已有部分已编译子结果 | G06, G08, G09 |
| [R12 固定径向参考与闭图域双侧逆](#r12) | 待形式化 | R06, R08, R10, R11 |
| [G12 全等变换的有限候选集](#g12) | 已有部分已编译子结果 | G06, G09, G15, D01 |
| [G16 总向外有向平均曲率不变](#g16) | 已有部分已编译子结果 | G06, G08, G09, G15, D02 |
| [N01 共同低阶几何邻域](#n01) | 已有部分已编译子结果 | R12, W01, W02, S05 |
| [X01 所有端点指数的同一几何加强](#x01) | 待形式化；加强旁支 | R05, R10, R11, R12 |
| [G13 闭球面像确实非全等](#g13) | 已有部分已编译子结果 | G08, G11, G12 |
| [N02 圆返回残差与小除数逆](#n02) | 待形式化 | R12, N01, W02 |
| [N03 固定特征返回的残差修正](#n03) | 待形式化 | N01, N02, W02, S05 |
| [N04 根坐标、正区间拼接与固定transmission](#n04) | 待形式化 | N01, N03, W01, W02 |
| [N05 增广参考逆和共同闭图域](#n05) | 待形式化 | R12, N04, W02 |
| [N06 同一Banach空间的相对小扰动](#n06) | 待形式化 | N01, N04, N05, W01 |
| [N07 扰动标量逆及高阶恢复](#n07) | 待形式化 | N05, N06, H02, W02 |
| [N08 联合残差、真实控制列与smoothing](#n08) | 待形式化 | S04, N01, N02, N07, W02 |
| [N09 耦合高度与圆方程的逆](#n09) | 待形式化 | N02, N07, N08, H02 |
| [N10 两个独立残差的精确二次误差](#n10) | 待形式化 | N03, N08, N09, S05, W02 |
| [N11 弱权非线性解支](#n11) | 待形式化 | H03, N08, N09, N10 |
| [N12 最小平坦环带核心](#n12) | 已有部分已编译子结果 | N11, W03, N01, R12, S03 |
| [X02 双倍端点权和二次控制加强](#x02) | 待形式化；加强旁支 | N11, S04, W02, W03, N01 |
| [G01 平坦端点扩大为真实开领圈](#g01) | 已有部分已编译子结果 | N12, W03, S03 |
| [MAIN 闭球面光滑周期等距弯曲主定理](#main) | 已有部分已编译子结果 | G01, G07, G08, G09, G13, G14, G15, G16 |

<a id="c00"></a>
## C00 主定理语义与四个接口

**状态：** 已有部分已编译子结果。**分支：** 目标与接口。主定理必要节点。

**数学陈述：** 固定标准单位球面 S²⊂E³。目标是光滑正定黎曼度量 gΣ、联合光滑 F:S²×ℝ→E³、非退化固定内盘及补帽，使每个 Fτ 为嵌入、Fτ*δ=gΣ、Fτ+1=Fτ；存在两个像不被任何欧氏仿射等距变换联系，且面积、围成体积、总向外有向平均曲率不变。

**证明提纲：** 先冻结 FlatAnnularCore、AnnularSolution、RadialReference、ClosedBending 的实际数学字段；优先取 gΣ=F₀*δ。此节点是规格，尚非已编译的 Lean 声明。

**直接依赖：** 无其他蓝图节点

**论文定位：** [01-introduction.tex:18–39](../paper/flexible-surface-rewrite/01-introduction.tex#L18)，`thm:main`

**目标文件：** `ContinuousFlexibility/Contracts/Main.lean`（节点组织目标；实际已存在的证明文件见下方，整个节点尚未完成）

**验收条件：**

- 不得用环境距离 Isometry 替代拉回度量等式
- 非全等比较 range 像集并量化全部 AffineIsometryEquiv
- 三项积分按标准几何/测度定义，不得以常值函数定义替代
- 本Lean版本的光滑阶为ContDiff ℝ ∞；⊤/ω表示解析，不得用于非平凡平坦bump的目标

**已经完成的子结果：**

- 已编译实际FlatAnnularCore及其同一w/z的AnnularSolution接口；两端常数独立，Core中没有P或Cartesian flatness输入
- 已证明IsometricGraphDevelopment输出非空，并固定一个共同实际发展供后续几何使用
- 稳定证据包含真实标准单位S²、现有流形结构、南北立体投影逆图及实际光滑图册接口；不由此推出完整MAIN存在性。
- 58 个闭合 Lean 目标类型已通过独立陈述构建和 owner 公理审计；MAIN 是真正 Nonempty ClosedBending，规格构建不是存在性证明。

**仍待闭合的义务：**

- 最终无条件见证和全工作区构建、公理审计与逐节点验收仍未完成。

**现有 Lean 证明：**

[Annular.lean](../ContinuousFlexibility/Contracts/Annular.lean)：

- [`ContinuousFlexibility.FlatAnnularCore.b_pos`](../ContinuousFlexibility/Contracts/Annular.lean#L46)
- [`ContinuousFlexibility.FlatAnnularCore.periodic_two_pi`](../ContinuousFlexibility/Contracts/Annular.lean#L49)
- [`ContinuousFlexibility.FlatAnnularCore.left_flat_germs`](../ContinuousFlexibility/Contracts/Annular.lean#L56)
- [`ContinuousFlexibility.FlatAnnularCore.right_flat_germs`](../ContinuousFlexibility/Contracts/Annular.lean#L67)
- [`ContinuousFlexibility.FlatAnnularCore.discriminant_pos_global`](../ContinuousFlexibility/Contracts/Annular.lean#L80)
- [`ContinuousFlexibility.FlatAnnularCore.residual_zero_global`](../ContinuousFlexibility/Contracts/Annular.lean#L92)

[SphereCoordinates.lean](../ContinuousFlexibility/Geometry/SphereCoordinates.lean)：

- [`ContinuousFlexibility.sphereStereoDenom_pos`](../ContinuousFlexibility/Geometry/SphereCoordinates.lean#L30)
- [`ContinuousFlexibility.e3_mem_unit_sphere_iff`](../ContinuousFlexibility/Geometry/SphereCoordinates.lean#L34)
- [`ContinuousFlexibility.spherePoint_coordinate_sq`](../ContinuousFlexibility/Geometry/SphereCoordinates.lean#L48)
- [`ContinuousFlexibility.spherePoint_vertical_bounds`](../ContinuousFlexibility/Geometry/SphereCoordinates.lean#L52)
- [`ContinuousFlexibility.spherePlaneEnergy_eq_radius_sq`](../ContinuousFlexibility/Geometry/SphereCoordinates.lean#L57)
- [`ContinuousFlexibility.sphere_chart_sources_cover`](../ContinuousFlexibility/Geometry/SphereCoordinates.lean#L73)
- [`ContinuousFlexibility.sphereNorthInvVector_mem`](../ContinuousFlexibility/Geometry/SphereCoordinates.lean#L90)
- [`ContinuousFlexibility.sphereSouthInvVector_mem`](../ContinuousFlexibility/Geometry/SphereCoordinates.lean#L98)
- [`ContinuousFlexibility.sphereNorthChart_energy`](../ContinuousFlexibility/Geometry/SphereCoordinates.lean#L112)
- [`ContinuousFlexibility.sphereSouthChart_energy`](../ContinuousFlexibility/Geometry/SphereCoordinates.lean#L124)
- [`ContinuousFlexibility.sphereNorthChart_inverse`](../ContinuousFlexibility/Geometry/SphereCoordinates.lean#L136)
- [`ContinuousFlexibility.sphereSouthChart_inverse`](../ContinuousFlexibility/Geometry/SphereCoordinates.lean#L147)
- [`ContinuousFlexibility.sphereNorthInverse_source`](../ContinuousFlexibility/Geometry/SphereCoordinates.lean#L158)
- [`ContinuousFlexibility.sphereSouthInverse_source`](../ContinuousFlexibility/Geometry/SphereCoordinates.lean#L167)
- [`ContinuousFlexibility.sphereNorthInverse_chart`](../ContinuousFlexibility/Geometry/SphereCoordinates.lean#L176)
- [`ContinuousFlexibility.sphereSouthInverse_chart`](../ContinuousFlexibility/Geometry/SphereCoordinates.lean#L205)
- [`ContinuousFlexibility.sphereNorthChart_injectiveOn`](../ContinuousFlexibility/Geometry/SphereCoordinates.lean#L234)
- [`ContinuousFlexibility.sphereSouthChart_injectiveOn`](../ContinuousFlexibility/Geometry/SphereCoordinates.lean#L238)
- [`ContinuousFlexibility.contMDiffAt_sphereNorthChart`](../ContinuousFlexibility/Geometry/SphereCoordinates.lean#L247)
- [`ContinuousFlexibility.contMDiffAt_sphereSouthChart`](../ContinuousFlexibility/Geometry/SphereCoordinates.lean#L259)
- [`ContinuousFlexibility.isOpen_sphereNorthSource`](../ContinuousFlexibility/Geometry/SphereCoordinates.lean#L271)
- [`ContinuousFlexibility.isOpen_sphereSouthSource`](../ContinuousFlexibility/Geometry/SphereCoordinates.lean#L274)
- [`ContinuousFlexibility.contDiff_spherePlaneEnergy`](../ContinuousFlexibility/Geometry/SphereCoordinates.lean#L277)
- [`ContinuousFlexibility.contDiff_sphereStereoDenom`](../ContinuousFlexibility/Geometry/SphereCoordinates.lean#L280)
- [`ContinuousFlexibility.contDiff_sphereNorthInvVector`](../ContinuousFlexibility/Geometry/SphereCoordinates.lean#L283)
- [`ContinuousFlexibility.contDiff_sphereSouthInvVector`](../ContinuousFlexibility/Geometry/SphereCoordinates.lean#L292)
- [`ContinuousFlexibility.contMDiff_sphereNorthInverse`](../ContinuousFlexibility/Geometry/SphereCoordinates.lean#L301)
- [`ContinuousFlexibility.contMDiff_sphereSouthInverse`](../ContinuousFlexibility/Geometry/SphereCoordinates.lean#L306)
- [`ContinuousFlexibility.sphereSouthChart_eq_inversion_north`](../ContinuousFlexibility/Geometry/SphereCoordinates.lean#L312)
- [`ContinuousFlexibility.sphereNorthChart_eq_inversion_south`](../ContinuousFlexibility/Geometry/SphereCoordinates.lean#L329)
- [`ContinuousFlexibility.sphereNorthChart_radius_le_one_iff`](../ContinuousFlexibility/Geometry/SphereCoordinates.lean#L377)
- [`ContinuousFlexibility.sphereSouthChart_radius_le_one_iff`](../ContinuousFlexibility/Geometry/SphereCoordinates.lean#L400)


<a id="s01"></a>
## S01 余度量正定与余标架

**状态：** 已形式化的局部节点。**分支：** 标量方程。主定理必要节点。

**数学陈述：** r>0、E>0 时，余度量坐标二次型正定 ⇔ D=E(1-p²)-k²>0；并有 D>0 ⇔ k²/E+p²<1、两个对角因子正性及余标架平方和等式。

**证明提纲：** 已用无除法完成平方证明必要性和充分性，再用平方根平方关系证明余标架展开。范围是点态坐标表达式。

**直接依赖：** 无其他蓝图节点

**论文定位：** [03-height-equation.tex:13–24](../paper/flexible-surface-rewrite/03-height-equation.tex#L13)，`eq:height-jet-notation`

**目标文件：** `ContinuousFlexibility/Scalar/Positivity.lean`（已有）

**验收条件：**

- 现有 Positivity 的10条及 Coframe 的1条精确覆盖此节点
- 尚未声称识别了流形范数或曲率

**现有 Lean 证明：**

[Positivity.lean](../ContinuousFlexibility/Scalar/Positivity.lean)：

- [`ContinuousFlexibility.radialEnergy_pos`](../ContinuousFlexibility/Scalar/Positivity.lean#L16)
- [`ContinuousFlexibility.angular_factor_pos_of_discriminant_pos`](../ContinuousFlexibility/Scalar/Positivity.lean#L21)
- [`ContinuousFlexibility.radial_factor_pos_of_discriminant_pos`](../ContinuousFlexibility/Scalar/Positivity.lean#L32)
- [`ContinuousFlexibility.discriminant_pos_iff_height_norm_sq_lt_one`](../ContinuousFlexibility/Scalar/Positivity.lean#L42)
- [`ContinuousFlexibility.remainder_matrix_determinant`](../ContinuousFlexibility/Scalar/Positivity.lean#L59)
- [`ContinuousFlexibility.remainder_complete_square`](../ContinuousFlexibility/Scalar/Positivity.lean#L66)
- [`ContinuousFlexibility.remainderPositive_of_discriminant_pos`](../ContinuousFlexibility/Scalar/Positivity.lean#L73)
- [`ContinuousFlexibility.discriminant_pos_of_remainderPositive`](../ContinuousFlexibility/Scalar/Positivity.lean#L94)
- [`ContinuousFlexibility.remainderPositive_iff_discriminant_pos`](../ContinuousFlexibility/Scalar/Positivity.lean#L122)
- [`ContinuousFlexibility.radial_remainderPositive_iff_discriminant_pos`](../ContinuousFlexibility/Scalar/Positivity.lean#L129)

[Coframe.lean](../ContinuousFlexibility/Scalar/Coframe.lean)：

- [`ContinuousFlexibility.coframe_square_sum`](../ContinuousFlexibility/Scalar/Coframe.lean#L24)


<a id="s02"></a>
## S02 线性系数行列式与残差修正

**状态：** 已形式化的局部节点。**分支：** 标量方程。主定理必要节点。

**数学陈述：** 对明确坐标残差 Nres 和系数 a,b,c，r≠0、D>0 时 ac-b²=K₀/D²+E D^(-3/2)Nres；再加 Q≠0，c̄=c-E Nres/Q 给 ac̄-b²=K₀/D²。含径向特化与零残差时修正消失。

**证明提纲：** 已先证明一般共同缩放因子的代数恒等式，再特化为 1/(D√D)。K₀=ww'/r 是参考系数，不等于原径向度量的高斯曲率。

**直接依赖：** 无其他蓝图节点

**论文定位：** [03-height-equation.tex:47–115](../paper/flexible-surface-rewrite/03-height-equation.tex#L47)，`eq:cart-determinant-identity`；[03-height-equation.tex:336–360](../paper/flexible-surface-rewrite/03-height-equation.tex#L336)，`eq:cart-completed-normalized-derivative`

**目标文件：** `ContinuousFlexibility/Scalar/Determinant.lean`（已有）

**验收条件：**

- 14条定理已覆盖点态代数
- 实际残差的微分识别另在S03/S05

**现有 Lean 证明：**

[Determinant.lean](../ContinuousFlexibility/Scalar/Determinant.lean)：

- [`ContinuousFlexibility.correctedAngular_eq_residual_correction`](../ContinuousFlexibility/Scalar/Determinant.lean#L45)
- [`ContinuousFlexibility.correctedAngular_of_residual_zero`](../ContinuousFlexibility/Scalar/Determinant.lean#L56)
- [`ContinuousFlexibility.heightQ_discriminant_identity`](../ContinuousFlexibility/Scalar/Determinant.lean#L63)
- [`ContinuousFlexibility.linear_determinant_scaled`](../ContinuousFlexibility/Scalar/Determinant.lean#L70)
- [`ContinuousFlexibility.inverseDThreeHalves_sq`](../ContinuousFlexibility/Scalar/Determinant.lean#L82)
- [`ContinuousFlexibility.inverseDThreeHalves_pos`](../ContinuousFlexibility/Scalar/Determinant.lean#L89)
- [`ContinuousFlexibility.discriminant_mul_inverseDThreeHalves_sq`](../ContinuousFlexibility/Scalar/Determinant.lean#L95)
- [`ContinuousFlexibility.linear_determinant`](../ContinuousFlexibility/Scalar/Determinant.lean#L106)
- [`ContinuousFlexibility.corrected_determinant_scaled`](../ContinuousFlexibility/Scalar/Determinant.lean#L130)
- [`ContinuousFlexibility.corrected_determinant`](../ContinuousFlexibility/Scalar/Determinant.lean#L144)
- [`ContinuousFlexibility.heightDiscriminant_radial`](../ContinuousFlexibility/Scalar/Determinant.lean#L159)
- [`ContinuousFlexibility.inverseDThreeHalves_one`](../ContinuousFlexibility/Scalar/Determinant.lean#L165)
- [`ContinuousFlexibility.radial_linear_coefficients`](../ContinuousFlexibility/Scalar/Determinant.lean#L174)
- [`ContinuousFlexibility.radial_coordinate_residual_zero`](../ContinuousFlexibility/Scalar/Determinant.lean#L191)


<a id="r01"></a>
## R01 真实导数下的对数幂 gauge

**状态：** 已形式化的局部节点。**分支：** 径向参考。主定理必要节点。

**数学陈述：** u(r)=r^aV(log r)、r>0，在现有明确可微假设下计算实际一二阶导数及 L_a u。令 p(y)=w(e^y)e^((2a-1)y)，有 (pV')'+a(a-1)pV=e^((a+1)y)L_a u(e^y)；取 a=j²。

**证明提纲：** 已用 HasDerivAt、deriv、局部相等的导数转移证明，含不除以w的版本和非齐次源的精确因子。

**直接依赖：** 无其他蓝图节点

**论文定位：** [05-flat-end-chain.tex:252–268](../paper/flexible-surface-rewrite/05-flat-end-chain.tex#L252)，`eq:rad-eq-rm13`

**目标文件：** `ContinuousFlexibility/Radial/Gauge.lean`（已有）

**验收条件：**

- 10条定理覆盖此局部微分节点
- Green配对与闭算子域换元仍由R06/R12证明

**现有 Lean 证明：**

[Gauge.lean](../ContinuousFlexibility/Radial/Gauge.lean)：

- [`ContinuousFlexibility.Radial.hasDerivAt_gaugeLift`](../ContinuousFlexibility/Radial/Gauge.lean#L35)
- [`ContinuousFlexibility.Radial.deriv_gaugeLift`](../ContinuousFlexibility/Radial/Gauge.lean#L48)
- [`ContinuousFlexibility.Radial.hasDerivAt_gaugeFirst`](../ContinuousFlexibility/Radial/Gauge.lean#L54)
- [`ContinuousFlexibility.Radial.deriv_deriv_gaugeLift`](../ContinuousFlexibility/Radial/Gauge.lean#L75)
- [`ContinuousFlexibility.Radial.radialJacobi_gauge`](../ContinuousFlexibility/Radial/Gauge.lean#L92)
- [`ContinuousFlexibility.Radial.radialJacobi_gauge_divided`](../ContinuousFlexibility/Radial/Gauge.lean#L118)
- [`ContinuousFlexibility.Radial.logGaugeWeight_eq`](../ContinuousFlexibility/Radial/Gauge.lean#L135)
- [`ContinuousFlexibility.Radial.logGaugeEquation_eq`](../ContinuousFlexibility/Radial/Gauge.lean#L146)
- [`ContinuousFlexibility.Radial.logGaugeEquation_source_identity`](../ContinuousFlexibility/Radial/Gauge.lean#L166)
- [`ContinuousFlexibility.Radial.radialJacobi_gauge_eq_zero_iff`](../ContinuousFlexibility/Radial/Gauge.lean#L183)


<a id="s03"></a>
## S03 高度微分、Cartan连接与真实变分

**状态：** 已有部分已编译子结果。**分支：** 标量方程。主定理必要节点。

**数学陈述：** 对光滑w,z及r>0,D>0，证明 rp_r=kθ-p、所示余标架的结构方程、α=D^(-1/2)(dθ+k dp/(1-p²))、dα=rNres dr∧dθ，以及实际高度变分的对称散度表达式。

**证明提纲：** 先把独立jet的恒等式绑定到真实偏导，证明混合偏导交换；然后算结构方程和连接变分。主定理可直接用 Nres=0⇒闭连接⇒归一化发展，通用Darboux曲率公式不是必须前置库。

**直接依赖：** [C00](#c00), [S01](#s01), [S02](#s02)

**论文定位：** [03-height-equation.tex:29–115](../paper/flexible-surface-rewrite/03-height-equation.tex#L29)，`prop:scalar-core`

**目标文件：** `ContinuousFlexibility/Scalar/S03.lean`（节点组织目标；实际已存在的证明文件见下方，整个节点尚未完成）

**验收条件：**

- 不得以自由jet代数代替真实微分
- 源密度明确为dr dθ
- Nres的零集必须实际给出局部欧氏余度量

**已经完成的子结果：**

- 真实高度偏导、混合偏导交换、Cartan方程及实际连接外微分
- 实际z+tη参数导数已与完整对称散度逐项识别；第三阶jet消去使用真实偏导

**仍待闭合的义务：**

- 接入后续加权空间的函数空间光滑性与公共接口，不能把点态C∞等同smooth tame

**现有 Lean 证明：**

[HeightDerivatives.lean](../ContinuousFlexibility/Scalar/HeightDerivatives.lean)：

- [`ContinuousFlexibility.radialPartial_const`](../ContinuousFlexibility/Scalar/HeightDerivatives.lean#L30)
- [`ContinuousFlexibility.angularPartial_const`](../ContinuousFlexibility/Scalar/HeightDerivatives.lean#L34)
- [`ContinuousFlexibility.radialPartial_add`](../ContinuousFlexibility/Scalar/HeightDerivatives.lean#L38)
- [`ContinuousFlexibility.angularPartial_add`](../ContinuousFlexibility/Scalar/HeightDerivatives.lean#L43)
- [`ContinuousFlexibility.radialPartial_sub`](../ContinuousFlexibility/Scalar/HeightDerivatives.lean#L48)
- [`ContinuousFlexibility.angularPartial_sub`](../ContinuousFlexibility/Scalar/HeightDerivatives.lean#L53)
- [`ContinuousFlexibility.radialPartial_mul`](../ContinuousFlexibility/Scalar/HeightDerivatives.lean#L58)
- [`ContinuousFlexibility.angularPartial_mul`](../ContinuousFlexibility/Scalar/HeightDerivatives.lean#L66)
- [`ContinuousFlexibility.radialPartial_sq`](../ContinuousFlexibility/Scalar/HeightDerivatives.lean#L74)
- [`ContinuousFlexibility.angularPartial_sq`](../ContinuousFlexibility/Scalar/HeightDerivatives.lean#L80)
- [`ContinuousFlexibility.polar_fderiv_div`](../ContinuousFlexibility/Scalar/HeightDerivatives.lean#L87)
- [`ContinuousFlexibility.radialPartial_div`](../ContinuousFlexibility/Scalar/HeightDerivatives.lean#L102)
- [`ContinuousFlexibility.angularPartial_div`](../ContinuousFlexibility/Scalar/HeightDerivatives.lean#L108)
- [`ContinuousFlexibility.radialPartial_fst`](../ContinuousFlexibility/Scalar/HeightDerivatives.lean#L114)
- [`ContinuousFlexibility.angularPartial_fst`](../ContinuousFlexibility/Scalar/HeightDerivatives.lean#L117)
- [`ContinuousFlexibility.radialPartial_snd`](../ContinuousFlexibility/Scalar/HeightDerivatives.lean#L120)
- [`ContinuousFlexibility.angularPartial_snd`](../ContinuousFlexibility/Scalar/HeightDerivatives.lean#L123)
- [`ContinuousFlexibility.contDiffAt_radialPartial`](../ContinuousFlexibility/Scalar/HeightDerivatives.lean#L126)
- [`ContinuousFlexibility.contDiffAt_angularPartial`](../ContinuousFlexibility/Scalar/HeightDerivatives.lean#L130)
- [`ContinuousFlexibility.contDiffAt_heightRadial`](../ContinuousFlexibility/Scalar/HeightDerivatives.lean#L134)
- [`ContinuousFlexibility.contDiffAt_heightAngular`](../ContinuousFlexibility/Scalar/HeightDerivatives.lean#L138)
- [`ContinuousFlexibility.polar_fderiv_partial`](../ContinuousFlexibility/Scalar/HeightDerivatives.lean#L143)
- [`ContinuousFlexibility.radial_angular_commute`](../ContinuousFlexibility/Scalar/HeightDerivatives.lean#L151)
- [`ContinuousFlexibility.height_compatibility`](../ContinuousFlexibility/Scalar/HeightDerivatives.lean#L160)
- [`ContinuousFlexibility.radialPartial_profileEnergy`](../ContinuousFlexibility/Scalar/HeightDerivatives.lean#L171)
- [`ContinuousFlexibility.angularPartial_profileEnergy`](../ContinuousFlexibility/Scalar/HeightDerivatives.lean#L181)
- [`ContinuousFlexibility.radialPartial_polarDiscriminant`](../ContinuousFlexibility/Scalar/HeightDerivatives.lean#L192)
- [`ContinuousFlexibility.angularPartial_polarDiscriminant`](../ContinuousFlexibility/Scalar/HeightDerivatives.lean#L214)

[ConnectionVariation.lean](../ContinuousFlexibility/Scalar/ConnectionVariation.lean)：

- [`ContinuousFlexibility.angular_factor_ne_zero_of_discriminant_pos`](../ContinuousFlexibility/Scalar/ConnectionVariation.lean#L51)
- [`ContinuousFlexibility.hasDerivAt_heightDiscriminant`](../ContinuousFlexibility/Scalar/ConnectionVariation.lean#L60)
- [`ContinuousFlexibility.hasDerivAt_inverse_sqrt`](../ContinuousFlexibility/Scalar/ConnectionVariation.lean#L76)
- [`ContinuousFlexibility.hasDerivAt_connectionInverseRoot`](../ContinuousFlexibility/Scalar/ConnectionVariation.lean#L92)
- [`ContinuousFlexibility.connectionInverseRoot_eq_discriminant_mul_scale`](../ContinuousFlexibility/Scalar/ConnectionVariation.lean#L103)
- [`ContinuousFlexibility.hasDerivAt_connectionB1`](../ContinuousFlexibility/Scalar/ConnectionVariation.lean#L111)
- [`ContinuousFlexibility.hasDerivAt_connectionB1_k`](../ContinuousFlexibility/Scalar/ConnectionVariation.lean#L140)
- [`ContinuousFlexibility.hasDerivAt_connectionB1_E`](../ContinuousFlexibility/Scalar/ConnectionVariation.lean#L149)
- [`ContinuousFlexibility.hasDerivAt_connectionB1_p`](../ContinuousFlexibility/Scalar/ConnectionVariation.lean#L158)
- [`ContinuousFlexibility.hasDerivAt_connectionRadialValue`](../ContinuousFlexibility/Scalar/ConnectionVariation.lean#L169)
- [`ContinuousFlexibility.hasDerivAt_connectionAngularValue`](../ContinuousFlexibility/Scalar/ConnectionVariation.lean#L180)

[CoframeDerivatives.lean](../ContinuousFlexibility/Scalar/CoframeDerivatives.lean)：

- [`ContinuousFlexibility.coframeOne_eq_AValue`](../ContinuousFlexibility/Scalar/CoframeDerivatives.lean#L37)
- [`ContinuousFlexibility.coframeTwo_eq_BCValue`](../ContinuousFlexibility/Scalar/CoframeDerivatives.lean#L40)
- [`ContinuousFlexibility.coframeAValue_mul_CValue`](../ContinuousFlexibility/Scalar/CoframeDerivatives.lean#L46)
- [`ContinuousFlexibility.hasDerivAt_angularFactor`](../ContinuousFlexibility/Scalar/CoframeDerivatives.lean#L53)
- [`ContinuousFlexibility.hasDerivAt_coframeAValue`](../ContinuousFlexibility/Scalar/CoframeDerivatives.lean#L60)
- [`ContinuousFlexibility.hasDerivAt_coframeBValue`](../ContinuousFlexibility/Scalar/CoframeDerivatives.lean#L88)
- [`ContinuousFlexibility.hasDerivAt_coframeCValue`](../ContinuousFlexibility/Scalar/CoframeDerivatives.lean#L110)

[Connection.lean](../ContinuousFlexibility/Scalar/Connection.lean)：

- [`ContinuousFlexibility.differentiableAt_connectionInverseRoot`](../ContinuousFlexibility/Scalar/Connection.lean#L32)
- [`ContinuousFlexibility.differentiableAt_connectionB1`](../ContinuousFlexibility/Scalar/Connection.lean#L47)
- [`ContinuousFlexibility.fderiv_connectionRadialField`](../ContinuousFlexibility/Scalar/Connection.lean#L66)
- [`ContinuousFlexibility.fderiv_connectionAngularField`](../ContinuousFlexibility/Scalar/Connection.lean#L86)
- [`ContinuousFlexibility.connectionCurl_expansion`](../ContinuousFlexibility/Scalar/Connection.lean#L110)
- [`ContinuousFlexibility.connectionCurl_eq_scaledNumerator`](../ContinuousFlexibility/Scalar/Connection.lean#L138)
- [`ContinuousFlexibility.polar_connectionCurl_eq_residual`](../ContinuousFlexibility/Scalar/Connection.lean#L165)
- [`ContinuousFlexibility.polar_connection_closed_iff`](../ContinuousFlexibility/Scalar/Connection.lean#L184)

[Cartan.lean](../ContinuousFlexibility/Scalar/Cartan.lean)：

- [`ContinuousFlexibility.polar_differentiableAt_div`](../ContinuousFlexibility/Scalar/Cartan.lean#L27)
- [`ContinuousFlexibility.differentiableAt_coframeAField`](../ContinuousFlexibility/Scalar/Cartan.lean#L35)
- [`ContinuousFlexibility.differentiableAt_coframeBField`](../ContinuousFlexibility/Scalar/Cartan.lean#L47)
- [`ContinuousFlexibility.differentiableAt_coframeCField`](../ContinuousFlexibility/Scalar/Cartan.lean#L55)
- [`ContinuousFlexibility.fderiv_coframeAField`](../ContinuousFlexibility/Scalar/Cartan.lean#L61)
- [`ContinuousFlexibility.fderiv_coframeBField`](../ContinuousFlexibility/Scalar/Cartan.lean#L80)
- [`ContinuousFlexibility.fderiv_coframeCField`](../ContinuousFlexibility/Scalar/Cartan.lean#L94)
- [`ContinuousFlexibility.cartan_first_algebra`](../ContinuousFlexibility/Scalar/Cartan.lean#L110)
- [`ContinuousFlexibility.cartan_second_algebra`](../ContinuousFlexibility/Scalar/Cartan.lean#L125)
- [`ContinuousFlexibility.cartan_first`](../ContinuousFlexibility/Scalar/Cartan.lean#L137)
- [`ContinuousFlexibility.cartan_second`](../ContinuousFlexibility/Scalar/Cartan.lean#L154)
- [`ContinuousFlexibility.polar_cartan_equations`](../ContinuousFlexibility/Scalar/Cartan.lean#L167)
- [`ContinuousFlexibility.polar_coframe_determinant_pos`](../ContinuousFlexibility/Scalar/Cartan.lean#L192)

[HeightVariation.lean](../ContinuousFlexibility/Scalar/HeightVariation.lean)：

- [`ContinuousFlexibility.heightFamily_zero`](../ContinuousFlexibility/Scalar/HeightVariation.lean#L24)
- [`ContinuousFlexibility.contDiff_heightFamily`](../ContinuousFlexibility/Scalar/HeightVariation.lean#L28)
- [`ContinuousFlexibility.radialPartial_heightFamily`](../ContinuousFlexibility/Scalar/HeightVariation.lean#L32)
- [`ContinuousFlexibility.angularPartial_heightFamily`](../ContinuousFlexibility/Scalar/HeightVariation.lean#L41)
- [`ContinuousFlexibility.heightRadial_heightFamily`](../ContinuousFlexibility/Scalar/HeightVariation.lean#L52)
- [`ContinuousFlexibility.heightAngular_heightFamily`](../ContinuousFlexibility/Scalar/HeightVariation.lean#L60)
- [`ContinuousFlexibility.radialPartial_heightRadial_heightFamily`](../ContinuousFlexibility/Scalar/HeightVariation.lean#L79)
- [`ContinuousFlexibility.angularPartial_heightRadial_heightFamily`](../ContinuousFlexibility/Scalar/HeightVariation.lean#L87)
- [`ContinuousFlexibility.radialPartial_heightAngular_heightFamily`](../ContinuousFlexibility/Scalar/HeightVariation.lean#L95)
- [`ContinuousFlexibility.angularPartial_heightAngular_heightFamily`](../ContinuousFlexibility/Scalar/HeightVariation.lean#L103)
- [`ContinuousFlexibility.hasDerivAt_heightRadial_heightFamily`](../ContinuousFlexibility/Scalar/HeightVariation.lean#L117)
- [`ContinuousFlexibility.hasDerivAt_heightAngular_heightFamily`](../ContinuousFlexibility/Scalar/HeightVariation.lean#L124)
- [`ContinuousFlexibility.hasDerivAt_radialPartial_heightRadial_heightFamily`](../ContinuousFlexibility/Scalar/HeightVariation.lean#L131)
- [`ContinuousFlexibility.hasDerivAt_radialPartial_heightAngular_heightFamily`](../ContinuousFlexibility/Scalar/HeightVariation.lean#L139)
- [`ContinuousFlexibility.hasDerivAt_angularPartial_heightAngular_heightFamily`](../ContinuousFlexibility/Scalar/HeightVariation.lean#L147)
- [`ContinuousFlexibility.hasDerivAt_darbouxNumerator`](../ContinuousFlexibility/Scalar/HeightVariation.lean#L162)
- [`ContinuousFlexibility.hasDerivAt_polarDiscriminant_heightFamily`](../ContinuousFlexibility/Scalar/HeightVariation.lean#L191)
- [`ContinuousFlexibility.hasDerivAt_polarCurvatureNumerator_heightFamily`](../ContinuousFlexibility/Scalar/HeightVariation.lean#L201)
- [`ContinuousFlexibility.hasDerivAt_inverseDThreeHalves`](../ContinuousFlexibility/Scalar/HeightVariation.lean#L215)
- [`ContinuousFlexibility.hasDerivAt_polarCoordinateResidual_heightFamily`](../ContinuousFlexibility/Scalar/HeightVariation.lean#L239)

[HeightCoframe.lean](../ContinuousFlexibility/Geometry/HeightCoframe.lean)：

- [`ContinuousFlexibility.heightCoframe_square_sum`](../ContinuousFlexibility/Geometry/HeightCoframe.lean#L30)
- [`ContinuousFlexibility.heightCoframe_wedge`](../ContinuousFlexibility/Geometry/HeightCoframe.lean#L42)
- [`ContinuousFlexibility.heightCoframe_wedge_pos`](../ContinuousFlexibility/Geometry/HeightCoframe.lean#L52)
- [`ContinuousFlexibility.heightCoframe_cartan`](../ContinuousFlexibility/Geometry/HeightCoframe.lean#L59)
- [`ContinuousFlexibility.heightConnection_exterior_eq_residual`](../ContinuousFlexibility/Geometry/HeightCoframe.lean#L74)
- [`ContinuousFlexibility.heightConnection_closed_of_residual_zero`](../ContinuousFlexibility/Geometry/HeightCoframe.lean#L82)
- [`ContinuousFlexibility.contDiffAt_heightCoframeOne_radial`](../ContinuousFlexibility/Geometry/HeightCoframe.lean#L90)
- [`ContinuousFlexibility.contDiffAt_heightCoframeTwo_radial`](../ContinuousFlexibility/Geometry/HeightCoframe.lean#L106)
- [`ContinuousFlexibility.contDiffAt_heightCoframeTwo_angular`](../ContinuousFlexibility/Geometry/HeightCoframe.lean#L119)
- [`ContinuousFlexibility.height_rotatedCoframe_closed`](../ContinuousFlexibility/Geometry/HeightCoframe.lean#L134)

[LinearizationAlgebra.lean](../ContinuousFlexibility/Scalar/LinearizationAlgebra.lean)：

- [`ContinuousFlexibility.linearization_radial_drift_algebra`](../ContinuousFlexibility/Scalar/LinearizationAlgebra.lean#L12)
- [`ContinuousFlexibility.linearization_angular_drift_algebra`](../ContinuousFlexibility/Scalar/LinearizationAlgebra.lean#L24)
- [`ContinuousFlexibility.linearization_expanded_algebra`](../ContinuousFlexibility/Scalar/LinearizationAlgebra.lean#L38)

[Linearization.lean](../ContinuousFlexibility/Scalar/Linearization.lean)：

- [`ContinuousFlexibility.angularPartial_radial_profileEnergy`](../ContinuousFlexibility/Scalar/Linearization.lean#L178)
- [`ContinuousFlexibility.angular_radial_heightRadial_identity`](../ContinuousFlexibility/Scalar/Linearization.lean#L191)
- [`ContinuousFlexibility.polarLinear_radial_drift`](../ContinuousFlexibility/Scalar/Linearization.lean#L218)
- [`ContinuousFlexibility.polarLinear_angular_drift`](../ContinuousFlexibility/Scalar/Linearization.lean#L260)
- [`ContinuousFlexibility.divergence_expansion_of_coefficients`](../ContinuousFlexibility/Scalar/Linearization.lean#L304)
- [`ContinuousFlexibility.angularSecond_eq_radius_mul_heightAngular`](../ContinuousFlexibility/Scalar/Linearization.lean#L328)
- [`ContinuousFlexibility.heightLinearizedDivergence_eq_variation`](../ContinuousFlexibility/Scalar/Linearization.lean#L339)
- [`ContinuousFlexibility.polarResidualVariation_eq_divergence`](../ContinuousFlexibility/Scalar/Linearization.lean#L372)
- [`ContinuousFlexibility.hasDerivAt_polarCoordinateResidual_divergence`](../ContinuousFlexibility/Scalar/Linearization.lean#L381)
- [`ContinuousFlexibility.hasDerivAt_radialScaledResidual_divergence`](../ContinuousFlexibility/Scalar/Linearization.lean#L392)


<a id="s04"></a>
## S04 归一化残差的可去延拓和守恒

**状态：** 已有部分已编译子结果。**分支：** 标量方程。主定理必要节点。

**数学陈述：** F_q(w,u)=rN_h(h+qu)/q 在q=0光滑延拓为 ℒ_wu，满足积分表示。对常高度端领圈或适当平坦端点，∫⟨F_q⟩dr=0；其全部高度和度量微分保持兼容性。

**证明提纲：** 用沿参数线段的微积分基本定理处理q=0；用连接period和Stokes/一维积分处理守恒，角平均采用归一化测度。

**直接依赖：** [S03](#s03)

**论文定位：** [03-height-equation.tex:287–326](../paper/flexible-surface-rewrite/03-height-equation.tex#L287)，`eq:normalized-integral`

**目标文件：** `ContinuousFlexibility/Scalar/S04.lean`（节点组织目标；实际已存在的证明文件见下方，整个节点尚未完成）

**验收条件：**

- 包括度量变化时h_w的变化
- 两端连接period均为2π
- 明确推广到后来加权平坦空间的边界极限

**已经完成的子结果：**

- 真实曲率分子的精确二次分解与q=0可去延拓，实参数局部C∞
- 周期高度、独立端点一阶jets下真实dr dθ守恒，无需常值开领圈
- 真实径向基点D=1、N=0，q=0规范化值等于真实Jacobi PDE，全部q的规范化源平均积分为零

**仍待闭合的义务：**

- 证明加权空间中的联合smooth tame、所有高度及度量微分兼容性
- 以实际加权端点延拓和统一参数邻域实例化目前明确的有限矩形假设

**现有 Lean 证明：**

[Conservation.lean](../ContinuousFlexibility/Scalar/Conservation.lean)：

- [`ContinuousFlexibility.hasDerivAt_radial_slice`](../ContinuousFlexibility/Scalar/Conservation.lean#L23)
- [`ContinuousFlexibility.hasDerivAt_angular_slice`](../ContinuousFlexibility/Scalar/Conservation.lean#L29)
- [`ContinuousFlexibility.periodic_radialPartial`](../ContinuousFlexibility/Scalar/Conservation.lean#L37)
- [`ContinuousFlexibility.periodic_angularPartial`](../ContinuousFlexibility/Scalar/Conservation.lean#L45)
- [`ContinuousFlexibility.heightConnection_periodic`](../ContinuousFlexibility/Scalar/Conservation.lean#L53)
- [`ContinuousFlexibility.integral_exteriorCoefficient_eq_zero`](../ContinuousFlexibility/Scalar/Conservation.lean#L71)
- [`ContinuousFlexibility.integral_heightResidual_eq_zero`](../ContinuousFlexibility/Scalar/Conservation.lean#L132)
- [`ContinuousFlexibility.heightConnection_of_boundary_jets`](../ContinuousFlexibility/Scalar/Conservation.lean#L157)
- [`ContinuousFlexibility.heightConnection_of_flat_collar`](../ContinuousFlexibility/Scalar/Conservation.lean#L168)
- [`ContinuousFlexibility.integral_heightResidual_eq_zero_of_flat_collars`](../ContinuousFlexibility/Scalar/Conservation.lean#L181)
- [`ContinuousFlexibility.integral_mean_heightResidual_eq_zero`](../ContinuousFlexibility/Scalar/Conservation.lean#L202)
- [`ContinuousFlexibility.integral_mean_heightResidual_eq_zero_of_boundary_jets`](../ContinuousFlexibility/Scalar/Conservation.lean#L225)

[Normalization.lean](../ContinuousFlexibility/Scalar/Normalization.lean)：

- [`ContinuousFlexibility.polarResidual_zero_iff_numerator_zero`](../ContinuousFlexibility/Scalar/Normalization.lean#L25)
- [`ContinuousFlexibility.polarCurvatureNumerator_heightFamily`](../ContinuousFlexibility/Scalar/Normalization.lean#L32)
- [`ContinuousFlexibility.normalizedHeightResidual_zero`](../ContinuousFlexibility/Scalar/Normalization.lean#L56)
- [`ContinuousFlexibility.normalizedHeightResidual_of_ne_zero`](../ContinuousFlexibility/Scalar/Normalization.lean#L61)
- [`ContinuousFlexibility.normalizedHeightResidual_eq_factored`](../ContinuousFlexibility/Scalar/Normalization.lean#L68)
- [`ContinuousFlexibility.contDiffAt_normalizedHeightResidual`](../ContinuousFlexibility/Scalar/Normalization.lean#L88)
- [`ContinuousFlexibility.contDiffAt_normalizedHeightResidual_of_residual_zero`](../ContinuousFlexibility/Scalar/Normalization.lean#L116)

[NormalizedConservation.lean](../ContinuousFlexibility/Scalar/NormalizedConservation.lean)：

- [`ContinuousFlexibility.contDiffAt_radialJacobiFlux`](../ContinuousFlexibility/Scalar/NormalizedConservation.lean#L31)
- [`ContinuousFlexibility.radialJacobiFlux_exterior_eq_radialPDE`](../ContinuousFlexibility/Scalar/NormalizedConservation.lean#L45)
- [`ContinuousFlexibility.integral_mean_radialPDE_eq_zero`](../ContinuousFlexibility/Scalar/NormalizedConservation.lean#L83)
- [`ContinuousFlexibility.contDiffAt_normalizedHeightResidual_radialHeight_zero`](../ContinuousFlexibility/Scalar/NormalizedConservation.lean#L120)
- [`ContinuousFlexibility.integral_mean_normalizedHeightResidual_eq_zero_of_ne_zero`](../ContinuousFlexibility/Scalar/NormalizedConservation.lean#L139)
- [`ContinuousFlexibility.integral_mean_normalizedHeightResidual_radialHeight_eq_zero`](../ContinuousFlexibility/Scalar/NormalizedConservation.lean#L164)

[RadialHeight.lean](../ContinuousFlexibility/Radial/RadialHeight.lean)：

- [`ContinuousFlexibility.Radial.contDiff_radialHeightField`](../ContinuousFlexibility/Radial/RadialHeight.lean#L24)
- [`ContinuousFlexibility.Radial.radialPartial_radialHeightField`](../ContinuousFlexibility/Radial/RadialHeight.lean#L27)
- [`ContinuousFlexibility.Radial.angularPartial_radialHeightField`](../ContinuousFlexibility/Radial/RadialHeight.lean#L37)
- [`ContinuousFlexibility.Radial.heightRadial_radialHeightField`](../ContinuousFlexibility/Radial/RadialHeight.lean#L47)
- [`ContinuousFlexibility.Radial.heightAngular_radialHeightField`](../ContinuousFlexibility/Radial/RadialHeight.lean#L54)
- [`ContinuousFlexibility.Radial.polarDiscriminant_radialHeightField`](../ContinuousFlexibility/Radial/RadialHeight.lean#L61)
- [`ContinuousFlexibility.Radial.polarCurvatureNumerator_radialHeightField`](../ContinuousFlexibility/Radial/RadialHeight.lean#L70)
- [`ContinuousFlexibility.Radial.polarCoordinateResidual_radialHeightField`](../ContinuousFlexibility/Radial/RadialHeight.lean#L81)
- [`ContinuousFlexibility.Radial.hasDerivAt_radialSlice`](../ContinuousFlexibility/Radial/RadialHeight.lean#L89)
- [`ContinuousFlexibility.Radial.hasDerivAt_angularSlice`](../ContinuousFlexibility/Radial/RadialHeight.lean#L97)
- [`ContinuousFlexibility.Radial.radialPDE_eq_polar_jets`](../ContinuousFlexibility/Radial/RadialHeight.lean#L107)
- [`ContinuousFlexibility.Radial.angularPartial_heightAngular_eq`](../ContinuousFlexibility/Radial/RadialHeight.lean#L137)
- [`ContinuousFlexibility.Radial.polarCurvatureNumeratorVariation_radialHeightField`](../ContinuousFlexibility/Radial/RadialHeight.lean#L149)
- [`ContinuousFlexibility.Radial.polarResidualVariation_radialHeightField`](../ContinuousFlexibility/Radial/RadialHeight.lean#L163)
- [`ContinuousFlexibility.Radial.hasDerivAt_radialHeightResidual`](../ContinuousFlexibility/Radial/RadialHeight.lean#L176)
- [`ContinuousFlexibility.Radial.normalizedHeightResidual_radialHeightField_zero`](../ContinuousFlexibility/Radial/RadialHeight.lean#L191)


<a id="s05"></a>
## S05 固定类型的真实修正算子

**状态：** 已有部分已编译子结果。**分支：** 标量方程。主定理必要节点。

**数学陈述：** 在共同正性邻域，真实 D_uF_qη= L̄η+q∂θ(B A ηθ)，B=E/(rQ)；L̄具有固定转型圆、同一法向通量、形式对称并杀常数，负区特征速度具有根点平方根退化。

**证明提纲：** 将S02代数代入真实变分；逐项证明散度误差、测试函数配对和端通量；推导特征斜率。

**直接依赖：** [S02](#s02), [S03](#s03), [S04](#s04)

**论文定位：** [03-height-equation.tex:336–375](../paper/flexible-surface-rewrite/03-height-equation.tex#L336)，`lem:type-completion`

**目标文件：** `ContinuousFlexibility/Scalar/S05.lean`（节点组织目标；实际已存在的证明文件见下方，整个节点尚未完成）

**验收条件：**

- 对称性列出测试函数/端点条件
- 修正误差对独立残差和增量双线性
- 类型是w'变号而非w变号

**已经完成的子结果：**

- 实际高度系数的修正行列式及正负零集恰对应w的实际导数
- 真实系数C∞与真实HasDerivAt修正误差；规范化源给精确q∂θ(B A ηθ)误差
- 真实Green恒等式、普通dr dθ下形式对称，周期与径向测试边界条件明确

**仍待闭合的义务：**

- 加权端点下实际A、B、修正C的光滑延拓与共同闭域
- 根点特征速度与固定类型逆所需定量估计；不得在平坦端点假设Q非零

**现有 Lean 证明：**

[TypeCorrection.lean](../ContinuousFlexibility/Scalar/TypeCorrection.lean)：

- [`ContinuousFlexibility.polarCorrectedC_eq_residual_correction`](../ContinuousFlexibility/Scalar/TypeCorrection.lean#L36)
- [`ContinuousFlexibility.polarCorrectedC_eq_typeB`](../ContinuousFlexibility/Scalar/TypeCorrection.lean#L42)
- [`ContinuousFlexibility.polarCorrectedC_eq_typeB_total`](../ContinuousFlexibility/Scalar/TypeCorrection.lean#L53)
- [`ContinuousFlexibility.polar_corrected_determinant`](../ContinuousFlexibility/Scalar/TypeCorrection.lean#L64)
- [`ContinuousFlexibility.polar_corrected_determinant_zero_iff`](../ContinuousFlexibility/Scalar/TypeCorrection.lean#L80)
- [`ContinuousFlexibility.polar_corrected_determinant_pos_iff`](../ContinuousFlexibility/Scalar/TypeCorrection.lean#L91)
- [`ContinuousFlexibility.polar_corrected_determinant_neg_iff`](../ContinuousFlexibility/Scalar/TypeCorrection.lean#L103)
- [`ContinuousFlexibility.heightCorrectedDivergence_const`](../ContinuousFlexibility/Scalar/TypeCorrection.lean#L117)
- [`ContinuousFlexibility.heightLinearizedDivergence_eq_corrected`](../ContinuousFlexibility/Scalar/TypeCorrection.lean#L124)
- [`ContinuousFlexibility.contDiffAt_heightLinearCoefficients`](../ContinuousFlexibility/Scalar/TypeCorrection.lean#L148)
- [`ContinuousFlexibility.heightLinearizedDivergence_eq_corrected_of_smooth`](../ContinuousFlexibility/Scalar/TypeCorrection.lean#L193)
- [`ContinuousFlexibility.hasDerivAt_radialScaledResidual_corrected`](../ContinuousFlexibility/Scalar/TypeCorrection.lean#L210)
- [`ContinuousFlexibility.parameter_mul_normalizedHeightResidual`](../ContinuousFlexibility/Scalar/TypeCorrection.lean#L224)
- [`ContinuousFlexibility.heightLinearizedDivergence_eq_corrected_normalized`](../ContinuousFlexibility/Scalar/TypeCorrection.lean#L236)

[GreenIdentity.lean](../ContinuousFlexibility/Scalar/GreenIdentity.lean)：

- [`ContinuousFlexibility.contDiffAt_symmetricNormalFlux`](../ContinuousFlexibility/Scalar/GreenIdentity.lean#L46)
- [`ContinuousFlexibility.contDiffAt_symmetricAngularFlux`](../ContinuousFlexibility/Scalar/GreenIdentity.lean#L54)
- [`ContinuousFlexibility.contDiffAt_symmetricGreenForm`](../ContinuousFlexibility/Scalar/GreenIdentity.lean#L61)
- [`ContinuousFlexibility.symmetric_green_identity`](../ContinuousFlexibility/Scalar/GreenIdentity.lean#L75)
- [`ContinuousFlexibility.symmetric_green_identity_exterior`](../ContinuousFlexibility/Scalar/GreenIdentity.lean#L102)
- [`ContinuousFlexibility.integral_symmetric_green_eq_zero`](../ContinuousFlexibility/Scalar/GreenIdentity.lean#L129)
- [`ContinuousFlexibility.greenNormalFlux_eq_zero_of_robin`](../ContinuousFlexibility/Scalar/GreenIdentity.lean#L168)
- [`ContinuousFlexibility.greenNormalFlux_eq_zero_of_dirichlet`](../ContinuousFlexibility/Scalar/GreenIdentity.lean#L177)
- [`ContinuousFlexibility.periodic_greenAngularFlux`](../ContinuousFlexibility/Scalar/GreenIdentity.lean#L183)
- [`ContinuousFlexibility.integral_symmetric_green_eq_zero_of_periodic`](../ContinuousFlexibility/Scalar/GreenIdentity.lean#L196)
- [`ContinuousFlexibility.periodic_heightCorrectedCoefficients`](../ContinuousFlexibility/Scalar/GreenIdentity.lean#L219)
- [`ContinuousFlexibility.heightCorrected_green_identity`](../ContinuousFlexibility/Scalar/GreenIdentity.lean#L244)
- [`ContinuousFlexibility.heightCorrected_normalFlux_eq_zero_of_boundary_jets`](../ContinuousFlexibility/Scalar/GreenIdentity.lean#L261)
- [`ContinuousFlexibility.integral_heightCorrected_green_eq_zero`](../ContinuousFlexibility/Scalar/GreenIdentity.lean#L274)
- [`ContinuousFlexibility.integral_heightCorrected_green_eq_zero_of_admissible`](../ContinuousFlexibility/Scalar/GreenIdentity.lean#L297)
- [`ContinuousFlexibility.integral_heightCorrected_green_eq_zero_of_boundary_jets`](../ContinuousFlexibility/Scalar/GreenIdentity.lean#L327)


<a id="r02"></a>
## R02 Liouville变换与径向实现

**状态：** 已有部分已编译子结果。**分支：** 径向参考。主定理必要节点。

**数学陈述：** 在半径方程和 r_X=v>0 下，严格推导由谱势到径向轮廓的Liouville变换，给出真实L_j的共轭表达式、源因子和两种测度。

**证明提纲：** 先证明换元微分恒等式和可逆坐标，再将各模型的r_X>0作为实际构造结论实例化。

**直接依赖：** [R01](#r01)

**论文定位：** [04-designing-the-profile.tex:118–137](../paper/flexible-surface-rewrite/04-designing-the-profile.tex#L118)，`eq:rad-eq-sc0`；[04-designing-the-profile.tex:272–301](../paper/flexible-surface-rewrite/04-designing-the-profile.tex#L272)，`eq:rad-eq-ha2`

**目标文件：** `ContinuousFlexibility/Radial/R02.lean`（节点组织目标；实际已存在的证明文件见下方，整个节点尚未完成）

**验收条件：**

- 不得把r_X>0假设当作模型构造
- 保留dr源配对与Hilbert谱测度的区别

**已经完成的子结果：**

- 真正Liouville微分恒等式和非齐次源因子
- P=s²及sqrtP潜势识别、普通dr与谱密度的真实有限区间积分替换
- 精确 generalLiouville_R02_statement 已通过。对任意满足假设的实际 R,s，构造开值域逆坐标、实际轮廓与原函数，验证径向共轭、源因子、Jacobian、两个真实 Hilbert 权及 ordinary dr 源配对。中央模型的正 R′ 已另从实际构造证明。
- 精确 generalLiouville_R02_statement 已通过。对任意满足假设的实际 R,s，已验证开值域逆坐标、轮廓、原函数、径向共轭、源因子、Jacobian、两种 Hilbert 权及 ordinary dr 源配对；一般光滑 ψ 的拉回只需在实际开值域光滑。中央模型正 R′ 已另证。
- 通用 R02 精确目标与实际开值域局部共轭均已通过。对同一个满足有限 Morse ODE 初值、正半径与正速度的真实保留单元，已实例化光滑逆、径向 Jacobi 与 Morse 方程的精确共轭及对应源项。

**仍待闭合的义务：**

- 将已证的有限单元算子恒等式和变换用于完整频率匹配与实际径向逆。

**现有 Lean 证明：**

[Liouville.lean](../ContinuousFlexibility/Radial/Liouville.lean)：

- [`ContinuousFlexibility.Radial.liouville_flux_at`](../ContinuousFlexibility/Radial/Liouville.lean#L35)
- [`ContinuousFlexibility.Radial.radialJacobi_liouville`](../ContinuousFlexibility/Radial/Liouville.lean#L61)
- [`ContinuousFlexibility.Radial.deriv_liouvilleDensity`](../ContinuousFlexibility/Radial/Liouville.lean#L119)
- [`ContinuousFlexibility.Radial.liouville_density_log_derivative`](../ContinuousFlexibility/Radial/Liouville.lean#L127)
- [`ContinuousFlexibility.Radial.liouvilleRho_eq_density`](../ContinuousFlexibility/Radial/Liouville.lean#L135)
- [`ContinuousFlexibility.Radial.liouvilleV0_eq_sqrtDensity`](../ContinuousFlexibility/Radial/Liouville.lean#L145)
- [`ContinuousFlexibility.Radial.liouville_forcing_iff`](../ContinuousFlexibility/Radial/Liouville.lean#L162)
- [`ContinuousFlexibility.Radial.liouville_source_pairing_density`](../ContinuousFlexibility/Radial/Liouville.lean#L181)
- [`ContinuousFlexibility.Radial.liouville_hilbert_density`](../ContinuousFlexibility/Radial/Liouville.lean#L189)

[RadiusChange.lean](../ContinuousFlexibility/Radial/RadiusChange.lean)：

- [`ContinuousFlexibility.Radial.liouville_source_pairing_integral`](../ContinuousFlexibility/Radial/RadiusChange.lean#L21)
- [`ContinuousFlexibility.Radial.liouville_hilbert_integral`](../ContinuousFlexibility/Radial/RadiusChange.lean#L38)

[GeneralLiouvilleTransport.lean](../ContinuousFlexibility/Radial/GeneralLiouvilleTransport.lean)：

- [`ContinuousFlexibility.Radial.generalLiouville_strictMono`](../ContinuousFlexibility/Radial/GeneralLiouvilleTransport.lean#L43)
- [`ContinuousFlexibility.Radial.generalLiouvilleCoordinate_apply`](../ContinuousFlexibility/Radial/GeneralLiouvilleTransport.lean#L46)
- [`ContinuousFlexibility.Radial.generalLiouvilleCoordinate_right`](../ContinuousFlexibility/Radial/GeneralLiouvilleTransport.lean#L50)
- [`ContinuousFlexibility.Radial.generalLiouvilleCoordinate_hasStrictDerivAt`](../ContinuousFlexibility/Radial/GeneralLiouvilleTransport.lean#L54)
- [`ContinuousFlexibility.Radial.generalLiouvilleCoordinate_contDiffAt`](../ContinuousFlexibility/Radial/GeneralLiouvilleTransport.lean#L60)
- [`ContinuousFlexibility.Radial.generalLiouville_isOpenEmbedding`](../ContinuousFlexibility/Radial/GeneralLiouvilleTransport.lean#L78)
- [`ContinuousFlexibility.Radial.generalLiouville_measurableEmbedding`](../ContinuousFlexibility/Radial/GeneralLiouvilleTransport.lean#L86)
- [`ContinuousFlexibility.Radial.generalLiouvilleProfile_apply`](../ContinuousFlexibility/Radial/GeneralLiouvilleTransport.lean#L91)
- [`ContinuousFlexibility.Radial.generalLiouvilleProfile_contDiffAt`](../ContinuousFlexibility/Radial/GeneralLiouvilleTransport.lean#L95)
- [`ContinuousFlexibility.Radial.generalLiouvillePrimitiveIntegrand_contDiff`](../ContinuousFlexibility/Radial/GeneralLiouvilleTransport.lean#L102)
- [`ContinuousFlexibility.Radial.generalLiouvilleModelPrimitive_hasDerivAt`](../ContinuousFlexibility/Radial/GeneralLiouvilleTransport.lean#L107)
- [`ContinuousFlexibility.Radial.generalLiouvilleModelPrimitive_contDiff`](../ContinuousFlexibility/Radial/GeneralLiouvilleTransport.lean#L115)
- [`ContinuousFlexibility.Radial.generalLiouvillePrimitive_contDiffAt`](../ContinuousFlexibility/Radial/GeneralLiouvilleTransport.lean#L126)
- [`ContinuousFlexibility.Radial.generalLiouvillePrimitive_hasDerivAt`](../ContinuousFlexibility/Radial/GeneralLiouvilleTransport.lean#L133)
- [`ContinuousFlexibility.Radial.generalLiouville_radialJacobi`](../ContinuousFlexibility/Radial/GeneralLiouvilleTransport.lean#L150)
- [`ContinuousFlexibility.Radial.generalLiouvilleModelDensity_continuous`](../ContinuousFlexibility/Radial/GeneralLiouvilleTransport.lean#L197)
- [`ContinuousFlexibility.Radial.generalLiouville_density`](../ContinuousFlexibility/Radial/GeneralLiouvilleTransport.lean#L203)
- [`ContinuousFlexibility.Radial.generalLiouville_lintegral_change`](../ContinuousFlexibility/Radial/GeneralLiouvilleTransport.lean#L211)
- [`ContinuousFlexibility.Radial.generalLiouville_integrable_iff`](../ContinuousFlexibility/Radial/GeneralLiouvilleTransport.lean#L219)
- [`ContinuousFlexibility.Radial.generalLiouville_integral_change`](../ContinuousFlexibility/Radial/GeneralLiouvilleTransport.lean#L228)
- [`ContinuousFlexibility.Radial.generalLiouville_map_measure`](../ContinuousFlexibility/Radial/GeneralLiouvilleTransport.lean#L236)
- [`ContinuousFlexibility.Radial.generalLiouvillePullbackMeasure_eq`](../ContinuousFlexibility/Radial/GeneralLiouvilleTransport.lean#L263)
- [`ContinuousFlexibility.Radial.generalLiouville_memLp_iff`](../ContinuousFlexibility/Radial/GeneralLiouvilleTransport.lean#L319)
- [`ContinuousFlexibility.Radial.generalLiouville_spectral_integral`](../ContinuousFlexibility/Radial/GeneralLiouvilleTransport.lean#L331)
- [`ContinuousFlexibility.Radial.generalLiouville_pullback_ae`](../ContinuousFlexibility/Radial/GeneralLiouvilleTransport.lean#L344)
- [`ContinuousFlexibility.Radial.generalLiouville_pushforward_ae`](../ContinuousFlexibility/Radial/GeneralLiouvilleTransport.lean#L360)
- [`ContinuousFlexibility.Radial.generalLiouvillePullback_ae`](../ContinuousFlexibility/Radial/GeneralLiouvilleTransport.lean#L433)
- [`ContinuousFlexibility.Radial.generalLiouvillePullback_surjective`](../ContinuousFlexibility/Radial/GeneralLiouvilleTransport.lean#L441)
- [`ContinuousFlexibility.Radial.generalLiouvilleTransport_symm_ae`](../ContinuousFlexibility/Radial/GeneralLiouvilleTransport.lean#L477)
- [`ContinuousFlexibility.Radial.generalLiouvilleTransport_ae`](../ContinuousFlexibility/Radial/GeneralLiouvilleTransport.lean#L485)
- [`ContinuousFlexibility.Radial.generalLiouville_source_pairing`](../ContinuousFlexibility/Radial/GeneralLiouvilleTransport.lean#L500)
- [`ContinuousFlexibility.Radial.generalLiouville_fullTransport`](../ContinuousFlexibility/Radial/GeneralLiouvilleTransport.lean#L516)
- [`ContinuousFlexibility.Radial.generalLiouville_R02_statement`](../ContinuousFlexibility/Radial/GeneralLiouvilleTransport.lean#L527)

[GeneralLiouvilleLocalConjugacy.lean](../ContinuousFlexibility/Radial/GeneralLiouvilleLocalConjugacy.lean)：

- [`ContinuousFlexibility.Radial.generalLiouvilleRadialHeight_apply`](../ContinuousFlexibility/Radial/GeneralLiouvilleLocalConjugacy.lean#L27)
- [`ContinuousFlexibility.Radial.generalLiouvilleRadialHeight_contDiffAt`](../ContinuousFlexibility/Radial/GeneralLiouvilleLocalConjugacy.lean#L32)
- [`ContinuousFlexibility.Radial.generalLiouvilleRadialHeight_contDiffOn`](../ContinuousFlexibility/Radial/GeneralLiouvilleLocalConjugacy.lean#L41)
- [`ContinuousFlexibility.Radial.generalLiouvilleRadialHeight_radialJacobi`](../ContinuousFlexibility/Radial/GeneralLiouvilleLocalConjugacy.lean#L50)
- [`ContinuousFlexibility.Radial.generalLiouvilleRadialHeight_forcing_iff`](../ContinuousFlexibility/Radial/GeneralLiouvilleLocalConjugacy.lean#L74)

[MorseCellLiouville.lean](../ContinuousFlexibility/Radial/MorseCellLiouville.lean)：

- [`ContinuousFlexibility.Radial.morseCellModelCoordinate_contDiffAt`](../ContinuousFlexibility/Radial/MorseCellLiouville.lean#L23)
- [`ContinuousFlexibility.Radial.morseCellRadialHeight_contDiffOn`](../ContinuousFlexibility/Radial/MorseCellLiouville.lean#L44)
- [`ContinuousFlexibility.Radial.morseCell_radialJacobi`](../ContinuousFlexibility/Radial/MorseCellLiouville.lean#L56)
- [`ContinuousFlexibility.Radial.morseCell_radialJacobi_forcing_iff`](../ContinuousFlexibility/Radial/MorseCellLiouville.lean#L114)
- [`ContinuousFlexibility.Radial.exists_morseRetainedCell_radialJacobi`](../ContinuousFlexibility/Radial/MorseCellLiouville.lean#L134)


<a id="r03"></a>
## R03 中央谐振子模型的完整实现

**状态：** 已有部分已编译子结果。**分支：** 径向参考。主定理必要节点。

**数学陈述：** 中央模型的闭二次型实现具有文中完整谱；二模恰一维零核，其余偶模有所需零能隙；得到正递增半径、端渐近、约化逆和双侧加权resolvent估计。另证明中央负区旅行角T_c=π/(2√2)及全部k≥1上的|sin(kT_c)|≥c/k。

**证明提纲：** 形式化谱实现或证明同样充分的零能估计；将能级算术、谱全集、核维数、加权逆界分为子引理。

**直接依赖：** [R02](#r02)

**论文定位：** [04-designing-the-profile.tex:177–301](../paper/flexible-surface-rewrite/04-designing-the-profile.tex#L177)，`eq:central-spectrum-new`

**目标文件：** `ContinuousFlexibility/Radial/R03.lean`（节点组织目标；实际已存在的证明文件见下方，整个节点尚未完成）

**验收条件：**

- 候选能级间隔不等于完整谱证明
- 约化逆保留二模边框
- 实际半径/权函数与抽象谱模型联系完整

**已经完成的子结果：**

- 实际Hermite完整基与微分闭图、sqrt-potential闭能量域/光滑core/form图、正确全源径向compact-test闭图及其核心闭包、μ-Hilbert传输和普通dr分布换元、真实ν双侧约化逆，以及两端全阶误差和材料导数估计已编译。完整R03目标合取尚待精确桥接。
- 精确 centralR03_statement 的全部十三项已通过：实际正增半径与简单转点、两端全阶、真实闭能量域与完整 Hermite 微分图、自然核/约化逆及双侧权界、普通 dr 平坦测试、辅助二模边框与旅行角小除数。

**仍待闭合的义务：**

- 精确 R03Statement 已证明；主蓝图节点的全部模型先决验收依赖 R02，且本结果不提供 R05–R12 的积聚径向参考或最终度量导数边框。

**优先核查程度：** high（任务风险标记，不是已发现错误）

**现有 Lean 证明：**

[CentralSmallDivisor.lean](../ContinuousFlexibility/Radial/CentralSmallDivisor.lean)：

- [`ContinuousFlexibility.Radial.centralTravelAngle_eq`](../ContinuousFlexibility/Radial/CentralSmallDivisor.lean#L25)
- [`ContinuousFlexibility.Radial.central_integer_norm_ne_zero`](../ContinuousFlexibility/Radial/CentralSmallDivisor.lean#L36)
- [`ContinuousFlexibility.Radial.central_phase_distance_lower_bound`](../ContinuousFlexibility/Radial/CentralSmallDivisor.lean#L61)
- [`ContinuousFlexibility.Radial.twice_distance_round_le_abs_sin_pi`](../ContinuousFlexibility/Radial/CentralSmallDivisor.lean#L101)
- [`ContinuousFlexibility.Radial.central_sine_small_divisor`](../ContinuousFlexibility/Radial/CentralSmallDivisor.lean#L122)
- [`ContinuousFlexibility.Radial.exists_central_sine_small_divisor`](../ContinuousFlexibility/Radial/CentralSmallDivisor.lean#L139)

[CentralTravelAngle.lean](../ContinuousFlexibility/Radial/CentralTravelAngle.lean)：

- [`ContinuousFlexibility.Radial.quadratic_positive_component`](../ContinuousFlexibility/Radial/CentralTravelAngle.lean#L25)
- [`ContinuousFlexibility.Radial.quadratic_travel_integrand_scale`](../ContinuousFlexibility/Radial/CentralTravelAngle.lean#L31)
- [`ContinuousFlexibility.Radial.quadraticTravelIntegral_eq`](../ContinuousFlexibility/Radial/CentralTravelAngle.lean#L39)
- [`ContinuousFlexibility.Radial.quadraticTravelIntegral_pos`](../ContinuousFlexibility/Radial/CentralTravelAngle.lean#L55)
- [`ContinuousFlexibility.Radial.centralOscillatorA_pos`](../ContinuousFlexibility/Radial/CentralTravelAngle.lean#L63)
- [`ContinuousFlexibility.Radial.central_travel_integral_eq`](../ContinuousFlexibility/Radial/CentralTravelAngle.lean#L69)
- [`ContinuousFlexibility.Radial.central_travel_integral_small_divisor`](../ContinuousFlexibility/Radial/CentralTravelAngle.lean#L78)
- [`ContinuousFlexibility.Radial.exists_central_travel_integral_small_divisor`](../ContinuousFlexibility/Radial/CentralTravelAngle.lean#L84)

[GaussianLaplace.lean](../ContinuousFlexibility/Radial/GaussianLaplace.lean)：

- [`ContinuousFlexibility.Radial.gaussianLaplaceKernel_pos`](../ContinuousFlexibility/Radial/GaussianLaplace.lean#L33)
- [`ContinuousFlexibility.Radial.continuousOn_gaussianLaplaceKernel`](../ContinuousFlexibility/Radial/GaussianLaplace.lean#L37)
- [`ContinuousFlexibility.Radial.gaussianLaplaceKernel_le_gamma`](../ContinuousFlexibility/Radial/GaussianLaplace.lean#L45)
- [`ContinuousFlexibility.Radial.integrableOn_gaussianLaplaceKernel`](../ContinuousFlexibility/Radial/GaussianLaplace.lean#L56)
- [`ContinuousFlexibility.Radial.gaussianLaplaceMoment_pos`](../ContinuousFlexibility/Radial/GaussianLaplace.lean#L64)
- [`ContinuousFlexibility.Radial.gaussianLaplaceKernel_succ`](../ContinuousFlexibility/Radial/GaussianLaplace.lean#L76)
- [`ContinuousFlexibility.Radial.gaussianLaplaceKernel_mono`](../ContinuousFlexibility/Radial/GaussianLaplace.lean#L85)
- [`ContinuousFlexibility.Radial.hasDerivAt_gaussianLaplaceKernel_parameter`](../ContinuousFlexibility/Radial/GaussianLaplace.lean#L92)
- [`ContinuousFlexibility.Radial.hasDerivAt_gaussianLaplaceMoment`](../ContinuousFlexibility/Radial/GaussianLaplace.lean#L109)
- [`ContinuousFlexibility.Radial.deriv_gaussianLaplaceMoment`](../ContinuousFlexibility/Radial/GaussianLaplace.lean#L137)
- [`ContinuousFlexibility.Radial.contDiff_gaussianLaplaceMoment`](../ContinuousFlexibility/Radial/GaussianLaplace.lean#L142)
- [`ContinuousFlexibility.Radial.hasDerivAt_gaussianLaplaceKernel_variable`](../ContinuousFlexibility/Radial/GaussianLaplace.lean#L164)
- [`ContinuousFlexibility.Radial.gaussianLaplaceMoment_recurrence`](../ContinuousFlexibility/Radial/GaussianLaplace.lean#L182)

[CentralRadius.lean](../ContinuousFlexibility/Radial/CentralRadius.lean)：

- [`ContinuousFlexibility.Radial.gaussianLaplacePsi_pos`](../ContinuousFlexibility/Radial/CentralRadius.lean#L29)
- [`ContinuousFlexibility.Radial.contDiff_gaussianLaplacePsi`](../ContinuousFlexibility/Radial/CentralRadius.lean#L33)
- [`ContinuousFlexibility.Radial.hasDerivAt_gaussianLaplacePsi`](../ContinuousFlexibility/Radial/CentralRadius.lean#L37)
- [`ContinuousFlexibility.Radial.deriv_gaussianLaplacePsi`](../ContinuousFlexibility/Radial/CentralRadius.lean#L49)
- [`ContinuousFlexibility.Radial.hasDerivAt_deriv_gaussianLaplacePsi`](../ContinuousFlexibility/Radial/CentralRadius.lean#L56)
- [`ContinuousFlexibility.Radial.gaussianLaplacePsi_ode`](../ContinuousFlexibility/Radial/CentralRadius.lean#L77)
- [`ContinuousFlexibility.Radial.deriv_gaussianLaplacePsi_pos_of_nonpos`](../ContinuousFlexibility/Radial/CentralRadius.lean#L82)
- [`ContinuousFlexibility.Radial.deriv_gaussianLaplacePsi_pos`](../ContinuousFlexibility/Radial/CentralRadius.lean#L94)
- [`ContinuousFlexibility.Radial.centralOscillatorA_gt_two_thirds`](../ContinuousFlexibility/Radial/CentralRadius.lean#L113)
- [`ContinuousFlexibility.Radial.centralRadiusA_pos`](../ContinuousFlexibility/Radial/CentralRadius.lean#L119)
- [`ContinuousFlexibility.Radial.centralRadiusA_sq`](../ContinuousFlexibility/Radial/CentralRadius.lean#L124)
- [`ContinuousFlexibility.Radial.centralRadiusC_pos`](../ContinuousFlexibility/Radial/CentralRadius.lean#L128)
- [`ContinuousFlexibility.Radial.centralRadiusAlpha_gt_half`](../ContinuousFlexibility/Radial/CentralRadius.lean#L132)
- [`ContinuousFlexibility.Radial.centralRadiusPsi_pos`](../ContinuousFlexibility/Radial/CentralRadius.lean#L144)
- [`ContinuousFlexibility.Radial.deriv_centralRadiusPsi_pos`](../ContinuousFlexibility/Radial/CentralRadius.lean#L147)
- [`ContinuousFlexibility.Radial.contDiff_centralRadiusPsi`](../ContinuousFlexibility/Radial/CentralRadius.lean#L150)
- [`ContinuousFlexibility.Radial.centralRadiusPsi_ode`](../ContinuousFlexibility/Radial/CentralRadius.lean#L153)
- [`ContinuousFlexibility.Radial.contDiff_centralRadius`](../ContinuousFlexibility/Radial/CentralRadius.lean#L162)
- [`ContinuousFlexibility.Radial.centralRadius_pos`](../ContinuousFlexibility/Radial/CentralRadius.lean#L165)
- [`ContinuousFlexibility.Radial.hasDerivAt_centralRadius`](../ContinuousFlexibility/Radial/CentralRadius.lean#L168)
- [`ContinuousFlexibility.Radial.deriv_centralRadius`](../ContinuousFlexibility/Radial/CentralRadius.lean#L179)
- [`ContinuousFlexibility.Radial.deriv_centralRadius_gt`](../ContinuousFlexibility/Radial/CentralRadius.lean#L186)
- [`ContinuousFlexibility.Radial.deriv_centralRadius_pos`](../ContinuousFlexibility/Radial/CentralRadius.lean#L193)
- [`ContinuousFlexibility.Radial.strictMono_centralRadius`](../ContinuousFlexibility/Radial/CentralRadius.lean#L196)
- [`ContinuousFlexibility.Radial.centralRadius_ode`](../ContinuousFlexibility/Radial/CentralRadius.lean#L200)
- [`ContinuousFlexibility.Radial.contDiff_centralDensityRoot`](../ContinuousFlexibility/Radial/CentralRadius.lean#L222)
- [`ContinuousFlexibility.Radial.centralDensityRoot_pos`](../ContinuousFlexibility/Radial/CentralRadius.lean#L225)
- [`ContinuousFlexibility.Radial.hasDerivAt_centralDensityRoot`](../ContinuousFlexibility/Radial/CentralRadius.lean#L227)
- [`ContinuousFlexibility.Radial.deriv_centralDensityRoot`](../ContinuousFlexibility/Radial/CentralRadius.lean#L235)
- [`ContinuousFlexibility.Radial.deriv_deriv_centralDensityRoot`](../ContinuousFlexibility/Radial/CentralRadius.lean#L239)
- [`ContinuousFlexibility.Radial.centralRadius_liouvilleRho`](../ContinuousFlexibility/Radial/CentralRadius.lean#L249)
- [`ContinuousFlexibility.Radial.centralDensityRoot_liouvilleV0`](../ContinuousFlexibility/Radial/CentralRadius.lean#L259)
- [`ContinuousFlexibility.Radial.central_liouvilleSchrodinger`](../ContinuousFlexibility/Radial/CentralRadius.lean#L267)

[CentralRadiusMetric.lean](../ContinuousFlexibility/Radial/CentralRadiusMetric.lean)：

- [`ContinuousFlexibility.Radial.strictMono_gaussianLaplaceMoment`](../ContinuousFlexibility/Radial/CentralRadiusMetric.lean#L24)
- [`ContinuousFlexibility.Radial.strictMono_centralRadiusPsi`](../ContinuousFlexibility/Radial/CentralRadiusMetric.lean#L32)
- [`ContinuousFlexibility.Radial.centralRadius_le_exp_of_nonpos`](../ContinuousFlexibility/Radial/CentralRadiusMetric.lean#L36)
- [`ContinuousFlexibility.Radial.tendsto_centralRadius_atBot`](../ContinuousFlexibility/Radial/CentralRadiusMetric.lean#L51)
- [`ContinuousFlexibility.Radial.tendsto_centralRadius_atTop`](../ContinuousFlexibility/Radial/CentralRadiusMetric.lean#L58)
- [`ContinuousFlexibility.Radial.range_centralRadius`](../ContinuousFlexibility/Radial/CentralRadiusMetric.lean#L65)
- [`ContinuousFlexibility.Radial.centralModelCoordinate_radius`](../ContinuousFlexibility/Radial/CentralRadiusMetric.lean#L80)
- [`ContinuousFlexibility.Radial.centralRadius_modelCoordinate`](../ContinuousFlexibility/Radial/CentralRadiusMetric.lean#L84)
- [`ContinuousFlexibility.Radial.hasStrictDerivAt_centralModelCoordinate`](../ContinuousFlexibility/Radial/CentralRadiusMetric.lean#L90)
- [`ContinuousFlexibility.Radial.contDiffAt_centralModelCoordinate`](../ContinuousFlexibility/Radial/CentralRadiusMetric.lean#L96)
- [`ContinuousFlexibility.Radial.centralRadialProfile_pullback`](../ContinuousFlexibility/Radial/CentralRadiusMetric.lean#L120)
- [`ContinuousFlexibility.Radial.contDiff_centralPulledProfile`](../ContinuousFlexibility/Radial/CentralRadiusMetric.lean#L125)
- [`ContinuousFlexibility.Radial.contDiffAt_centralRadialProfile`](../ContinuousFlexibility/Radial/CentralRadiusMetric.lean#L129)
- [`ContinuousFlexibility.Radial.centralRadialProfile_pos`](../ContinuousFlexibility/Radial/CentralRadiusMetric.lean#L133)
- [`ContinuousFlexibility.Radial.contDiffOn_centralRadialProfile`](../ContinuousFlexibility/Radial/CentralRadiusMetric.lean#L139)

[CentralModel.lean](../ContinuousFlexibility/Radial/CentralModel.lean)：

- [`ContinuousFlexibility.Radial.centralRadialProfile_deriv_scaled`](../ContinuousFlexibility/Radial/CentralModel.lean#L21)
- [`ContinuousFlexibility.Radial.centralRadialProfile_deriv_zero_iff`](../ContinuousFlexibility/Radial/CentralModel.lean#L48)
- [`ContinuousFlexibility.Radial.centralRadialProfile_deriv_pos_iff`](../ContinuousFlexibility/Radial/CentralModel.lean#L61)
- [`ContinuousFlexibility.Radial.centralRadialProfile_deriv_neg_iff`](../ContinuousFlexibility/Radial/CentralModel.lean#L68)
- [`ContinuousFlexibility.Radial.contDiff_centralOscillatorGround`](../ContinuousFlexibility/Radial/CentralModel.lean#L86)
- [`ContinuousFlexibility.Radial.hasDerivAt_centralOscillatorGround`](../ContinuousFlexibility/Radial/CentralModel.lean#L89)
- [`ContinuousFlexibility.Radial.deriv_centralOscillatorGround`](../ContinuousFlexibility/Radial/CentralModel.lean#L97)
- [`ContinuousFlexibility.Radial.deriv_deriv_centralOscillatorGround`](../ContinuousFlexibility/Radial/CentralModel.lean#L101)
- [`ContinuousFlexibility.Radial.centralOscillatorGround_liouville`](../ContinuousFlexibility/Radial/CentralModel.lean#L111)
- [`ContinuousFlexibility.Radial.centralKernelHeight_pos`](../ContinuousFlexibility/Radial/CentralModel.lean#L119)
- [`ContinuousFlexibility.Radial.centralKernelHeight_pullback`](../ContinuousFlexibility/Radial/CentralModel.lean#L121)
- [`ContinuousFlexibility.Radial.centralKernelHeight_liouville_pullback`](../ContinuousFlexibility/Radial/CentralModel.lean#L125)
- [`ContinuousFlexibility.Radial.contDiffAt_centralKernelHeight`](../ContinuousFlexibility/Radial/CentralModel.lean#L133)
- [`ContinuousFlexibility.Radial.radialJacobi_centralKernel`](../ContinuousFlexibility/Radial/CentralModel.lean#L140)

[OscillatorKernel.lean](../ContinuousFlexibility/Radial/OscillatorKernel.lean)：

- [`ContinuousFlexibility.Radial.contDiff_oscillatorGround`](../ContinuousFlexibility/Radial/OscillatorKernel.lean#L41)
- [`ContinuousFlexibility.Radial.oscillatorGround_pos`](../ContinuousFlexibility/Radial/OscillatorKernel.lean#L44)
- [`ContinuousFlexibility.Radial.oscillatorGround_zero`](../ContinuousFlexibility/Radial/OscillatorKernel.lean#L46)
- [`ContinuousFlexibility.Radial.hasDerivAt_oscillatorGround`](../ContinuousFlexibility/Radial/OscillatorKernel.lean#L49)
- [`ContinuousFlexibility.Radial.deriv_oscillatorGround`](../ContinuousFlexibility/Radial/OscillatorKernel.lean#L57)
- [`ContinuousFlexibility.Radial.deriv_deriv_oscillatorGround`](../ContinuousFlexibility/Radial/OscillatorKernel.lean#L61)
- [`ContinuousFlexibility.Radial.oscillatorGround_equation`](../ContinuousFlexibility/Radial/OscillatorKernel.lean#L72)
- [`ContinuousFlexibility.Radial.eq_exp_sq_of_hasDerivAt_linear`](../ContinuousFlexibility/Radial/OscillatorKernel.lean#L79)
- [`ContinuousFlexibility.Radial.zero_coefficient_of_memLp_exp_sq`](../ContinuousFlexibility/Radial/OscillatorKernel.lean#L101)
- [`ContinuousFlexibility.Radial.hasDerivAt_oscillatorAnnihilation`](../ContinuousFlexibility/Radial/OscillatorKernel.lean#L117)
- [`ContinuousFlexibility.Radial.memLp_oscillatorAnnihilation`](../ContinuousFlexibility/Radial/OscillatorKernel.lean#L133)
- [`ContinuousFlexibility.Radial.oscillatorAnnihilation_eq_zero`](../ContinuousFlexibility/Radial/OscillatorKernel.lean#L143)
- [`ContinuousFlexibility.Radial.oscillator_ground_unique`](../ContinuousFlexibility/Radial/OscillatorKernel.lean#L153)
- [`ContinuousFlexibility.Radial.oscillator_memLp_two_iff_integrable_sq`](../ContinuousFlexibility/Radial/OscillatorKernel.lean#L184)
- [`ContinuousFlexibility.Radial.oscillatorGround_sq`](../ContinuousFlexibility/Radial/OscillatorKernel.lean#L190)
- [`ContinuousFlexibility.Radial.memLp_oscillatorGround`](../ContinuousFlexibility/Radial/OscillatorKernel.lean#L197)
- [`ContinuousFlexibility.Radial.memLp_mul_oscillatorGround`](../ContinuousFlexibility/Radial/OscillatorKernel.lean#L205)
- [`ContinuousFlexibility.Radial.memLp_deriv_oscillatorGround`](../ContinuousFlexibility/Radial/OscillatorKernel.lean#L217)
- [`ContinuousFlexibility.Radial.oscillatorGround_energyDomain`](../ContinuousFlexibility/Radial/OscillatorKernel.lean#L226)
- [`ContinuousFlexibility.Radial.oscillatorEnergyDomain_const_mul`](../ContinuousFlexibility/Radial/OscillatorKernel.lean#L231)
- [`ContinuousFlexibility.Radial.oscillatorExpression_const_mul`](../ContinuousFlexibility/Radial/OscillatorKernel.lean#L244)
- [`ContinuousFlexibility.Radial.oscillator_ground_eigenspace`](../ContinuousFlexibility/Radial/OscillatorKernel.lean#L260)
- [`ContinuousFlexibility.Radial.oscillatorGround_two`](../ContinuousFlexibility/Radial/OscillatorKernel.lean#L275)
- [`ContinuousFlexibility.Radial.central_liouville_zero_iff_ground_equation`](../ContinuousFlexibility/Radial/OscillatorKernel.lean#L283)
- [`ContinuousFlexibility.Radial.central_oscillator_kernel_eigenspace`](../ContinuousFlexibility/Radial/OscillatorKernel.lean#L293)

[HermitePolynomial.lean](../ContinuousFlexibility/Radial/HermitePolynomial.lean)：

- [`ContinuousFlexibility.Radial.derivative_integerHermite_succ`](../ContinuousFlexibility/Radial/HermitePolynomial.lean#L22)
- [`ContinuousFlexibility.Radial.integerHermite_differentialEquation`](../ContinuousFlexibility/Radial/HermitePolynomial.lean#L41)
- [`ContinuousFlexibility.Radial.hermitePolynomial_zero`](../ContinuousFlexibility/Radial/HermitePolynomial.lean#L55)
- [`ContinuousFlexibility.Radial.hermitePolynomial_monic`](../ContinuousFlexibility/Radial/HermitePolynomial.lean#L58)
- [`ContinuousFlexibility.Radial.hermitePolynomial_ne_zero`](../ContinuousFlexibility/Radial/HermitePolynomial.lean#L61)
- [`ContinuousFlexibility.Radial.hermitePolynomial_differentialEquation`](../ContinuousFlexibility/Radial/HermitePolynomial.lean#L64)
- [`ContinuousFlexibility.Radial.hermitePolynomial_differentialEquation_eval`](../ContinuousFlexibility/Radial/HermitePolynomial.lean#L70)

[OscillatorSpectrum.lean](../ContinuousFlexibility/Radial/OscillatorSpectrum.lean)：

- [`ContinuousFlexibility.Radial.contDiff_polynomialGaussian`](../ContinuousFlexibility/Radial/OscillatorSpectrum.lean#L28)
- [`ContinuousFlexibility.Radial.hasDerivAt_polynomialGaussian`](../ContinuousFlexibility/Radial/OscillatorSpectrum.lean#L34)
- [`ContinuousFlexibility.Radial.deriv_polynomialGaussian`](../ContinuousFlexibility/Radial/OscillatorSpectrum.lean#L42)
- [`ContinuousFlexibility.Radial.oscillatorExpression_polynomialGaussian`](../ContinuousFlexibility/Radial/OscillatorSpectrum.lean#L47)
- [`ContinuousFlexibility.Radial.integrable_polynomialGaussian`](../ContinuousFlexibility/Radial/OscillatorSpectrum.lean#L60)
- [`ContinuousFlexibility.Radial.memLp_polynomialGaussian`](../ContinuousFlexibility/Radial/OscillatorSpectrum.lean#L78)
- [`ContinuousFlexibility.Radial.polynomialGaussian_energyDomain`](../ContinuousFlexibility/Radial/OscillatorSpectrum.lean#L90)
- [`ContinuousFlexibility.Radial.oscillatorHermiteMode_eq`](../ContinuousFlexibility/Radial/OscillatorSpectrum.lean#L106)
- [`ContinuousFlexibility.Radial.oscillatorHermiteMode_energyDomain`](../ContinuousFlexibility/Radial/OscillatorSpectrum.lean#L112)
- [`ContinuousFlexibility.Radial.oscillatorHermiteMode_equation`](../ContinuousFlexibility/Radial/OscillatorSpectrum.lean#L116)
- [`ContinuousFlexibility.Radial.integrable_mul_second_of_oscillator_eigen`](../ContinuousFlexibility/Radial/OscillatorSpectrum.lean#L135)
- [`ContinuousFlexibility.Radial.oscillator_eigen_orthogonal`](../ContinuousFlexibility/Radial/OscillatorSpectrum.lean#L152)
- [`ContinuousFlexibility.Radial.oscillatorHermiteMode_orthogonal`](../ContinuousFlexibility/Radial/OscillatorSpectrum.lean#L192)
- [`ContinuousFlexibility.Radial.oscillatorHermiteMode_nonzero`](../ContinuousFlexibility/Radial/OscillatorSpectrum.lean#L203)
- [`ContinuousFlexibility.Radial.oscillatorHermiteMode_sqIntegral_pos`](../ContinuousFlexibility/Radial/OscillatorSpectrum.lean#L223)
- [`ContinuousFlexibility.Radial.oscillatorHermiteNorm_pos`](../ContinuousFlexibility/Radial/OscillatorSpectrum.lean#L239)
- [`ContinuousFlexibility.Radial.oscillatorHermiteNorm_sq`](../ContinuousFlexibility/Radial/OscillatorSpectrum.lean#L243)
- [`ContinuousFlexibility.Radial.normalizedOscillatorHermite_energyDomain`](../ContinuousFlexibility/Radial/OscillatorSpectrum.lean#L247)
- [`ContinuousFlexibility.Radial.normalizedOscillatorHermite_equation`](../ContinuousFlexibility/Radial/OscillatorSpectrum.lean#L255)
- [`ContinuousFlexibility.Radial.integral_normalizedOscillatorHermite_mul`](../ContinuousFlexibility/Radial/OscillatorSpectrum.lean#L269)
- [`ContinuousFlexibility.Radial.central_normalizedHermite_equation`](../ContinuousFlexibility/Radial/OscillatorSpectrum.lean#L300)

[ExponentialMoments.lean](../ContinuousFlexibility/Radial/ExponentialMoments.lean)：

- [`ContinuousFlexibility.Radial.integrableExpSet_id_eq_univ`](../ContinuousFlexibility/Radial/ExponentialMoments.lean#L25)
- [`ContinuousFlexibility.Radial.differentiable_complexMGF_of_exponential_integrability`](../ContinuousFlexibility/Radial/ExponentialMoments.lean#L32)
- [`ContinuousFlexibility.Radial.measure_eq_of_all_exponential_moments`](../ContinuousFlexibility/Radial/ExponentialMoments.lean#L42)
- [`ContinuousFlexibility.Radial.integrable_posPart_mul_of_integrable_mul`](../ContinuousFlexibility/Radial/ExponentialMoments.lean#L72)
- [`ContinuousFlexibility.Radial.integrable_ofRealDensity_of_integrable_mul`](../ContinuousFlexibility/Radial/ExponentialMoments.lean#L85)
- [`ContinuousFlexibility.Radial.integral_ofRealDensity`](../ContinuousFlexibility/Radial/ExponentialMoments.lean#L94)
- [`ContinuousFlexibility.Radial.ae_eq_zero_of_exponential_moments`](../ContinuousFlexibility/Radial/ExponentialMoments.lean#L104)

[HermiteCompleteness.lean](../ContinuousFlexibility/Radial/HermiteCompleteness.lean)：

- [`ContinuousFlexibility.Radial.memLp_exponentialGaussian`](../ContinuousFlexibility/Radial/HermiteCompleteness.lean#L28)
- [`ContinuousFlexibility.Radial.hermitePolynomial_degree`](../ContinuousFlexibility/Radial/HermiteCompleteness.lean#L44)
- [`ContinuousFlexibility.Radial.oscillatorHermitePolynomial_degree`](../ContinuousFlexibility/Radial/HermiteCompleteness.lean#L49)
- [`ContinuousFlexibility.Radial.span_oscillatorHermitePolynomial`](../ContinuousFlexibility/Radial/HermiteCompleteness.lean#L62)
- [`ContinuousFlexibility.Radial.integrable_weightedGaussian_polynomial`](../ContinuousFlexibility/Radial/HermiteCompleteness.lean#L69)
- [`ContinuousFlexibility.Radial.weightedGaussian_polynomial_integral_eq_zero`](../ContinuousFlexibility/Radial/HermiteCompleteness.lean#L96)
- [`ContinuousFlexibility.Radial.normalizedHermite_total_of_measurable`](../ContinuousFlexibility/Radial/HermiteCompleteness.lean#L128)
- [`ContinuousFlexibility.Radial.normalizedHermite_total`](../ContinuousFlexibility/Radial/HermiteCompleteness.lean#L157)
- [`ContinuousFlexibility.Radial.normalizedHermite_complete_Lp`](../ContinuousFlexibility/Radial/HermiteCompleteness.lean#L177)

[CentralEnergyIdentity.lean](../ContinuousFlexibility/Radial/CentralEnergyIdentity.lean)：

- [`ContinuousFlexibility.Radial.centralEnergyShift_level`](../ContinuousFlexibility/Radial/CentralEnergyIdentity.lean#L32)
- [`ContinuousFlexibility.Radial.oscillator_form_pairing`](../ContinuousFlexibility/Radial/CentralEnergyIdentity.lean#L39)
- [`ContinuousFlexibility.Radial.central_shifted_form_pairing`](../ContinuousFlexibility/Radial/CentralEnergyIdentity.lean#L65)
- [`ContinuousFlexibility.Radial.oscillatorEnergyPairing_self_nonneg`](../ContinuousFlexibility/Radial/CentralEnergyIdentity.lean#L98)
- [`ContinuousFlexibility.Radial.shiftedCentralEnergyPairing_controls_L2`](../ContinuousFlexibility/Radial/CentralEnergyIdentity.lean#L104)
- [`ContinuousFlexibility.Radial.integral_finiteHermiteFunction_mul_mode`](../ContinuousFlexibility/Radial/CentralEnergyIdentity.lean#L111)
- [`ContinuousFlexibility.Radial.integral_finiteHermiteFunction_mul`](../ContinuousFlexibility/Radial/CentralEnergyIdentity.lean#L138)
- [`ContinuousFlexibility.Radial.finiteHermiteFunction_central_memLp`](../ContinuousFlexibility/Radial/CentralEnergyIdentity.lean#L167)
- [`ContinuousFlexibility.Radial.finiteHermiteFunction_shifted_energy`](../ContinuousFlexibility/Radial/CentralEnergyIdentity.lean#L181)

[CentralGraphAdjoint.lean](../ContinuousFlexibility/Radial/CentralGraphAdjoint.lean)：

- [`ContinuousFlexibility.Radial.centralClosedGraph_eigenpair`](../ContinuousFlexibility/Radial/CentralGraphAdjoint.lean#L26)
- [`ContinuousFlexibility.Radial.centralClosedGraph_symmetric`](../ContinuousFlexibility/Radial/CentralGraphAdjoint.lean#L33)
- [`ContinuousFlexibility.Radial.centralClosedGraph_pairing_iff`](../ContinuousFlexibility/Radial/CentralGraphAdjoint.lean#L51)
- [`ContinuousFlexibility.Radial.centralClosedGraph_completeSpace`](../ContinuousFlexibility/Radial/CentralGraphAdjoint.lean#L69)
- [`ContinuousFlexibility.Radial.centralClosedGraph_two_kernel_iff`](../ContinuousFlexibility/Radial/CentralGraphAdjoint.lean#L89)
- [`ContinuousFlexibility.Radial.centralClosedGraph_even_kernel_iff`](../ContinuousFlexibility/Radial/CentralGraphAdjoint.lean#L126)

[CentralPositionInverse.lean](../ContinuousFlexibility/Radial/CentralPositionInverse.lean)：

- [`ContinuousFlexibility.Radial.centralInverseEnergyLift_base`](../ContinuousFlexibility/Radial/CentralPositionInverse.lean#L54)
- [`ContinuousFlexibility.Radial.centralInverseEnergyLift_pairing`](../ContinuousFlexibility/Radial/CentralPositionInverse.lean#L61)
- [`ContinuousFlexibility.Radial.centralInverseEnergyLift_energy`](../ContinuousFlexibility/Radial/CentralPositionInverse.lean#L68)
- [`ContinuousFlexibility.Radial.centralInverseEnergyLift_norm_bound`](../ContinuousFlexibility/Radial/CentralPositionInverse.lean#L77)
- [`ContinuousFlexibility.Radial.centralPositionInverseValue_ae`](../ContinuousFlexibility/Radial/CentralPositionInverse.lean#L128)
- [`ContinuousFlexibility.Radial.centralPositionInverseValue_norm_bound`](../ContinuousFlexibility/Radial/CentralPositionInverse.lean#L144)
- [`ContinuousFlexibility.Radial.centralHilbertInverse_position_memLp`](../ContinuousFlexibility/Radial/CentralPositionInverse.lean#L160)
- [`ContinuousFlexibility.Radial.centralPositionInverse_apply`](../ContinuousFlexibility/Radial/CentralPositionInverse.lean#L200)
- [`ContinuousFlexibility.Radial.centralPositionInverse_norm_le`](../ContinuousFlexibility/Radial/CentralPositionInverse.lean#L203)
- [`ContinuousFlexibility.Radial.centralPositionInverse_ae`](../ContinuousFlexibility/Radial/CentralPositionInverse.lean#L209)
- [`ContinuousFlexibility.Radial.HasPositionL2.unique`](../ContinuousFlexibility/Radial/CentralPositionInverse.lean#L219)
- [`ContinuousFlexibility.Radial.positionL2_pairing_swap`](../ContinuousFlexibility/Radial/CentralPositionInverse.lean#L224)
- [`ContinuousFlexibility.Radial.centralHilbertInverse_inner_swap`](../ContinuousFlexibility/Radial/CentralPositionInverse.lean#L234)
- [`ContinuousFlexibility.Radial.centralRightPositionInverse_norm_le`](../ContinuousFlexibility/Radial/CentralPositionInverse.lean#L246)
- [`ContinuousFlexibility.Radial.centralRightPositionInverse_bound`](../ContinuousFlexibility/Radial/CentralPositionInverse.lean#L251)
- [`ContinuousFlexibility.Radial.centralRightPositionInverse_eq`](../ContinuousFlexibility/Radial/CentralPositionInverse.lean#L257)
- [`ContinuousFlexibility.Radial.HasPositionL2.smul`](../ContinuousFlexibility/Radial/CentralPositionInverse.lean#L269)
- [`ContinuousFlexibility.Radial.physicalEnergy_scaledPosition_ae`](../ContinuousFlexibility/Radial/CentralPositionInverse.lean#L277)
- [`ContinuousFlexibility.Radial.centralHermitePositionVector_ae`](../ContinuousFlexibility/Radial/CentralPositionInverse.lean#L292)
- [`ContinuousFlexibility.Radial.centralHilbertInverse_mode`](../ContinuousFlexibility/Radial/CentralPositionInverse.lean#L300)
- [`ContinuousFlexibility.Radial.centralPositionInverse_mode`](../ContinuousFlexibility/Radial/CentralPositionInverse.lean#L306)
- [`ContinuousFlexibility.Radial.physicalHermiteLift_scaledPosition`](../ContinuousFlexibility/Radial/CentralPositionInverse.lean#L317)
- [`ContinuousFlexibility.Radial.centralRightPositionInverse_coefficient_energy`](../ContinuousFlexibility/Radial/CentralPositionInverse.lean#L324)
- [`ContinuousFlexibility.Radial.centralRightInverseEnergyLift_pairing`](../ContinuousFlexibility/Radial/CentralPositionInverse.lean#L356)
- [`ContinuousFlexibility.Radial.centralRightInverseEnergyLift_base`](../ContinuousFlexibility/Radial/CentralPositionInverse.lean#L366)
- [`ContinuousFlexibility.Radial.centralDoublePositionInverseValue_ae`](../ContinuousFlexibility/Radial/CentralPositionInverse.lean#L387)
- [`ContinuousFlexibility.Radial.centralRightInverseEnergyLift_energy`](../ContinuousFlexibility/Radial/CentralPositionInverse.lean#L394)
- [`ContinuousFlexibility.Radial.centralDoublePositionInverseValue_norm_bound`](../ContinuousFlexibility/Radial/CentralPositionInverse.lean#L415)
- [`ContinuousFlexibility.Radial.centralDoublePositionInverse_norm_le`](../ContinuousFlexibility/Radial/CentralPositionInverse.lean#L498)
- [`ContinuousFlexibility.Radial.centralDoublePositionInverse_ae`](../ContinuousFlexibility/Radial/CentralPositionInverse.lean#L504)
- [`ContinuousFlexibility.Radial.centralDoublePositionInverse_eq`](../ContinuousFlexibility/Radial/CentralPositionInverse.lean#L510)
- [`ContinuousFlexibility.Radial.centralDoublePositionInverse_inner_swap`](../ContinuousFlexibility/Radial/CentralPositionInverse.lean#L517)

[CentralRadialWeightedInverse.lean](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean)：

- [`ContinuousFlexibility.Radial.boundedScalarMultiplier_ae`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L86)
- [`ContinuousFlexibility.Radial.boundedScalarMultiplier_bound`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L92)
- [`ContinuousFlexibility.Radial.boundedScalarMultiplier_norm_le`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L97)
- [`ContinuousFlexibility.Radial.boundedScalarMultiplier_inner_swap`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L102)
- [`ContinuousFlexibility.Radial.measurable_centralRadialBoundedWeight`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L122)
- [`ContinuousFlexibility.Radial.measurable_centralRadialSignedWeight`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L127)
- [`ContinuousFlexibility.Radial.centralRadialBoundedWeight_abs_le`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L130)
- [`ContinuousFlexibility.Radial.centralRadialSignedWeight_abs_le`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L137)
- [`ContinuousFlexibility.Radial.centralRadiusLogDerivative_decomposition`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L158)
- [`ContinuousFlexibility.Radial.centralRadialBMultiplier_ae`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L178)
- [`ContinuousFlexibility.Radial.centralRadialCMultiplier_ae`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L183)
- [`ContinuousFlexibility.Radial.centralRadialBMultiplier_norm_le`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L188)
- [`ContinuousFlexibility.Radial.centralRadialCMultiplier_norm_le`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L192)
- [`ContinuousFlexibility.Radial.centralRadialBMultiplier_inner_swap`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L196)
- [`ContinuousFlexibility.Radial.centralRadialCMultiplier_inner_swap`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L200)
- [`ContinuousFlexibility.Radial.HasCentralRadialWeightL2.unique`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L209)
- [`ContinuousFlexibility.Radial.centralRadialWeight_domain_iff`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L213)
- [`ContinuousFlexibility.Radial.centralRadialWeight_of_position`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L222)
- [`ContinuousFlexibility.Radial.centralRadialC_position_of_weight`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L238)
- [`ContinuousFlexibility.Radial.centralRadialDoubleInverse_apply`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L280)
- [`ContinuousFlexibility.Radial.centralRadialLeftInverse_norm_le`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L290)
- [`ContinuousFlexibility.Radial.centralRadialRightInverse_norm_le`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L308)
- [`ContinuousFlexibility.Radial.centralRadialRightPositionInverse_norm_le`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L326)
- [`ContinuousFlexibility.Radial.centralRadialDoubleInverse_norm_le`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L344)
- [`ContinuousFlexibility.Radial.centralRadialLeftInverse_ae`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L362)
- [`ContinuousFlexibility.Radial.centralRadialRightInverse_position`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L366)
- [`ContinuousFlexibility.Radial.centralRadialDoubleInverse_ae`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L385)
- [`ContinuousFlexibility.Radial.centralRadialRightInverse_eq`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L389)
- [`ContinuousFlexibility.Radial.centralRadialDoubleInverse_weighted`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L400)
- [`ContinuousFlexibility.Radial.centralRadialDoubleInverse_memLp_source`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L406)
- [`ContinuousFlexibility.Radial.centralRadialRightInverse_inner_swap`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L415)
- [`ContinuousFlexibility.Radial.centralRadialReducedLeftInverse_norm_le`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L466)
- [`ContinuousFlexibility.Radial.centralRadialReducedRightInverse_norm_le`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L476)
- [`ContinuousFlexibility.Radial.centralRadialReducedRightPositionInverse_norm_le`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L485)
- [`ContinuousFlexibility.Radial.centralRadialReducedDoubleInverse_norm_le`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L494)
- [`ContinuousFlexibility.Radial.centralRadialReducedDoubleInverse_norm_le_uniform`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L505)
- [`ContinuousFlexibility.Radial.centralRadialReducedDoubleInverse_apply`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L514)
- [`ContinuousFlexibility.Radial.centralRadialReducedLeftInverse_ae`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L524)
- [`ContinuousFlexibility.Radial.centralRadialReducedRightInverse_position`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L528)
- [`ContinuousFlexibility.Radial.centralRadialReducedDoubleInverse_ae`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L550)
- [`ContinuousFlexibility.Radial.centralRadialReducedRightInverse_eq`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L554)
- [`ContinuousFlexibility.Radial.centralRadialReducedDoubleInverse_weighted`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L563)
- [`ContinuousFlexibility.Radial.centralRadialReducedDoubleInverse_memLp_source`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L569)
- [`ContinuousFlexibility.Radial.centralRadialReducedRightInverse_inner_swap`](../ContinuousFlexibility/Radial/CentralRadialWeightedInverse.lean#L576)

[CentralRadiusGrowth.lean](../ContinuousFlexibility/Radial/CentralRadiusGrowth.lean)：

- [`ContinuousFlexibility.Radial.gaussianLaplaceMoment_variance`](../ContinuousFlexibility/Radial/CentralRadiusGrowth.lean#L21)
- [`ContinuousFlexibility.Radial.gaussianLaplaceRatio_pos`](../ContinuousFlexibility/Radial/CentralRadiusGrowth.lean#L63)
- [`ContinuousFlexibility.Radial.gaussianLaplaceRatio_quadratic`](../ContinuousFlexibility/Radial/CentralRadiusGrowth.lean#L68)
- [`ContinuousFlexibility.Radial.gaussianLaplaceRatio_le_sqrt_of_nonpos`](../ContinuousFlexibility/Radial/CentralRadiusGrowth.lean#L82)
- [`ContinuousFlexibility.Radial.gaussianLaplaceRatio_le_of_nonneg`](../ContinuousFlexibility/Radial/CentralRadiusGrowth.lean#L92)
- [`ContinuousFlexibility.Radial.gaussianLaplacePsi_log_deriv`](../ContinuousFlexibility/Radial/CentralRadiusGrowth.lean#L105)
- [`ContinuousFlexibility.Radial.centralRadiusLogDerivative_eq`](../ContinuousFlexibility/Radial/CentralRadiusGrowth.lean#L115)
- [`ContinuousFlexibility.Radial.centralRadiusLogDerivative_gt`](../ContinuousFlexibility/Radial/CentralRadiusGrowth.lean#L130)
- [`ContinuousFlexibility.Radial.centralRadiusLogDerivative_le`](../ContinuousFlexibility/Radial/CentralRadiusGrowth.lean#L138)
- [`ContinuousFlexibility.Radial.centralRadiusLogDerivative_pos`](../ContinuousFlexibility/Radial/CentralRadiusGrowth.lean#L162)
- [`ContinuousFlexibility.Radial.contDiff_centralRadiusLogDerivative`](../ContinuousFlexibility/Radial/CentralRadiusGrowth.lean#L165)
- [`ContinuousFlexibility.Radial.centralRadiusLogDerivative_norm_le`](../ContinuousFlexibility/Radial/CentralRadiusGrowth.lean#L170)
- [`ContinuousFlexibility.Radial.centralRadiusWeightConstant_pos`](../ContinuousFlexibility/Radial/CentralRadiusGrowth.lean#L179)
- [`ContinuousFlexibility.Radial.centralRadiusLogDerivative_norm_le_linear`](../ContinuousFlexibility/Radial/CentralRadiusGrowth.lean#L183)

[CentralReducedPositionInverse.lean](../ContinuousFlexibility/Radial/CentralReducedPositionInverse.lean)：

- [`ContinuousFlexibility.Radial.centralEnergyShift_two`](../ContinuousFlexibility/Radial/CentralReducedPositionInverse.lean#L20)
- [`ContinuousFlexibility.Radial.centralGroundProjection_inner_zero`](../ContinuousFlexibility/Radial/CentralReducedPositionInverse.lean#L25)
- [`ContinuousFlexibility.Radial.centralReducedHilbertInverse_inner_swap`](../ContinuousFlexibility/Radial/CentralReducedPositionInverse.lean#L31)
- [`ContinuousFlexibility.Radial.centralReducedInverseEnergyLift_base`](../ContinuousFlexibility/Radial/CentralReducedPositionInverse.lean#L50)
- [`ContinuousFlexibility.Radial.centralReducedInverseEnergyLift_pairing`](../ContinuousFlexibility/Radial/CentralReducedPositionInverse.lean#L56)
- [`ContinuousFlexibility.Radial.centralReducedInverseEnergyLift_energy`](../ContinuousFlexibility/Radial/CentralReducedPositionInverse.lean#L62)
- [`ContinuousFlexibility.Radial.centralReducedInverseEnergyLift_norm_bound`](../ContinuousFlexibility/Radial/CentralReducedPositionInverse.lean#L72)
- [`ContinuousFlexibility.Radial.centralReducedPositionInverseValue_ae`](../ContinuousFlexibility/Radial/CentralReducedPositionInverse.lean#L98)
- [`ContinuousFlexibility.Radial.centralReducedPositionInverseValue_norm_bound`](../ContinuousFlexibility/Radial/CentralReducedPositionInverse.lean#L104)
- [`ContinuousFlexibility.Radial.centralReducedHilbertInverse_position_memLp`](../ContinuousFlexibility/Radial/CentralReducedPositionInverse.lean#L115)
- [`ContinuousFlexibility.Radial.centralReducedPositionInverse_norm_le`](../ContinuousFlexibility/Radial/CentralReducedPositionInverse.lean#L154)
- [`ContinuousFlexibility.Radial.centralReducedPositionInverse_ae`](../ContinuousFlexibility/Radial/CentralReducedPositionInverse.lean#L157)
- [`ContinuousFlexibility.Radial.centralReducedRightPositionInverse_norm_le`](../ContinuousFlexibility/Radial/CentralReducedPositionInverse.lean#L164)
- [`ContinuousFlexibility.Radial.centralReducedRightPositionInverse_bound`](../ContinuousFlexibility/Radial/CentralReducedPositionInverse.lean#L168)
- [`ContinuousFlexibility.Radial.centralReducedRightPositionInverse_eq`](../ContinuousFlexibility/Radial/CentralReducedPositionInverse.lean#L173)
- [`ContinuousFlexibility.Radial.centralReducedHilbertInverse_mode`](../ContinuousFlexibility/Radial/CentralReducedPositionInverse.lean#L184)
- [`ContinuousFlexibility.Radial.centralReducedPositionInverse_mode`](../ContinuousFlexibility/Radial/CentralReducedPositionInverse.lean#L189)
- [`ContinuousFlexibility.Radial.centralReducedRightPositionInverse_coefficient`](../ContinuousFlexibility/Radial/CentralReducedPositionInverse.lean#L199)
- [`ContinuousFlexibility.Radial.centralReducedRightPositionInverse_zero_coefficient`](../ContinuousFlexibility/Radial/CentralReducedPositionInverse.lean#L208)
- [`ContinuousFlexibility.Radial.centralReducedRightPositionInverse_coefficient_energy`](../ContinuousFlexibility/Radial/CentralReducedPositionInverse.lean#L213)
- [`ContinuousFlexibility.Radial.centralReducedRightInverseEnergyLift_pairing`](../ContinuousFlexibility/Radial/CentralReducedPositionInverse.lean#L232)
- [`ContinuousFlexibility.Radial.centralReducedRightInverseEnergyLift_base`](../ContinuousFlexibility/Radial/CentralReducedPositionInverse.lean#L242)
- [`ContinuousFlexibility.Radial.centralReducedDoublePositionInverseValue_ae`](../ContinuousFlexibility/Radial/CentralReducedPositionInverse.lean#L271)
- [`ContinuousFlexibility.Radial.centralReducedRightInverseEnergyLift_energy`](../ContinuousFlexibility/Radial/CentralReducedPositionInverse.lean#L277)
- [`ContinuousFlexibility.Radial.centralReducedDoublePositionInverseValue_norm_bound`](../ContinuousFlexibility/Radial/CentralReducedPositionInverse.lean#L290)
- [`ContinuousFlexibility.Radial.centralReducedDoublePositionInverse_norm_le`](../ContinuousFlexibility/Radial/CentralReducedPositionInverse.lean#L365)
- [`ContinuousFlexibility.Radial.centralReducedDoublePositionInverse_ae`](../ContinuousFlexibility/Radial/CentralReducedPositionInverse.lean#L368)
- [`ContinuousFlexibility.Radial.centralReducedDoublePositionInverse_eq`](../ContinuousFlexibility/Radial/CentralReducedPositionInverse.lean#L372)
- [`ContinuousFlexibility.Radial.centralReducedDoublePositionInverse_inner_swap`](../ContinuousFlexibility/Radial/CentralReducedPositionInverse.lean#L378)

[CentralSpectralGap.lean](../ContinuousFlexibility/Radial/CentralSpectralGap.lean)：

- [`ContinuousFlexibility.Radial.centralOscillatorA_eq_sqrt_half`](../ContinuousFlexibility/Radial/CentralSpectralGap.lean#L24)
- [`ContinuousFlexibility.Radial.centralOscillatorA_sq`](../ContinuousFlexibility/Radial/CentralSpectralGap.lean#L31)
- [`ContinuousFlexibility.Radial.centralGapDelta_pos`](../ContinuousFlexibility/Radial/CentralSpectralGap.lean#L35)
- [`ContinuousFlexibility.Radial.centralGapDelta_lt_one`](../ContinuousFlexibility/Radial/CentralSpectralGap.lean#L41)
- [`ContinuousFlexibility.Radial.central_norm_between`](../ContinuousFlexibility/Radial/CentralSpectralGap.lean#L59)
- [`ContinuousFlexibility.Radial.centralSpectralLevel_two`](../ContinuousFlexibility/Radial/CentralSpectralGap.lean#L86)
- [`ContinuousFlexibility.Radial.centralSpectralLevel_even_gap`](../ContinuousFlexibility/Radial/CentralSpectralGap.lean#L93)
- [`ContinuousFlexibility.Radial.central_normalizedHermite_spectralLevel`](../ContinuousFlexibility/Radial/CentralSpectralGap.lean#L158)

[CentralSpectralInverse.lean](../ContinuousFlexibility/Radial/CentralSpectralInverse.lean)：

- [`ContinuousFlexibility.Radial.hermiteBoundedMultiplier_coefficient`](../ContinuousFlexibility/Radial/CentralSpectralInverse.lean#L53)
- [`ContinuousFlexibility.Radial.hermiteBoundedMultiplier_bound`](../ContinuousFlexibility/Radial/CentralSpectralInverse.lean#L65)
- [`ContinuousFlexibility.Radial.hermiteBoundedMultiplier_norm_le`](../ContinuousFlexibility/Radial/CentralSpectralInverse.lean#L75)
- [`ContinuousFlexibility.Radial.hermiteBoundedMultiplier_vector`](../ContinuousFlexibility/Radial/CentralSpectralInverse.lean#L81)
- [`ContinuousFlexibility.Radial.central_inverse_level_bound`](../ContinuousFlexibility/Radial/CentralSpectralInverse.lean#L100)
- [`ContinuousFlexibility.Radial.centralHilbertInverse_bound`](../ContinuousFlexibility/Radial/CentralSpectralInverse.lean#L120)
- [`ContinuousFlexibility.Radial.centralHilbertInverse_norm_le`](../ContinuousFlexibility/Radial/CentralSpectralInverse.lean#L124)
- [`ContinuousFlexibility.Radial.centralHilbertInverse_graph`](../ContinuousFlexibility/Radial/CentralSpectralInverse.lean#L128)
- [`ContinuousFlexibility.Radial.centralHilbertInverse_left`](../ContinuousFlexibility/Radial/CentralSpectralInverse.lean#L144)
- [`ContinuousFlexibility.Radial.centralClosedGraph_even_exists_unique`](../ContinuousFlexibility/Radial/CentralSpectralInverse.lean#L165)
- [`ContinuousFlexibility.Radial.reduced_inverse_level_bound`](../ContinuousFlexibility/Radial/CentralSpectralInverse.lean#L171)
- [`ContinuousFlexibility.Radial.centralReducedHilbertInverse_bound`](../ContinuousFlexibility/Radial/CentralSpectralInverse.lean#L184)
- [`ContinuousFlexibility.Radial.centralReducedHilbertInverse_norm_le`](../ContinuousFlexibility/Radial/CentralSpectralInverse.lean#L188)
- [`ContinuousFlexibility.Radial.centralReducedHilbertInverse_norm`](../ContinuousFlexibility/Radial/CentralSpectralInverse.lean#L194)
- [`ContinuousFlexibility.Radial.centralReducedHilbertInverse_zero_coefficient`](../ContinuousFlexibility/Radial/CentralSpectralInverse.lean#L209)
- [`ContinuousFlexibility.Radial.centralReducedHilbertInverse_graph`](../ContinuousFlexibility/Radial/CentralSpectralInverse.lean#L216)
- [`ContinuousFlexibility.Radial.centralReducedHilbertInverse_left`](../ContinuousFlexibility/Radial/CentralSpectralInverse.lean#L231)
- [`ContinuousFlexibility.Radial.centralClosedGraph_two_source_compatible`](../ContinuousFlexibility/Radial/CentralSpectralInverse.lean#L249)
- [`ContinuousFlexibility.Radial.centralClosedGraph_two_exists_unique_iff`](../ContinuousFlexibility/Radial/CentralSpectralInverse.lean#L258)
- [`ContinuousFlexibility.Radial.centralGroundProjection_apply`](../ContinuousFlexibility/Radial/CentralSpectralInverse.lean#L278)
- [`ContinuousFlexibility.Radial.centralGroundProjection_coefficient`](../ContinuousFlexibility/Radial/CentralSpectralInverse.lean#L284)
- [`ContinuousFlexibility.Radial.centralGroundProjection_idempotent`](../ContinuousFlexibility/Radial/CentralSpectralInverse.lean#L294)
- [`ContinuousFlexibility.Radial.centralGroundProjection_orthogonal`](../ContinuousFlexibility/Radial/CentralSpectralInverse.lean#L299)
- [`ContinuousFlexibility.Radial.centralReducedHilbertInverse_graph_projected`](../ContinuousFlexibility/Radial/CentralSpectralInverse.lean#L308)
- [`ContinuousFlexibility.Radial.centralReducedHilbertInverse_left_projected`](../ContinuousFlexibility/Radial/CentralSpectralInverse.lean#L328)

[GaussianLaplaceLeftBounds.lean](../ContinuousFlexibility/Radial/GaussianLaplaceLeftBounds.lean)：

- [`ContinuousFlexibility.Radial.gammaLaplaceMoment_eq`](../ContinuousFlexibility/Radial/GaussianLaplaceLeftBounds.lean#L27)
- [`ContinuousFlexibility.Radial.gammaLaplaceMoment_pos`](../ContinuousFlexibility/Radial/GaussianLaplaceLeftBounds.lean#L31)
- [`ContinuousFlexibility.Radial.integrableOn_gammaLaplaceKernel`](../ContinuousFlexibility/Radial/GaussianLaplaceLeftBounds.lean#L36)
- [`ContinuousFlexibility.Radial.gammaLaplaceKernel_succ`](../ContinuousFlexibility/Radial/GaussianLaplaceLeftBounds.lean#L40)
- [`ContinuousFlexibility.Radial.gammaLaplaceMoment_succ`](../ContinuousFlexibility/Radial/GaussianLaplaceLeftBounds.lean#L49)
- [`ContinuousFlexibility.Radial.gammaLaplaceMoment_succ_two`](../ContinuousFlexibility/Radial/GaussianLaplaceLeftBounds.lean#L56)
- [`ContinuousFlexibility.Radial.gaussianLaplaceKernel_left_factor`](../ContinuousFlexibility/Radial/GaussianLaplaceLeftBounds.lean#L63)
- [`ContinuousFlexibility.Radial.gaussianLaplaceKernel_left_defect`](../ContinuousFlexibility/Radial/GaussianLaplaceLeftBounds.lean#L77)
- [`ContinuousFlexibility.Radial.gaussianLaplaceMoment_left_defect`](../ContinuousFlexibility/Radial/GaussianLaplaceLeftBounds.lean#L99)
- [`ContinuousFlexibility.Radial.gaussianLaplaceMoment_left_relative_error`](../ContinuousFlexibility/Radial/GaussianLaplaceLeftBounds.lean#L124)
- [`ContinuousFlexibility.Radial.iteratedDeriv_gaussianLaplaceMoment`](../ContinuousFlexibility/Radial/GaussianLaplaceLeftBounds.lean#L144)
- [`ContinuousFlexibility.Radial.iteratedDeriv_gaussianLaplaceMoment_neg`](../ContinuousFlexibility/Radial/GaussianLaplaceLeftBounds.lean#L158)
- [`ContinuousFlexibility.Radial.gaussianLaplaceMoment_left_derivative_error`](../ContinuousFlexibility/Radial/GaussianLaplaceLeftBounds.lean#L176)
- [`ContinuousFlexibility.Radial.gaussianLaplaceMoment_left_ratio_tendsto`](../ContinuousFlexibility/Radial/GaussianLaplaceLeftBounds.lean#L198)
- [`ContinuousFlexibility.Radial.gaussianLaplaceMoment_left_derivative_ratio_tendsto`](../ContinuousFlexibility/Radial/GaussianLaplaceLeftBounds.lean#L225)

[HermiteBasis.lean](../ContinuousFlexibility/Radial/HermiteBasis.lean)：

- [`ContinuousFlexibility.Radial.hermiteL2Vector_coeFn`](../ContinuousFlexibility/Radial/HermiteBasis.lean#L31)
- [`ContinuousFlexibility.Radial.hermiteL2Vector_inner`](../ContinuousFlexibility/Radial/HermiteBasis.lean#L35)
- [`ContinuousFlexibility.Radial.hermiteL2Vector_orthonormal`](../ContinuousFlexibility/Radial/HermiteBasis.lean#L47)
- [`ContinuousFlexibility.Radial.hermiteCoefficient_integrable`](../ContinuousFlexibility/Radial/HermiteBasis.lean#L55)
- [`ContinuousFlexibility.Radial.inner_hermiteL2Vector_left`](../ContinuousFlexibility/Radial/HermiteBasis.lean#L59)
- [`ContinuousFlexibility.Radial.inner_hermiteL2Vector_right`](../ContinuousFlexibility/Radial/HermiteBasis.lean#L68)
- [`ContinuousFlexibility.Radial.hermiteL2Vector_span_orthogonal`](../ContinuousFlexibility/Radial/HermiteBasis.lean#L76)
- [`ContinuousFlexibility.Radial.hermiteBasis_apply`](../ContinuousFlexibility/Radial/HermiteBasis.lean#L94)
- [`ContinuousFlexibility.Radial.hermiteBasis_coeFn`](../ContinuousFlexibility/Radial/HermiteBasis.lean#L99)
- [`ContinuousFlexibility.Radial.hermiteBasis_repr_eq_coefficient`](../ContinuousFlexibility/Radial/HermiteBasis.lean#L104)
- [`ContinuousFlexibility.Radial.hermiteCoefficientTransform_apply`](../ContinuousFlexibility/Radial/HermiteBasis.lean#L114)
- [`ContinuousFlexibility.Radial.hermiteCoefficientTransform_norm`](../ContinuousFlexibility/Radial/HermiteBasis.lean#L119)
- [`ContinuousFlexibility.Radial.hermiteSynthesis_hasSum`](../ContinuousFlexibility/Radial/HermiteBasis.lean#L124)
- [`ContinuousFlexibility.Radial.hermiteExpansion_hasSum`](../ContinuousFlexibility/Radial/HermiteBasis.lean#L132)
- [`ContinuousFlexibility.Radial.hermiteExpansion_tsum`](../ContinuousFlexibility/Radial/HermiteBasis.lean#L137)
- [`ContinuousFlexibility.Radial.hermiteExpansion_partialSums`](../ContinuousFlexibility/Radial/HermiteBasis.lean#L141)
- [`ContinuousFlexibility.Radial.hermiteL2Vector_dense_span`](../ContinuousFlexibility/Radial/HermiteBasis.lean#L146)
- [`ContinuousFlexibility.Radial.hermiteCoefficient_hasSum_sq`](../ContinuousFlexibility/Radial/HermiteBasis.lean#L153)
- [`ContinuousFlexibility.Radial.hermiteCoefficient_summable_sq`](../ContinuousFlexibility/Radial/HermiteBasis.lean#L159)
- [`ContinuousFlexibility.Radial.hermiteCoefficient_parseval`](../ContinuousFlexibility/Radial/HermiteBasis.lean#L163)
- [`ContinuousFlexibility.Radial.hermiteCoefficient_hasSum_mul`](../ContinuousFlexibility/Radial/HermiteBasis.lean#L167)
- [`ContinuousFlexibility.Radial.hermiteCoefficient_parseval_integral`](../ContinuousFlexibility/Radial/HermiteBasis.lean#L174)
- [`ContinuousFlexibility.Radial.hermiteCoefficient_parseval_integral_sq`](../ContinuousFlexibility/Radial/HermiteBasis.lean#L186)

[OscillatorClosedForm.lean](../ContinuousFlexibility/Radial/OscillatorClosedForm.lean)：

- [`ContinuousFlexibility.Radial.physicalFormRepresentative_pairing`](../ContinuousFlexibility/Radial/OscillatorClosedForm.lean#L31)
- [`ContinuousFlexibility.Radial.physicalFormRepresentative_unique`](../ContinuousFlexibility/Radial/OscillatorClosedForm.lean#L36)
- [`ContinuousFlexibility.Radial.physicalEnergyBase_opNorm_le`](../ContinuousFlexibility/Radial/OscillatorClosedForm.lean#L45)
- [`ContinuousFlexibility.Radial.physicalFormFunctional_norm_le`](../ContinuousFlexibility/Radial/OscillatorClosedForm.lean#L50)
- [`ContinuousFlexibility.Radial.physicalFormRepresentative_norm_le`](../ContinuousFlexibility/Radial/OscillatorClosedForm.lean#L60)
- [`ContinuousFlexibility.Radial.physicalFormRepresentative_base_norm_le`](../ContinuousFlexibility/Radial/OscillatorClosedForm.lean#L67)
- [`ContinuousFlexibility.Radial.mem_physicalClosedFormGraph_iff`](../ContinuousFlexibility/Radial/OscillatorClosedForm.lean#L113)
- [`ContinuousFlexibility.Radial.physicalClosedFormEquation_iff_representative`](../ContinuousFlexibility/Radial/OscillatorClosedForm.lean#L118)
- [`ContinuousFlexibility.Radial.PhysicalClosedFormEquation.mem_centralClosedGraph`](../ContinuousFlexibility/Radial/OscillatorClosedForm.lean#L136)
- [`ContinuousFlexibility.Radial.physicalClosedFormEquation_of_mem_centralClosedGraph`](../ContinuousFlexibility/Radial/OscillatorClosedForm.lean#L154)
- [`ContinuousFlexibility.Radial.physicalClosedFormEquation_iff_centralClosedGraph`](../ContinuousFlexibility/Radial/OscillatorClosedForm.lean#L182)
- [`ContinuousFlexibility.Radial.physicalClosedFormGraph_eq_centralClosedGraph`](../ContinuousFlexibility/Radial/OscillatorClosedForm.lean#L188)
- [`ContinuousFlexibility.Radial.physicalClosedFormGraph_isClosed`](../ContinuousFlexibility/Radial/OscillatorClosedForm.lean#L194)
- [`ContinuousFlexibility.Radial.physicalClosedFormEquation_unique`](../ContinuousFlexibility/Radial/OscillatorClosedForm.lean#L199)
- [`ContinuousFlexibility.Radial.physicalClosedFormEquation_domain_iff`](../ContinuousFlexibility/Radial/OscillatorClosedForm.lean#L205)

[OscillatorClosedGraph.lean](../ContinuousFlexibility/Radial/OscillatorClosedGraph.lean)：

- [`ContinuousFlexibility.Radial.hermiteCoefficientCLM_apply`](../ContinuousFlexibility/Radial/OscillatorClosedGraph.lean#L31)
- [`ContinuousFlexibility.Radial.hermiteCoefficient_continuous`](../ContinuousFlexibility/Radial/OscillatorClosedGraph.lean#L36)
- [`ContinuousFlexibility.Radial.hermiteCoefficient_hermiteL2Vector`](../ContinuousFlexibility/Radial/OscillatorClosedGraph.lean#L45)
- [`ContinuousFlexibility.Radial.mem_centralClosedGraph_iff`](../ContinuousFlexibility/Radial/OscillatorClosedGraph.lean#L111)
- [`ContinuousFlexibility.Radial.centralClosedGraph_isClosed`](../ContinuousFlexibility/Radial/OscillatorClosedGraph.lean#L138)
- [`ContinuousFlexibility.Radial.centralClosedGraph_unique`](../ContinuousFlexibility/Radial/OscillatorClosedGraph.lean#L143)
- [`ContinuousFlexibility.Radial.centralClosedGraph_domain_iff`](../ContinuousFlexibility/Radial/OscillatorClosedGraph.lean#L155)
- [`ContinuousFlexibility.Radial.centralFiniteGraph_domain_span`](../ContinuousFlexibility/Radial/OscillatorClosedGraph.lean#L175)
- [`ContinuousFlexibility.Radial.centralClosedGraph_domain_dense`](../ContinuousFlexibility/Radial/OscillatorClosedGraph.lean#L184)

[OscillatorCompactCore.lean](../ContinuousFlexibility/Radial/OscillatorCompactCore.lean)：

- [`ContinuousFlexibility.Radial.contDiff_oscillatorCutoff`](../ContinuousFlexibility/Radial/OscillatorCompactCore.lean#L31)
- [`ContinuousFlexibility.Radial.oscillatorCutoff_nonneg`](../ContinuousFlexibility/Radial/OscillatorCompactCore.lean#L35)
- [`ContinuousFlexibility.Radial.oscillatorCutoff_le_one`](../ContinuousFlexibility/Radial/OscillatorCompactCore.lean#L38)
- [`ContinuousFlexibility.Radial.oscillatorCutoff_eq_one`](../ContinuousFlexibility/Radial/OscillatorCompactCore.lean#L42)
- [`ContinuousFlexibility.Radial.oscillatorCutoff_eq_zero`](../ContinuousFlexibility/Radial/OscillatorCompactCore.lean#L48)
- [`ContinuousFlexibility.Radial.oscillatorCutoff_hasCompactSupport`](../ContinuousFlexibility/Radial/OscillatorCompactCore.lean#L57)
- [`ContinuousFlexibility.Radial.oscillatorCutoff_derivative_bounds`](../ContinuousFlexibility/Radial/OscillatorCompactCore.lean#L65)
- [`ContinuousFlexibility.Radial.contDiff_scaledOscillatorCutoff`](../ContinuousFlexibility/Radial/OscillatorCompactCore.lean#L85)
- [`ContinuousFlexibility.Radial.scaledOscillatorCutoff_nonneg`](../ContinuousFlexibility/Radial/OscillatorCompactCore.lean#L89)
- [`ContinuousFlexibility.Radial.scaledOscillatorCutoff_le_one`](../ContinuousFlexibility/Radial/OscillatorCompactCore.lean#L92)
- [`ContinuousFlexibility.Radial.scaledOscillatorCutoff_hasCompactSupport`](../ContinuousFlexibility/Radial/OscillatorCompactCore.lean#L95)
- [`ContinuousFlexibility.Radial.deriv_scaledOscillatorCutoff`](../ContinuousFlexibility/Radial/OscillatorCompactCore.lean#L107)
- [`ContinuousFlexibility.Radial.deriv_deriv_scaledOscillatorCutoff`](../ContinuousFlexibility/Radial/OscillatorCompactCore.lean#L116)
- [`ContinuousFlexibility.Radial.tendsto_scaledOscillatorCutoff`](../ContinuousFlexibility/Radial/OscillatorCompactCore.lean#L130)
- [`ContinuousFlexibility.Radial.central_expression_mul`](../ContinuousFlexibility/Radial/OscillatorCompactCore.lean#L142)
- [`ContinuousFlexibility.Radial.scaledOscillatorCutoff_derivative_bounds`](../ContinuousFlexibility/Radial/OscillatorCompactCore.lean#L160)
- [`ContinuousFlexibility.Radial.tendsto_derivatives_scaledOscillatorCutoff`](../ContinuousFlexibility/Radial/OscillatorCompactCore.lean#L171)
- [`ContinuousFlexibility.Radial.contDiff_centralExpression`](../ContinuousFlexibility/Radial/OscillatorCompactCore.lean#L192)
- [`ContinuousFlexibility.Radial.hasCompactSupport_centralExpression`](../ContinuousFlexibility/Radial/OscillatorCompactCore.lean#L202)
- [`ContinuousFlexibility.Radial.compactSmooth_energyDomain`](../ContinuousFlexibility/Radial/OscillatorCompactCore.lean#L211)
- [`ContinuousFlexibility.Radial.compactSmooth_centralImage_memLp`](../ContinuousFlexibility/Radial/OscillatorCompactCore.lean#L218)
- [`ContinuousFlexibility.Radial.oscillator_tendsto_toLp_of_dominated`](../ContinuousFlexibility/Radial/OscillatorCompactCore.lean#L237)
- [`ContinuousFlexibility.Radial.contDiff_compactHermiteFunction`](../ContinuousFlexibility/Radial/OscillatorCompactCore.lean#L265)
- [`ContinuousFlexibility.Radial.compactHermiteFunction_hasCompactSupport`](../ContinuousFlexibility/Radial/OscillatorCompactCore.lean#L269)
- [`ContinuousFlexibility.Radial.compactHermiteFunction_memLp`](../ContinuousFlexibility/Radial/OscillatorCompactCore.lean#L273)
- [`ContinuousFlexibility.Radial.compactHermiteImage_memLp`](../ContinuousFlexibility/Radial/OscillatorCompactCore.lean#L278)
- [`ContinuousFlexibility.Radial.compactHermiteFunction_tendsto_L2`](../ContinuousFlexibility/Radial/OscillatorCompactCore.lean#L284)
- [`ContinuousFlexibility.Radial.compactHermiteImage_apply`](../ContinuousFlexibility/Radial/OscillatorCompactCore.lean#L307)
- [`ContinuousFlexibility.Radial.compactHermiteImage_tendsto_pointwise`](../ContinuousFlexibility/Radial/OscillatorCompactCore.lean#L319)
- [`ContinuousFlexibility.Radial.compactHermiteImage_tendsto_L2`](../ContinuousFlexibility/Radial/OscillatorCompactCore.lean#L332)
- [`ContinuousFlexibility.Radial.central_smooth_energy_graph`](../ContinuousFlexibility/Radial/OscillatorCompactCore.lean#L411)
- [`ContinuousFlexibility.Radial.centralClosedGraph_iff_compact_weak`](../ContinuousFlexibility/Radial/OscillatorCompactCore.lean#L442)
- [`ContinuousFlexibility.Radial.mem_centralCompactSmoothGraph`](../ContinuousFlexibility/Radial/OscillatorCompactCore.lean#L559)
- [`ContinuousFlexibility.Radial.centralCompactSmoothGraph_le`](../ContinuousFlexibility/Radial/OscillatorCompactCore.lean#L568)
- [`ContinuousFlexibility.Radial.centralCompactSmoothGraph_closure`](../ContinuousFlexibility/Radial/OscillatorCompactCore.lean#L577)

[OscillatorDifferentialPairing.lean](../ContinuousFlexibility/Radial/OscillatorDifferentialPairing.lean)：

- [`ContinuousFlexibility.Radial.integrable_mul_second_of_oscillator_image`](../ContinuousFlexibility/Radial/OscillatorDifferentialPairing.lean#L28)
- [`ContinuousFlexibility.Radial.oscillatorExpression_pairing_symm`](../ContinuousFlexibility/Radial/OscillatorDifferentialPairing.lean#L42)
- [`ContinuousFlexibility.Radial.oscillator_normalizedHermite_pairing`](../ContinuousFlexibility/Radial/OscillatorDifferentialPairing.lean#L84)
- [`ContinuousFlexibility.Radial.central_liouvilleSchrodinger_eq_oscillator_shift`](../ContinuousFlexibility/Radial/OscillatorDifferentialPairing.lean#L110)
- [`ContinuousFlexibility.Radial.central_memLp_image_iff`](../ContinuousFlexibility/Radial/OscillatorDifferentialPairing.lean#L121)
- [`ContinuousFlexibility.Radial.central_normalizedHermite_pairing`](../ContinuousFlexibility/Radial/OscillatorDifferentialPairing.lean#L138)
- [`ContinuousFlexibility.Radial.oscillatorEnergyDomain_zero`](../ContinuousFlexibility/Radial/OscillatorDifferentialPairing.lean#L168)
- [`ContinuousFlexibility.Radial.oscillatorEnergyDomain_add`](../ContinuousFlexibility/Radial/OscillatorDifferentialPairing.lean#L171)
- [`ContinuousFlexibility.Radial.oscillatorEnergyDomain_finset_sum`](../ContinuousFlexibility/Radial/OscillatorDifferentialPairing.lean#L186)
- [`ContinuousFlexibility.Radial.oscillatorExpression_add`](../ContinuousFlexibility/Radial/OscillatorDifferentialPairing.lean#L201)
- [`ContinuousFlexibility.Radial.oscillatorExpression_finset_sum`](../ContinuousFlexibility/Radial/OscillatorDifferentialPairing.lean#L217)
- [`ContinuousFlexibility.Radial.contDiff_normalizedOscillatorHermite`](../ContinuousFlexibility/Radial/OscillatorDifferentialPairing.lean#L240)
- [`ContinuousFlexibility.Radial.contDiff_finiteHermiteFunction`](../ContinuousFlexibility/Radial/OscillatorDifferentialPairing.lean#L244)
- [`ContinuousFlexibility.Radial.finiteHermiteFunction_energyDomain`](../ContinuousFlexibility/Radial/OscillatorDifferentialPairing.lean#L248)
- [`ContinuousFlexibility.Radial.oscillatorExpression_finiteHermiteFunction`](../ContinuousFlexibility/Radial/OscillatorDifferentialPairing.lean#L255)
- [`ContinuousFlexibility.Radial.centralExpression_finiteHermiteFunction`](../ContinuousFlexibility/Radial/OscillatorDifferentialPairing.lean#L271)

[OscillatorPhysicalFormBasis.lean](../ContinuousFlexibility/Radial/OscillatorPhysicalFormBasis.lean)：

- [`ContinuousFlexibility.Radial.physicalHermiteWeight_pos`](../ContinuousFlexibility/Radial/OscillatorPhysicalFormBasis.lean#L22)
- [`ContinuousFlexibility.Radial.memLp_sq_mul_normalizedHermite`](../ContinuousFlexibility/Radial/OscillatorPhysicalFormBasis.lean#L27)
- [`ContinuousFlexibility.Radial.memLp_second_deriv_normalizedHermite`](../ContinuousFlexibility/Radial/OscillatorPhysicalFormBasis.lean#L37)
- [`ContinuousFlexibility.Radial.physicalEnergy_inner_coordinates`](../ContinuousFlexibility/Radial/OscillatorPhysicalFormBasis.lean#L48)
- [`ContinuousFlexibility.Radial.physicalEnergyLift_inner`](../ContinuousFlexibility/Radial/OscillatorPhysicalFormBasis.lean#L70)
- [`ContinuousFlexibility.Radial.physicalEnergyLift_norm_sq`](../ContinuousFlexibility/Radial/OscillatorPhysicalFormBasis.lean#L87)
- [`ContinuousFlexibility.Radial.physicalEnergyLift_inner_operator`](../ContinuousFlexibility/Radial/OscillatorPhysicalFormBasis.lean#L92)
- [`ContinuousFlexibility.Radial.physicalEnergyLift_norm_sub_sq`](../ContinuousFlexibility/Radial/OscillatorPhysicalFormBasis.lean#L103)
- [`ContinuousFlexibility.Radial.centralHermiteImage_memLp`](../ContinuousFlexibility/Radial/OscillatorPhysicalFormBasis.lean#L123)
- [`ContinuousFlexibility.Radial.centralHermiteImage_toLp`](../ContinuousFlexibility/Radial/OscillatorPhysicalFormBasis.lean#L131)
- [`ContinuousFlexibility.Radial.physicalHermiteLift_inner`](../ContinuousFlexibility/Radial/OscillatorPhysicalFormBasis.lean#L147)
- [`ContinuousFlexibility.Radial.physicalHermiteLift_base`](../ContinuousFlexibility/Radial/OscillatorPhysicalFormBasis.lean#L158)
- [`ContinuousFlexibility.Radial.physicalHermiteVector_inner`](../ContinuousFlexibility/Radial/OscillatorPhysicalFormBasis.lean#L164)
- [`ContinuousFlexibility.Radial.physicalHermiteVector_orthonormal`](../ContinuousFlexibility/Radial/OscillatorPhysicalFormBasis.lean#L178)
- [`ContinuousFlexibility.Radial.physicalHermiteVector_base`](../ContinuousFlexibility/Radial/OscillatorPhysicalFormBasis.lean#L182)
- [`ContinuousFlexibility.Radial.physicalEnergy_position_pairing`](../ContinuousFlexibility/Radial/OscillatorPhysicalFormBasis.lean#L192)
- [`ContinuousFlexibility.Radial.physicalEnergy_inner_compact_operator`](../ContinuousFlexibility/Radial/OscillatorPhysicalFormBasis.lean#L212)
- [`ContinuousFlexibility.Radial.physicalHermiteCutoffLift_tendsto`](../ContinuousFlexibility/Radial/OscillatorPhysicalFormBasis.lean#L275)
- [`ContinuousFlexibility.Radial.physicalEnergy_inner_hermite`](../ContinuousFlexibility/Radial/OscillatorPhysicalFormBasis.lean#L309)
- [`ContinuousFlexibility.Radial.physicalHermiteVector_inner_left`](../ContinuousFlexibility/Radial/OscillatorPhysicalFormBasis.lean#L343)
- [`ContinuousFlexibility.Radial.physicalHermiteVector_inner_right`](../ContinuousFlexibility/Radial/OscillatorPhysicalFormBasis.lean#L356)
- [`ContinuousFlexibility.Radial.physicalHermiteVector_span_orthogonal`](../ContinuousFlexibility/Radial/OscillatorPhysicalFormBasis.lean#L363)
- [`ContinuousFlexibility.Radial.physicalHermiteBasis_apply`](../ContinuousFlexibility/Radial/OscillatorPhysicalFormBasis.lean#L385)
- [`ContinuousFlexibility.Radial.physicalHermiteBasis_repr`](../ContinuousFlexibility/Radial/OscillatorPhysicalFormBasis.lean#L390)
- [`ContinuousFlexibility.Radial.physicalEnergy_weighted_parseval`](../ContinuousFlexibility/Radial/OscillatorPhysicalFormBasis.lean#L397)
- [`ContinuousFlexibility.Radial.physicalEnergy_domain_iff`](../ContinuousFlexibility/Radial/OscillatorPhysicalFormBasis.lean#L410)
- [`ContinuousFlexibility.Radial.physicalCompactSmoothCore_dense`](../ContinuousFlexibility/Radial/OscillatorPhysicalFormBasis.lean#L460)

[OscillatorWeakEnergy.lean](../ContinuousFlexibility/Radial/OscillatorWeakEnergy.lean)：

- [`ContinuousFlexibility.Radial.physicalTestPairing_apply`](../ContinuousFlexibility/Radial/OscillatorWeakEnergy.lean#L38)
- [`ContinuousFlexibility.Radial.hasWeakDerivativeL2_iff_pairings`](../ContinuousFlexibility/Radial/OscillatorWeakEnergy.lean#L48)
- [`ContinuousFlexibility.Radial.hasWeakDerivativeL2_zero`](../ContinuousFlexibility/Radial/OscillatorWeakEnergy.lean#L59)
- [`ContinuousFlexibility.Radial.HasWeakDerivativeL2.add`](../ContinuousFlexibility/Radial/OscillatorWeakEnergy.lean#L64)
- [`ContinuousFlexibility.Radial.HasWeakDerivativeL2.smul`](../ContinuousFlexibility/Radial/OscillatorWeakEnergy.lean#L74)
- [`ContinuousFlexibility.Radial.physicalEnergyGraph_isClosed`](../ContinuousFlexibility/Radial/OscillatorWeakEnergy.lean#L161)
- [`ContinuousFlexibility.Radial.physicalEnergyCoordinate_apply`](../ContinuousFlexibility/Radial/OscillatorWeakEnergy.lean#L186)
- [`ContinuousFlexibility.Radial.physicalEnergyCoordinate_norm_le`](../ContinuousFlexibility/Radial/OscillatorWeakEnergy.lean#L189)
- [`ContinuousFlexibility.Radial.physicalEnergyTriple_norm_sq`](../ContinuousFlexibility/Radial/OscillatorWeakEnergy.lean#L193)
- [`ContinuousFlexibility.Radial.physicalEnergyBase_apply`](../ContinuousFlexibility/Radial/OscillatorWeakEnergy.lean#L198)
- [`ContinuousFlexibility.Radial.physicalEnergyDerivative_apply`](../ContinuousFlexibility/Radial/OscillatorWeakEnergy.lean#L201)
- [`ContinuousFlexibility.Radial.physicalEnergyPosition_apply`](../ContinuousFlexibility/Radial/OscillatorWeakEnergy.lean#L204)
- [`ContinuousFlexibility.Radial.physicalEnergySpace_norm_sq`](../ContinuousFlexibility/Radial/OscillatorWeakEnergy.lean#L207)
- [`ContinuousFlexibility.Radial.HasWeakDerivativeL2.zero_left`](../ContinuousFlexibility/Radial/OscillatorWeakEnergy.lean#L214)
- [`ContinuousFlexibility.Radial.physicalEnergySpace_zero_base`](../ContinuousFlexibility/Radial/OscillatorWeakEnergy.lean#L230)
- [`ContinuousFlexibility.Radial.physicalEnergyBase_injective`](../ContinuousFlexibility/Radial/OscillatorWeakEnergy.lean#L252)
- [`ContinuousFlexibility.Radial.physicalTestPairing_toLp`](../ContinuousFlexibility/Radial/OscillatorWeakEnergy.lean#L257)
- [`ContinuousFlexibility.Radial.hasWeakDerivativeL2_of_energyDomain`](../ContinuousFlexibility/Radial/OscillatorWeakEnergy.lean#L267)
- [`ContinuousFlexibility.Radial.physicalEnergy_weighted_memLp`](../ContinuousFlexibility/Radial/OscillatorWeakEnergy.lean#L282)
- [`ContinuousFlexibility.Radial.physicalEnergyLift_base`](../ContinuousFlexibility/Radial/OscillatorWeakEnergy.lean#L301)
- [`ContinuousFlexibility.Radial.physicalEnergyLift_derivative`](../ContinuousFlexibility/Radial/OscillatorWeakEnergy.lean#L305)
- [`ContinuousFlexibility.Radial.physicalEnergyLift_position`](../ContinuousFlexibility/Radial/OscillatorWeakEnergy.lean#L309)

[RadialSymbolBounds.lean](../ContinuousFlexibility/Radial/RadialSymbolBounds.lean)：

- [`ContinuousFlexibility.Radial.RadialSymbolBounds.contDiffAt`](../ContinuousFlexibility/Radial/RadialSymbolBounds.lean#L32)
- [`ContinuousFlexibility.Radial.RadialSymbolBounds.add`](../ContinuousFlexibility/Radial/RadialSymbolBounds.lean#L37)
- [`ContinuousFlexibility.Radial.RadialSymbolBounds.mul`](../ContinuousFlexibility/Radial/RadialSymbolBounds.lean#L68)
- [`ContinuousFlexibility.Radial.RadialSymbolBounds.const_mul`](../ContinuousFlexibility/Radial/RadialSymbolBounds.lean#L99)
- [`ContinuousFlexibility.Radial.RadialSymbolBounds.inv`](../ContinuousFlexibility/Radial/RadialSymbolBounds.lean#L152)
- [`ContinuousFlexibility.Radial.RadialSymbolBounds.neg`](../ContinuousFlexibility/Radial/RadialSymbolBounds.lean#L214)
- [`ContinuousFlexibility.Radial.RadialSymbolBounds.sub`](../ContinuousFlexibility/Radial/RadialSymbolBounds.lean#L221)
- [`ContinuousFlexibility.Radial.RadialSymbolBounds.div`](../ContinuousFlexibility/Radial/RadialSymbolBounds.lean#L228)

[CentralLeftAsymptotics.lean](../ContinuousFlexibility/Radial/CentralLeftAsymptotics.lean)：

- [`ContinuousFlexibility.Radial.gaussianLaplaceRatio_left_error`](../ContinuousFlexibility/Radial/CentralLeftAsymptotics.lean#L52)
- [`ContinuousFlexibility.Radial.centralRadiusLogDerivative_left_error`](../ContinuousFlexibility/Radial/CentralLeftAsymptotics.lean#L78)
- [`ContinuousFlexibility.Radial.centralRadiusLogDerivative_left_remainder_tendsto`](../ContinuousFlexibility/Radial/CentralLeftAsymptotics.lean#L106)
- [`ContinuousFlexibility.Radial.centralRadiusLogDerivative_left_sub_tendsto`](../ContinuousFlexibility/Radial/CentralLeftAsymptotics.lean#L115)
- [`ContinuousFlexibility.Radial.centralRadiusLogDerivative_left_ratio_tendsto`](../ContinuousFlexibility/Radial/CentralLeftAsymptotics.lean#L126)
- [`ContinuousFlexibility.Radial.hasDerivAt_centralLogRadius`](../ContinuousFlexibility/Radial/CentralLeftAsymptotics.lean#L138)
- [`ContinuousFlexibility.Radial.range_centralLogRadius`](../ContinuousFlexibility/Radial/CentralLeftAsymptotics.lean#L143)
- [`ContinuousFlexibility.Radial.hasDerivAt_centralLogRadiusInverse`](../ContinuousFlexibility/Radial/CentralLeftAsymptotics.lean#L151)
- [`ContinuousFlexibility.Radial.centralKernelHeight_logarithmic_derivative`](../ContinuousFlexibility/Radial/CentralLeftAsymptotics.lean#L168)
- [`ContinuousFlexibility.Radial.centralKernelHeight_left_logarithmic_slope_tendsto`](../ContinuousFlexibility/Radial/CentralLeftAsymptotics.lean#L192)
- [`ContinuousFlexibility.Radial.centralRadialProfile_logarithmic_derivative`](../ContinuousFlexibility/Radial/CentralLeftAsymptotics.lean#L213)
- [`ContinuousFlexibility.Radial.centralRadialProfile_left_logarithmic_slope_tendsto`](../ContinuousFlexibility/Radial/CentralLeftAsymptotics.lean#L240)
- [`ContinuousFlexibility.Radial.centralRadiusLogDerivative_left_symbol`](../ContinuousFlexibility/Radial/CentralLeftAsymptotics.lean#L274)
- [`ContinuousFlexibility.Radial.centralRadiusLogDerivative_left_derivative_error`](../ContinuousFlexibility/Radial/CentralLeftAsymptotics.lean#L328)
- [`ContinuousFlexibility.Radial.centralRadiusLogDerivative_left_original_derivative_error`](../ContinuousFlexibility/Radial/CentralLeftAsymptotics.lean#L338)
- [`ContinuousFlexibility.Radial.centralRadiusLogDerivative_left_growth_symbol`](../ContinuousFlexibility/Radial/CentralLeftAsymptotics.lean#L390)
- [`ContinuousFlexibility.Radial.centralRadiusLogDerivative_left_lower`](../ContinuousFlexibility/Radial/CentralLeftAsymptotics.lean#L410)
- [`ContinuousFlexibility.Radial.centralRadiusLogDerivative_left_inverse_symbol`](../ContinuousFlexibility/Radial/CentralLeftAsymptotics.lean#L418)
- [`ContinuousFlexibility.Radial.centralKernelHeight_left_slope_symbol`](../ContinuousFlexibility/Radial/CentralLeftAsymptotics.lean#L428)
- [`ContinuousFlexibility.Radial.centralRadialProfile_left_slope_symbol`](../ContinuousFlexibility/Radial/CentralLeftAsymptotics.lean#L443)

[CentralRadialClosedGraph.lean](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean)：

- [`ContinuousFlexibility.Radial.centralRadialInverseWeight_abs_le`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L27)
- [`ContinuousFlexibility.Radial.centralRadialInverseWeight_ae`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L38)
- [`ContinuousFlexibility.Radial.centralRadialInverseWeight_norm_le`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L43)
- [`ContinuousFlexibility.Radial.centralRadialInverseWeight_inner_swap`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L47)
- [`ContinuousFlexibility.Radial.centralRadialInverseWeight_hasWeight`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L51)
- [`ContinuousFlexibility.Radial.centralRadialInverseWeight_weighted`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L57)
- [`ContinuousFlexibility.Radial.centralRadialInverseWeight_injective`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L64)
- [`ContinuousFlexibility.Radial.centralRadialTestWeight_ae`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L76)
- [`ContinuousFlexibility.Radial.centralRadialTestWeight_hasWeight`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L81)
- [`ContinuousFlexibility.Radial.centralRadialInverseWeight_testWeight`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L89)
- [`ContinuousFlexibility.Radial.mem_centralRadialClosedGraph`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L122)
- [`ContinuousFlexibility.Radial.centralRadialClosedGraph_isClosed`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L125)
- [`ContinuousFlexibility.Radial.centralRadialClosedGraph_completeSpace`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L138)
- [`ContinuousFlexibility.Radial.centralRadialLeftInverse_testImage`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L152)
- [`ContinuousFlexibility.Radial.centralRadialInverseWeight_doubleInverse`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L166)
- [`ContinuousFlexibility.Radial.centralRadialDoubleInverse_graph`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L173)
- [`ContinuousFlexibility.Radial.centralRadialClosedGraph_even_kernel_iff`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L190)
- [`ContinuousFlexibility.Radial.mem_centralRadialClosedGraph_even_iff`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L201)
- [`ContinuousFlexibility.Radial.centralRadialClosedGraph_source_zero`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L236)
- [`ContinuousFlexibility.Radial.centralRadialClosedGraph_unique`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L256)
- [`ContinuousFlexibility.Radial.centralRadialClosedGraph_of_central`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L266)
- [`ContinuousFlexibility.Radial.centralRadialStrongGraphMap_apply`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L284)
- [`ContinuousFlexibility.Radial.centralRadialStrongGraphMap_test`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L288)
- [`ContinuousFlexibility.Radial.mem_centralRadialCompactSmoothGraph`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L305)
- [`ContinuousFlexibility.Radial.centralRadialCompactSmoothGraph_le`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L321)
- [`ContinuousFlexibility.Radial.centralRadialStrongGraphMap_mem_closure`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L330)
- [`ContinuousFlexibility.Radial.centralRadialCompactSmoothGraph_closure`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L359)
- [`ContinuousFlexibility.Radial.centralRadialHilbertInverse_norm_le`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L388)
- [`ContinuousFlexibility.Radial.centralRadialKernelVector_hasWeight`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L401)
- [`ContinuousFlexibility.Radial.centralRadialInverseWeight_kernel`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L405)
- [`ContinuousFlexibility.Radial.centralRadialKernel_pairing`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L409)
- [`ContinuousFlexibility.Radial.centralRadialKernelVector_graph`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L420)
- [`ContinuousFlexibility.Radial.centralRadialClosedGraph_two_kernel_iff`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L426)
- [`ContinuousFlexibility.Radial.centralRadialReducedLeftInverse_testImage`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L440)
- [`ContinuousFlexibility.Radial.centralRadialTwoGraphWeight_apply`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L462)
- [`ContinuousFlexibility.Radial.centralRadialTwoGraphWeight_test`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L469)
- [`ContinuousFlexibility.Radial.centralRadialTwoGraphWeight_ground`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L480)
- [`ContinuousFlexibility.Radial.centralRadialClosedGraph_two_compat`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L485)
- [`ContinuousFlexibility.Radial.centralRadialObliqueSource_apply`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L510)
- [`ContinuousFlexibility.Radial.centralRadialObliqueSource_compat`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L515)
- [`ContinuousFlexibility.Radial.centralRadialReducedHilbertInverse_graph`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L524)
- [`ContinuousFlexibility.Radial.centralRadialReducedHilbertInverse_graph_compatible`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L536)
- [`ContinuousFlexibility.Radial.mem_centralRadialClosedGraph_two_iff`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L542)
- [`ContinuousFlexibility.Radial.centralRadialInverseWeight_twoGraphWeight`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L562)
- [`ContinuousFlexibility.Radial.mem_centralRadialTwoCompactSmoothGraph`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L578)
- [`ContinuousFlexibility.Radial.centralRadialTwoCompactSmoothGraph_closure`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L626)
- [`ContinuousFlexibility.Radial.centralRadialReducedHilbertInverse_row`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L691)
- [`ContinuousFlexibility.Radial.centralRadialReducedHilbertInverse_unique`](../ContinuousFlexibility/Radial/CentralRadialClosedGraph.lean#L700)

[CentralRadialHilbert.lean](../ContinuousFlexibility/Radial/CentralRadialHilbert.lean)：

- [`ContinuousFlexibility.Radial.continuous_centralRadialAmplitude`](../ContinuousFlexibility/Radial/CentralRadialHilbert.lean#L29)
- [`ContinuousFlexibility.Radial.centralRadialAmplitude_pos`](../ContinuousFlexibility/Radial/CentralRadialHilbert.lean#L34)
- [`ContinuousFlexibility.Radial.centralRadialAmplitude_sq`](../ContinuousFlexibility/Radial/CentralRadialHilbert.lean#L39)
- [`ContinuousFlexibility.Radial.centralRadial_pullback_ae`](../ContinuousFlexibility/Radial/CentralRadialHilbert.lean#L53)
- [`ContinuousFlexibility.Radial.centralRadialPullback_memLp_iff`](../ContinuousFlexibility/Radial/CentralRadialHilbert.lean#L62)
- [`ContinuousFlexibility.Radial.centralRadial_memLp_iff`](../ContinuousFlexibility/Radial/CentralRadialHilbert.lean#L105)
- [`ContinuousFlexibility.Radial.centralRadialHilbertEquiv_ae`](../ContinuousFlexibility/Radial/CentralRadialHilbert.lean#L211)
- [`ContinuousFlexibility.Radial.centralRadialHilbertEquiv_symm_pullback_ae`](../ContinuousFlexibility/Radial/CentralRadialHilbert.lean#L217)
- [`ContinuousFlexibility.Radial.centralRadialHeight_pullback`](../ContinuousFlexibility/Radial/CentralRadialHilbert.lean#L230)
- [`ContinuousFlexibility.Radial.centralRadialHeight_memLp`](../ContinuousFlexibility/Radial/CentralRadialHilbert.lean#L234)
- [`ContinuousFlexibility.Radial.centralRadialHilbertEquiv_height`](../ContinuousFlexibility/Radial/CentralRadialHilbert.lean#L246)
- [`ContinuousFlexibility.Radial.centralRadialHeight_norm_sq`](../ContinuousFlexibility/Radial/CentralRadialHilbert.lean#L263)
- [`ContinuousFlexibility.Radial.contDiffAt_centralRadialHeight`](../ContinuousFlexibility/Radial/CentralRadialHilbert.lean#L274)
- [`ContinuousFlexibility.Radial.radialJacobi_centralRadialHeight`](../ContinuousFlexibility/Radial/CentralRadialHilbert.lean#L283)
- [`ContinuousFlexibility.Radial.centralRadial_ordinary_forcing_iff`](../ContinuousFlexibility/Radial/CentralRadialHilbert.lean#L307)
- [`ContinuousFlexibility.Radial.centralRadialSpectralExpression_height`](../ContinuousFlexibility/Radial/CentralRadialHilbert.lean#L321)
- [`ContinuousFlexibility.Radial.centralRadial_spectral_forcing_iff`](../ContinuousFlexibility/Radial/CentralRadialHilbert.lean#L333)
- [`ContinuousFlexibility.Radial.centralRadialSpectralExpression_normalized`](../ContinuousFlexibility/Radial/CentralRadialHilbert.lean#L345)
- [`ContinuousFlexibility.Radial.memLp_centralRadialWeight`](../ContinuousFlexibility/Radial/CentralRadialHilbert.lean#L357)
- [`ContinuousFlexibility.Radial.memLp_centralRadialWeightedGround`](../ContinuousFlexibility/Radial/CentralRadialHilbert.lean#L374)
- [`ContinuousFlexibility.Radial.centralRadialHeight_ground_eq`](../ContinuousFlexibility/Radial/CentralRadialHilbert.lean#L380)
- [`ContinuousFlexibility.Radial.memLp_centralKernelHeight`](../ContinuousFlexibility/Radial/CentralRadialHilbert.lean#L388)
- [`ContinuousFlexibility.Radial.centralRadialHilbertEquiv_kernel`](../ContinuousFlexibility/Radial/CentralRadialHilbert.lean#L395)

[CentralRadialMeasure.lean](../ContinuousFlexibility/Radial/CentralRadialMeasure.lean)：

- [`ContinuousFlexibility.Radial.measurableEmbedding_centralRadius`](../ContinuousFlexibility/Radial/CentralRadialMeasure.lean#L33)
- [`ContinuousFlexibility.Radial.centralRadius_lintegral_change`](../ContinuousFlexibility/Radial/CentralRadialMeasure.lean#L37)
- [`ContinuousFlexibility.Radial.centralRadius_integrable_iff`](../ContinuousFlexibility/Radial/CentralRadialMeasure.lean#L46)
- [`ContinuousFlexibility.Radial.centralRadius_integral_change`](../ContinuousFlexibility/Radial/CentralRadialMeasure.lean#L55)
- [`ContinuousFlexibility.Radial.centralRadialVarpi_pos`](../ContinuousFlexibility/Radial/CentralRadialMeasure.lean#L75)
- [`ContinuousFlexibility.Radial.continuousOn_centralRadialVarpi`](../ContinuousFlexibility/Radial/CentralRadialMeasure.lean#L79)
- [`ContinuousFlexibility.Radial.centralRadialVarpi_aemeasurable`](../ContinuousFlexibility/Radial/CentralRadialMeasure.lean#L84)
- [`ContinuousFlexibility.Radial.continuous_centralRadialPullbackDensity`](../ContinuousFlexibility/Radial/CentralRadialMeasure.lean#L89)
- [`ContinuousFlexibility.Radial.centralRadialPullbackDensity_pos`](../ContinuousFlexibility/Radial/CentralRadialMeasure.lean#L95)
- [`ContinuousFlexibility.Radial.centralRadialVarpi_pullback_density`](../ContinuousFlexibility/Radial/CentralRadialMeasure.lean#L100)
- [`ContinuousFlexibility.Radial.centralRadialSpectralMeasure_map`](../ContinuousFlexibility/Radial/CentralRadialMeasure.lean#L107)
- [`ContinuousFlexibility.Radial.centralRadialSpectral_integrable_iff`](../ContinuousFlexibility/Radial/CentralRadialMeasure.lean#L136)
- [`ContinuousFlexibility.Radial.centralRadialSpectral_integral_change`](../ContinuousFlexibility/Radial/CentralRadialMeasure.lean#L147)
- [`ContinuousFlexibility.Radial.centralRadial_source_pairing_integral`](../ContinuousFlexibility/Radial/CentralRadialMeasure.lean#L157)
- [`ContinuousFlexibility.Radial.centralRadial_source_pairing_integrable_iff`](../ContinuousFlexibility/Radial/CentralRadialMeasure.lean#L165)
- [`ContinuousFlexibility.Radial.centralRadial_height_sq_integral`](../ContinuousFlexibility/Radial/CentralRadialMeasure.lean#L179)
- [`ContinuousFlexibility.Radial.centralRadial_height_sq_integrable_iff`](../ContinuousFlexibility/Radial/CentralRadialMeasure.lean#L190)
- [`ContinuousFlexibility.Radial.centralRadial_spectral_pairing_integral`](../ContinuousFlexibility/Radial/CentralRadialMeasure.lean#L205)
- [`ContinuousFlexibility.Radial.centralRadial_dr_truncation`](../ContinuousFlexibility/Radial/CentralRadialMeasure.lean#L234)
- [`ContinuousFlexibility.Radial.centralRadial_spectral_truncation`](../ContinuousFlexibility/Radial/CentralRadialMeasure.lean#L251)

[CentralRadialWeakTransport.lean](../ContinuousFlexibility/Radial/CentralRadialWeakTransport.lean)：

- [`ContinuousFlexibility.Radial.centralRadialCompactTest_pullback`](../ContinuousFlexibility/Radial/CentralRadialWeakTransport.lean#L29)
- [`ContinuousFlexibility.Radial.centralRadialCompactTest_tsupport_subset`](../ContinuousFlexibility/Radial/CentralRadialWeakTransport.lean#L45)
- [`ContinuousFlexibility.Radial.centralRadialCompactTest_hasCompactSupport`](../ContinuousFlexibility/Radial/CentralRadialWeakTransport.lean#L49)
- [`ContinuousFlexibility.Radial.centralRadialCompactTest_tsupport_positive`](../ContinuousFlexibility/Radial/CentralRadialWeakTransport.lean#L54)
- [`ContinuousFlexibility.Radial.centralRadialCompactTest_eventuallyEq`](../ContinuousFlexibility/Radial/CentralRadialWeakTransport.lean#L60)
- [`ContinuousFlexibility.Radial.contDiff_centralRadialCompactTest`](../ContinuousFlexibility/Radial/CentralRadialWeakTransport.lean#L65)
- [`ContinuousFlexibility.Radial.contDiff_centralRadialTestPullback`](../ContinuousFlexibility/Radial/CentralRadialWeakTransport.lean#L86)
- [`ContinuousFlexibility.Radial.centralRadialTestPullback_hasCompactSupport`](../ContinuousFlexibility/Radial/CentralRadialWeakTransport.lean#L90)
- [`ContinuousFlexibility.Radial.centralRadialTestPullback_compactTest`](../ContinuousFlexibility/Radial/CentralRadialWeakTransport.lean#L102)
- [`ContinuousFlexibility.Radial.centralRadialCompactTest_testPullback`](../ContinuousFlexibility/Radial/CentralRadialWeakTransport.lean#L108)
- [`ContinuousFlexibility.Radial.radialJacobi_centralRadialCompactTest`](../ContinuousFlexibility/Radial/CentralRadialWeakTransport.lean#L127)
- [`ContinuousFlexibility.Radial.centralRadial_dr_test_pairing`](../ContinuousFlexibility/Radial/CentralRadialWeakTransport.lean#L146)
- [`ContinuousFlexibility.Radial.centralRadial_spectral_test_pairing`](../ContinuousFlexibility/Radial/CentralRadialWeakTransport.lean#L187)
- [`ContinuousFlexibility.Radial.centralRadial_distribution_test_integrable`](../ContinuousFlexibility/Radial/CentralRadialWeakTransport.lean#L223)
- [`ContinuousFlexibility.Radial.centralRadialDistributionEquation_iff_normalized`](../ContinuousFlexibility/Radial/CentralRadialWeakTransport.lean#L261)
- [`ContinuousFlexibility.Radial.centralRadialDistributionEquation_iff_graph`](../ContinuousFlexibility/Radial/CentralRadialWeakTransport.lean#L287)

[CentralRightAsymptotics.lean](../ContinuousFlexibility/Radial/CentralRightAsymptotics.lean)：

- [`ContinuousFlexibility.Radial.hasDerivAt_centralRadiusLogDerivative`](../ContinuousFlexibility/Radial/CentralRightAsymptotics.lean#L57)
- [`ContinuousFlexibility.Radial.centralRadiusLogDerivative_riccati`](../ContinuousFlexibility/Radial/CentralRightAsymptotics.lean#L69)
- [`ContinuousFlexibility.Radial.centralRightLogDerivativeError_contDiffOn`](../ContinuousFlexibility/Radial/CentralRightAsymptotics.lean#L87)
- [`ContinuousFlexibility.Radial.hasDerivAt_centralRightLogDerivativeError`](../ContinuousFlexibility/Radial/CentralRightAsymptotics.lean#L108)
- [`ContinuousFlexibility.Radial.centralRightLogDerivativeError_zero_bound`](../ContinuousFlexibility/Radial/CentralRightAsymptotics.lean#L178)
- [`ContinuousFlexibility.Radial.centralRightLogDerivativeError_symbol`](../ContinuousFlexibility/Radial/CentralRightAsymptotics.lean#L403)
- [`ContinuousFlexibility.Radial.centralRadiusLogDerivative_right_derivative_error`](../ContinuousFlexibility/Radial/CentralRightAsymptotics.lean#L472)
- [`ContinuousFlexibility.Radial.centralRadiusLogDerivative_right_remainder_tendsto`](../ContinuousFlexibility/Radial/CentralRightAsymptotics.lean#L488)
- [`ContinuousFlexibility.Radial.centralRadiusLogDerivative_right_sub_tendsto`](../ContinuousFlexibility/Radial/CentralRightAsymptotics.lean#L497)
- [`ContinuousFlexibility.Radial.centralRadiusLogDerivative_right_ratio_tendsto`](../ContinuousFlexibility/Radial/CentralRightAsymptotics.lean#L510)
- [`ContinuousFlexibility.Radial.centralRadiusLogDerivative_right_symbol`](../ContinuousFlexibility/Radial/CentralRightAsymptotics.lean#L528)
- [`ContinuousFlexibility.Radial.centralRadiusLogDerivative_right_linear_lower`](../ContinuousFlexibility/Radial/CentralRightAsymptotics.lean#L542)
- [`ContinuousFlexibility.Radial.centralRadiusLogDerivative_right_inverse_symbol`](../ContinuousFlexibility/Radial/CentralRightAsymptotics.lean#L566)
- [`ContinuousFlexibility.Radial.centralRightHeightSlope_symbol`](../ContinuousFlexibility/Radial/CentralRightAsymptotics.lean#L576)
- [`ContinuousFlexibility.Radial.centralRightProfileSlope_symbol`](../ContinuousFlexibility/Radial/CentralRightAsymptotics.lean#L595)
- [`ContinuousFlexibility.Radial.centralRightHeightSlope_tendsto`](../ContinuousFlexibility/Radial/CentralRightAsymptotics.lean#L618)
- [`ContinuousFlexibility.Radial.centralRightProfileSlope_tendsto`](../ContinuousFlexibility/Radial/CentralRightAsymptotics.lean#L635)

[CentralTurningPoints.lean](../ContinuousFlexibility/Radial/CentralTurningPoints.lean)：

- [`ContinuousFlexibility.Radial.centralRadialProfile_second_deriv_scaled_at_turning`](../ContinuousFlexibility/Radial/CentralTurningPoints.lean#L23)
- [`ContinuousFlexibility.Radial.centralRadialProfile_critical_iff`](../ContinuousFlexibility/Radial/CentralTurningPoints.lean#L53)
- [`ContinuousFlexibility.Radial.central_turning_radii_pos_ordered`](../ContinuousFlexibility/Radial/CentralTurningPoints.lean#L72)
- [`ContinuousFlexibility.Radial.centralRadialProfile_second_deriv_left_neg`](../ContinuousFlexibility/Radial/CentralTurningPoints.lean#L79)
- [`ContinuousFlexibility.Radial.centralRadialProfile_second_deriv_right_pos`](../ContinuousFlexibility/Radial/CentralTurningPoints.lean#L95)

[GaussianLaplaceLeftSymbols.lean](../ContinuousFlexibility/Radial/GaussianLaplaceLeftSymbols.lean)：

- [`ContinuousFlexibility.Radial.RadialSymbolBounds.congr`](../ContinuousFlexibility/Radial/GaussianLaplaceLeftSymbols.lean#L24)
- [`ContinuousFlexibility.Radial.gammaLaplaceMoment_left_scale`](../ContinuousFlexibility/Radial/GaussianLaplaceLeftSymbols.lean#L35)
- [`ContinuousFlexibility.Radial.gammaLaplaceMoment_left_succ`](../ContinuousFlexibility/Radial/GaussianLaplaceLeftSymbols.lean#L43)
- [`ContinuousFlexibility.Radial.contDiffOn_gammaLaplaceMoment_left`](../ContinuousFlexibility/Radial/GaussianLaplaceLeftSymbols.lean#L48)
- [`ContinuousFlexibility.Radial.hasDerivAt_gammaLaplaceMoment_left`](../ContinuousFlexibility/Radial/GaussianLaplaceLeftSymbols.lean#L59)
- [`ContinuousFlexibility.Radial.iteratedDeriv_gammaLaplaceMoment_left`](../ContinuousFlexibility/Radial/GaussianLaplaceLeftSymbols.lean#L78)
- [`ContinuousFlexibility.Radial.gammaLaplaceMoment_left_symbol`](../ContinuousFlexibility/Radial/GaussianLaplaceLeftSymbols.lean#L99)
- [`ContinuousFlexibility.Radial.gaussianLaplaceMoment_left_symbol`](../ContinuousFlexibility/Radial/GaussianLaplaceLeftSymbols.lean#L117)
- [`ContinuousFlexibility.Radial.gaussianLaplaceMoment_left_error_symbol`](../ContinuousFlexibility/Radial/GaussianLaplaceLeftSymbols.lean#L141)
- [`ContinuousFlexibility.Radial.gaussianLaplaceMoment_left_lower_constant_pos`](../ContinuousFlexibility/Radial/GaussianLaplaceLeftSymbols.lean#L169)
- [`ContinuousFlexibility.Radial.gaussianLaplaceMoment_left_lower`](../ContinuousFlexibility/Radial/GaussianLaplaceLeftSymbols.lean#L175)
- [`ContinuousFlexibility.Radial.gaussianLaplaceMoment_left_ne_zero`](../ContinuousFlexibility/Radial/GaussianLaplaceLeftSymbols.lean#L194)
- [`ContinuousFlexibility.Radial.gammaLaplaceQuotient_left_symbol`](../ContinuousFlexibility/Radial/GaussianLaplaceLeftSymbols.lean#L198)

[OscillatorPotentialEnergy.lean](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean)：

- [`ContinuousFlexibility.Radial.continuous_potentialEnergyWeight`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L31)
- [`ContinuousFlexibility.Radial.potentialEnergyWeight_pos`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L36)
- [`ContinuousFlexibility.Radial.potentialEnergyWeightConstant_pos`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L39)
- [`ContinuousFlexibility.Radial.potentialEnergyWeight_sq`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L43)
- [`ContinuousFlexibility.Radial.potentialEnergyWeightConstant_sq`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L47)
- [`ContinuousFlexibility.Radial.potentialEnergyWeight_controls_position`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L56)
- [`ContinuousFlexibility.Radial.potentialEnergyWeight_le_linear`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L72)
- [`ContinuousFlexibility.Radial.measurable_potentialPositionCoefficient`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L100)
- [`ContinuousFlexibility.Radial.measurable_potentialBaseCoefficient`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L104)
- [`ContinuousFlexibility.Radial.measurable_potentialSignedCoefficient`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L109)
- [`ContinuousFlexibility.Radial.potentialPositionCoefficient_abs_le`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L115)
- [`ContinuousFlexibility.Radial.potentialBaseCoefficient_abs_le`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L122)
- [`ContinuousFlexibility.Radial.potentialSignedCoefficient_abs_le`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L130)
- [`ContinuousFlexibility.Radial.potentialPositionCoefficient_mul_weight`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L140)
- [`ContinuousFlexibility.Radial.potentialEnergyWeight_decomposition`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L144)
- [`ContinuousFlexibility.Radial.potentialPositionMultiplier_ae`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L174)
- [`ContinuousFlexibility.Radial.potentialBaseMultiplier_ae`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L179)
- [`ContinuousFlexibility.Radial.potentialSignedMultiplier_ae`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L184)
- [`ContinuousFlexibility.Radial.potentialToPosition_zero`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L206)
- [`ContinuousFlexibility.Radial.potentialToPosition_one`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L209)
- [`ContinuousFlexibility.Radial.potentialToPosition_two`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L212)
- [`ContinuousFlexibility.Radial.positionToPotential_zero`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L215)
- [`ContinuousFlexibility.Radial.positionToPotential_one`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L218)
- [`ContinuousFlexibility.Radial.positionToPotential_two`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L221)
- [`ContinuousFlexibility.Radial.potentialToPosition_mem`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L255)
- [`ContinuousFlexibility.Radial.positionToPotential_mem`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L262)
- [`ContinuousFlexibility.Radial.positionToPotential_potentialToPosition`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L278)
- [`ContinuousFlexibility.Radial.potentialToPosition_positionToPotential`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L292)
- [`ContinuousFlexibility.Radial.mem_potentialEnergyGraph_iff`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L308)
- [`ContinuousFlexibility.Radial.potentialEnergyGraph_isClosed`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L321)
- [`ContinuousFlexibility.Radial.physicalEnergyToPotential_potentialEnergyToPhysical`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L345)
- [`ContinuousFlexibility.Radial.potentialEnergyToPhysical_physicalEnergyToPotential`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L349)
- [`ContinuousFlexibility.Radial.positionToPotential_compact_lift`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L361)
- [`ContinuousFlexibility.Radial.potentialCompactSmoothCore_subset`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L381)
- [`ContinuousFlexibility.Radial.potentialCompactSmoothCore_closure`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L414)
- [`ContinuousFlexibility.Radial.physical_potential_pairing_ae`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L447)
- [`ContinuousFlexibility.Radial.physical_potential_integrable`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L460)
- [`ContinuousFlexibility.Radial.physical_potential_integral`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L470)
- [`ContinuousFlexibility.Radial.potentialEnergy_integrable`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L484)
- [`ContinuousFlexibility.Radial.physicalEnergy_inner_potential`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L489)
- [`ContinuousFlexibility.Radial.potentialClosedFormEquation_iff_physical`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L508)
- [`ContinuousFlexibility.Radial.potentialClosedFormEquation_iff_centralClosedGraph`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L545)
- [`ContinuousFlexibility.Radial.centralPotentialValue_lower`](../ContinuousFlexibility/Radial/OscillatorPotentialEnergy.lean#L551)

[RadialDampedBounds.lean](../ContinuousFlexibility/Radial/RadialDampedBounds.lean)：

- [`ContinuousFlexibility.Radial.extend_norm_power_bound_from_tail`](../ContinuousFlexibility/Radial/RadialDampedBounds.lean#L28)
- [`ContinuousFlexibility.Radial.exists_norm_power_bound_of_damped_deriv`](../ContinuousFlexibility/Radial/RadialDampedBounds.lean#L102)

[RadialMaterialJets.lean](../ContinuousFlexibility/Radial/RadialMaterialJets.lean)：

- [`ContinuousFlexibility.Radial.RadialSymbolBounds.deriv`](../ContinuousFlexibility/Radial/RadialMaterialJets.lean#L22)
- [`ContinuousFlexibility.Radial.contDiff_radialMaterialDeriv`](../ContinuousFlexibility/Radial/RadialMaterialJets.lean#L37)
- [`ContinuousFlexibility.Radial.contDiff_iterate_radialMaterialDeriv`](../ContinuousFlexibility/Radial/RadialMaterialJets.lean#L42)
- [`ContinuousFlexibility.Radial.deriv_comp_radialMaterialDeriv`](../ContinuousFlexibility/Radial/RadialMaterialJets.lean#L51)
- [`ContinuousFlexibility.Radial.iteratedDeriv_comp_radialMaterialDeriv`](../ContinuousFlexibility/Radial/RadialMaterialJets.lean#L62)
- [`ContinuousFlexibility.Radial.RadialSymbolBounds.materialDeriv`](../ContinuousFlexibility/Radial/RadialMaterialJets.lean#L73)
- [`ContinuousFlexibility.Radial.RadialSymbolBounds.iterate_materialDeriv`](../ContinuousFlexibility/Radial/RadialMaterialJets.lean#L80)
- [`ContinuousFlexibility.Radial.contDiff_centralLogModelCoordinate`](../ContinuousFlexibility/Radial/RadialMaterialJets.lean#L93)
- [`ContinuousFlexibility.Radial.centralLogModelCoordinate_logRadius`](../ContinuousFlexibility/Radial/RadialMaterialJets.lean#L100)
- [`ContinuousFlexibility.Radial.contDiff_centralMaterialCoefficient`](../ContinuousFlexibility/Radial/RadialMaterialJets.lean#L109)
- [`ContinuousFlexibility.Radial.contDiff_centralOrientedCoordinate`](../ContinuousFlexibility/Radial/RadialMaterialJets.lean#L115)
- [`ContinuousFlexibility.Radial.hasDerivAt_centralOrientedCoordinate`](../ContinuousFlexibility/Radial/RadialMaterialJets.lean#L119)
- [`ContinuousFlexibility.Radial.centralOrientedCoordinate_logRadius`](../ContinuousFlexibility/Radial/RadialMaterialJets.lean#L127)
- [`ContinuousFlexibility.Radial.iteratedDeriv_comp_centralOrientedCoordinate`](../ContinuousFlexibility/Radial/RadialMaterialJets.lean#L132)
- [`ContinuousFlexibility.Radial.centralMaterialCoefficient_right_symbol`](../ContinuousFlexibility/Radial/RadialMaterialJets.lean#L140)
- [`ContinuousFlexibility.Radial.centralMaterialCoefficient_left_symbol`](../ContinuousFlexibility/Radial/RadialMaterialJets.lean#L147)
- [`ContinuousFlexibility.Radial.central_material_pullback_bound`](../ContinuousFlexibility/Radial/RadialMaterialJets.lean#L157)
- [`ContinuousFlexibility.Radial.contDiff_centralHeightSlopeOnRay`](../ContinuousFlexibility/Radial/RadialMaterialJets.lean#L186)
- [`ContinuousFlexibility.Radial.contDiff_centralProfileSlopeOnRay`](../ContinuousFlexibility/Radial/RadialMaterialJets.lean#L192)
- [`ContinuousFlexibility.Radial.centralHeightLogSlope_eq_oriented`](../ContinuousFlexibility/Radial/RadialMaterialJets.lean#L198)
- [`ContinuousFlexibility.Radial.centralProfileLogSlope_eq_oriented`](../ContinuousFlexibility/Radial/RadialMaterialJets.lean#L207)
- [`ContinuousFlexibility.Radial.centralHeightLogSlope_right_derivative_bound`](../ContinuousFlexibility/Radial/RadialMaterialJets.lean#L243)
- [`ContinuousFlexibility.Radial.centralHeightLogSlope_left_derivative_bound`](../ContinuousFlexibility/Radial/RadialMaterialJets.lean#L256)
- [`ContinuousFlexibility.Radial.centralProfileLogSlope_right_derivative_bound`](../ContinuousFlexibility/Radial/RadialMaterialJets.lean#L271)
- [`ContinuousFlexibility.Radial.centralProfileLogSlope_left_derivative_bound`](../ContinuousFlexibility/Radial/RadialMaterialJets.lean#L284)

[CentralAuxiliaryBorder.lean](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean)：

- [`ContinuousFlexibility.Radial.contDiff_centralAuxiliaryDensity`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L28)
- [`ContinuousFlexibility.Radial.centralAuxiliaryDensity_hasCompactSupport`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L31)
- [`ContinuousFlexibility.Radial.centralAuxiliaryDensity_tsupport_positive`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L34)
- [`ContinuousFlexibility.Radial.centralAuxiliaryFunction_nonneg`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L47)
- [`ContinuousFlexibility.Radial.centralAuxiliaryFunction_tsupport_subset`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L50)
- [`ContinuousFlexibility.Radial.centralAuxiliaryFunction_tsupport_positive`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L59)
- [`ContinuousFlexibility.Radial.centralAuxiliaryFunction_hasCompactSupport`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L62)
- [`ContinuousFlexibility.Radial.contDiff_centralAuxiliaryFunction`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L66)
- [`ContinuousFlexibility.Radial.centralAuxiliaryFunction_mul_kernel`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L78)
- [`ContinuousFlexibility.Radial.centralAuxiliaryFunction_pairing`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L82)
- [`ContinuousFlexibility.Radial.centralAuxiliaryFunction_pairing_positive`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L89)
- [`ContinuousFlexibility.Radial.centralAuxiliarySourceFunction_apply`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L101)
- [`ContinuousFlexibility.Radial.contDiff_centralAuxiliarySourceFunction`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L108)
- [`ContinuousFlexibility.Radial.centralAuxiliarySourceFunction_hasCompactSupport`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L114)
- [`ContinuousFlexibility.Radial.centralAuxiliarySourceFunction_memLp`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L119)
- [`ContinuousFlexibility.Radial.centralAuxiliarySourceVector_ae`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L126)
- [`ContinuousFlexibility.Radial.centralAuxiliaryColumnFunction_transform`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L154)
- [`ContinuousFlexibility.Radial.centralAuxiliaryColumnFunction_memLp`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L168)
- [`ContinuousFlexibility.Radial.centralAuxiliaryColumn_transform`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L180)
- [`ContinuousFlexibility.Radial.centralAuxiliaryColumn_norm`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L190)
- [`ContinuousFlexibility.Radial.centralAuxiliaryRow_integrable`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L209)
- [`ContinuousFlexibility.Radial.centralAuxiliaryRow_pairing`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L219)
- [`ContinuousFlexibility.Radial.centralAuxiliaryRow_norm`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L237)
- [`ContinuousFlexibility.Radial.centralAuxiliaryRow_transport`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L241)
- [`ContinuousFlexibility.Radial.centralAuxiliaryKernelScale_pos`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L250)
- [`ContinuousFlexibility.Radial.centralAuxiliaryKernelVector_ae`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L268)
- [`ContinuousFlexibility.Radial.centralAuxiliaryKernelVector_graph`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L287)
- [`ContinuousFlexibility.Radial.centralAuxiliarySource_kernel_pairing`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L293)
- [`ContinuousFlexibility.Radial.centralAuxiliaryKernelFunction_memLp`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L310)
- [`ContinuousFlexibility.Radial.centralAuxiliaryKernel_transform`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L319)
- [`ContinuousFlexibility.Radial.centralAuxiliaryKernel_norm`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L332)
- [`ContinuousFlexibility.Radial.centralAuxiliary_scaled_pairing`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L336)
- [`ContinuousFlexibility.Radial.centralAuxiliaryRow_kernel`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L346)
- [`ContinuousFlexibility.Radial.centralAuxiliaryBorderColumn_bound`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L359)
- [`ContinuousFlexibility.Radial.centralAuxiliaryBorderColumn_pairing`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L364)
- [`ContinuousFlexibility.Radial.centralAuxiliaryCorrectedSource_apply`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L375)
- [`ContinuousFlexibility.Radial.centralAuxiliaryCorrectedSource_compat`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L381)
- [`ContinuousFlexibility.Radial.centralAuxiliaryOutput_apply`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L412)
- [`ContinuousFlexibility.Radial.centralAuxiliaryScalar_apply`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L419)
- [`ContinuousFlexibility.Radial.centralAuxiliaryInverse_apply`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L424)
- [`ContinuousFlexibility.Radial.centralAuxiliaryInverse_solves`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L435)
- [`ContinuousFlexibility.Radial.centralAuxiliaryInverse_unique`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L462)
- [`ContinuousFlexibility.Radial.centralAuxiliaryPairEquiv_apply`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L500)
- [`ContinuousFlexibility.Radial.centralAuxiliaryPhysicalEquation_iff`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L511)
- [`ContinuousFlexibility.Radial.centralAuxiliaryPhysicalInverse_apply`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L526)
- [`ContinuousFlexibility.Radial.centralAuxiliaryPhysicalInverse_transform`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L531)
- [`ContinuousFlexibility.Radial.centralAuxiliaryPhysicalInverse_solves`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L539)
- [`ContinuousFlexibility.Radial.centralAuxiliaryPhysicalInverse_unique`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L552)
- [`ContinuousFlexibility.Radial.centralAuxiliaryPhysicalInverse_uniform_bound`](../ContinuousFlexibility/Radial/CentralAuxiliaryBorder.lean#L564)

[CentralFullStatement.lean](../ContinuousFlexibility/Radial/CentralFullStatement.lean)：

- [`ContinuousFlexibility.Radial.centralAuxiliaryScalarReflection_apply`](../ContinuousFlexibility/Radial/CentralFullStatement.lean#L26)
- [`ContinuousFlexibility.Radial.centralAuxiliaryScalarReflection_norm`](../ContinuousFlexibility/Radial/CentralFullStatement.lean#L30)
- [`ContinuousFlexibility.Radial.centralAuxiliaryScalarReflection_involutive`](../ContinuousFlexibility/Radial/CentralFullStatement.lean#L36)
- [`ContinuousFlexibility.Radial.centralAuxiliaryStatementInverse_solves`](../ContinuousFlexibility/Radial/CentralFullStatement.lean#L48)
- [`ContinuousFlexibility.Radial.centralAuxiliaryStatementInverse_unique`](../ContinuousFlexibility/Radial/CentralFullStatement.lean#L58)
- [`ContinuousFlexibility.Radial.centralAuxiliaryStatementInverse_norm_le`](../ContinuousFlexibility/Radial/CentralFullStatement.lean#L67)
- [`ContinuousFlexibility.Radial.bridge_centralRadialSpectral_integral_density`](../ContinuousFlexibility/Radial/CentralFullStatement.lean#L84)
- [`ContinuousFlexibility.Radial.centralAuxiliaryGraph_implies_physicalEquation`](../ContinuousFlexibility/Radial/CentralFullStatement.lean#L97)
- [`ContinuousFlexibility.Radial.centralAuxiliaryColumn_square_integrable`](../ContinuousFlexibility/Radial/CentralFullStatement.lean#L187)
- [`ContinuousFlexibility.Radial.centralAuxiliaryColumn_square_integral`](../ContinuousFlexibility/Radial/CentralFullStatement.lean#L200)
- [`ContinuousFlexibility.Radial.centralAuxiliaryKernel_square_integrable`](../ContinuousFlexibility/Radial/CentralFullStatement.lean#L216)
- [`ContinuousFlexibility.Radial.centralAuxiliaryKernel_square_integral`](../ContinuousFlexibility/Radial/CentralFullStatement.lean#L228)
- [`ContinuousFlexibility.Radial.centralAuxiliaryStatement_uniform_estimates`](../ContinuousFlexibility/Radial/CentralFullStatement.lean#L243)
- [`ContinuousFlexibility.Radial.centralAuxiliaryColumn_pairing_test`](../ContinuousFlexibility/Radial/CentralFullStatement.lean#L271)
- [`ContinuousFlexibility.Radial.centralAuxiliaryPhysicalEquation_implies_statement`](../ContinuousFlexibility/Radial/CentralFullStatement.lean#L293)
- [`ContinuousFlexibility.Radial.centralCompactAuxiliaryBorder_statement`](../ContinuousFlexibility/Radial/CentralFullStatement.lean#L342)
- [`ContinuousFlexibility.Radial.centralR03_statement`](../ContinuousFlexibility/Radial/CentralFullStatement.lean#L361)

[CentralRadialFlatTests.lean](../ContinuousFlexibility/Radial/CentralRadialFlatTests.lean)：

- [`ContinuousFlexibility.Radial.positive_support_test_elementary_bounds`](../ContinuousFlexibility/Radial/CentralRadialFlatTests.lean#L163)
- [`ContinuousFlexibility.Radial.centralRadial_flat_test_energy`](../ContinuousFlexibility/Radial/CentralRadialFlatTests.lean#L311)
- [`ContinuousFlexibility.Radial.centralRadial_flat_test_integrable`](../ContinuousFlexibility/Radial/CentralRadialFlatTests.lean#L470)
- [`ContinuousFlexibility.Radial.centralRadialDistributionEquation_flat_test`](../ContinuousFlexibility/Radial/CentralRadialFlatTests.lean#L482)
- [`ContinuousFlexibility.Radial.centralRadial_spectral_pairing_density`](../ContinuousFlexibility/Radial/CentralRadialFlatTests.lean#L511)
- [`ContinuousFlexibility.Radial.centralRadialDistributionEquation_iff_flat`](../ContinuousFlexibility/Radial/CentralRadialFlatTests.lean#L536)

[CentralStatementBridges.lean](../ContinuousFlexibility/Radial/CentralStatementBridges.lean)：

- [`ContinuousFlexibility.Radial.centralPotential_statement_eq`](../ContinuousFlexibility/Radial/CentralStatementBridges.lean#L26)
- [`ContinuousFlexibility.Radial.centralWeakRadialDerivative_iff`](../ContinuousFlexibility/Radial/CentralStatementBridges.lean#L32)
- [`ContinuousFlexibility.Radial.centralStatementEnergyHomeomorph_zero`](../ContinuousFlexibility/Radial/CentralStatementBridges.lean#L59)
- [`ContinuousFlexibility.Radial.centralStatementEnergyHomeomorph_one`](../ContinuousFlexibility/Radial/CentralStatementBridges.lean#L63)
- [`ContinuousFlexibility.Radial.centralStatementEnergyHomeomorph_two`](../ContinuousFlexibility/Radial/CentralStatementBridges.lean#L67)
- [`ContinuousFlexibility.Radial.centralStatementEnergyLift_eq_preimage`](../ContinuousFlexibility/Radial/CentralStatementBridges.lean#L71)
- [`ContinuousFlexibility.Radial.centralStatementEnergyCore_eq_preimage`](../ContinuousFlexibility/Radial/CentralStatementBridges.lean#L82)
- [`ContinuousFlexibility.Radial.centralStatementEnergyLift_isClosed`](../ContinuousFlexibility/Radial/CentralStatementBridges.lean#L94)
- [`ContinuousFlexibility.Radial.centralStatementEnergyCore_closure`](../ContinuousFlexibility/Radial/CentralStatementBridges.lean#L99)
- [`ContinuousFlexibility.Radial.centralSchrodingerFormGraph_iff`](../ContinuousFlexibility/Radial/CentralStatementBridges.lean#L106)
- [`ContinuousFlexibility.Radial.centralWeakSchrodingerGraph_iff`](../ContinuousFlexibility/Radial/CentralStatementBridges.lean#L146)
- [`ContinuousFlexibility.Radial.centralActualClosedFormRealization`](../ContinuousFlexibility/Radial/CentralStatementBridges.lean#L153)
- [`ContinuousFlexibility.Radial.centralFullDifferentialSpectrum_statement`](../ContinuousFlexibility/Radial/CentralStatementBridges.lean#L164)
- [`ContinuousFlexibility.Radial.centralReducedInverse_statement`](../ContinuousFlexibility/Radial/CentralStatementBridges.lean#L170)
- [`ContinuousFlexibility.Radial.centralWeakResolventBound_statement`](../ContinuousFlexibility/Radial/CentralStatementBridges.lean#L179)
- [`ContinuousFlexibility.Radial.centralWeakKernel_statement`](../ContinuousFlexibility/Radial/CentralStatementBridges.lean#L191)
- [`ContinuousFlexibility.Radial.centralWeightedInverseBounds_statement`](../ContinuousFlexibility/Radial/CentralStatementBridges.lean#L197)
- [`ContinuousFlexibility.Radial.radialJet_eq_iteratedDeriv`](../ContinuousFlexibility/Radial/CentralStatementBridges.lean#L246)
- [`ContinuousFlexibility.Radial.centralAllOrderAsymptotics_statement`](../ContinuousFlexibility/Radial/CentralStatementBridges.lean#L252)
- [`ContinuousFlexibility.Radial.centralKernelHeight_radial_logarithmic_derivative`](../ContinuousFlexibility/Radial/CentralStatementBridges.lean#L286)
- [`ContinuousFlexibility.Radial.centralRadialProfile_radial_logarithmic_derivative`](../ContinuousFlexibility/Radial/CentralStatementBridges.lean#L300)
- [`ContinuousFlexibility.Radial.centralRadialContact_statement`](../ContinuousFlexibility/Radial/CentralStatementBridges.lean#L311)
- [`ContinuousFlexibility.Radial.centralRadialProfile_simple_turning`](../ContinuousFlexibility/Radial/CentralStatementBridges.lean#L332)


<a id="r04"></a>
## R04 Morse模型的两类非共振

**状态：** 已有部分已编译子结果。**分支：** 径向参考。主定理必要节点。

**数学陈述：** Morse闭实现具有所需离散谱和essential threshold，非平方参数给零能逆界；另精确计算旅行角并证明全部正频率的特征返回小除数下界。

**证明提纲：** 分别证明谱非共振和旅行角非共振，再绑定到同一实际局部模型。

**直接依赖：** [R02](#r02)

**论文定位：** [04-designing-the-profile.tex:304–377](../paper/flexible-surface-rewrite/04-designing-the-profile.tex#L304)，`eq:rad-eq-fs1`

**目标文件：** `ContinuousFlexibility/Radial/R04.lean`（节点组织目标；实际已存在的证明文件见下方，整个节点尚未完成）

**验收条件：**

- 正频率k≥1，零模另处理
- 谱相位与特征相位不可混同
- 闭算子实现和resolvent界不能由形式谱公式代替

**已经完成的子结果：**

- 实际Morse ground条件、一阶因子、weak-D/e^-X闭Hilbert能量空间、真实关联自伴图、真C_c∞能量core、逐向量L²卷积逼近及能量类内compact弱方程与关联图的等价已编译；没有声称任意L²分布解已有能量正则性。
- 实际 Morse 的 √(1+|V|) 权能量域闭、与指数权能量域连续线性等价，真实 C_c∞ 能量核心及 signed form/associated graph 已编译。
- 实际 Morse 权能量域、真实 C_c∞ 核心与有号闭形式已验证；任意 L² 的分布方程与关联算子图等价，包括由弱方程得到所需能量提升。
- 实际 Morse 任意 L² 的弱方程与闭关联图已验证，并推广到任意 α 的真实 partner 势。已验证 Weyl 阈值的两个方向，阈值恰为 j²B。真实能量域上的两个 Darboux 形式分解也已验证。
- Morse 的精确 MorseFullDifferentialSpectrum 已通过，覆盖真实闭形式、阈值以下离散本征值的存在、穷尽及单重性和 Weyl 半线；实际转折点之间的积分和整数范数间隙亦已验证。

**仍待闭合的义务：**

- 构造真实零能定量 resolvent 并合成精确 R04Statement。

**优先核查程度：** high（任务风险标记，不是已发现错误）

**现有 Lean 证明：**

[MorseModel.lean](../ContinuousFlexibility/Radial/MorseModel.lean)：

- [`ContinuousFlexibility.Radial.contDiff_morseGround`](../ContinuousFlexibility/Radial/MorseModel.lean#L45)
- [`ContinuousFlexibility.Radial.morseGround_pos`](../ContinuousFlexibility/Radial/MorseModel.lean#L49)
- [`ContinuousFlexibility.Radial.hasDerivAt_morseGround`](../ContinuousFlexibility/Radial/MorseModel.lean#L51)
- [`ContinuousFlexibility.Radial.deriv_morseGround`](../ContinuousFlexibility/Radial/MorseModel.lean#L60)
- [`ContinuousFlexibility.Radial.deriv_deriv_morseGround`](../ContinuousFlexibility/Radial/MorseModel.lean#L64)
- [`ContinuousFlexibility.Radial.morseAnnihilation_ground`](../ContinuousFlexibility/Radial/MorseModel.lean#L78)
- [`ContinuousFlexibility.Radial.morseGround_equation`](../ContinuousFlexibility/Radial/MorseModel.lean#L84)
- [`ContinuousFlexibility.Radial.morseSchrodingerExpression_eq`](../ContinuousFlexibility/Radial/MorseModel.lean#L90)
- [`ContinuousFlexibility.Radial.morseGround_paper_equation`](../ContinuousFlexibility/Radial/MorseModel.lean#L108)
- [`ContinuousFlexibility.Radial.integrable_morseGround_sq`](../ContinuousFlexibility/Radial/MorseModel.lean#L117)
- [`ContinuousFlexibility.Radial.memLp_morseGround`](../ContinuousFlexibility/Radial/MorseModel.lean#L132)
- [`ContinuousFlexibility.Radial.morseGround_lower_bound`](../ContinuousFlexibility/Radial/MorseModel.lean#L137)
- [`ContinuousFlexibility.Radial.not_memLp_morseGround_of_nonpos`](../ContinuousFlexibility/Radial/MorseModel.lean#L144)
- [`ContinuousFlexibility.Radial.memLp_morseGround_iff`](../ContinuousFlexibility/Radial/MorseModel.lean#L156)
- [`ContinuousFlexibility.Radial.morseGround_weight`](../ContinuousFlexibility/Radial/MorseModel.lean#L164)
- [`ContinuousFlexibility.Radial.memLp_exp_neg_mul_morseGround`](../ContinuousFlexibility/Radial/MorseModel.lean#L171)
- [`ContinuousFlexibility.Radial.memLp_deriv_morseGround`](../ContinuousFlexibility/Radial/MorseModel.lean#L176)
- [`ContinuousFlexibility.Radial.morseGround_energyDomain`](../ContinuousFlexibility/Radial/MorseModel.lean#L192)
- [`ContinuousFlexibility.Radial.morseGround_paper_memLp_iff`](../ContinuousFlexibility/Radial/MorseModel.lean#L197)
- [`ContinuousFlexibility.Radial.morseGround_paper_energyDomain`](../ContinuousFlexibility/Radial/MorseModel.lean#L203)
- [`ContinuousFlexibility.Radial.hasDerivAt_morseAnnihilation`](../ContinuousFlexibility/Radial/MorseModel.lean#L207)
- [`ContinuousFlexibility.Radial.hasDerivAt_morseCreation`](../ContinuousFlexibility/Radial/MorseModel.lean#L218)
- [`ContinuousFlexibility.Radial.morseExpression_factor`](../ContinuousFlexibility/Radial/MorseModel.lean#L230)
- [`ContinuousFlexibility.Radial.morseExpression_partner_factor`](../ContinuousFlexibility/Radial/MorseModel.lean#L239)
- [`ContinuousFlexibility.Radial.contDiff_morseAnnihilation`](../ContinuousFlexibility/Radial/MorseModel.lean#L248)
- [`ContinuousFlexibility.Radial.integral_morse_factor`](../ContinuousFlexibility/Radial/MorseModel.lean#L255)
- [`ContinuousFlexibility.Radial.integral_morse_shifted_nonneg`](../ContinuousFlexibility/Radial/MorseModel.lean#L285)

[MorseWeakEnergy.lean](../ContinuousFlexibility/Radial/MorseWeakEnergy.lean)：

- [`ContinuousFlexibility.Radial.compactSmooth_morseEnergyDomain`](../ContinuousFlexibility/Radial/MorseWeakEnergy.lean#L28)
- [`ContinuousFlexibility.Radial.morseTestPairing_apply`](../ContinuousFlexibility/Radial/MorseWeakEnergy.lean#L38)
- [`ContinuousFlexibility.Radial.morseTestPairing_toLp`](../ContinuousFlexibility/Radial/MorseWeakEnergy.lean#L47)
- [`ContinuousFlexibility.Radial.morseWeakDerivativeL2_iff_pairings`](../ContinuousFlexibility/Radial/MorseWeakEnergy.lean#L60)
- [`ContinuousFlexibility.Radial.morseWeakDerivativeL2_zero`](../ContinuousFlexibility/Radial/MorseWeakEnergy.lean#L71)
- [`ContinuousFlexibility.Radial.MorseWeakDerivativeL2.add`](../ContinuousFlexibility/Radial/MorseWeakEnergy.lean#L76)
- [`ContinuousFlexibility.Radial.MorseWeakDerivativeL2.smul`](../ContinuousFlexibility/Radial/MorseWeakEnergy.lean#L86)
- [`ContinuousFlexibility.Radial.MorseWeakDerivativeL2.unique`](../ContinuousFlexibility/Radial/MorseWeakEnergy.lean#L97)
- [`ContinuousFlexibility.Radial.morseWeightRelation_iff_pairings`](../ContinuousFlexibility/Radial/MorseWeakEnergy.lean#L107)
- [`ContinuousFlexibility.Radial.mem_morseEnergyGraph_iff`](../ContinuousFlexibility/Radial/MorseWeakEnergy.lean#L151)
- [`ContinuousFlexibility.Radial.morseEnergyGraph_isClosed`](../ContinuousFlexibility/Radial/MorseWeakEnergy.lean#L159)
- [`ContinuousFlexibility.Radial.morseEnergyCoordinate_apply`](../ContinuousFlexibility/Radial/MorseWeakEnergy.lean#L213)
- [`ContinuousFlexibility.Radial.morseEnergyCoordinate_norm_le`](../ContinuousFlexibility/Radial/MorseWeakEnergy.lean#L216)
- [`ContinuousFlexibility.Radial.morseWeakEnergy_norm_sq`](../ContinuousFlexibility/Radial/MorseWeakEnergy.lean#L219)
- [`ContinuousFlexibility.Radial.morseEnergyDerivative_weak`](../ContinuousFlexibility/Radial/MorseWeakEnergy.lean#L226)
- [`ContinuousFlexibility.Radial.morseEnergyWeight_ae`](../ContinuousFlexibility/Radial/MorseWeakEnergy.lean#L229)
- [`ContinuousFlexibility.Radial.morseEnergyBase_injective`](../ContinuousFlexibility/Radial/MorseWeakEnergy.lean#L234)
- [`ContinuousFlexibility.Radial.morseWeakDerivativeL2_of_energyDomain`](../ContinuousFlexibility/Radial/MorseWeakEnergy.lean#L259)
- [`ContinuousFlexibility.Radial.morseEnergyLift_base`](../ContinuousFlexibility/Radial/MorseWeakEnergy.lean#L281)
- [`ContinuousFlexibility.Radial.morseEnergyLift_derivative`](../ContinuousFlexibility/Radial/MorseWeakEnergy.lean#L284)
- [`ContinuousFlexibility.Radial.morseEnergyLift_weight`](../ContinuousFlexibility/Radial/MorseWeakEnergy.lean#L287)
- [`ContinuousFlexibility.Radial.morseEnergyBase_denseRange`](../ContinuousFlexibility/Radial/MorseWeakEnergy.lean#L296)
- [`ContinuousFlexibility.Radial.morsePhysicalForm_apply`](../ContinuousFlexibility/Radial/MorseWeakEnergy.lean#L335)
- [`ContinuousFlexibility.Radial.morsePhysicalForm_bound`](../ContinuousFlexibility/Radial/MorseWeakEnergy.lean#L342)
- [`ContinuousFlexibility.Radial.morseWeight_pairing_symm`](../ContinuousFlexibility/Radial/MorseWeakEnergy.lean#L346)
- [`ContinuousFlexibility.Radial.morsePhysicalForm_symm`](../ContinuousFlexibility/Radial/MorseWeakEnergy.lean#L356)
- [`ContinuousFlexibility.Radial.morsePhysicalForm_lower_bound`](../ContinuousFlexibility/Radial/MorseWeakEnergy.lean#L365)
- [`ContinuousFlexibility.Radial.morseShiftedForm_apply`](../ContinuousFlexibility/Radial/MorseWeakEnergy.lean#L385)
- [`ContinuousFlexibility.Radial.morseCoercivityConstant_pos`](../ContinuousFlexibility/Radial/MorseWeakEnergy.lean#L389)
- [`ContinuousFlexibility.Radial.morseShiftedForm_coercive_bound`](../ContinuousFlexibility/Radial/MorseWeakEnergy.lean#L393)
- [`ContinuousFlexibility.Radial.morseShiftedForm_isCoercive`](../ContinuousFlexibility/Radial/MorseWeakEnergy.lean#L407)
- [`ContinuousFlexibility.Radial.morseShiftedForm_norm_equivalence`](../ContinuousFlexibility/Radial/MorseWeakEnergy.lean#L413)
- [`ContinuousFlexibility.Radial.morseL2_inner_toLp`](../ContinuousFlexibility/Radial/MorseWeakEnergy.lean#L422)
- [`ContinuousFlexibility.Radial.morsePhysicalForm_lift_apply`](../ContinuousFlexibility/Radial/MorseWeakEnergy.lean#L431)
- [`ContinuousFlexibility.Radial.morsePhysicalForm_compact_test`](../ContinuousFlexibility/Radial/MorseWeakEnergy.lean#L444)
- [`ContinuousFlexibility.Radial.morseGroundEnergy_compact_pairing`](../ContinuousFlexibility/Radial/MorseWeakEnergy.lean#L482)

[LpConvolution.lean](../ContinuousFlexibility/Radial/LpConvolution.lean)：

- [`ContinuousFlexibility.Radial.realL2Translate_coeFn`](../ContinuousFlexibility/Radial/LpConvolution.lean#L30)
- [`ContinuousFlexibility.Radial.realL2Translate_norm`](../ContinuousFlexibility/Radial/LpConvolution.lean#L34)
- [`ContinuousFlexibility.Radial.realL2Translate_zero`](../ContinuousFlexibility/Radial/LpConvolution.lean#L37)
- [`ContinuousFlexibility.Radial.continuous_realL2Translate`](../ContinuousFlexibility/Radial/LpConvolution.lean#L43)
- [`ContinuousFlexibility.Radial.realL2Convolution_integrable`](../ContinuousFlexibility/Radial/LpConvolution.lean#L57)
- [`ContinuousFlexibility.Radial.realL2Convolution_norm_le`](../ContinuousFlexibility/Radial/LpConvolution.lean#L65)
- [`ContinuousFlexibility.Radial.realL2ConvolutionOperator_apply`](../ContinuousFlexibility/Radial/LpConvolution.lean#L94)
- [`ContinuousFlexibility.Radial.realL2Convolution_pairing`](../ContinuousFlexibility/Radial/LpConvolution.lean#L98)
- [`ContinuousFlexibility.Radial.realL2Convolution_sub_kernel`](../ContinuousFlexibility/Radial/LpConvolution.lean#L104)
- [`ContinuousFlexibility.Radial.realL2Convolution_sub_norm_le`](../ContinuousFlexibility/Radial/LpConvolution.lean#L111)
- [`ContinuousFlexibility.Radial.realL2Convolution_tendsto`](../ContinuousFlexibility/Radial/LpConvolution.lean#L120)

[MorseAssociatedOperator.lean](../ContinuousFlexibility/Radial/MorseAssociatedOperator.lean)：

- [`ContinuousFlexibility.Radial.morseShiftedForm_symm`](../ContinuousFlexibility/Radial/MorseAssociatedOperator.lean#L29)
- [`ContinuousFlexibility.Radial.morseLaxMilgramEquiv_inner`](../ContinuousFlexibility/Radial/MorseAssociatedOperator.lean#L39)
- [`ContinuousFlexibility.Radial.morseEnergyResolvent_spec`](../ContinuousFlexibility/Radial/MorseAssociatedOperator.lean#L48)
- [`ContinuousFlexibility.Radial.morseEnergyResolvent_unique`](../ContinuousFlexibility/Radial/MorseAssociatedOperator.lean#L61)
- [`ContinuousFlexibility.Radial.morseShiftedResolvent_apply`](../ContinuousFlexibility/Radial/MorseAssociatedOperator.lean#L74)
- [`ContinuousFlexibility.Radial.morseEnergyResolvent_norm_bound`](../ContinuousFlexibility/Radial/MorseAssociatedOperator.lean#L77)
- [`ContinuousFlexibility.Radial.morseShiftedResolvent_norm_bound`](../ContinuousFlexibility/Radial/MorseAssociatedOperator.lean#L96)
- [`ContinuousFlexibility.Radial.morseShiftedResolvent_injective`](../ContinuousFlexibility/Radial/MorseAssociatedOperator.lean#L100)
- [`ContinuousFlexibility.Radial.morseShiftedResolvent_pairing`](../ContinuousFlexibility/Radial/MorseAssociatedOperator.lean#L112)
- [`ContinuousFlexibility.Radial.morseShiftedResolvent_denseRange`](../ContinuousFlexibility/Radial/MorseAssociatedOperator.lean#L123)
- [`ContinuousFlexibility.Radial.mem_morseAssociatedGraph_shift_iff`](../ContinuousFlexibility/Radial/MorseAssociatedOperator.lean#L165)
- [`ContinuousFlexibility.Radial.mem_morseAssociatedGraph_iff_resolvent`](../ContinuousFlexibility/Radial/MorseAssociatedOperator.lean#L183)
- [`ContinuousFlexibility.Radial.morseShiftedResolvent_mem_graph`](../ContinuousFlexibility/Radial/MorseAssociatedOperator.lean#L201)
- [`ContinuousFlexibility.Radial.morseAssociatedGraph_isClosed`](../ContinuousFlexibility/Radial/MorseAssociatedOperator.lean#L206)
- [`ContinuousFlexibility.Radial.morseAssociatedGraph_domain_iff`](../ContinuousFlexibility/Radial/MorseAssociatedOperator.lean#L217)
- [`ContinuousFlexibility.Radial.morseAssociatedGraph_domain_dense`](../ContinuousFlexibility/Radial/MorseAssociatedOperator.lean#L227)
- [`ContinuousFlexibility.Radial.morseAssociatedGraph_unique`](../ContinuousFlexibility/Radial/MorseAssociatedOperator.lean#L236)
- [`ContinuousFlexibility.Radial.morseAssociatedGraph_semibounded`](../ContinuousFlexibility/Radial/MorseAssociatedOperator.lean#L247)
- [`ContinuousFlexibility.Radial.morseAssociatedGraph_symmetric`](../ContinuousFlexibility/Radial/MorseAssociatedOperator.lean#L256)
- [`ContinuousFlexibility.Radial.morseAssociatedGraph_eq_adjoint`](../ContinuousFlexibility/Radial/MorseAssociatedOperator.lean#L280)
- [`ContinuousFlexibility.Radial.morseL2_inner_right_toLp`](../ContinuousFlexibility/Radial/MorseAssociatedOperator.lean#L297)
- [`ContinuousFlexibility.Radial.morseCompactImage_memLp`](../ContinuousFlexibility/Radial/MorseAssociatedOperator.lean#L303)
- [`ContinuousFlexibility.Radial.morsePhysicalForm_weak_test`](../ContinuousFlexibility/Radial/MorseAssociatedOperator.lean#L320)
- [`ContinuousFlexibility.Radial.morseCompact_pair_mem_graph`](../ContinuousFlexibility/Radial/MorseAssociatedOperator.lean#L379)
- [`ContinuousFlexibility.Radial.morseAssociatedGraph_compact_weak`](../ContinuousFlexibility/Radial/MorseAssociatedOperator.lean#L400)

[MorseEnergyCutoff.lean](../ContinuousFlexibility/Radial/MorseEnergyCutoff.lean)：

- [`ContinuousFlexibility.Radial.morseMemLp_bounded_mul`](../ContinuousFlexibility/Radial/MorseEnergyCutoff.lean#L24)
- [`ContinuousFlexibility.Radial.morseL2Mul_coeFn`](../ContinuousFlexibility/Radial/MorseEnergyCutoff.lean#L36)
- [`ContinuousFlexibility.Radial.morseL2Mul_norm_le`](../ContinuousFlexibility/Radial/MorseEnergyCutoff.lean#L41)
- [`ContinuousFlexibility.Radial.morseL2Multiplier_apply`](../ContinuousFlexibility/Radial/MorseEnergyCutoff.lean#L79)
- [`ContinuousFlexibility.Radial.morseL2Multiplier_pairing`](../ContinuousFlexibility/Radial/MorseEnergyCutoff.lean#L83)
- [`ContinuousFlexibility.Radial.MorseWeakDerivativeL2.bounded_smooth_mul`](../ContinuousFlexibility/Radial/MorseEnergyCutoff.lean#L94)
- [`ContinuousFlexibility.Radial.morseCutoffTriple_mem`](../ContinuousFlexibility/Radial/MorseEnergyCutoff.lean#L143)
- [`ContinuousFlexibility.Radial.morseEnergyCutoff_base`](../ContinuousFlexibility/Radial/MorseEnergyCutoff.lean#L163)
- [`ContinuousFlexibility.Radial.morseEnergyCutoff_derivative`](../ContinuousFlexibility/Radial/MorseEnergyCutoff.lean#L168)
- [`ContinuousFlexibility.Radial.morseEnergyCutoff_weight`](../ContinuousFlexibility/Radial/MorseEnergyCutoff.lean#L175)
- [`ContinuousFlexibility.Radial.morseEnergyCutoff_compact`](../ContinuousFlexibility/Radial/MorseEnergyCutoff.lean#L185)
- [`ContinuousFlexibility.Radial.morseCutoffDerivativeConstant_nonneg`](../ContinuousFlexibility/Radial/MorseEnergyCutoff.lean#L215)
- [`ContinuousFlexibility.Radial.morseScaledCutoff_abs_le_one`](../ContinuousFlexibility/Radial/MorseEnergyCutoff.lean#L218)
- [`ContinuousFlexibility.Radial.morseScaledCutoff_deriv_abs_le`](../ContinuousFlexibility/Radial/MorseEnergyCutoff.lean#L223)
- [`ContinuousFlexibility.Radial.morseScaledEnergyCutoff_compact`](../ContinuousFlexibility/Radial/MorseEnergyCutoff.lean#L237)
- [`ContinuousFlexibility.Radial.morseScaledL2Multiplier_tendsto`](../ContinuousFlexibility/Radial/MorseEnergyCutoff.lean#L242)
- [`ContinuousFlexibility.Radial.morseScaledDerivativeMultiplier_tendsto`](../ContinuousFlexibility/Radial/MorseEnergyCutoff.lean#L264)
- [`ContinuousFlexibility.Radial.morseScaledEnergyCutoff_tendsto`](../ContinuousFlexibility/Radial/MorseEnergyCutoff.lean#L291)
- [`ContinuousFlexibility.Radial.morseCompactEnergy_dense`](../ContinuousFlexibility/Radial/MorseEnergyCutoff.lean#L316)

[MorseSmoothCore.lean](../ContinuousFlexibility/Radial/MorseSmoothCore.lean)：

- [`ContinuousFlexibility.Radial.morseCompact_memLp_integrable`](../ContinuousFlexibility/Radial/MorseSmoothCore.lean#L26)
- [`ContinuousFlexibility.Radial.morseConvolution_integral_test`](../ContinuousFlexibility/Radial/MorseSmoothCore.lean#L32)
- [`ContinuousFlexibility.Radial.morseConvolution_contDiff`](../ContinuousFlexibility/Radial/MorseSmoothCore.lean#L58)
- [`ContinuousFlexibility.Radial.morseConvolution_memLp`](../ContinuousFlexibility/Radial/MorseSmoothCore.lean#L64)
- [`ContinuousFlexibility.Radial.morseConvolution_toLp`](../ContinuousFlexibility/Radial/MorseSmoothCore.lean#L72)
- [`ContinuousFlexibility.Radial.morseCompactRepresentative_support`](../ContinuousFlexibility/Radial/MorseSmoothCore.lean#L123)
- [`ContinuousFlexibility.Radial.morseCompactRepresentative_ae`](../ContinuousFlexibility/Radial/MorseSmoothCore.lean#L128)
- [`ContinuousFlexibility.Radial.morseCompactRepresentative_memLp`](../ContinuousFlexibility/Radial/MorseSmoothCore.lean#L133)
- [`ContinuousFlexibility.Radial.morseCompactRepresentative_weight_ae`](../ContinuousFlexibility/Radial/MorseSmoothCore.lean#L138)
- [`ContinuousFlexibility.Radial.morseConvolution_deriv`](../ContinuousFlexibility/Radial/MorseSmoothCore.lean#L150)
- [`ContinuousFlexibility.Radial.morseTiltedKernel_contDiff`](../ContinuousFlexibility/Radial/MorseSmoothCore.lean#L191)
- [`ContinuousFlexibility.Radial.morseTiltedKernel_support`](../ContinuousFlexibility/Radial/MorseSmoothCore.lean#L195)
- [`ContinuousFlexibility.Radial.morseConvolution_weight`](../ContinuousFlexibility/Radial/MorseSmoothCore.lean#L199)
- [`ContinuousFlexibility.Radial.morseCompactSmoothing_base`](../ContinuousFlexibility/Radial/MorseSmoothCore.lean#L224)
- [`ContinuousFlexibility.Radial.morseCompactSmoothing_derivative`](../ContinuousFlexibility/Radial/MorseSmoothCore.lean#L233)
- [`ContinuousFlexibility.Radial.morseCompactSmoothing_weight`](../ContinuousFlexibility/Radial/MorseSmoothCore.lean#L256)
- [`ContinuousFlexibility.Radial.morseMollifier_contDiff`](../ContinuousFlexibility/Radial/MorseSmoothCore.lean#L291)
- [`ContinuousFlexibility.Radial.morseMollifier_support`](../ContinuousFlexibility/Radial/MorseSmoothCore.lean#L294)
- [`ContinuousFlexibility.Radial.morseMollifier_nonneg`](../ContinuousFlexibility/Radial/MorseSmoothCore.lean#L297)
- [`ContinuousFlexibility.Radial.morseMollifier_integral`](../ContinuousFlexibility/Radial/MorseSmoothCore.lean#L300)
- [`ContinuousFlexibility.Radial.morseMollifier_support_tendsto`](../ContinuousFlexibility/Radial/MorseSmoothCore.lean#L303)
- [`ContinuousFlexibility.Radial.morseMollifier_convolution_tendsto`](../ContinuousFlexibility/Radial/MorseSmoothCore.lean#L309)
- [`ContinuousFlexibility.Radial.morseMollifier_tilted_convolution_tendsto`](../ContinuousFlexibility/Radial/MorseSmoothCore.lean#L317)
- [`ContinuousFlexibility.Radial.morseCompactSmoothApprox_tendsto`](../ContinuousFlexibility/Radial/MorseSmoothCore.lean#L344)
- [`ContinuousFlexibility.Radial.morseCompactSmoothEnergy_dense`](../ContinuousFlexibility/Radial/MorseSmoothCore.lean#L370)

[MorseWeakOperator.lean](../ContinuousFlexibility/Radial/MorseWeakOperator.lean)：

- [`ContinuousFlexibility.Radial.morsePhysicalForm_pairing_of_compactWeak`](../ContinuousFlexibility/Radial/MorseWeakOperator.lean#L31)
- [`ContinuousFlexibility.Radial.morsePhysicalForm_pairing_iff_compactWeak`](../ContinuousFlexibility/Radial/MorseWeakOperator.lean#L60)
- [`ContinuousFlexibility.Radial.morseAssociatedGraph_iff_compactWeak_of_energy`](../ContinuousFlexibility/Radial/MorseWeakOperator.lean#L72)
- [`ContinuousFlexibility.Radial.morseAssociatedGraph_iff_energy_compactWeak`](../ContinuousFlexibility/Radial/MorseWeakOperator.lean#L83)

[MorsePotentialEnergy.lean](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean)：

- [`ContinuousFlexibility.Radial.morsePotential_quadratic`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L33)
- [`ContinuousFlexibility.Radial.continuous_morseAbsoluteWeight`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L42)
- [`ContinuousFlexibility.Radial.morseAbsoluteWeight_pos`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L48)
- [`ContinuousFlexibility.Radial.morseAbsoluteWeight_sq`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L51)
- [`ContinuousFlexibility.Radial.morsePotential_lower`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L55)
- [`ContinuousFlexibility.Radial.morseAbsoluteWeight_controls_exp`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L62)
- [`ContinuousFlexibility.Radial.morseAbsoluteWeight_le_exp`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L85)
- [`ContinuousFlexibility.Radial.continuous_morsePotentialExpCoefficient`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L120)
- [`ContinuousFlexibility.Radial.continuous_morsePotentialSumCoefficient`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L125)
- [`ContinuousFlexibility.Radial.morsePotentialExpCoefficient_bound`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L130)
- [`ContinuousFlexibility.Radial.morsePotentialSumCoefficient_bound`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L137)
- [`ContinuousFlexibility.Radial.morsePotentialExpMultiplier_ae`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L154)
- [`ContinuousFlexibility.Radial.morsePotentialSumMultiplier_ae`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L161)
- [`ContinuousFlexibility.Radial.morsePotentialExpCoefficient_mul`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L168)
- [`ContinuousFlexibility.Radial.morsePotentialSumCoefficient_mul`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L172)
- [`ContinuousFlexibility.Radial.morsePotential_memLp_iff_exp`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L176)
- [`ContinuousFlexibility.Radial.morseWeakDerivative_iff_public`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L195)
- [`ContinuousFlexibility.Radial.morsePotentialEnergyGraph_eq_public`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L229)
- [`ContinuousFlexibility.Radial.morsePotentialToExp_zero`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L261)
- [`ContinuousFlexibility.Radial.morsePotentialToExp_one`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L264)
- [`ContinuousFlexibility.Radial.morsePotentialToExp_two`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L267)
- [`ContinuousFlexibility.Radial.morseExpToPotential_base`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L271)
- [`ContinuousFlexibility.Radial.morseExpToPotential_derivative`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L274)
- [`ContinuousFlexibility.Radial.morseExpToPotential_weight`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L277)
- [`ContinuousFlexibility.Radial.morsePotentialToExp_mem`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L282)
- [`ContinuousFlexibility.Radial.morseExpToPotential_mem`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L291)
- [`ContinuousFlexibility.Radial.morseExpToPotential_toExp`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L309)
- [`ContinuousFlexibility.Radial.morsePotentialToExp_toPotential`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L320)
- [`ContinuousFlexibility.Radial.morsePotentialEnergyGraph_isClosed`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L338)
- [`ContinuousFlexibility.Radial.morsePotentialEnergySpace_completeSpace`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L358)
- [`ContinuousFlexibility.Radial.morsePublicEnergyLift_isClosed`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L379)
- [`ContinuousFlexibility.Radial.morseExpToPotential_compact_lift`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L385)
- [`ContinuousFlexibility.Radial.morsePublicEnergyCore_subset`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L408)
- [`ContinuousFlexibility.Radial.morsePublicEnergyCore_closure`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L426)
- [`ContinuousFlexibility.Radial.morsePotential_pairing_ae`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L459)
- [`ContinuousFlexibility.Radial.morsePotential_pairing_integrable`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L468)
- [`ContinuousFlexibility.Radial.morsePotential_pairing_integral`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L480)
- [`ContinuousFlexibility.Radial.morsePhysicalForm_eq_potential_integral`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L500)
- [`ContinuousFlexibility.Radial.morsePublicFormGraph_iff_associated`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L514)
- [`ContinuousFlexibility.Radial.morsePublicWeakGraph_iff_compactWeak`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L560)
- [`ContinuousFlexibility.Radial.morsePublicWeakGraph_iff_formGraph_of_energy`](../ContinuousFlexibility/Radial/MorsePotentialEnergy.lean#L575)

[MorseMaximalDomain.lean](../ContinuousFlexibility/Radial/MorseMaximalDomain.lean)：

- [`ContinuousFlexibility.Radial.morseWeakPositiveKernel_eq_zero`](../ContinuousFlexibility/Radial/MorseMaximalDomain.lean#L313)
- [`ContinuousFlexibility.Radial.morsePublicWeakGraph_iff_associated`](../ContinuousFlexibility/Radial/MorseMaximalDomain.lean#L392)
- [`ContinuousFlexibility.Radial.morsePublicWeakGraph_iff_formGraph`](../ContinuousFlexibility/Radial/MorseMaximalDomain.lean#L427)
- [`ContinuousFlexibility.Radial.morseActualClosedFormRealization`](../ContinuousFlexibility/Radial/MorseMaximalDomain.lean#L434)

[MorseDarbouxForms.lean](../ContinuousFlexibility/Radial/MorseDarbouxForms.lean)：

- [`ContinuousFlexibility.Radial.morseAnnihilationL2_apply`](../ContinuousFlexibility/Radial/MorseDarbouxForms.lean#L34)
- [`ContinuousFlexibility.Radial.morseCreationL2_apply`](../ContinuousFlexibility/Radial/MorseDarbouxForms.lean#L39)
- [`ContinuousFlexibility.Radial.contDiff_morseCreation`](../ContinuousFlexibility/Radial/MorseDarbouxForms.lean#L44)
- [`ContinuousFlexibility.Radial.hasCompactSupport_morseAnnihilation`](../ContinuousFlexibility/Radial/MorseDarbouxForms.lean#L49)
- [`ContinuousFlexibility.Radial.hasCompactSupport_morseCreation`](../ContinuousFlexibility/Radial/MorseDarbouxForms.lean#L53)
- [`ContinuousFlexibility.Radial.morseAnnihilation_memLp_of_energy`](../ContinuousFlexibility/Radial/MorseDarbouxForms.lean#L70)
- [`ContinuousFlexibility.Radial.morseCreation_memLp_of_energy`](../ContinuousFlexibility/Radial/MorseDarbouxForms.lean#L74)
- [`ContinuousFlexibility.Radial.morseAnnihilationL2_lift`](../ContinuousFlexibility/Radial/MorseDarbouxForms.lean#L95)
- [`ContinuousFlexibility.Radial.morseCreationL2_lift`](../ContinuousFlexibility/Radial/MorseDarbouxForms.lean#L100)
- [`ContinuousFlexibility.Radial.morseAnnihilationL2_compact_adjoint`](../ContinuousFlexibility/Radial/MorseDarbouxForms.lean#L142)
- [`ContinuousFlexibility.Radial.morseCreationL2_compact_adjoint`](../ContinuousFlexibility/Radial/MorseDarbouxForms.lean#L151)
- [`ContinuousFlexibility.Radial.morseAnnihilationL2_adjoint`](../ContinuousFlexibility/Radial/MorseDarbouxForms.lean#L173)
- [`ContinuousFlexibility.Radial.morsePhysicalForm_factorization`](../ContinuousFlexibility/Radial/MorseDarbouxForms.lean#L227)
- [`ContinuousFlexibility.Radial.morsePartnerPhysicalForm_factorization`](../ContinuousFlexibility/Radial/MorseDarbouxForms.lean#L249)

[MorsePartnerWeakGraph.lean](../ContinuousFlexibility/Radial/MorsePartnerWeakGraph.lean)：

- [`ContinuousFlexibility.Radial.morsePartnerPotential_contDiff`](../ContinuousFlexibility/Radial/MorsePartnerWeakGraph.lean#L23)
- [`ContinuousFlexibility.Radial.morsePartnerPotential_paper`](../ContinuousFlexibility/Radial/MorsePartnerWeakGraph.lean#L27)
- [`ContinuousFlexibility.Radial.morsePartnerPotential_add_shift_ge_one`](../ContinuousFlexibility/Radial/MorsePartnerWeakGraph.lean#L38)
- [`ContinuousFlexibility.Radial.morsePartner_weakGraph_iff_compactWeak`](../ContinuousFlexibility/Radial/MorsePartnerWeakGraph.lean#L44)
- [`ContinuousFlexibility.Radial.morsePartner_compactWeak_iff_associated`](../ContinuousFlexibility/Radial/MorsePartnerWeakGraph.lean#L116)
- [`ContinuousFlexibility.Radial.morsePartner_weakGraph_iff_associated`](../ContinuousFlexibility/Radial/MorsePartnerWeakGraph.lean#L130)

[MorseWeylExclusion.lean](../ContinuousFlexibility/Radial/MorseWeylExclusion.lean)：

- [`ContinuousFlexibility.Radial.morseThreshold_le_of_essentialWeylValue`](../ContinuousFlexibility/Radial/MorseWeylExclusion.lean#L263)

[MorseWeylSequence.lean](../ContinuousFlexibility/Radial/MorseWeylSequence.lean)：

- [`ContinuousFlexibility.Radial.morseEssentialWeylValue_of_threshold_le`](../ContinuousFlexibility/Radial/MorseWeylSequence.lean#L428)

[MorseArithmeticGap.lean](../ContinuousFlexibility/Radial/MorseArithmeticGap.lean)：

- [`ContinuousFlexibility.Radial.morse_integer_phase_gap`](../ContinuousFlexibility/Radial/MorseArithmeticGap.lean#L39)
- [`ContinuousFlexibility.Radial.morse_normalized_phase_gap`](../ContinuousFlexibility/Radial/MorseArithmeticGap.lean#L66)
- [`ContinuousFlexibility.Radial.morse_return_small_divisor`](../ContinuousFlexibility/Radial/MorseArithmeticGap.lean#L79)
- [`ContinuousFlexibility.Radial.morse_discrete_level_gap`](../ContinuousFlexibility/Radial/MorseArithmeticGap.lean#L99)

[MorseDarbouxGround.lean](../ContinuousFlexibility/Radial/MorseDarbouxGround.lean)：

- [`ContinuousFlexibility.Radial.morseAnnihilationL2_ae_ground`](../ContinuousFlexibility/Radial/MorseDarbouxGround.lean#L121)
- [`ContinuousFlexibility.Radial.morseAnnihilationL2_eq_zero_implies_pos`](../ContinuousFlexibility/Radial/MorseDarbouxGround.lean#L176)
- [`ContinuousFlexibility.Radial.morseGroundL2_ae`](../ContinuousFlexibility/Radial/MorseDarbouxGround.lean#L196)
- [`ContinuousFlexibility.Radial.morseGroundL2_ne_zero`](../ContinuousFlexibility/Radial/MorseDarbouxGround.lean#L200)
- [`ContinuousFlexibility.Radial.morseGroundL2_mem_graph`](../ContinuousFlexibility/Radial/MorseDarbouxGround.lean#L207)
- [`ContinuousFlexibility.Radial.morseGround_weakGraph_iff_span`](../ContinuousFlexibility/Radial/MorseDarbouxGround.lean#L225)
- [`ContinuousFlexibility.Radial.morsePhysicalForm_threshold_le_of_nonpos`](../ContinuousFlexibility/Radial/MorseDarbouxGround.lean#L259)
- [`ContinuousFlexibility.Radial.not_morsePartnerEigen_lt_threshold_of_nonpos`](../ContinuousFlexibility/Radial/MorseDarbouxGround.lean#L274)

[MorseDarbouxIntertwining.lean](../ContinuousFlexibility/Radial/MorseDarbouxIntertwining.lean)：

- [`ContinuousFlexibility.Radial.contDiff_morseExpression`](../ContinuousFlexibility/Radial/MorseDarbouxIntertwining.lean#L20)
- [`ContinuousFlexibility.Radial.hasCompactSupport_morseExpression`](../ContinuousFlexibility/Radial/MorseDarbouxIntertwining.lean#L25)
- [`ContinuousFlexibility.Radial.morseAnnihilation_intertwines`](../ContinuousFlexibility/Radial/MorseDarbouxIntertwining.lean#L50)
- [`ContinuousFlexibility.Radial.morseCreation_intertwines`](../ContinuousFlexibility/Radial/MorseDarbouxIntertwining.lean#L67)
- [`ContinuousFlexibility.Radial.morseAnnihilationL2_mem_partnerGraph`](../ContinuousFlexibility/Radial/MorseDarbouxIntertwining.lean#L104)
- [`ContinuousFlexibility.Radial.morseCreationL2_mem_graph`](../ContinuousFlexibility/Radial/MorseDarbouxIntertwining.lean#L130)
- [`ContinuousFlexibility.Radial.morseEigenForm_pairing`](../ContinuousFlexibility/Radial/MorseDarbouxIntertwining.lean#L154)
- [`ContinuousFlexibility.Radial.morseAnnihilationL2_eigen_norm_sq`](../ContinuousFlexibility/Radial/MorseDarbouxIntertwining.lean#L163)
- [`ContinuousFlexibility.Radial.morseCreationL2_eigen_norm_sq`](../ContinuousFlexibility/Radial/MorseDarbouxIntertwining.lean#L170)
- [`ContinuousFlexibility.Radial.morseAnnihilationL2_eigen_ne_zero_iff`](../ContinuousFlexibility/Radial/MorseDarbouxIntertwining.lean#L189)
- [`ContinuousFlexibility.Radial.morseCreationL2_eigen_ne_zero_iff`](../ContinuousFlexibility/Radial/MorseDarbouxIntertwining.lean#L195)

[MorseDiscreteSpectrum.lean](../ContinuousFlexibility/Radial/MorseDiscreteSpectrum.lean)：

- [`ContinuousFlexibility.Radial.morsePartner_level_eigen`](../ContinuousFlexibility/Radial/MorseDiscreteSpectrum.lean#L44)
- [`ContinuousFlexibility.Radial.morsePartner_eigen_classification`](../ContinuousFlexibility/Radial/MorseDiscreteSpectrum.lean#L176)
- [`ContinuousFlexibility.Radial.morsePartner_actualEigenvalue_iff`](../ContinuousFlexibility/Radial/MorseDiscreteSpectrum.lean#L185)
- [`ContinuousFlexibility.Radial.morseFullDifferentialSpectrum`](../ContinuousFlexibility/Radial/MorseDiscreteSpectrum.lean#L196)

[MorseNoWeylResolvent.lean](../ContinuousFlexibility/Radial/MorseNoWeylResolvent.lean)：

- [`ContinuousFlexibility.Radial.morseWeakGraph_boundedBelow_of_noEigen`](../ContinuousFlexibility/Radial/MorseNoWeylResolvent.lean#L152)
- [`ContinuousFlexibility.Radial.morseWeakResolventBound_of_noEigen`](../ContinuousFlexibility/Radial/MorseNoWeylResolvent.lean#L193)

[MorseTravelIntegral.lean](../ContinuousFlexibility/Radial/MorseTravelIntegral.lean)：

- [`ContinuousFlexibility.Radial.integral_one_div_cos_affine`](../ContinuousFlexibility/Radial/MorseTravelIntegral.lean#L146)
- [`ContinuousFlexibility.Radial.morseTravel_eq_pi_sqrt`](../ContinuousFlexibility/Radial/MorseTravelIntegral.lean#L225)


<a id="r05"></a>
## R05 真实单元、连接与累积平坦轮廓

**状态：** 已有部分已编译子结果。**分支：** 径向参考。主定理必要节点。

**数学陈述：** 对所有足够大的N及全部高度选择σ_n∈[1,2]，构造Morse单元和正连接，使半径累积于正的有限端点、轮廓正、转点简单、零延拓C∞平坦；推出质量/阻力、离散尺度和全部固定阶jet界。

**证明提纲：** 给出A_n,H_n,ℰ_n的定量常数和索引阈值，逐单元估计再证明无限拼接；对所有高度选择保持统一性。

**直接依赖：** [R04](#r04), [R01](#r01)

**论文定位：** [05-flat-end-chain.tex:20–268](../paper/flexible-surface-rewrite/05-flat-end-chain.tex#L20)，`eq:geometry-profile-jets`

**目标文件：** `ContinuousFlexibility/Radial/R05.lean`（节点组织目标；实际已存在的证明文件见下方，整个节点尚未完成）

**验收条件：**

- 显式保留N可继续增大的构造自由
- 零延拓包括全部阶数
- 证明估计对整个参数立方体一致

**已经完成的子结果：**

- 真实非平方整数尺度、所有高度选择的统一乘积对数预算、相邻幅度递推及 ε 吸收已编译。
- 真实非平方整数尺度和统一幅度预算、Morse 轮廓的三简单根、保留区间的同一光滑 ODE 解、右帽正性及真实行程、左帽的质量系数和一阶积分误差已验证。
- 真实 Morse 单元的左右正帽与整个保留区间的同一正 ODE 解、真实质量与阻力换元和短帽光学积分已验证。通用正接段构造保持两端完整光滑芽并控制对数斜率。实际两侧物理逆坐标帽的对数斜率与正性已验证。双侧半径按指定相邻接段长度定位，实际比例有界，正有限聚点已验证。
- R05/R06 的规格已按实际右转点、左右质量/阻力区间、相邻交叠与外向标号修订并通过构建。已证双侧正有限聚点、端距、相邻高度对比、真模型芽的光滑正接段、局部半开索引拼接及模型坐标全阶 jets。真物理半径上的剖面与倒数全阶 jets 已验证。

**仍待闭合的义务：**

- 将已证局部构造组装成同一双侧无穷剖面和交叠单位分解，验证所有 σ 的全阶平坦性、真实 I/J 积分界、迹宽与统一端距。

**现有 Lean 证明：**

[MorseChainScales.lean](../ContinuousFlexibility/Radial/MorseChainScales.lean)：

- [`ContinuousFlexibility.Radial.positive_nat_nonsquare_or_succ`](../ContinuousFlexibility/Radial/MorseChainScales.lean#L27)
- [`ContinuousFlexibility.Radial.exists_nonsquare_between`](../ContinuousFlexibility/Radial/MorseChainScales.lean#L50)
- [`ContinuousFlexibility.Radial.exists_morseChainInteger`](../ContinuousFlexibility/Radial/MorseChainScales.lean#L64)
- [`ContinuousFlexibility.Radial.morseChainInteger_spec`](../ContinuousFlexibility/Radial/MorseChainScales.lean#L73)
- [`ContinuousFlexibility.Radial.morseChainInteger_minimal`](../ContinuousFlexibility/Radial/MorseChainScales.lean#L80)
- [`ContinuousFlexibility.Radial.morseChainInteger_lt`](../ContinuousFlexibility/Radial/MorseChainScales.lean#L87)
- [`ContinuousFlexibility.Radial.morseChainInteger_ge_two`](../ContinuousFlexibility/Radial/MorseChainScales.lean#L95)
- [`ContinuousFlexibility.Radial.morseChainInteger_error`](../ContinuousFlexibility/Radial/MorseChainScales.lean#L104)
- [`ContinuousFlexibility.Radial.finite_sigma_product_bounds`](../ContinuousFlexibility/Radial/MorseChainScales.lean#L109)
- [`ContinuousFlexibility.Radial.morseChainAmplitude_bounds`](../ContinuousFlexibility/Radial/MorseChainScales.lean#L119)
- [`ContinuousFlexibility.Radial.morseChainAmplitude_pos`](../ContinuousFlexibility/Radial/MorseChainScales.lean#L130)
- [`ContinuousFlexibility.Radial.morseChainAmplitude_log_bounds`](../ContinuousFlexibility/Radial/MorseChainScales.lean#L135)
- [`ContinuousFlexibility.Radial.morseChainAmplitude_succ`](../ContinuousFlexibility/Radial/MorseChainScales.lean#L158)
- [`ContinuousFlexibility.Radial.radial_nat_sq_le_Q`](../ContinuousFlexibility/Radial/MorseChainScales.lean#L186)
- [`ContinuousFlexibility.Radial.radial_scale_absorption`](../ContinuousFlexibility/Radial/MorseChainScales.lean#L203)

[MorseChainParameters.lean](../ContinuousFlexibility/Radial/MorseChainParameters.lean)：

- [`ContinuousFlexibility.Radial.morseChainA_factor`](../ContinuousFlexibility/Radial/MorseChainParameters.lean#L20)
- [`ContinuousFlexibility.Radial.morseChainB_inv_pow`](../ContinuousFlexibility/Radial/MorseChainParameters.lean#L42)
- [`ContinuousFlexibility.Radial.morseChainA_inv_bounds`](../ContinuousFlexibility/Radial/MorseChainParameters.lean#L49)
- [`ContinuousFlexibility.Radial.morseChainB_A_bounds`](../ContinuousFlexibility/Radial/MorseChainParameters.lean#L76)
- [`ContinuousFlexibility.Radial.morseChainParameters_pos`](../ContinuousFlexibility/Radial/MorseChainParameters.lean#L90)
- [`ContinuousFlexibility.Radial.morseChainA_exp_bounds`](../ContinuousFlexibility/Radial/MorseChainParameters.lean#L110)
- [`ContinuousFlexibility.Radial.morseChainA_le_of_sq_ge_log`](../ContinuousFlexibility/Radial/MorseChainParameters.lean#L138)
- [`ContinuousFlexibility.Radial.morseRootT_bounds`](../ContinuousFlexibility/Radial/MorseChainParameters.lean#L165)
- [`ContinuousFlexibility.Radial.morseRootT_sum`](../ContinuousFlexibility/Radial/MorseChainParameters.lean#L177)
- [`ContinuousFlexibility.Radial.morseRootT_mul`](../ContinuousFlexibility/Radial/MorseChainParameters.lean#L181)
- [`ContinuousFlexibility.Radial.morseRightRootT_ratio_bounds`](../ContinuousFlexibility/Radial/MorseChainParameters.lean#L189)
- [`ContinuousFlexibility.Radial.morseRightTurn_log_bounds`](../ContinuousFlexibility/Radial/MorseChainParameters.lean#L200)
- [`ContinuousFlexibility.Radial.morseTurn_order`](../ContinuousFlexibility/Radial/MorseChainParameters.lean#L209)
- [`ContinuousFlexibility.Radial.exp_neg_morseLeftTurn`](../ContinuousFlexibility/Radial/MorseChainParameters.lean#L214)
- [`ContinuousFlexibility.Radial.exp_neg_morseRightTurn`](../ContinuousFlexibility/Radial/MorseChainParameters.lean#L220)
- [`ContinuousFlexibility.Radial.morseRho_factor`](../ContinuousFlexibility/Radial/MorseChainParameters.lean#L229)
- [`ContinuousFlexibility.Radial.morseRho_zero_iff_turn`](../ContinuousFlexibility/Radial/MorseChainParameters.lean#L242)
- [`ContinuousFlexibility.Radial.morseRho_pos_between_turns`](../ContinuousFlexibility/Radial/MorseChainParameters.lean#L259)
- [`ContinuousFlexibility.Radial.morseRho_neg_before_left_turn`](../ContinuousFlexibility/Radial/MorseChainParameters.lean#L271)
- [`ContinuousFlexibility.Radial.morseRho_neg_after_right_turn`](../ContinuousFlexibility/Radial/MorseChainParameters.lean#L282)
- [`ContinuousFlexibility.Radial.morseRho_right_cap_bounds`](../ContinuousFlexibility/Radial/MorseChainParameters.lean#L294)
- [`ContinuousFlexibility.Radial.morseRho_right_cap_lower`](../ContinuousFlexibility/Radial/MorseChainParameters.lean#L313)
- [`ContinuousFlexibility.Radial.hasDerivAt_morseRho`](../ContinuousFlexibility/Radial/MorseChainParameters.lean#L339)
- [`ContinuousFlexibility.Radial.morseRho_deriv_left_turn_pos`](../ContinuousFlexibility/Radial/MorseChainParameters.lean#L349)
- [`ContinuousFlexibility.Radial.morseRho_deriv_right_turn_neg`](../ContinuousFlexibility/Radial/MorseChainParameters.lean#L356)

[MorseLeftCapIntegrals.lean](../ContinuousFlexibility/Radial/MorseLeftCapIntegrals.lean)：

- [`ContinuousFlexibility.Radial.exp_neg_morseCellLeftCut`](../ContinuousFlexibility/Radial/MorseLeftCapIntegrals.lean#L26)
- [`ContinuousFlexibility.Radial.morseCellLeftCut_lt_rightTurn`](../ContinuousFlexibility/Radial/MorseLeftCapIntegrals.lean#L29)
- [`ContinuousFlexibility.Radial.morseLeftMassLength_log_le`](../ContinuousFlexibility/Radial/MorseLeftCapIntegrals.lean#L36)
- [`ContinuousFlexibility.Radial.morseLeftMassLength_le_hundred_div`](../ContinuousFlexibility/Radial/MorseLeftCapIntegrals.lean#L46)
- [`ContinuousFlexibility.Radial.abs_morseRho_le`](../ContinuousFlexibility/Radial/MorseLeftCapIntegrals.lean#L163)
- [`ContinuousFlexibility.Radial.morseLeftMass_integral`](../ContinuousFlexibility/Radial/MorseLeftCapIntegrals.lean#L227)
- [`ContinuousFlexibility.Radial.morseLeftMass_first_moment`](../ContinuousFlexibility/Radial/MorseLeftCapIntegrals.lean#L237)
- [`ContinuousFlexibility.Radial.morseLeftMass_abs_integral_le`](../ContinuousFlexibility/Radial/MorseLeftCapIntegrals.lean#L249)
- [`ContinuousFlexibility.Radial.morseLeftMass_abs_first_moment_le`](../ContinuousFlexibility/Radial/MorseLeftCapIntegrals.lean#L262)
- [`ContinuousFlexibility.Radial.morseLeftMass_abs_integral_from_le`](../ContinuousFlexibility/Radial/MorseLeftCapIntegrals.lean#L281)
- [`ContinuousFlexibility.Radial.morseLeftMass_abs_first_moment_from_le`](../ContinuousFlexibility/Radial/MorseLeftCapIntegrals.lean#L290)
- [`ContinuousFlexibility.Radial.morseLeftMass_integral_error`](../ContinuousFlexibility/Radial/MorseLeftCapIntegrals.lean#L317)
- [`ContinuousFlexibility.Radial.morseLeftMass_first_moment_error`](../ContinuousFlexibility/Radial/MorseLeftCapIntegrals.lean#L337)

[MorseRadiusODE.lean](../ContinuousFlexibility/Radial/MorseRadiusODE.lean)：

- [`ContinuousFlexibility.Radial.contDiff_morseRho`](../ContinuousFlexibility/Radial/MorseRadiusODE.lean#L243)
- [`ContinuousFlexibility.Radial.exists_morseRadiusSystem`](../ContinuousFlexibility/Radial/MorseRadiusODE.lean#L250)
- [`ContinuousFlexibility.Radial.exists_morseRadius`](../ContinuousFlexibility/Radial/MorseRadiusODE.lean#L271)
- [`ContinuousFlexibility.Radial.morseRadius_eqOn`](../ContinuousFlexibility/Radial/MorseRadiusODE.lean#L288)
- [`ContinuousFlexibility.Radial.morseRadius_velocity_eq_integral`](../ContinuousFlexibility/Radial/MorseRadiusODE.lean#L336)
- [`ContinuousFlexibility.Radial.morseRadius_eq_volterra`](../ContinuousFlexibility/Radial/MorseRadiusODE.lean#L358)

[MorseRightCapBounds.lean](../ContinuousFlexibility/Radial/MorseRightCapBounds.lean)：

- [`ContinuousFlexibility.Radial.morseRightCapLength_pos`](../ContinuousFlexibility/Radial/MorseRightCapBounds.lean#L29)
- [`ContinuousFlexibility.Radial.morseRightCap_radius_bounds`](../ContinuousFlexibility/Radial/MorseRightCapBounds.lean#L72)
- [`ContinuousFlexibility.Radial.morseRightCap_radius_span`](../ContinuousFlexibility/Radial/MorseRightCapBounds.lean#L211)
- [`ContinuousFlexibility.Radial.morseRightCap_travel_bounds`](../ContinuousFlexibility/Radial/MorseRightCapBounds.lean#L284)
- [`ContinuousFlexibility.Radial.morseRightCap_travel_bounds_fixed`](../ContinuousFlexibility/Radial/MorseRightCapBounds.lean#L323)
- [`ContinuousFlexibility.Radial.exists_morseRadius_with_rightCap`](../ContinuousFlexibility/Radial/MorseRightCapBounds.lean#L344)

[MorseCellJoinCollars.lean](../ContinuousFlexibility/Radial/MorseCellJoinCollars.lean)：

- [`ContinuousFlexibility.Radial.morseRadius_joinCollar_bounds`](../ContinuousFlexibility/Radial/MorseCellJoinCollars.lean#L145)
- [`ContinuousFlexibility.Radial.exists_morseRadius_with_joinCollars`](../ContinuousFlexibility/Radial/MorseCellJoinCollars.lean#L246)
- [`ContinuousFlexibility.Radial.morseCollarLogProfile_jet`](../ContinuousFlexibility/Radial/MorseCellJoinCollars.lean#L325)
- [`ContinuousFlexibility.Radial.morseCollarLogSlope_bounds`](../ContinuousFlexibility/Radial/MorseCellJoinCollars.lean#L387)
- [`ContinuousFlexibility.Radial.morseCollarLogSlope_ge_two_div`](../ContinuousFlexibility/Radial/MorseCellJoinCollars.lean#L453)

[MorseCellMassTravel.lean](../ContinuousFlexibility/Radial/MorseCellMassTravel.lean)：

- [`ContinuousFlexibility.Radial.morseCellLeftCut_lt_shortLeftCapCut`](../ContinuousFlexibility/Radial/MorseCellMassTravel.lean#L32)
- [`ContinuousFlexibility.Radial.morseShortLeftCapLength_pos`](../ContinuousFlexibility/Radial/MorseCellMassTravel.lean#L36)
- [`ContinuousFlexibility.Radial.morseShortLeftCapCut_lt_leftTurn`](../ContinuousFlexibility/Radial/MorseCellMassTravel.lean#L39)
- [`ContinuousFlexibility.Radial.morseShortLeftCap_negRho_lower`](../ContinuousFlexibility/Radial/MorseCellMassTravel.lean#L55)
- [`ContinuousFlexibility.Radial.morseLeftCap_negRho_upper`](../ContinuousFlexibility/Radial/MorseCellMassTravel.lean#L72)
- [`ContinuousFlexibility.Radial.morseLeftCap_travel_bounds`](../ContinuousFlexibility/Radial/MorseCellMassTravel.lean#L102)
- [`ContinuousFlexibility.Radial.morseLeftCell_velocity_mass_bounds`](../ContinuousFlexibility/Radial/MorseCellMassTravel.lean#L136)
- [`ContinuousFlexibility.Radial.exists_morseRadius_retainedCell_mass_travel`](../ContinuousFlexibility/Radial/MorseCellMassTravel.lean#L201)
- [`ContinuousFlexibility.Radial.morseCell_strictMonoOn`](../ContinuousFlexibility/Radial/MorseCellMassTravel.lean#L241)
- [`ContinuousFlexibility.Radial.morseCellModelCoordinate_apply`](../ContinuousFlexibility/Radial/MorseCellMassTravel.lean#L246)
- [`ContinuousFlexibility.Radial.morseCellModelCoordinate_right`](../ContinuousFlexibility/Radial/MorseCellMassTravel.lean#L251)
- [`ContinuousFlexibility.Radial.morseCellRadialProfile_apply`](../ContinuousFlexibility/Radial/MorseCellMassTravel.lean#L259)
- [`ContinuousFlexibility.Radial.morseCell_coreTransfer_mass_resistance_change`](../ContinuousFlexibility/Radial/MorseCellMassTravel.lean#L291)
- [`ContinuousFlexibility.Radial.morseCell_chain_mass_resistance_change`](../ContinuousFlexibility/Radial/MorseCellMassTravel.lean#L324)
- [`ContinuousFlexibility.Radial.morseRetainedCell_chain_mass_resistance_change`](../ContinuousFlexibility/Radial/MorseCellMassTravel.lean#L371)

[MorseChainRadiusPlacement.lean](../ContinuousFlexibility/Radial/MorseChainRadiusPlacement.lean)：

- [`ContinuousFlexibility.Radial.morseChainA_summable_shift`](../ContinuousFlexibility/Radial/MorseChainRadiusPlacement.lean#L57)
- [`ContinuousFlexibility.Radial.exists_morseChainRadiusPlacement`](../ContinuousFlexibility/Radial/MorseChainRadiusPlacement.lean#L165)

[MorseLeftCapBounds.lean](../ContinuousFlexibility/Radial/MorseLeftCapBounds.lean)：

- [`ContinuousFlexibility.Radial.morseLeftCap_radius_bounds`](../ContinuousFlexibility/Radial/MorseLeftCapBounds.lean#L125)
- [`ContinuousFlexibility.Radial.exists_morseRadius_retainedCell`](../ContinuousFlexibility/Radial/MorseLeftCapBounds.lean#L305)

[MorsePositiveJoin.lean](../ContinuousFlexibility/Radial/MorsePositiveJoin.lean)：

- [`ContinuousFlexibility.Radial.contDiff_morseJoinLeftWeight`](../ContinuousFlexibility/Radial/MorsePositiveJoin.lean#L27)
- [`ContinuousFlexibility.Radial.contDiff_morseJoinRightWeight`](../ContinuousFlexibility/Radial/MorsePositiveJoin.lean#L33)
- [`ContinuousFlexibility.Radial.morseJoinLeftWeight_one`](../ContinuousFlexibility/Radial/MorsePositiveJoin.lean#L39)
- [`ContinuousFlexibility.Radial.morseJoinLeftWeight_zero`](../ContinuousFlexibility/Radial/MorsePositiveJoin.lean#L46)
- [`ContinuousFlexibility.Radial.morseJoinRightWeight_one`](../ContinuousFlexibility/Radial/MorsePositiveJoin.lean#L53)
- [`ContinuousFlexibility.Radial.morseJoinRightWeight_zero`](../ContinuousFlexibility/Radial/MorsePositiveJoin.lean#L60)
- [`ContinuousFlexibility.Radial.morseJoin_weights_disjoint`](../ContinuousFlexibility/Radial/MorsePositiveJoin.lean#L67)
- [`ContinuousFlexibility.Radial.morseJoinDenominator_bounds`](../ContinuousFlexibility/Radial/MorsePositiveJoin.lean#L119)
- [`ContinuousFlexibility.Radial.morseJoinDenominator_pos`](../ContinuousFlexibility/Radial/MorsePositiveJoin.lean#L151)
- [`ContinuousFlexibility.Radial.contDiff_morseJoinSlope`](../ContinuousFlexibility/Radial/MorsePositiveJoin.lean#L163)
- [`ContinuousFlexibility.Radial.hasDerivAt_morseJoinLog`](../ContinuousFlexibility/Radial/MorsePositiveJoin.lean#L169)
- [`ContinuousFlexibility.Radial.contDiff_morseJoinLog`](../ContinuousFlexibility/Radial/MorsePositiveJoin.lean#L176)
- [`ContinuousFlexibility.Radial.morseJoinLog_right_value`](../ContinuousFlexibility/Radial/MorsePositiveJoin.lean#L200)
- [`ContinuousFlexibility.Radial.morseJoinLog_eqOn_left`](../ContinuousFlexibility/Radial/MorsePositiveJoin.lean#L230)
- [`ContinuousFlexibility.Radial.morseJoinLog_eqOn_right`](../ContinuousFlexibility/Radial/MorsePositiveJoin.lean#L254)
- [`ContinuousFlexibility.Radial.morseJoinLog_endpoint_germs`](../ContinuousFlexibility/Radial/MorsePositiveJoin.lean#L283)
- [`ContinuousFlexibility.Radial.morseJoinProfile_endpoint_germs`](../ContinuousFlexibility/Radial/MorsePositiveJoin.lean#L294)
- [`ContinuousFlexibility.Radial.morseJoinLog_deriv_middle`](../ContinuousFlexibility/Radial/MorsePositiveJoin.lean#L302)
- [`ContinuousFlexibility.Radial.morseJoinConstant_ge`](../ContinuousFlexibility/Radial/MorsePositiveJoin.lean#L316)
- [`ContinuousFlexibility.Radial.morseJoinLog_deriv_ge`](../ContinuousFlexibility/Radial/MorsePositiveJoin.lean#L326)
- [`ContinuousFlexibility.Radial.morseJoinProfile_deriv`](../ContinuousFlexibility/Radial/MorsePositiveJoin.lean#L352)
- [`ContinuousFlexibility.Radial.morseJoinProfile_positive_mono`](../ContinuousFlexibility/Radial/MorsePositiveJoin.lean#L361)
- [`ContinuousFlexibility.Radial.morseJoinBudget_of_upper_slopes`](../ContinuousFlexibility/Radial/MorsePositiveJoin.lean#L391)
- [`ContinuousFlexibility.Radial.exists_morseJoinWeight_jet_bound`](../ContinuousFlexibility/Radial/MorsePositiveJoin.lean#L475)
- [`ContinuousFlexibility.Radial.iteratedDeriv_morseJoinLog_succ`](../ContinuousFlexibility/Radial/MorsePositiveJoin.lean#L512)

[MorseCellModelJets.lean](../ContinuousFlexibility/Radial/MorseCellModelJets.lean)：

- [`ContinuousFlexibility.Radial.morseRho_iteratedDeriv_abs_le`](../ContinuousFlexibility/Radial/MorseCellModelJets.lean#L40)
- [`ContinuousFlexibility.Radial.exists_morseRadius_modelJet_bound`](../ContinuousFlexibility/Radial/MorseCellModelJets.lean#L95)
- [`ContinuousFlexibility.Radial.exists_morseRadius_with_modelJets`](../ContinuousFlexibility/Radial/MorseCellModelJets.lean#L153)

[MorseCellPhysicalJets.lean](../ContinuousFlexibility/Radial/MorseCellPhysicalJets.lean)：

- [`ContinuousFlexibility.Radial.morseCollarCoordinate_physicalChart`](../ContinuousFlexibility/Radial/MorseCellPhysicalJets.lean#L257)
- [`ContinuousFlexibility.Radial.morseCellPhysical_iteratedDeriv`](../ContinuousFlexibility/Radial/MorseCellPhysicalJets.lean#L318)
- [`ContinuousFlexibility.Radial.morseCellPhysicalHeight_smooth`](../ContinuousFlexibility/Radial/MorseCellPhysicalJets.lean#L363)
- [`ContinuousFlexibility.Radial.morseCellPhysicalHeight_value_bounds`](../ContinuousFlexibility/Radial/MorseCellPhysicalJets.lean#L378)
- [`ContinuousFlexibility.Radial.exists_morseCellPhysicalJet_bound`](../ContinuousFlexibility/Radial/MorseCellPhysicalJets.lean#L403)
- [`ContinuousFlexibility.Radial.exists_morseRadius_with_physicalJets`](../ContinuousFlexibility/Radial/MorseCellPhysicalJets.lean#L465)

[MorseChainEndpointDistances.lean](../ContinuousFlexibility/Radial/MorseChainEndpointDistances.lean)：

- [`ContinuousFlexibility.Radial.morseChainA_tail_control`](../ContinuousFlexibility/Radial/MorseChainEndpointDistances.lean#L37)
- [`ContinuousFlexibility.Radial.morse_outward_distances`](../ContinuousFlexibility/Radial/MorseChainEndpointDistances.lean#L89)
- [`ContinuousFlexibility.Radial.morsePlaced_endpoint_distances`](../ContinuousFlexibility/Radial/MorseChainEndpointDistances.lean#L124)

[MorseChainLocalGluing.lean](../ContinuousFlexibility/Radial/MorseChainLocalGluing.lean)：

- [`ContinuousFlexibility.Radial.morseGlueCut_eventually_left`](../ContinuousFlexibility/Radial/MorseChainLocalGluing.lean#L21)
- [`ContinuousFlexibility.Radial.morseGlueCut_eventually_right`](../ContinuousFlexibility/Radial/MorseChainLocalGluing.lean#L33)
- [`ContinuousFlexibility.Radial.contDiff_morseGlueCut`](../ContinuousFlexibility/Radial/MorseChainLocalGluing.lean#L42)
- [`ContinuousFlexibility.Radial.morse_outward_block_exists`](../ContinuousFlexibility/Radial/MorseChainLocalGluing.lean#L66)
- [`ContinuousFlexibility.Radial.morseOutwardGlue_apply_block`](../ContinuousFlexibility/Radial/MorseChainLocalGluing.lean#L83)
- [`ContinuousFlexibility.Radial.morseOutwardGlue_eventually_piece`](../ContinuousFlexibility/Radial/MorseChainLocalGluing.lean#L99)
- [`ContinuousFlexibility.Radial.morseOutwardGlue_iteratedDeriv_eq`](../ContinuousFlexibility/Radial/MorseChainLocalGluing.lean#L131)
- [`ContinuousFlexibility.Radial.morseOutwardGlue_eq_zero_of_le`](../ContinuousFlexibility/Radial/MorseChainLocalGluing.lean#L138)
- [`ContinuousFlexibility.Radial.contDiffOn_morseOutwardGlue`](../ContinuousFlexibility/Radial/MorseChainLocalGluing.lean#L153)
- [`ContinuousFlexibility.Radial.exists_morseOutwardGlue_models_joins`](../ContinuousFlexibility/Radial/MorseChainLocalGluing.lean#L172)

[MorseJoinActualGerms.lean](../ContinuousFlexibility/Radial/MorseJoinActualGerms.lean)：

- [`ContinuousFlexibility.Radial.exists_contDiff_joinGerm_extension`](../ContinuousFlexibility/Radial/MorseJoinActualGerms.lean#L23)
- [`ContinuousFlexibility.Radial.morseCollar_scaledRadius_image_Ioo`](../ContinuousFlexibility/Radial/MorseJoinActualGerms.lean#L86)
- [`ContinuousFlexibility.Radial.morseCollarLogProfile_at_model`](../ContinuousFlexibility/Radial/MorseJoinActualGerms.lean#L94)
- [`ContinuousFlexibility.Radial.exp_morseCollarLogProfile_eqOn`](../ContinuousFlexibility/Radial/MorseJoinActualGerms.lean#L105)
- [`ContinuousFlexibility.Radial.contDiffOn_morseCollarLogProfile`](../ContinuousFlexibility/Radial/MorseJoinActualGerms.lean#L122)
- [`ContinuousFlexibility.Radial.exists_morseCollarLogProfile_extension`](../ContinuousFlexibility/Radial/MorseJoinActualGerms.lean#L134)
- [`ContinuousFlexibility.Radial.morseJoinBudget_congr_of_germs`](../ContinuousFlexibility/Radial/MorseJoinActualGerms.lean#L151)
- [`ContinuousFlexibility.Radial.exists_morseJoin_of_model_germs`](../ContinuousFlexibility/Radial/MorseJoinActualGerms.lean#L184)

[MorseJoinHeightContrast.lean](../ContinuousFlexibility/Radial/MorseJoinHeightContrast.lean)：

- [`ContinuousFlexibility.Radial.morseJoin_rpow_increment`](../ContinuousFlexibility/Radial/MorseJoinHeightContrast.lean#L22)
- [`ContinuousFlexibility.Radial.morseChainAmplitude_log_succ`](../ContinuousFlexibility/Radial/MorseJoinHeightContrast.lean#L69)
- [`ContinuousFlexibility.Radial.morseChainAmplitude_log_adjacent_bound`](../ContinuousFlexibility/Radial/MorseJoinHeightContrast.lean#L90)
- [`ContinuousFlexibility.Radial.morseChainA_log_error`](../ContinuousFlexibility/Radial/MorseJoinHeightContrast.lean#L119)
- [`ContinuousFlexibility.Radial.morseJoin_scaleRatio_log_bound`](../ContinuousFlexibility/Radial/MorseJoinHeightContrast.lean#L141)
- [`ContinuousFlexibility.Radial.morseJoin_height_log_range_of_error`](../ContinuousFlexibility/Radial/MorseJoinHeightContrast.lean#L184)
- [`ContinuousFlexibility.Radial.morseJoin_height_budget`](../ContinuousFlexibility/Radial/MorseJoinHeightContrast.lean#L210)
- [`ContinuousFlexibility.Radial.morseJoin_height_log_contrast`](../ContinuousFlexibility/Radial/MorseJoinHeightContrast.lean#L221)


<a id="r06"></a>
## R06 深尾连续算子逆与唯一衰减线

**状态：** 已有部分已编译子结果。**分支：** 径向参考。主定理必要节点。

**数学陈述：** 深尾条件下，A_p=-p⁻¹(p∂x)'的Dirichlet/Friedrichs实现具有文中逆界，端点恰有一条自然L²齐次解线；其衰减、原半径平坦性、Green核衰减和参数连续性成立。

**证明提纲：** 严格做连续Dirichlet-to-Neumann化、离散形式分解、有限截断极限识别及limit-point；再转换回原半径和dr配对。

**直接依赖：** [R01](#r01), [R05](#r05)

**论文定位：** [05-flat-end-chain.tex:271–505](../paper/flexible-surface-rewrite/05-flat-end-chain.tex#L271)，`lem:radial-deep-inverse`

**目标文件：** `ContinuousFlexibility/Radial/R06.lean`（节点组织目标；实际已存在的证明文件见下方，整个节点尚未完成）

**验收条件：**

- 连续与离散form domain对应
- 有限截断极限确实实现目标连续算子
- 唯一解线、平坦性及product-topology连续性分别证明
- 左端x=−log r时显式处理mass/resistance顺序的一格索引移动及源Jacobian

**已经完成的子结果：**

- 实际电阻坐标单边上，Dirichlet 端点零值给出以 G₀(s,s) 为常数的点值平方估计，已证精确加权相对能量界。
- 实际单边 Dirichlet 能量、Green 三点乘积、对角质量阻力界、零势 Green 积分解和端点导数已验证。物理局部化规格允许左侧的两个相邻编号及实际初边。已由实际对角积分收缩构造连续源的带势 Dirichlet 解。

**仍待闭合的义务：**

- 把实际 p 输运到电阻坐标，完成 L² 单边逆、Poisson 通量矩阵、节点与全尾逆及衰减线。
- 从实际 R05 数据验证深尾条件、边界与物理平坦性。

**优先核查程度：** critical（任务风险标记，不是已发现错误）

**现有 Lean 证明：**

[TailEdgeEnergy.lean](../ContinuousFlexibility/Radial/TailEdgeEnergy.lean)：

- [`ContinuousFlexibility.Radial.tailEdgeGreen_self`](../ContinuousFlexibility/Radial/TailEdgeEnergy.lean#L22)
- [`ContinuousFlexibility.Radial.tailEdge_value_sq_le_green_energy`](../ContinuousFlexibility/Radial/TailEdgeEnergy.lean#L62)
- [`ContinuousFlexibility.Radial.tailEdge_weighted_energy_bound`](../ContinuousFlexibility/Radial/TailEdgeEnergy.lean#L94)

[TailEdgeKernel.lean](../ContinuousFlexibility/Radial/TailEdgeKernel.lean)：

- [`ContinuousFlexibility.Radial.tailEdgeGreen_comm`](../ContinuousFlexibility/Radial/TailEdgeKernel.lean#L17)
- [`ContinuousFlexibility.Radial.tailEdgeGreen_nonneg`](../ContinuousFlexibility/Radial/TailEdgeKernel.lean#L22)
- [`ContinuousFlexibility.Radial.tailEdgeGreen_threePoint`](../ContinuousFlexibility/Radial/TailEdgeKernel.lean#L68)
- [`ContinuousFlexibility.Radial.tailEdgeGreen_leftHeight`](../ContinuousFlexibility/Radial/TailEdgeKernel.lean#L82)
- [`ContinuousFlexibility.Radial.tailEdgeGreen_rightHeight`](../ContinuousFlexibility/Radial/TailEdgeKernel.lean#L104)

[TailEdgeMassResistance.lean](../ContinuousFlexibility/Radial/TailEdgeMassResistance.lean)：

- [`ContinuousFlexibility.Radial.tailEdgeGreen_self_le_left`](../ContinuousFlexibility/Radial/TailEdgeMassResistance.lean#L17)
- [`ContinuousFlexibility.Radial.tailEdgeGreen_self_le_right`](../ContinuousFlexibility/Radial/TailEdgeMassResistance.lean#L23)
- [`ContinuousFlexibility.Radial.tailEdge_green_diagonal_le_mass_resistance`](../ContinuousFlexibility/Radial/TailEdgeMassResistance.lean#L34)

[TailEdgePerturbedGreen.lean](../ContinuousFlexibility/Radial/TailEdgePerturbedGreen.lean)：

- [`ContinuousFlexibility.Radial.tailEdgeGreen_le_diagonal`](../ContinuousFlexibility/Radial/TailEdgePerturbedGreen.lean#L37)
- [`ContinuousFlexibility.Radial.tailEdgeGreenAction_apply`](../ContinuousFlexibility/Radial/TailEdgePerturbedGreen.lean#L75)
- [`ContinuousFlexibility.Radial.norm_tailEdgeGreenAction_le`](../ContinuousFlexibility/Radial/TailEdgePerturbedGreen.lean#L98)
- [`ContinuousFlexibility.Radial.tailEdgeGreenStep_contracting`](../ContinuousFlexibility/Radial/TailEdgePerturbedGreen.lean#L130)
- [`ContinuousFlexibility.Radial.existsUnique_tailEdgeIntegralSolution`](../ContinuousFlexibility/Radial/TailEdgePerturbedGreen.lean#L141)
- [`ContinuousFlexibility.Radial.exists_tailEdge_perturbed_boundary`](../ContinuousFlexibility/Radial/TailEdgePerturbedGreen.lean#L167)

[TailEdgeZeroGreen.lean](../ContinuousFlexibility/Radial/TailEdgeZeroGreen.lean)：

- [`ContinuousFlexibility.Radial.hasDerivAt_tailEdgeZeroSolve`](../ContinuousFlexibility/Radial/TailEdgeZeroGreen.lean#L43)
- [`ContinuousFlexibility.Radial.hasDerivAt_deriv_tailEdgeZeroSolve`](../ContinuousFlexibility/Radial/TailEdgeZeroGreen.lean#L56)
- [`ContinuousFlexibility.Radial.tailEdgeZeroSolve_endpoints`](../ContinuousFlexibility/Radial/TailEdgeZeroGreen.lean#L67)
- [`ContinuousFlexibility.Radial.tailEdgeZeroSolve_endpoint_deriv`](../ContinuousFlexibility/Radial/TailEdgeZeroGreen.lean#L71)
- [`ContinuousFlexibility.Radial.tailEdgeZeroSolve_eq_integral`](../ContinuousFlexibility/Radial/TailEdgeZeroGreen.lean#L81)


<a id="r07"></a>
## R07 过渡区与所有频率同时选高

**状态：** 待形式化。**分支：** 径向参考。主定理必要节点。

**数学陈述：** 每个偶正频率具有唯一过渡单元；存在同一个高度序列(σ_n)，使所有频率的incoming line与自然端线具有文中定量角度下界。

**证明提纲：** 证明单坐标坏集测度界、有限维Fubini/并集估计、闭条件和乘积紧性极限。

**直接依赖：** [R04](#r04), [R05](#r05), [R06](#r06)

**论文定位：** [05-flat-end-chain.tex:507–667](../paper/flexible-surface-rewrite/05-flat-end-chain.tex#L507)，`lem:radial-product-selection`

**目标文件：** `ContinuousFlexibility/Radial/R07.lean`（拟建，尚无此证明）

**验收条件：**

- 量词为∃(σ_n)∀j，而非∀j∃(σ_n)
- 无限条件的闭性与线连续性
- 核验过渡/深尾频率区域确实穷尽全部偶正频率

**优先核查程度：** critical（任务风险标记，不是已发现错误）

<a id="r08"></a>
## R08 保留二模的中央目标连接

**状态：** 待形式化。**分支：** 径向参考。主定理必要节点。

**数学陈述：** 构造把两个已选尾和中央模型连起来的光滑径向轮廓及非零全局二模平坦解φ*，保留可调cut/cone-head长度并不改变负区旅行角。

**证明提纲：** 通过二模解的对数斜率设计正连接，证明正性和端点匹配；保留后续全局估计需要的参数自由。

**直接依赖：** [R03](#r03), [R07](#r07)

**论文定位：** [06-global-reference-inverse.tex:50–98](../paper/flexible-surface-rewrite/06-global-reference-inverse.tex#L50)，`eq:rad-eq-sp1`

**目标文件：** `ContinuousFlexibility/Radial/R08.lean`（拟建，尚无此证明）

**验收条件：**

- φ*是真实非零解
- 新增连接不破坏已选角度
- 后续不得暗中重选已冻结的几何

<a id="r09"></a>
## R09 正buffer压缩与Poisson边界矩阵

**状态：** 待形式化。**分支：** 径向参考。主定理必要节点。

**数学陈述：** 从full-model或bordered inverse及正势下界，得到保留区Dirichlet逆、Poisson lift及boundary derivative矩阵的实际界和正定性。

**证明提纲：** 用正区间指数衰减估计cutoff误差，分别处理点源Green列与普通L²源。

**直接依赖：** [R03](#r03), [R04](#r04)

**论文定位：** [06-global-reference-inverse.tex:100–229](../paper/flexible-surface-rewrite/06-global-reference-inverse.tex#L100)，`lem:fence-compression`

**目标文件：** `ContinuousFlexibility/Radial/R09.lean`（拟建，尚无此证明）

**验收条件：**

- 标量边框support远离cut
- 点源不能当作普通L²源
- 得到可用于拼接的边界配对和符号

<a id="r10"></a>
## R10 全局匹配Green逆

**状态：** 待形式化。**分支：** 径向参考。主定理必要节点。

**数学陈述：** 保留完整正interface能量构造内部逆，构造不除入口高度的外逆，证明最终2×2匹配矩阵可逆，得到真实全局matched Green逆和对称block公式。

**证明提纲：** 分别组装内部、过渡、外部；用选高角界及前一正cap衰减控制返回内部的block。

**直接依赖：** [R06](#r06), [R07](#r07), [R08](#r08), [R09](#r09)

**论文定位：** [06-global-reference-inverse.tex:231–590](../paper/flexible-surface-rewrite/06-global-reference-inverse.tex#L231)，`eq:rad-eq-tm11`

**目标文件：** `ContinuousFlexibility/Radial/R10.lean`（拟建，尚无此证明）

**验收条件：**

- Hilbert测度12w/r² dr与源dr显式转换
- 辅助二模边框贯穿拼接
- 匹配矩阵恒等式与其定量可逆性分开

**优先核查程度：** high（任务风险标记，不是已发现错误）

<a id="r11"></a>
## R11 同一几何上的双权全局估计

**状态：** 待形式化。**分支：** 径向参考。主定理必要节点。

**数学陈述：** 先固定β=3/4和一个ε∈(0,1/4)，在同一几何上对β−ε、β、β+ε获得足够的加权block/Schur逆界和一阶法向估计。

**证明提纲：** 冻结源权指数、几何参数、输出权指数的选择顺序，区分外部输出和返回固定内部的代价吸收。

**直接依赖：** [R05](#r05), [R10](#r10)

**论文定位：** [06-global-reference-inverse.tex:570–764](../paper/flexible-surface-rewrite/06-global-reference-inverse.tex#L570)，`lem:radial-uniform-exponents`

**目标文件：** `ContinuousFlexibility/Radial/R11.lean`（拟建，尚无此证明）

**验收条件：**

- 不同指数必须共用w*,φ*,边框和自然端点逆
- 几何不依赖最终微分阶数
- 全(0,1)紧区间版本另列X01，不是不同指数分别造几何

**优先核查程度：** critical（任务风险标记，不是已发现错误）

<a id="r12"></a>
## R12 固定径向参考与闭图域双侧逆

**状态：** 待形式化。**分支：** 径向参考。主定理必要节点。

**数学陈述：** 实例化RadialReference：同一w*,φ*,g*,ℓ*满足偶余弦二模核恰一维、其余偶模核零、返回小除数、边框归一化及兼容源上的双侧逆。图域有分布意义、smooth core闭包识别；右端归零、左端常数自由。

**证明提纲：** 零模用两次primitive求解；证明LG=I和GL=I、Green reciprocity、closed graph及core稠密；把辅助边框替换成真实度量导数列。

**直接依赖：** [R06](#r06), [R08](#r08), [R10](#r10), [R11](#r11)

**论文定位：** [04-designing-the-profile.tex:74–106](../paper/flexible-surface-rewrite/04-designing-the-profile.tex#L74)，`prop:rad-fixed-theorem`；[06-global-reference-inverse.tex:766–908](../paper/flexible-surface-rewrite/06-global-reference-inverse.tex#L766)，`lem:rad-green-completion`

**目标文件：** `ContinuousFlexibility/Radial/R12.lean`（拟建，尚无此证明）

**验收条件：**

- 不能仅把域定义成逆的像而略去物理域识别
- ℓ*u=∫g*u₂dr且∫g*φ*dr=1
- R12只使用§4源范数/§6图域，不依赖§7物理空间W02，防止循环

**优先核查程度：** critical（任务风险标记，不是已发现错误）

<a id="w01"></a>
## W01 材料坐标与连续权函数

**状态：** 已有部分已编译子结果。**分支：** 分析基础与加权空间。主定理必要节点。

**数学陈述：** 定义x∂,H,E₀,M,ℓ,ρ并证明ρ为全实轴光滑坐标；E₀^A≤C_AM、H^ε M^A≤C_{A,ε}，材料导数和径向导数各阶换算系数受控，且与离散单元尺度一致。

**证明提纲：** 先证明连续实变量的对数比较，再用R05的端点距离/单元界实例化。所需实际轮廓jet来自R05，不必等待整个R12。

**直接依赖：** [R05](#r05)

**论文定位：** [07-fixed-geometry.tex:22–59](../paper/flexible-surface-rewrite/07-fixed-geometry.tex#L22)，`eq:readable-physical-weights`

**目标文件：** `ContinuousFlexibility/Analysis/W01.lean`（节点组织目标；实际已存在的证明文件见下方，整个节点尚未完成）

**验收条件：**

- 明确所有量词为固定阶数后存在常数
- 比较连续权和离散H_n,ℰ_n
- 普通径向导数的代价全部记账

**已经完成的子结果：**

- 实际H/E0/M采用论文的实分数幂与对数指数；任意固定实A均有全x≥0的正统一常数包络E0^A≤CM及H^εM^A≤C
- 实际log²(e+x)/sqrt(x)趋零与compact补尾界；H^εM^A和H^εE0^A对每ε>0真实趋零
- 左端实际X(d)=sqrt(log(d0/d))、ell与rho的真实导数、双向指数反函数及端点无穷极限；权重沿真实d→0+趋零
- 归一材料区间的真实正光滑ell、积分rho全实轴坐标及光滑逆、实际左右拼接权和任意固定实指数全局包络已编译。
- 单位区间正光滑材料长度与实际权已有显式仿射移植；正 rho、全实轴材料坐标及光滑逆、左右权、材料单位窗比较、端点全阶吸收和三次指数移位包络已通过。
- 仿射材料模型的全区间 log H、log M、log ell 的任意固定正阶材料导数界已验证；已有材料坐标、左右拼接和实际全局包络。
- 精确 W01Statement 已通过。对任一满足 IsAccumulatingProfile 的实际径向输入，同一个仿射材料数据满足全部坐标、全阶权与径向展开、离散取样、定量迹宽及单元比较条件。

**仍待闭合的义务：**

- 从 R05 实际构造积聚轮廓见证，并将该 W01 定理用于 W02 的物理空间。

**现有 Lean 证明：**

[MaterialCoordinate.lean](../ContinuousFlexibility/Analysis/MaterialCoordinate.lean)：

- [`ContinuousFlexibility.Analysis.endpoint_log_pos`](../ContinuousFlexibility/Analysis/MaterialCoordinate.lean#L41)
- [`ContinuousFlexibility.Analysis.endpointX_pos`](../ContinuousFlexibility/Analysis/MaterialCoordinate.lean#L45)
- [`ContinuousFlexibility.Analysis.endpointEll_pos`](../ContinuousFlexibility/Analysis/MaterialCoordinate.lean#L48)
- [`ContinuousFlexibility.Analysis.hasDerivAt_endpoint_log`](../ContinuousFlexibility/Analysis/MaterialCoordinate.lean#L53)
- [`ContinuousFlexibility.Analysis.hasDerivAt_endpointX`](../ContinuousFlexibility/Analysis/MaterialCoordinate.lean#L64)
- [`ContinuousFlexibility.Analysis.contDiffAt_endpointX`](../ContinuousFlexibility/Analysis/MaterialCoordinate.lean#L71)
- [`ContinuousFlexibility.Analysis.endpointMaterialDerivative_X`](../ContinuousFlexibility/Analysis/MaterialCoordinate.lean#L77)
- [`ContinuousFlexibility.Analysis.hasDerivAt_log_materialH_endpointX`](../ContinuousFlexibility/Analysis/MaterialCoordinate.lean#L86)
- [`ContinuousFlexibility.Analysis.endpointMaterialDerivative_logH`](../ContinuousFlexibility/Analysis/MaterialCoordinate.lean#L101)
- [`ContinuousFlexibility.Analysis.endpointMaterialDerivative_logH_bounds`](../ContinuousFlexibility/Analysis/MaterialCoordinate.lean#L109)
- [`ContinuousFlexibility.Analysis.hasDerivAt_endpointRho`](../ContinuousFlexibility/Analysis/MaterialCoordinate.lean#L118)
- [`ContinuousFlexibility.Analysis.hasDerivAt_endpointRhoOfDistance`](../ContinuousFlexibility/Analysis/MaterialCoordinate.lean#L127)
- [`ContinuousFlexibility.Analysis.tendsto_endpointX_atTop`](../ContinuousFlexibility/Analysis/MaterialCoordinate.lean#L137)
- [`ContinuousFlexibility.Analysis.tendsto_endpointRho_atBot`](../ContinuousFlexibility/Analysis/MaterialCoordinate.lean#L144)
- [`ContinuousFlexibility.Analysis.tendsto_endpointRhoOfDistance_atBot`](../ContinuousFlexibility/Analysis/MaterialCoordinate.lean#L153)
- [`ContinuousFlexibility.Analysis.endpointDistance_pos`](../ContinuousFlexibility/Analysis/MaterialCoordinate.lean#L157)
- [`ContinuousFlexibility.Analysis.endpointX_endpointDistance`](../ContinuousFlexibility/Analysis/MaterialCoordinate.lean#L160)
- [`ContinuousFlexibility.Analysis.endpointDistance_endpointX`](../ContinuousFlexibility/Analysis/MaterialCoordinate.lean#L171)
- [`ContinuousFlexibility.Analysis.hasDerivAt_endpointDistance`](../ContinuousFlexibility/Analysis/MaterialCoordinate.lean#L180)
- [`ContinuousFlexibility.Analysis.endpointDistance_lt`](../ContinuousFlexibility/Analysis/MaterialCoordinate.lean#L188)
- [`ContinuousFlexibility.Analysis.endpointMaterialDerivative_rho`](../ContinuousFlexibility/Analysis/MaterialCoordinate.lean#L194)
- [`ContinuousFlexibility.Analysis.tendsto_endpoint_H_rpow_M_rpow_zero`](../ContinuousFlexibility/Analysis/MaterialCoordinate.lean#L203)
- [`ContinuousFlexibility.Analysis.tendsto_endpoint_H_rpow_E0_rpow_zero`](../ContinuousFlexibility/Analysis/MaterialCoordinate.lean#L209)

[MaterialWeights.lean](../ContinuousFlexibility/Analysis/MaterialWeights.lean)：

- [`ContinuousFlexibility.Analysis.materialH_pos`](../ContinuousFlexibility/Analysis/MaterialWeights.lean#L38)
- [`ContinuousFlexibility.Analysis.materialE0_pos`](../ContinuousFlexibility/Analysis/MaterialWeights.lean#L40)
- [`ContinuousFlexibility.Analysis.materialM_pos`](../ContinuousFlexibility/Analysis/MaterialWeights.lean#L42)
- [`ContinuousFlexibility.Analysis.continuous_materialH`](../ContinuousFlexibility/Analysis/MaterialWeights.lean#L44)
- [`ContinuousFlexibility.Analysis.continuousOn_materialLogFactor`](../ContinuousFlexibility/Analysis/MaterialWeights.lean#L49)
- [`ContinuousFlexibility.Analysis.continuousOn_materialE0Exponent`](../ContinuousFlexibility/Analysis/MaterialWeights.lean#L53)
- [`ContinuousFlexibility.Analysis.continuousOn_materialMExponent`](../ContinuousFlexibility/Analysis/MaterialWeights.lean#L58)
- [`ContinuousFlexibility.Analysis.continuousOn_materialE0`](../ContinuousFlexibility/Analysis/MaterialWeights.lean#L63)
- [`ContinuousFlexibility.Analysis.continuousOn_materialM`](../ContinuousFlexibility/Analysis/MaterialWeights.lean#L66)
- [`ContinuousFlexibility.Analysis.tendsto_materialLogFactor_atTop`](../ContinuousFlexibility/Analysis/MaterialWeights.lean#L76)
- [`ContinuousFlexibility.Analysis.tendsto_materialLogFactor_sq_div_rpow`](../ContinuousFlexibility/Analysis/MaterialWeights.lean#L92)
- [`ContinuousFlexibility.Analysis.tendsto_materialM_term_div_cube`](../ContinuousFlexibility/Analysis/MaterialWeights.lean#L114)
- [`ContinuousFlexibility.Analysis.materialE0_rpow_div_materialM`](../ContinuousFlexibility/Analysis/MaterialWeights.lean#L139)
- [`ContinuousFlexibility.Analysis.materialE0_rpow_le_materialM`](../ContinuousFlexibility/Analysis/MaterialWeights.lean#L148)
- [`ContinuousFlexibility.Analysis.materialH_rpow_mul_materialM_rpow`](../ContinuousFlexibility/Analysis/MaterialWeights.lean#L169)
- [`ContinuousFlexibility.Analysis.materialH_rpow_mul_materialM_rpow_le`](../ContinuousFlexibility/Analysis/MaterialWeights.lean#L178)
- [`ContinuousFlexibility.Analysis.tendsto_materialH_zero`](../ContinuousFlexibility/Analysis/MaterialWeights.lean#L202)
- [`ContinuousFlexibility.Analysis.tendsto_materialH_rpow_mul_materialM_rpow_zero`](../ContinuousFlexibility/Analysis/MaterialWeights.lean#L214)
- [`ContinuousFlexibility.Analysis.materialH_rpow_mul_materialE0_rpow_le`](../ContinuousFlexibility/Analysis/MaterialWeights.lean#L234)
- [`ContinuousFlexibility.Analysis.tendsto_materialH_rpow_mul_materialE0_rpow_zero`](../ContinuousFlexibility/Analysis/MaterialWeights.lean#L247)

[MaterialInterval.lean](../ContinuousFlexibility/Analysis/MaterialInterval.lean)：

- [`ContinuousFlexibility.Analysis.contDiff_materialIntervalTransition`](../ContinuousFlexibility/Analysis/MaterialInterval.lean#L40)
- [`ContinuousFlexibility.Analysis.materialIntervalTransition_nonneg`](../ContinuousFlexibility/Analysis/MaterialInterval.lean#L43)
- [`ContinuousFlexibility.Analysis.materialIntervalTransition_le_one`](../ContinuousFlexibility/Analysis/MaterialInterval.lean#L46)
- [`ContinuousFlexibility.Analysis.materialIntervalTransition_eq_zero`](../ContinuousFlexibility/Analysis/MaterialInterval.lean#L49)
- [`ContinuousFlexibility.Analysis.materialIntervalTransition_eq_one`](../ContinuousFlexibility/Analysis/MaterialInterval.lean#L53)
- [`ContinuousFlexibility.Analysis.materialIntervalXL_pos`](../ContinuousFlexibility/Analysis/MaterialInterval.lean#L57)
- [`ContinuousFlexibility.Analysis.materialIntervalXR_pos`](../ContinuousFlexibility/Analysis/MaterialInterval.lean#L60)
- [`ContinuousFlexibility.Analysis.contDiffAt_materialIntervalXL`](../ContinuousFlexibility/Analysis/MaterialInterval.lean#L63)
- [`ContinuousFlexibility.Analysis.contDiffAt_materialIntervalXR`](../ContinuousFlexibility/Analysis/MaterialInterval.lean#L66)
- [`ContinuousFlexibility.Analysis.materialIntervalEll_pos`](../ContinuousFlexibility/Analysis/MaterialInterval.lean#L71)
- [`ContinuousFlexibility.Analysis.materialIntervalEll_eq_left`](../ContinuousFlexibility/Analysis/MaterialInterval.lean#L80)
- [`ContinuousFlexibility.Analysis.materialIntervalEll_eq_right`](../ContinuousFlexibility/Analysis/MaterialInterval.lean#L84)
- [`ContinuousFlexibility.Analysis.contDiffAt_materialIntervalEll`](../ContinuousFlexibility/Analysis/MaterialInterval.lean#L88)
- [`ContinuousFlexibility.Analysis.contDiffOn_materialIntervalEll`](../ContinuousFlexibility/Analysis/MaterialInterval.lean#L101)
- [`ContinuousFlexibility.Analysis.materialIntervalDensity_pos`](../ContinuousFlexibility/Analysis/MaterialInterval.lean#L104)
- [`ContinuousFlexibility.Analysis.contDiffAt_materialIntervalDensity`](../ContinuousFlexibility/Analysis/MaterialInterval.lean#L107)
- [`ContinuousFlexibility.Analysis.contDiffOn_materialIntervalDensity`](../ContinuousFlexibility/Analysis/MaterialInterval.lean#L111)
- [`ContinuousFlexibility.Analysis.intervalIntegrable_materialIntervalDensity`](../ContinuousFlexibility/Analysis/MaterialInterval.lean#L115)
- [`ContinuousFlexibility.Analysis.hasDerivAt_materialIntervalRho`](../ContinuousFlexibility/Analysis/MaterialInterval.lean#L121)
- [`ContinuousFlexibility.Analysis.contDiffOn_materialIntervalRho`](../ContinuousFlexibility/Analysis/MaterialInterval.lean#L128)
- [`ContinuousFlexibility.Analysis.contDiffAt_materialIntervalRho`](../ContinuousFlexibility/Analysis/MaterialInterval.lean#L133)
- [`ContinuousFlexibility.Analysis.materialIntervalRho_deriv_pos`](../ContinuousFlexibility/Analysis/MaterialInterval.lean#L137)
- [`ContinuousFlexibility.Analysis.strictMonoOn_materialIntervalRho`](../ContinuousFlexibility/Analysis/MaterialInterval.lean#L142)
- [`ContinuousFlexibility.Analysis.materialIntervalRho_half`](../ContinuousFlexibility/Analysis/MaterialInterval.lean#L147)
- [`ContinuousFlexibility.Analysis.exists_materialIntervalRho_eq_left`](../ContinuousFlexibility/Analysis/MaterialInterval.lean#L150)
- [`ContinuousFlexibility.Analysis.hasDerivAt_reflectedEndpointRho`](../ContinuousFlexibility/Analysis/MaterialInterval.lean#L164)
- [`ContinuousFlexibility.Analysis.exists_materialIntervalRho_eq_right`](../ContinuousFlexibility/Analysis/MaterialInterval.lean#L177)
- [`ContinuousFlexibility.Analysis.tendsto_reflectedDistance_zero`](../ContinuousFlexibility/Analysis/MaterialInterval.lean#L190)
- [`ContinuousFlexibility.Analysis.tendsto_materialIntervalRho_left`](../ContinuousFlexibility/Analysis/MaterialInterval.lean#L199)
- [`ContinuousFlexibility.Analysis.tendsto_materialIntervalRho_right`](../ContinuousFlexibility/Analysis/MaterialInterval.lean#L210)
- [`ContinuousFlexibility.Analysis.surjOn_materialIntervalRho`](../ContinuousFlexibility/Analysis/MaterialInterval.lean#L223)
- [`ContinuousFlexibility.Analysis.bijective_materialIntervalRho`](../ContinuousFlexibility/Analysis/MaterialInterval.lean#L240)
- [`ContinuousFlexibility.Analysis.materialIntervalInverse_mem`](../ContinuousFlexibility/Analysis/MaterialInterval.lean#L257)
- [`ContinuousFlexibility.Analysis.materialIntervalRho_inverse`](../ContinuousFlexibility/Analysis/MaterialInterval.lean#L260)
- [`ContinuousFlexibility.Analysis.materialIntervalInverse_rho`](../ContinuousFlexibility/Analysis/MaterialInterval.lean#L263)
- [`ContinuousFlexibility.Analysis.hasStrictDerivAt_materialIntervalInverse_rho`](../ContinuousFlexibility/Analysis/MaterialInterval.lean#L272)
- [`ContinuousFlexibility.Analysis.contDiffAt_materialIntervalInverse_rho`](../ContinuousFlexibility/Analysis/MaterialInterval.lean#L279)
- [`ContinuousFlexibility.Analysis.contDiff_materialIntervalInverse`](../ContinuousFlexibility/Analysis/MaterialInterval.lean#L296)
- [`ContinuousFlexibility.Analysis.hasDerivAt_materialIntervalInverse`](../ContinuousFlexibility/Analysis/MaterialInterval.lean#L302)

[MaterialIntervalWeights.lean](../ContinuousFlexibility/Analysis/MaterialIntervalWeights.lean)：

- [`ContinuousFlexibility.Analysis.materialIntervalH_pos`](../ContinuousFlexibility/Analysis/MaterialIntervalWeights.lean#L43)
- [`ContinuousFlexibility.Analysis.materialIntervalE0_pos`](../ContinuousFlexibility/Analysis/MaterialIntervalWeights.lean#L45)
- [`ContinuousFlexibility.Analysis.materialIntervalM_pos`](../ContinuousFlexibility/Analysis/MaterialIntervalWeights.lean#L47)
- [`ContinuousFlexibility.Analysis.materialIntervalLogBlend_eq_left`](../ContinuousFlexibility/Analysis/MaterialIntervalWeights.lean#L49)
- [`ContinuousFlexibility.Analysis.materialIntervalLogBlend_eq_right`](../ContinuousFlexibility/Analysis/MaterialIntervalWeights.lean#L53)
- [`ContinuousFlexibility.Analysis.materialIntervalH_eq_left`](../ContinuousFlexibility/Analysis/MaterialIntervalWeights.lean#L57)
- [`ContinuousFlexibility.Analysis.materialIntervalH_eq_right`](../ContinuousFlexibility/Analysis/MaterialIntervalWeights.lean#L62)
- [`ContinuousFlexibility.Analysis.materialIntervalE0_eq_left`](../ContinuousFlexibility/Analysis/MaterialIntervalWeights.lean#L67)
- [`ContinuousFlexibility.Analysis.materialIntervalE0_eq_right`](../ContinuousFlexibility/Analysis/MaterialIntervalWeights.lean#L72)
- [`ContinuousFlexibility.Analysis.materialIntervalM_eq_left`](../ContinuousFlexibility/Analysis/MaterialIntervalWeights.lean#L77)
- [`ContinuousFlexibility.Analysis.materialIntervalM_eq_right`](../ContinuousFlexibility/Analysis/MaterialIntervalWeights.lean#L82)
- [`ContinuousFlexibility.Analysis.contDiffAt_materialIntervalLogBlend`](../ContinuousFlexibility/Analysis/MaterialIntervalWeights.lean#L87)
- [`ContinuousFlexibility.Analysis.contDiff_log_materialH`](../ContinuousFlexibility/Analysis/MaterialIntervalWeights.lean#L96)
- [`ContinuousFlexibility.Analysis.contDiffAt_log_materialE0`](../ContinuousFlexibility/Analysis/MaterialIntervalWeights.lean#L103)
- [`ContinuousFlexibility.Analysis.contDiffAt_log_materialM`](../ContinuousFlexibility/Analysis/MaterialIntervalWeights.lean#L113)
- [`ContinuousFlexibility.Analysis.contDiffAt_materialIntervalH`](../ContinuousFlexibility/Analysis/MaterialIntervalWeights.lean#L123)
- [`ContinuousFlexibility.Analysis.contDiffAt_materialIntervalE0`](../ContinuousFlexibility/Analysis/MaterialIntervalWeights.lean#L128)
- [`ContinuousFlexibility.Analysis.contDiffAt_materialIntervalM`](../ContinuousFlexibility/Analysis/MaterialIntervalWeights.lean#L133)
- [`ContinuousFlexibility.Analysis.contDiffOn_materialIntervalH`](../ContinuousFlexibility/Analysis/MaterialIntervalWeights.lean#L138)
- [`ContinuousFlexibility.Analysis.contDiffOn_materialIntervalE0`](../ContinuousFlexibility/Analysis/MaterialIntervalWeights.lean#L141)
- [`ContinuousFlexibility.Analysis.contDiffOn_materialIntervalM`](../ContinuousFlexibility/Analysis/MaterialIntervalWeights.lean#L144)
- [`ContinuousFlexibility.Analysis.materialIntervalLogBlend_le`](../ContinuousFlexibility/Analysis/MaterialIntervalWeights.lean#L149)
- [`ContinuousFlexibility.Analysis.materialIntervalE0_rpow_le_M`](../ContinuousFlexibility/Analysis/MaterialIntervalWeights.lean#L161)
- [`ContinuousFlexibility.Analysis.materialIntervalH_rpow_mul_M_rpow_le`](../ContinuousFlexibility/Analysis/MaterialIntervalWeights.lean#L209)
- [`ContinuousFlexibility.Analysis.materialIntervalH_rpow_mul_E0_rpow_le`](../ContinuousFlexibility/Analysis/MaterialIntervalWeights.lean#L214)
- [`ContinuousFlexibility.Analysis.tendsto_materialIntervalH_rpow_mul_M_left`](../ContinuousFlexibility/Analysis/MaterialIntervalWeights.lean#L247)
- [`ContinuousFlexibility.Analysis.tendsto_materialIntervalH_rpow_mul_M_right`](../ContinuousFlexibility/Analysis/MaterialIntervalWeights.lean#L255)
- [`ContinuousFlexibility.Analysis.tendsto_materialIntervalH_rpow_mul_E0_left`](../ContinuousFlexibility/Analysis/MaterialIntervalWeights.lean#L264)
- [`ContinuousFlexibility.Analysis.tendsto_materialIntervalH_rpow_mul_E0_right`](../ContinuousFlexibility/Analysis/MaterialIntervalWeights.lean#L272)
- [`ContinuousFlexibility.Analysis.tendsto_materialIntervalH_left`](../ContinuousFlexibility/Analysis/MaterialIntervalWeights.lean#L281)
- [`ContinuousFlexibility.Analysis.tendsto_materialIntervalH_right`](../ContinuousFlexibility/Analysis/MaterialIntervalWeights.lean#L284)

[AffineMaterialData.lean](../ContinuousFlexibility/Analysis/AffineMaterialData.lean)：

- [`ContinuousFlexibility.Statements.affineMaterialUnitCoordinate_mem`](../ContinuousFlexibility/Analysis/AffineMaterialData.lean#L38)
- [`ContinuousFlexibility.Statements.affineMaterialData_smooth_scalar`](../ContinuousFlexibility/Analysis/AffineMaterialData.lean#L85)
- [`ContinuousFlexibility.Statements.affineMaterialData_positive`](../ContinuousFlexibility/Analysis/AffineMaterialData.lean#L116)
- [`ContinuousFlexibility.Statements.hasDerivAt_affineMaterialData_rho`](../ContinuousFlexibility/Analysis/AffineMaterialData.lean#L122)
- [`ContinuousFlexibility.Statements.strictMonoOn_affineMaterialData_rho`](../ContinuousFlexibility/Analysis/AffineMaterialData.lean#L130)
- [`ContinuousFlexibility.Statements.tendsto_affineMaterialData_rho_left`](../ContinuousFlexibility/Analysis/AffineMaterialData.lean#L135)
- [`ContinuousFlexibility.Statements.tendsto_affineMaterialData_rho_right`](../ContinuousFlexibility/Analysis/AffineMaterialData.lean#L139)
- [`ContinuousFlexibility.Statements.contDiff_affineMaterialData_radius`](../ContinuousFlexibility/Analysis/AffineMaterialData.lean#L143)
- [`ContinuousFlexibility.Statements.affineMaterialUnitCoordinate_radius`](../ContinuousFlexibility/Analysis/AffineMaterialData.lean#L147)
- [`ContinuousFlexibility.Statements.affineMaterialData_radius_mem_rho`](../ContinuousFlexibility/Analysis/AffineMaterialData.lean#L153)
- [`ContinuousFlexibility.Statements.affineMaterialData_radius_rho`](../ContinuousFlexibility/Analysis/AffineMaterialData.lean#L167)
- [`ContinuousFlexibility.Statements.hasDerivAt_affineMaterialData_radius`](../ContinuousFlexibility/Analysis/AffineMaterialData.lean#L175)
- [`ContinuousFlexibility.Statements.affineMaterialData_endpoint_formulas`](../ContinuousFlexibility/Analysis/AffineMaterialData.lean#L185)
- [`ContinuousFlexibility.Statements.affineMaterialData_E0_rpow_le_M`](../ContinuousFlexibility/Analysis/AffineMaterialData.lean#L247)
- [`ContinuousFlexibility.Statements.affineMaterialData_H_rpow_mul_M_rpow`](../ContinuousFlexibility/Analysis/AffineMaterialData.lean#L253)

[MaterialShiftedEnvelope.lean](../ContinuousFlexibility/Analysis/MaterialShiftedEnvelope.lean)：

- [`ContinuousFlexibility.Analysis.material_shifted_envelope`](../ContinuousFlexibility/Analysis/MaterialShiftedEnvelope.lean#L15)
- [`ContinuousFlexibility.Analysis.material_bounded_shift_envelope`](../ContinuousFlexibility/Analysis/MaterialShiftedEnvelope.lean#L39)

[MaterialLogJets.lean](../ContinuousFlexibility/Analysis/MaterialLogJets.lean)：

- [`ContinuousFlexibility.Statements.materialEndpointLogDerivative_iterate_symbol`](../ContinuousFlexibility/Analysis/MaterialLogJets.lean#L124)
- [`ContinuousFlexibility.Statements.logarithmicDerivativeBounds_affineMaterialData`](../ContinuousFlexibility/Analysis/MaterialLogJets.lean#L342)

[AffineMaterialFull.lean](../ContinuousFlexibility/Analysis/AffineMaterialFull.lean)：

- [`ContinuousFlexibility.Statements.affineMaterial_W01_statement`](../ContinuousFlexibility/Analysis/AffineMaterialFull.lean#L15)

[AffineMaterialSampling.lean](../ContinuousFlexibility/Analysis/AffineMaterialSampling.lean)：

- [`ContinuousFlexibility.Statements.affineMaterialData_cell_log_bounds`](../ContinuousFlexibility/Analysis/AffineMaterialSampling.lean#L254)
- [`ContinuousFlexibility.Statements.exists_affineMaterialData_sampling`](../ContinuousFlexibility/Analysis/AffineMaterialSampling.lean#L314)

[MaterialRadialExpansion.lean](../ContinuousFlexibility/Analysis/MaterialRadialExpansion.lean)：

- [`ContinuousFlexibility.Statements.iteratedDeriv_comp_affineMaterialRadius`](../ContinuousFlexibility/Analysis/MaterialRadialExpansion.lean#L228)
- [`ContinuousFlexibility.Statements.affineMaterialData_inv_ell_le_E0_sq`](../ContinuousFlexibility/Analysis/MaterialRadialExpansion.lean#L295)
- [`ContinuousFlexibility.Statements.radialMaterialExpansion_affineMaterialData`](../ContinuousFlexibility/Analysis/MaterialRadialExpansion.lean#L341)


<a id="h01"></a>
## H01 分次空间、方向微分与tame基础

**状态：** 已有部分已编译子结果。**分支：** 分析基础与加权空间。主定理必要节点。

**数学陈述：** 建立真实graded Fréchet或兼容Banach-scale定义、方向微分、smooth tame、固定导数损失、smoothing/retraction及线性/双线性/复合/积分/直和/投影的闭合定理。

**证明提纲：** 适配本地WithSeminorms等基础；选择Hamilton式方向微积分或明确scale实现，并证明与具体函数/参数微分的对应。

**直接依赖：** 无其他蓝图节点

**论文定位：** [07-fixed-geometry.tex:102–150](../paper/flexible-surface-rewrite/07-fixed-geometry.tex#L102)，`prop:full-physical-tame`

**目标文件：** `ContinuousFlexibility/Analysis/H01.lean`（节点组织目标；实际已存在的证明文件见下方，整个节点尚未完成）

**验收条件：**

- 不得把任意谓词命名SmoothTame后视为理论
- smoothing和插值必须有实际算子与估计
- H02/H03的定理接口必须与此定义完全一致

**已经完成的子结果：**

- 真实projective拓扑中的曲线差商、变量连续多线性乘积规则、全阶jet沿曲线求导及真实一阶/二阶复合方向导数已编译；未在projective源上虚构NormedSpace，Schwarz和全阶复合族仍在后续源码。
- 实际 projective 拓扑的曲线差商、全阶 jet 沿曲线规则、连续线性/多线性的前两阶复合及二阶 Schwarz 对称已验证。

**仍待闭合的义务：**

- 全阶对称与复合 jet 族。
- 物理加权 Sobolev 空间上的完整高阶 tame 估计。

**优先核查程度：** critical（任务风险标记，不是已发现错误）

**现有 Lean 证明：**

[Graded.lean](../ContinuousFlexibility/Analysis/Graded.lean)：

- [`ContinuousFlexibility.Analysis.mem_compatibleSubmodule`](../ContinuousFlexibility/Analysis/Graded.lean#L53)
- [`ContinuousFlexibility.Analysis.isClosed_compatibleSubmodule`](../ContinuousFlexibility/Analysis/Graded.lean#L56)
- [`ContinuousFlexibility.Analysis.projectiveCoordinate_apply`](../ContinuousFlexibility/Analysis/Graded.lean#L86)
- [`ContinuousFlexibility.Analysis.projectiveCoordinate_bond`](../ContinuousFlexibility/Analysis/Graded.lean#L89)
- [`ContinuousFlexibility.Analysis.tendsto_projectiveLimit_iff`](../ContinuousFlexibility/Analysis/Graded.lean#L96)
- [`ContinuousFlexibility.Analysis.projectiveLift_apply`](../ContinuousFlexibility/Analysis/Graded.lean#L111)
- [`ContinuousFlexibility.Analysis.projectiveLift_unique`](../ContinuousFlexibility/Analysis/Graded.lean#L116)
- [`ContinuousFlexibility.Analysis.withSeminorms_productCoordinate`](../ContinuousFlexibility/Analysis/Graded.lean#L131)
- [`ContinuousFlexibility.Analysis.coordinateSeminorm_apply`](../ContinuousFlexibility/Analysis/Graded.lean#L144)
- [`ContinuousFlexibility.Analysis.withSeminorms_coordinate`](../ContinuousFlexibility/Analysis/Graded.lean#L147)
- [`ContinuousFlexibility.Analysis.withSeminorms_graded`](../ContinuousFlexibility/Analysis/Graded.lean#L155)
- [`ContinuousFlexibility.Analysis.gradedSeminorm_monotone`](../ContinuousFlexibility/Analysis/Graded.lean#L158)
- [`ContinuousFlexibility.Analysis.norm_coordinate_le_graded`](../ContinuousFlexibility/Analysis/Graded.lean#L164)
- [`ContinuousFlexibility.Analysis.gradedSeminorm_le_iff`](../ContinuousFlexibility/Analysis/Graded.lean#L169)
- [`ContinuousFlexibility.Analysis.gradedSeminorm_exists_norm`](../ContinuousFlexibility/Analysis/Graded.lean#L177)
- [`ContinuousFlexibility.Analysis.continuous_gradedSeminorm`](../ContinuousFlexibility/Analysis/Graded.lean#L183)
- [`ContinuousFlexibility.Analysis.gradedSeminorms_separate`](../ContinuousFlexibility/Analysis/Graded.lean#L188)

[TameLinear.lean](../ContinuousFlexibility/Analysis/TameLinear.lean)：

- [`ContinuousFlexibility.Analysis.IsTameLinear.weaken`](../ContinuousFlexibility/Analysis/TameLinear.lean#L41)
- [`ContinuousFlexibility.Analysis.IsTameLinear.id`](../ContinuousFlexibility/Analysis/TameLinear.lean#L48)
- [`ContinuousFlexibility.Analysis.IsTameLinear.zero`](../ContinuousFlexibility/Analysis/TameLinear.lean#L52)
- [`ContinuousFlexibility.Analysis.IsTameLinear.smul`](../ContinuousFlexibility/Analysis/TameLinear.lean#L57)
- [`ContinuousFlexibility.Analysis.IsTameLinear.neg`](../ContinuousFlexibility/Analysis/TameLinear.lean#L69)
- [`ContinuousFlexibility.Analysis.IsTameLinear.add`](../ContinuousFlexibility/Analysis/TameLinear.lean#L72)
- [`ContinuousFlexibility.Analysis.IsTameLinear.sub`](../ContinuousFlexibility/Analysis/TameLinear.lean#L88)
- [`ContinuousFlexibility.Analysis.IsTameLinear.comp`](../ContinuousFlexibility/Analysis/TameLinear.lean#L95)
- [`ContinuousFlexibility.Analysis.IsTameLinear.sum`](../ContinuousFlexibility/Analysis/TameLinear.lean#L110)
- [`ContinuousFlexibility.Analysis.IsTameLinear.isBounded`](../ContinuousFlexibility/Analysis/TameLinear.lean#L123)
- [`ContinuousFlexibility.Analysis.IsTameLinear.continuous`](../ContinuousFlexibility/Analysis/TameLinear.lean#L132)
- [`ContinuousFlexibility.Analysis.IsTameLinear.toContinuousLinearMap_apply`](../ContinuousFlexibility/Analysis/TameLinear.lean#L145)

[TameLinear.lean](../ContinuousFlexibility/Analysis/TameLinear.lean)：

- [`ContinuousFlexibility.Analysis.finiteProductGrading_monotone`](../ContinuousFlexibility/Analysis/TameLinear.lean#L162)
- [`ContinuousFlexibility.Analysis.withSeminorms_finiteProduct`](../ContinuousFlexibility/Analysis/TameLinear.lean#L170)
- [`ContinuousFlexibility.Analysis.IsTameLinear.pi`](../ContinuousFlexibility/Analysis/TameLinear.lean#L187)
- [`ContinuousFlexibility.Analysis.finiteProductProjection_isTame`](../ContinuousFlexibility/Analysis/TameLinear.lean#L214)
- [`ContinuousFlexibility.Analysis.IsTameLinear.piMap`](../ContinuousFlexibility/Analysis/TameLinear.lean#L225)
- [`ContinuousFlexibility.Analysis.continuous_projectiveLimit_of_tame`](../ContinuousFlexibility/Analysis/TameLinear.lean#L250)
- [`ContinuousFlexibility.Analysis.projectiveCoordinate_isTame`](../ContinuousFlexibility/Analysis/TameLinear.lean#L258)

[BastianiCurveChain.lean](../ContinuousFlexibility/Analysis/BastianiCurveChain.lean)：

- [`ContinuousFlexibility.Analysis.hasDerivAt_affineLine_of_hasLineDerivAt`](../ContinuousFlexibility/Analysis/BastianiCurveChain.lean#L40)
- [`ContinuousFlexibility.Analysis.continuousOn_bastiani_segment`](../ContinuousFlexibility/Analysis/BastianiCurveChain.lean#L49)
- [`ContinuousFlexibility.Analysis.bastiani_segment_integral`](../ContinuousFlexibility/Analysis/BastianiCurveChain.lean#L61)
- [`ContinuousFlexibility.Analysis.bastiani_segment_scaled_integral`](../ContinuousFlexibility/Analysis/BastianiCurveChain.lean#L80)
- [`ContinuousFlexibility.Analysis.eventually_uniform_bastiani_segment`](../ContinuousFlexibility/Analysis/BastianiCurveChain.lean#L95)
- [`ContinuousFlexibility.Analysis.hasDerivAt_bastiani_comp_curve`](../ContinuousFlexibility/Analysis/BastianiCurveChain.lean#L117)
- [`ContinuousFlexibility.Analysis.hasDerivAt_bastiani_comp_projective_curve`](../ContinuousFlexibility/Analysis/BastianiCurveChain.lean#L176)
- [`ContinuousFlexibility.Analysis.HasProjectiveCurveDerivAt.bastiani_comp`](../ContinuousFlexibility/Analysis/BastianiCurveChain.lean#L195)
- [`ContinuousFlexibility.Analysis.HasProjectiveLineDerivAt.bastiani_comp`](../ContinuousFlexibility/Analysis/BastianiCurveChain.lean#L220)

[ExponentialSequenceSpace.lean](../ContinuousFlexibility/Analysis/ExponentialSequenceSpace.lean)：

- [`ContinuousFlexibility.Analysis.sequenceDiagonal_apply`](../ContinuousFlexibility/Analysis/ExponentialSequenceSpace.lean#L61)
- [`ContinuousFlexibility.Analysis.sequenceDiagonal_norm_le`](../ContinuousFlexibility/Analysis/ExponentialSequenceSpace.lean#L65)
- [`ContinuousFlexibility.Analysis.exponentialSequenceBond_apply`](../ContinuousFlexibility/Analysis/ExponentialSequenceSpace.lean#L82)
- [`ContinuousFlexibility.Analysis.isClosed_exponentialSequenceSpace`](../ContinuousFlexibility/Analysis/ExponentialSequenceSpace.lean#L90)
- [`ContinuousFlexibility.Analysis.exponentialSequence_complete`](../ContinuousFlexibility/Analysis/ExponentialSequenceSpace.lean#L95)
- [`ContinuousFlexibility.Analysis.exponentialSequence_locallyConvex`](../ContinuousFlexibility/Analysis/ExponentialSequenceSpace.lean#L98)
- [`ContinuousFlexibility.Analysis.exponentialSequence_metrizable`](../ContinuousFlexibility/Analysis/ExponentialSequenceSpace.lean#L101)
- [`ContinuousFlexibility.Analysis.exponentialSequence_completelyMetrizable`](../ContinuousFlexibility/Analysis/ExponentialSequenceSpace.lean#L104)
- [`ContinuousFlexibility.Analysis.exponentialSequenceSeminorm_apply`](../ContinuousFlexibility/Analysis/ExponentialSequenceSpace.lean#L114)
- [`ContinuousFlexibility.Analysis.withSeminorms_exponentialSequence`](../ContinuousFlexibility/Analysis/ExponentialSequenceSpace.lean#L117)
- [`ContinuousFlexibility.Analysis.exponentialSequenceSeminorm_monotone`](../ContinuousFlexibility/Analysis/ExponentialSequenceSpace.lean#L120)
- [`ContinuousFlexibility.Analysis.exponentialSequence_level_eq_weighted_raw`](../ContinuousFlexibility/Analysis/ExponentialSequenceSpace.lean#L129)
- [`ContinuousFlexibility.Analysis.exponentialSequence_weighted_memℓp`](../ContinuousFlexibility/Analysis/ExponentialSequenceSpace.lean#L146)
- [`ContinuousFlexibility.Analysis.exponentialSequenceRaw_ofRaw`](../ContinuousFlexibility/Analysis/ExponentialSequenceSpace.lean#L169)
- [`ContinuousFlexibility.Analysis.exponentialSequenceRaw_injective`](../ContinuousFlexibility/Analysis/ExponentialSequenceSpace.lean#L175)
- [`ContinuousFlexibility.Analysis.exponentialSequenceOfRaw_raw`](../ContinuousFlexibility/Analysis/ExponentialSequenceSpace.lean#L183)
- [`ContinuousFlexibility.Analysis.exponentialSequence_level_relation`](../ContinuousFlexibility/Analysis/ExponentialSequenceSpace.lean#L191)
- [`ContinuousFlexibility.Analysis.exponentialSequenceCutLevel_apply`](../ContinuousFlexibility/Analysis/ExponentialSequenceSpace.lean#L203)
- [`ContinuousFlexibility.Analysis.exponentialSequenceSmoothing_apply`](../ContinuousFlexibility/Analysis/ExponentialSequenceSpace.lean#L229)
- [`ContinuousFlexibility.Analysis.exponentialSequenceSmoothing_raw`](../ContinuousFlexibility/Analysis/ExponentialSequenceSpace.lean#L234)
- [`ContinuousFlexibility.Analysis.exponentialSequenceSmoothing_support`](../ContinuousFlexibility/Analysis/ExponentialSequenceSpace.lean#L240)
- [`ContinuousFlexibility.Analysis.exponentialSequenceSmoothing_finite_support`](../ContinuousFlexibility/Analysis/ExponentialSequenceSpace.lean#L247)
- [`ContinuousFlexibility.Analysis.exponentialSequenceSmoothing_idempotent`](../ContinuousFlexibility/Analysis/ExponentialSequenceSpace.lean#L251)
- [`ContinuousFlexibility.Analysis.exponentialSequenceSmoothing_forward`](../ContinuousFlexibility/Analysis/ExponentialSequenceSpace.lean#L261)
- [`ContinuousFlexibility.Analysis.exponentialSequenceSmoothing_tail`](../ContinuousFlexibility/Analysis/ExponentialSequenceSpace.lean#L280)
- [`ContinuousFlexibility.Analysis.tendsto_exponentialSequenceSmoothing`](../ContinuousFlexibility/Analysis/ExponentialSequenceSpace.lean#L305)
- [`ContinuousFlexibility.Analysis.exponentialDecayL2_apply`](../ContinuousFlexibility/Analysis/ExponentialSequenceSpace.lean#L343)
- [`ContinuousFlexibility.Analysis.one_le_exponentialL2ComparisonConstant`](../ContinuousFlexibility/Analysis/ExponentialSequenceSpace.lean#L349)
- [`ContinuousFlexibility.Analysis.exponentialSequence_level_memℓp_two`](../ContinuousFlexibility/Analysis/ExponentialSequenceSpace.lean#L354)
- [`ContinuousFlexibility.Analysis.exponentialSequenceL2Level_apply`](../ContinuousFlexibility/Analysis/ExponentialSequenceSpace.lean#L372)
- [`ContinuousFlexibility.Analysis.exponentialSequenceSeminorm_le_l2`](../ContinuousFlexibility/Analysis/ExponentialSequenceSpace.lean#L376)
- [`ContinuousFlexibility.Analysis.exponentialSequenceL2Level_norm_le`](../ContinuousFlexibility/Analysis/ExponentialSequenceSpace.lean#L384)
- [`ContinuousFlexibility.Analysis.all_exponential_memℓp_infty_iff_two`](../ContinuousFlexibility/Analysis/ExponentialSequenceSpace.lean#L408)

[ProjectiveDifferential.lean](../ContinuousFlexibility/Analysis/ProjectiveDifferential.lean)：

- [`ContinuousFlexibility.Analysis.HasProjectiveCurveDerivAt.unique`](../ContinuousFlexibility/Analysis/ProjectiveDifferential.lean#L44)
- [`ContinuousFlexibility.Analysis.HasProjectiveLineDerivAt.unique`](../ContinuousFlexibility/Analysis/ProjectiveDifferential.lean#L48)
- [`ContinuousFlexibility.Analysis.hasProjectiveCurveDerivAt_const`](../ContinuousFlexibility/Analysis/ProjectiveDifferential.lean#L53)
- [`ContinuousFlexibility.Analysis.hasProjectiveLineDerivAt_const`](../ContinuousFlexibility/Analysis/ProjectiveDifferential.lean#L59)
- [`ContinuousFlexibility.Analysis.hasProjectiveLineDerivAt_zero_direction`](../ContinuousFlexibility/Analysis/ProjectiveDifferential.lean#L63)
- [`ContinuousFlexibility.Analysis.HasProjectiveCurveDerivAt.add`](../ContinuousFlexibility/Analysis/ProjectiveDifferential.lean#L68)
- [`ContinuousFlexibility.Analysis.HasProjectiveCurveDerivAt.const_smul`](../ContinuousFlexibility/Analysis/ProjectiveDifferential.lean#L75)
- [`ContinuousFlexibility.Analysis.HasProjectiveLineDerivAt.add`](../ContinuousFlexibility/Analysis/ProjectiveDifferential.lean#L84)
- [`ContinuousFlexibility.Analysis.HasProjectiveLineDerivAt.const_smul`](../ContinuousFlexibility/Analysis/ProjectiveDifferential.lean#L90)
- [`ContinuousFlexibility.Analysis.HasProjectiveCurveDerivAt.clm_comp`](../ContinuousFlexibility/Analysis/ProjectiveDifferential.lean#L100)
- [`ContinuousFlexibility.Analysis.HasProjectiveLineDerivAt.clm_comp`](../ContinuousFlexibility/Analysis/ProjectiveDifferential.lean#L106)
- [`ContinuousFlexibility.Analysis.HasProjectiveLineDerivAt.comp_linear`](../ContinuousFlexibility/Analysis/ProjectiveDifferential.lean#L114)
- [`ContinuousFlexibility.Analysis.hasProjectiveLineDerivAt_clm`](../ContinuousFlexibility/Analysis/ProjectiveDifferential.lean#L121)
- [`ContinuousFlexibility.Analysis.continuous_clm_projective_direction`](../ContinuousFlexibility/Analysis/ProjectiveDifferential.lean#L134)
- [`ContinuousFlexibility.Analysis.hasProjectiveCurveDerivAt_iff_levels`](../ContinuousFlexibility/Analysis/ProjectiveDifferential.lean#L147)
- [`ContinuousFlexibility.Analysis.hasProjectiveLineDerivAt_iff_levels`](../ContinuousFlexibility/Analysis/ProjectiveDifferential.lean#L159)
- [`ContinuousFlexibility.Analysis.hasDerivAt_projectiveAffineLine`](../ContinuousFlexibility/Analysis/ProjectiveDifferential.lean#L167)
- [`ContinuousFlexibility.Analysis.HasProjectiveCurveDerivAt.continuousAt`](../ContinuousFlexibility/Analysis/ProjectiveDifferential.lean#L175)
- [`ContinuousFlexibility.Analysis.continuous_projective_map_iff_levels`](../ContinuousFlexibility/Analysis/ProjectiveDifferential.lean#L183)
- [`ContinuousFlexibility.Analysis.continuous_projective_direction_iff_levels`](../ContinuousFlexibility/Analysis/ProjectiveDifferential.lean#L195)
- [`ContinuousFlexibility.Analysis.projectiveCurveDerivatives_compatible`](../ContinuousFlexibility/Analysis/ProjectiveDifferential.lean#L203)
- [`ContinuousFlexibility.Analysis.exists_projectiveCurveDerivAt_of_levels`](../ContinuousFlexibility/Analysis/ProjectiveDifferential.lean#L216)
- [`ContinuousFlexibility.Analysis.exists_projectiveLineDerivAt_of_levels`](../ContinuousFlexibility/Analysis/ProjectiveDifferential.lean#L222)
- [`ContinuousFlexibility.Analysis.HasProjectiveLineDerivAt.smul_direction`](../ContinuousFlexibility/Analysis/ProjectiveDifferential.lean#L230)
- [`ContinuousFlexibility.Analysis.HasProjectiveCurveDerivAt.scomp`](../ContinuousFlexibility/Analysis/ProjectiveDifferential.lean#L241)
- [`ContinuousFlexibility.Analysis.exists_projectiveLineDerivAt_of_banach_factors`](../ContinuousFlexibility/Analysis/ProjectiveDifferential.lean#L265)

[ProjectiveJets.lean](../ContinuousFlexibility/Analysis/ProjectiveJets.lean)：

- [`ContinuousFlexibility.Analysis.HasProjectiveLineDerivAt.congr_germ`](../ContinuousFlexibility/Analysis/ProjectiveJets.lean#L47)
- [`ContinuousFlexibility.Analysis.HasProjectiveJetsOn.unique`](../ContinuousFlexibility/Analysis/ProjectiveJets.lean#L64)
- [`ContinuousFlexibility.Analysis.hasProjectiveJetsOn_continuousLinear`](../ContinuousFlexibility/Analysis/ProjectiveJets.lean#L94)
- [`ContinuousFlexibility.Analysis.projectiveMultilinearLift_apply`](../ContinuousFlexibility/Analysis/ProjectiveJets.lean#L128)
- [`ContinuousFlexibility.Analysis.projectiveMultilinearLift_unique`](../ContinuousFlexibility/Analysis/ProjectiveJets.lean#L133)
- [`ContinuousFlexibility.Analysis.continuousOn_projective_map_iff_levels`](../ContinuousFlexibility/Analysis/ProjectiveJets.lean#L144)
- [`ContinuousFlexibility.Analysis.hasProjectiveJetsOn_iff_banach_levels`](../ContinuousFlexibility/Analysis/ProjectiveJets.lean#L156)
- [`ContinuousFlexibility.Analysis.quadraticJetFirst_apply`](../ContinuousFlexibility/Analysis/ProjectiveJets.lean#L245)
- [`ContinuousFlexibility.Analysis.quadraticJetSecond_apply`](../ContinuousFlexibility/Analysis/ProjectiveJets.lean#L253)
- [`ContinuousFlexibility.Analysis.hasProjectiveLineDerivAt_quadraticJetValue`](../ContinuousFlexibility/Analysis/ProjectiveJets.lean#L274)
- [`ContinuousFlexibility.Analysis.quadraticJets_order_ge_three`](../ContinuousFlexibility/Analysis/ProjectiveJets.lean#L297)
- [`ContinuousFlexibility.Analysis.hasProjectiveJetsOn_quadratic`](../ContinuousFlexibility/Analysis/ProjectiveJets.lean#L302)

[ProjectiveJetEvaluation.lean](../ContinuousFlexibility/Analysis/ProjectiveJetEvaluation.lean)：

- [`ContinuousFlexibility.Analysis.projectiveJetHeadLinear_apply`](../ContinuousFlexibility/Analysis/ProjectiveJetEvaluation.lean#L37)
- [`ContinuousFlexibility.Analysis.HasProjectiveJetsOn.continuousOn_headLinear`](../ContinuousFlexibility/Analysis/ProjectiveJetEvaluation.lean#L49)
- [`ContinuousFlexibility.Analysis.HasProjectiveCurveDerivAt.jet_eval_fixed`](../ContinuousFlexibility/Analysis/ProjectiveJetEvaluation.lean#L88)
- [`ContinuousFlexibility.Analysis.HasProjectiveCurveDerivAt.jet_eval`](../ContinuousFlexibility/Analysis/ProjectiveJetEvaluation.lean#L108)
- [`ContinuousFlexibility.Analysis.HasProjectiveCurveDerivAt.firstJet_eval`](../ContinuousFlexibility/Analysis/ProjectiveJetEvaluation.lean#L144)
- [`ContinuousFlexibility.Analysis.HasProjectiveJetsOn.hasLineDerivAt`](../ContinuousFlexibility/Analysis/ProjectiveJetEvaluation.lean#L178)
- [`ContinuousFlexibility.Analysis.hasProjectiveLineDerivAt_comp_of_jets`](../ContinuousFlexibility/Analysis/ProjectiveJetEvaluation.lean#L203)
- [`ContinuousFlexibility.Analysis.hasProjectiveLineDerivAt_comp_firstJet`](../ContinuousFlexibility/Analysis/ProjectiveJetEvaluation.lean#L226)

[ProjectiveMultilinearCalculus.lean](../ContinuousFlexibility/Analysis/ProjectiveMultilinearCalculus.lean)：

- [`ContinuousFlexibility.Analysis.HasProjectiveCurveDerivAt.tendsto_shift`](../ContinuousFlexibility/Analysis/ProjectiveMultilinearCalculus.lean#L33)
- [`ContinuousFlexibility.Analysis.multilinear_sub_eq_sum_updates`](../ContinuousFlexibility/Analysis/ProjectiveMultilinearCalculus.lean#L108)
- [`ContinuousFlexibility.Analysis.multilinear_smul_sub_eq_sum_updates`](../ContinuousFlexibility/Analysis/ProjectiveMultilinearCalculus.lean#L124)
- [`ContinuousFlexibility.Analysis.variable_multilinear_quotient_identity`](../ContinuousFlexibility/Analysis/ProjectiveMultilinearCalculus.lean#L133)
- [`ContinuousFlexibility.Analysis.hasProjectiveCurveDerivAt_variableMultilinear`](../ContinuousFlexibility/Analysis/ProjectiveMultilinearCalculus.lean#L153)
- [`ContinuousFlexibility.Analysis.hasProjectiveCurveDerivAt_multilinear`](../ContinuousFlexibility/Analysis/ProjectiveMultilinearCalculus.lean#L196)
- [`ContinuousFlexibility.Analysis.hasProjectiveCurveDerivAt_multilinear_zero`](../ContinuousFlexibility/Analysis/ProjectiveMultilinearCalculus.lean#L221)
- [`ContinuousFlexibility.Analysis.hasProjectiveCurveDerivAt_multilinear_one`](../ContinuousFlexibility/Analysis/ProjectiveMultilinearCalculus.lean#L238)

[ProjectiveJetCompositionTwo.lean](../ContinuousFlexibility/Analysis/ProjectiveJetCompositionTwo.lean)：

- [`ContinuousFlexibility.Analysis.projectiveCompFirst_apply`](../ContinuousFlexibility/Analysis/ProjectiveJetCompositionTwo.lean#L35)
- [`ContinuousFlexibility.Analysis.projectiveCompSecond_apply`](../ContinuousFlexibility/Analysis/ProjectiveJetCompositionTwo.lean#L51)
- [`ContinuousFlexibility.Analysis.projectiveCompSecond_cons`](../ContinuousFlexibility/Analysis/ProjectiveJetCompositionTwo.lean#L58)
- [`ContinuousFlexibility.Analysis.HasProjectiveJetsOn.continuousOn`](../ContinuousFlexibility/Analysis/ProjectiveJetCompositionTwo.lean#L75)
- [`ContinuousFlexibility.Analysis.HasProjectiveJetsOn.continuousOn_compFirst`](../ContinuousFlexibility/Analysis/ProjectiveJetCompositionTwo.lean#L85)
- [`ContinuousFlexibility.Analysis.HasProjectiveJetsOn.continuousOn_compSecond`](../ContinuousFlexibility/Analysis/ProjectiveJetCompositionTwo.lean#L98)
- [`ContinuousFlexibility.Analysis.projective_comp_through_two`](../ContinuousFlexibility/Analysis/ProjectiveJetCompositionTwo.lean#L150)

[ProjectiveJetSchwarz.lean](../ContinuousFlexibility/Analysis/ProjectiveJetSchwarz.lean)：

- [`ContinuousFlexibility.Analysis.hasFDerivAt_of_continuous_line_differential`](../ContinuousFlexibility/Analysis/ProjectiveJetSchwarz.lean#L34)
- [`ContinuousFlexibility.Analysis.HasProjectiveJetsOn.second_symmetric`](../ContinuousFlexibility/Analysis/ProjectiveJetSchwarz.lean#L217)


<a id="w02"></a>
## W02 加权高度、源与圆序列空间

**状态：** 已有部分已编译子结果。**分支：** 分析基础与加权空间。主定理必要节点。

**数学陈述：** 构造Xγ⁰、Xγ=Xγ⁰⊕ℝχL、Yβ=ker Q、Zγ及Kγ，证明完备拓扑、实偶半周期sector、兼容投影、tame retraction PJ=I及固定损失的乘积/倒数/复合/trace和右逆。

**证明提纲：** 在有限重叠材料圆柱上建立混合Sobolev估计，再做频率/权的retraction。一般cutoff和单元结构可先选，二模slice的实际ℓ*在R12后加入。

**直接依赖：** [W01](#w01), [H01](#h01)

**论文定位：** [07-fixed-geometry.tex:72–150](../paper/flexible-surface-rewrite/07-fixed-geometry.tex#L72)，`def:readable-physical-grading`

**目标文件：** `ContinuousFlexibility/Analysis/W02.lean`（节点组织目标；实际已存在的证明文件见下方，整个节点尚未完成）

**验收条件：**

- χL记录两端高度差
- 不能只定义所有范数有限而省略完备性
- 三类源测度的连接有明确连续映射

**已经完成的子结果：**

- 真实二维径向Jacobi算子对单个及有限余弦模的分离
- 正频余弦模的真实归一化角积分正交，偶数模的实偶与π周期性

**仍待闭合的义务：**

- 定义并证明全部加权高度、源、圆序列空间的完备拓扑及smooth tame性质
- 无限Fourier重建、加权序列估计、兼容投影及tame retraction

**优先核查程度：** high（任务风险标记，不是已发现错误）

**现有 Lean 证明：**

[FourierModes.lean](../ContinuousFlexibility/Radial/FourierModes.lean)：

- [`ContinuousFlexibility.Radial.hasDerivAt_cosineMode`](../ContinuousFlexibility/Radial/FourierModes.lean#L32)
- [`ContinuousFlexibility.Radial.hasDerivAt_cosineModeFirst`](../ContinuousFlexibility/Radial/FourierModes.lean#L41)
- [`ContinuousFlexibility.Radial.deriv_cosineMode`](../ContinuousFlexibility/Radial/FourierModes.lean#L51)
- [`ContinuousFlexibility.Radial.deriv_deriv_cosineMode`](../ContinuousFlexibility/Radial/FourierModes.lean#L55)
- [`ContinuousFlexibility.Radial.deriv_deriv_const_mul_cosineMode`](../ContinuousFlexibility/Radial/FourierModes.lean#L60)
- [`ContinuousFlexibility.Radial.radialPDE_cosine_lift`](../ContinuousFlexibility/Radial/FourierModes.lean#L73)
- [`ContinuousFlexibility.Radial.deriv_finite_cosine_sum`](../ContinuousFlexibility/Radial/FourierModes.lean#L90)
- [`ContinuousFlexibility.Radial.deriv_deriv_finite_cosine_sum`](../ContinuousFlexibility/Radial/FourierModes.lean#L95)
- [`ContinuousFlexibility.Radial.radialPDE_finite_cosine_sum`](../ContinuousFlexibility/Radial/FourierModes.lean#L108)
- [`ContinuousFlexibility.Radial.cosineMode_even`](../ContinuousFlexibility/Radial/FourierModes.lean#L135)
- [`ContinuousFlexibility.Radial.cosineMode_even_frequency_periodic`](../ContinuousFlexibility/Radial/FourierModes.lean#L141)
- [`ContinuousFlexibility.Radial.finite_even_cosine_sum_even`](../ContinuousFlexibility/Radial/FourierModes.lean#L149)
- [`ContinuousFlexibility.Radial.finite_even_cosine_sum_periodic`](../ContinuousFlexibility/Radial/FourierModes.lean#L156)

[FourierOrthogonality.lean](../ContinuousFlexibility/Radial/FourierOrthogonality.lean)：

- [`ContinuousFlexibility.Radial.integral_cos_int_frequency`](../ContinuousFlexibility/Radial/FourierOrthogonality.lean#L27)
- [`ContinuousFlexibility.Radial.integral_cosineMode`](../ContinuousFlexibility/Radial/FourierOrthogonality.lean#L37)
- [`ContinuousFlexibility.Radial.angularAverage_cosineMode`](../ContinuousFlexibility/Radial/FourierOrthogonality.lean#L46)
- [`ContinuousFlexibility.Radial.cosineMode_product_formula`](../ContinuousFlexibility/Radial/FourierOrthogonality.lean#L52)
- [`ContinuousFlexibility.Radial.integral_cosineMode_product_of_ne`](../ContinuousFlexibility/Radial/FourierOrthogonality.lean#L68)
- [`ContinuousFlexibility.Radial.integral_cosineMode_product_self`](../ContinuousFlexibility/Radial/FourierOrthogonality.lean#L91)
- [`ContinuousFlexibility.Radial.angularPairing_cosineMode`](../ContinuousFlexibility/Radial/FourierOrthogonality.lean#L115)


<a id="w03"></a>
## W03 正指数弱空间的全阶平坦延拓

**状态：** 已有部分已编译子结果。**分支：** 分析基础与加权空间。主定理必要节点。

**数学陈述：** γ>0且u∈Xγ⁰蕴含任意a,b,k下d∂^(-k)∂r^a∂θ^b u→0，零延拓C∞；Xγ则两端分别常值延拓，参数导数同样成立。

**证明提纲：** 局部Sobolev嵌入加H压倒所有固定系数损失，证明mixed jets和参数方向极限。

**直接依赖：** [W01](#w01), [W02](#w02)

**论文定位：** [07-fixed-geometry.tex:102–156](../paper/flexible-surface-rewrite/07-fixed-geometry.tex#L102)，`prop:full-physical-tame`

**目标文件：** `ContinuousFlexibility/Analysis/W03.lean`（节点组织目标；实际已存在的证明文件见下方，整个节点尚未完成）

**验收条件：**

- 不是只证明值趋零
- 左右常数不要求相等
- 共同参数邻域内的参数导数也覆盖

**已经完成的子结果：**

- 实际半轴/有限区间上各阶真实iteratedDeriv单侧趋0，推出实际零延拓全局C∞且所有端点jets=0
- 任意实范数空间值域、constant/reference延拓均已证明；reference允许独立两端常数
- 从实际 HeightMember 的加权 L² 各阶范数出发，已证明材料圆柱上混合导数的逐点界，换成通常径向混合导数后得到双端任意阶平坦性及实际零延拓全局 C∞。带截断的物理高度也已验证。

**仍待闭合的义务：**

- 同一非零参数区间上高度的联合参数正则性与统一平坦延拓。

**现有 Lean 证明：**

[FlatExtension.lean](../ContinuousFlexibility/Analysis/FlatExtension.lean)：

- [`ContinuousFlexibility.Analysis.extendZeroLeft_of_gt`](../ContinuousFlexibility/Analysis/FlatExtension.lean#L32)
- [`ContinuousFlexibility.Analysis.extendZeroLeft_of_le`](../ContinuousFlexibility/Analysis/FlatExtension.lean#L35)
- [`ContinuousFlexibility.Analysis.extendZeroLeft_eventuallyEq_of_gt`](../ContinuousFlexibility/Analysis/FlatExtension.lean#L38)
- [`ContinuousFlexibility.Analysis.extendZeroLeft_eventuallyEq_zero_of_lt`](../ContinuousFlexibility/Analysis/FlatExtension.lean#L43)
- [`ContinuousFlexibility.Analysis.continuousAt_extendZeroLeft`](../ContinuousFlexibility/Analysis/FlatExtension.lean#L50)
- [`ContinuousFlexibility.Analysis.hasDerivAt_extendZeroLeft`](../ContinuousFlexibility/Analysis/FlatExtension.lean#L69)
- [`ContinuousFlexibility.Analysis.differentiableOn_iteratedDeriv_Ioi`](../ContinuousFlexibility/Analysis/FlatExtension.lean#L86)
- [`ContinuousFlexibility.Analysis.iteratedDeriv_extendZeroLeft`](../ContinuousFlexibility/Analysis/FlatExtension.lean#L97)
- [`ContinuousFlexibility.Analysis.contDiff_extendZeroLeft`](../ContinuousFlexibility/Analysis/FlatExtension.lean#L115)
- [`ContinuousFlexibility.Analysis.iteratedDeriv_extendZeroLeft_eq_zero`](../ContinuousFlexibility/Analysis/FlatExtension.lean#L130)
- [`ContinuousFlexibility.Analysis.contDiff_extendConstantLeft`](../ContinuousFlexibility/Analysis/FlatExtension.lean#L142)
- [`ContinuousFlexibility.Analysis.extendConstantLeft_of_le`](../ContinuousFlexibility/Analysis/FlatExtension.lean#L150)
- [`ContinuousFlexibility.Analysis.extendConstantLeft_of_gt`](../ContinuousFlexibility/Analysis/FlatExtension.lean#L155)
- [`ContinuousFlexibility.Analysis.iteratedDeriv_extendConstantLeft_eq_zero`](../ContinuousFlexibility/Analysis/FlatExtension.lean#L159)
- [`ContinuousFlexibility.Analysis.extendZeroOutside_of_mem`](../ContinuousFlexibility/Analysis/FlatExtension.lean#L175)
- [`ContinuousFlexibility.Analysis.extendZeroOutside_of_notMem`](../ContinuousFlexibility/Analysis/FlatExtension.lean#L180)
- [`ContinuousFlexibility.Analysis.extendZeroOutside_eventuallyEq_of_mem`](../ContinuousFlexibility/Analysis/FlatExtension.lean#L185)
- [`ContinuousFlexibility.Analysis.extendZeroOutside_eventuallyEq_zero_of_lt`](../ContinuousFlexibility/Analysis/FlatExtension.lean#L191)
- [`ContinuousFlexibility.Analysis.extendZeroOutside_eventuallyEq_zero_of_gt`](../ContinuousFlexibility/Analysis/FlatExtension.lean#L197)
- [`ContinuousFlexibility.Analysis.continuousAt_extendZeroOutside_left`](../ContinuousFlexibility/Analysis/FlatExtension.lean#L203)
- [`ContinuousFlexibility.Analysis.continuousAt_extendZeroOutside_right`](../ContinuousFlexibility/Analysis/FlatExtension.lean#L220)
- [`ContinuousFlexibility.Analysis.hasDerivAt_extendZeroOutside`](../ContinuousFlexibility/Analysis/FlatExtension.lean#L238)
- [`ContinuousFlexibility.Analysis.differentiableOn_iteratedDeriv_Ioo`](../ContinuousFlexibility/Analysis/FlatExtension.lean#L289)
- [`ContinuousFlexibility.Analysis.iteratedDeriv_extendZeroOutside`](../ContinuousFlexibility/Analysis/FlatExtension.lean#L297)
- [`ContinuousFlexibility.Analysis.contDiff_extendZeroOutside`](../ContinuousFlexibility/Analysis/FlatExtension.lean#L319)
- [`ContinuousFlexibility.Analysis.iteratedDeriv_extendZeroOutside_eq_zero`](../ContinuousFlexibility/Analysis/FlatExtension.lean#L336)
- [`ContinuousFlexibility.Analysis.contDiff_extendByReference`](../ContinuousFlexibility/Analysis/FlatExtension.lean#L351)
- [`ContinuousFlexibility.Analysis.extendByReference_of_mem`](../ContinuousFlexibility/Analysis/FlatExtension.lean#L362)
- [`ContinuousFlexibility.Analysis.extendByReference_of_notMem`](../ContinuousFlexibility/Analysis/FlatExtension.lean#L367)
- [`ContinuousFlexibility.Analysis.iteratedDeriv_extendByReference_eq`](../ContinuousFlexibility/Analysis/FlatExtension.lean#L373)

[CylinderMixedJets.lean](../ContinuousFlexibility/Analysis/CylinderMixedJets.lean)：

- [`ContinuousFlexibility.Statements.contDiffOn_mixedDerivative`](../ContinuousFlexibility/Analysis/CylinderMixedJets.lean#L101)
- [`ContinuousFlexibility.Statements.mixedDerivative_radialPartial`](../ContinuousFlexibility/Analysis/CylinderMixedJets.lean#L123)
- [`ContinuousFlexibility.Statements.mixedDerivative_angularPartial`](../ContinuousFlexibility/Analysis/CylinderMixedJets.lean#L131)
- [`ContinuousFlexibility.Statements.iteratedFDeriv_cylinderBasis_eq_mixedDerivative`](../ContinuousFlexibility/Analysis/CylinderMixedJets.lean#L158)
- [`ContinuousFlexibility.Statements.norm_iteratedFDeriv_le_of_mixedDerivative`](../ContinuousFlexibility/Analysis/CylinderMixedJets.lean#L208)

[CylinderSobolev.lean](../ContinuousFlexibility/Analysis/CylinderSobolev.lean)：

- [`ContinuousFlexibility.Analysis.abs_le_interval_average_add_deriv`](../ContinuousFlexibility/Analysis/CylinderSobolev.lean#L29)
- [`ContinuousFlexibility.Analysis.deriv_cylinder_radial_slice`](../ContinuousFlexibility/Analysis/CylinderSobolev.lean#L80)
- [`ContinuousFlexibility.Analysis.deriv_cylinder_angular_slice`](../ContinuousFlexibility/Analysis/CylinderSobolev.lean#L85)
- [`ContinuousFlexibility.Analysis.contDiff_cylinder_radialPartial`](../ContinuousFlexibility/Analysis/CylinderSobolev.lean#L90)
- [`ContinuousFlexibility.Analysis.contDiff_cylinder_angularPartial`](../ContinuousFlexibility/Analysis/CylinderSobolev.lean#L94)
- [`ContinuousFlexibility.Analysis.deriv_cylinder_mixed_slice`](../ContinuousFlexibility/Analysis/CylinderSobolev.lean#L98)
- [`ContinuousFlexibility.Analysis.cylinderWindowMeasure_eq_prod`](../ContinuousFlexibility/Analysis/CylinderSobolev.lean#L114)
- [`ContinuousFlexibility.Analysis.cylinderWindowMeasure_eq_restrict_strip`](../ContinuousFlexibility/Analysis/CylinderSobolev.lean#L121)
- [`ContinuousFlexibility.Analysis.cylinderWindowMeasure_univ`](../ContinuousFlexibility/Analysis/CylinderSobolev.lean#L130)
- [`ContinuousFlexibility.Analysis.continuous_memLp_cylinderWindow`](../ContinuousFlexibility/Analysis/CylinderSobolev.lean#L143)
- [`ContinuousFlexibility.Analysis.abs_le_cylinderWindow_L1`](../ContinuousFlexibility/Analysis/CylinderSobolev.lean#L180)
- [`ContinuousFlexibility.Analysis.integral_cylinderWindow_abs_le_L2`](../ContinuousFlexibility/Analysis/CylinderSobolev.lean#L204)
- [`ContinuousFlexibility.Analysis.abs_le_cylinderWindow_L2`](../ContinuousFlexibility/Analysis/CylinderSobolev.lean#L232)

[FlatCylinderExtension.lean](../ContinuousFlexibility/Analysis/FlatCylinderExtension.lean)：

- [`ContinuousFlexibility.Analysis.smooth_zero_extension_of_jet_bounds`](../ContinuousFlexibility/Analysis/FlatCylinderExtension.lean#L29)
- [`ContinuousFlexibility.Analysis.smooth_cylinder_zero_extension`](../ContinuousFlexibility/Analysis/FlatCylinderExtension.lean#L87)

[MaterialCylinderPointwise.lean](../ContinuousFlexibility/Analysis/MaterialCylinderPointwise.lean)：

- [`ContinuousFlexibility.Statements.contDiff_materialPullback`](../ContinuousFlexibility/Analysis/MaterialCylinderPointwise.lean#L25)
- [`ContinuousFlexibility.Statements.contDiff_mixedDerivative`](../ContinuousFlexibility/Analysis/MaterialCylinderPointwise.lean#L41)
- [`ContinuousFlexibility.Statements.radialPartial_mixedDerivative`](../ContinuousFlexibility/Analysis/MaterialCylinderPointwise.lean#L45)
- [`ContinuousFlexibility.Statements.angularPartial_mixedDerivative`](../ContinuousFlexibility/Analysis/MaterialCylinderPointwise.lean#L52)
- [`ContinuousFlexibility.Statements.mixedDerivative_angular_periodic`](../ContinuousFlexibility/Analysis/MaterialCylinderPointwise.lean#L80)
- [`ContinuousFlexibility.Statements.materialPullback_angular_periodic`](../ContinuousFlexibility/Analysis/MaterialCylinderPointwise.lean#L91)
- [`ContinuousFlexibility.Statements.cylinderWindowMeasure_eq_materialCylinderRestrict`](../ContinuousFlexibility/Analysis/MaterialCylinderPointwise.lean#L102)
- [`ContinuousFlexibility.Statements.cylinderWindowL2Norm_le_materialCylinder`](../ContinuousFlexibility/Analysis/MaterialCylinderPointwise.lean#L106)
- [`ContinuousFlexibility.Statements.abs_le_materialCylinder_L2`](../ContinuousFlexibility/Analysis/MaterialCylinderPointwise.lean#L114)
- [`ContinuousFlexibility.Statements.heightMember_materialPullback_mixedDerivative_memLp`](../ContinuousFlexibility/Analysis/MaterialCylinderPointwise.lean#L136)
- [`ContinuousFlexibility.Statements.heightMember_materialPullback_mixedDerivative_uniform_bound`](../ContinuousFlexibility/Analysis/MaterialCylinderPointwise.lean#L148)

[MaterialEndpointDecay.lean](../ContinuousFlexibility/Analysis/MaterialEndpointDecay.lean)：

- [`ContinuousFlexibility.Analysis.tendsto_endpoint_H_rpow_div_pow_zero`](../ContinuousFlexibility/Analysis/MaterialEndpointDecay.lean#L18)
- [`ContinuousFlexibility.Analysis.tendsto_endpoint_H_rpow_M_rpow_div_pow_zero`](../ContinuousFlexibility/Analysis/MaterialEndpointDecay.lean#L59)

[MaterialEndpointDecay.lean](../ContinuousFlexibility/Analysis/MaterialEndpointDecay.lean)：

- [`ContinuousFlexibility.Statements.exists_material_endpoint_decay`](../ContinuousFlexibility/Analysis/MaterialEndpointDecay.lean#L85)

[MaterialHeightExtension.lean](../ContinuousFlexibility/Analysis/MaterialHeightExtension.lean)：

- [`ContinuousFlexibility.Statements.material_height_extension_of_ordinary_bounds`](../ContinuousFlexibility/Analysis/MaterialHeightExtension.lean#L54)

[MaterialHeightRegularity.lean](../ContinuousFlexibility/Analysis/MaterialHeightRegularity.lean)：

- [`ContinuousFlexibility.Statements.heightMember_contDiff_and_flatJets`](../ContinuousFlexibility/Analysis/MaterialHeightRegularity.lean#L21)
- [`ContinuousFlexibility.Statements.physical_height_contDiff_and_flatJets`](../ContinuousFlexibility/Analysis/MaterialHeightRegularity.lean#L30)
- [`ContinuousFlexibility.Statements.physical_height_with_cutoff_contDiff`](../ContinuousFlexibility/Analysis/MaterialHeightRegularity.lean#L36)

[MaterialLocalComparison.lean](../ContinuousFlexibility/Analysis/MaterialLocalComparison.lean)：

- [`ContinuousFlexibility.Statements.material_M_log_derivative_bound`](../ContinuousFlexibility/Analysis/MaterialLocalComparison.lean#L39)
- [`ContinuousFlexibility.Statements.material_M_unit_window_comparison`](../ContinuousFlexibility/Analysis/MaterialLocalComparison.lean#L57)

[MaterialOrdinaryJets.lean](../ContinuousFlexibility/Analysis/MaterialOrdinaryJets.lean)：

- [`ContinuousFlexibility.Statements.iteratedDeriv_comp_materialRadius`](../ContinuousFlexibility/Analysis/MaterialOrdinaryJets.lean#L28)
- [`ContinuousFlexibility.Statements.iteratedDeriv_exp_majorant`](../ContinuousFlexibility/Analysis/MaterialOrdinaryJets.lean#L91)
- [`ContinuousFlexibility.Statements.iteratedDeriv_materialH_rpow_bound`](../ContinuousFlexibility/Analysis/MaterialOrdinaryJets.lean#L119)
- [`ContinuousFlexibility.Statements.materialDerivative_angular_slice_bound`](../ContinuousFlexibility/Analysis/MaterialOrdinaryJets.lean#L157)
- [`ContinuousFlexibility.Statements.mixedDerivative_bound_of_materialPullback`](../ContinuousFlexibility/Analysis/MaterialOrdinaryJets.lean#L206)


<a id="n01"></a>
## N01 共同低阶几何邻域

**状态：** 已有部分已编译子结果。**分支：** 非线性存在性。主定理必要节点。

**数学陈述：** 存在固定b₀,ε₀,d*，使所有分量在n_{b₀}<ε₀上同时满足w/w*∈[1/2,2]、Q/w∈[7/8,9/8]、D∈[1/2,3/2]；根点germs不变，原物理系数及普通特征流的各阶变分/差具有H_m^βℰ_m^{C_s}界。根正则坐标及三阶除后系数的jet界另由N04证明。

**证明提纲：** 由低阶局部嵌入和参考jet界一次选邻域；高阶用流方程/逆映射变分，损失固定。

**直接依赖：** [R12](#r12), [W01](#w01), [W02](#w02), [S05](#s05)

**论文定位：** [07-fixed-geometry.tex:208–338](../paper/flexible-surface-rewrite/07-fixed-geometry.tex#L208)，`prop:uniform-physical-geometry`

**目标文件：** `ContinuousFlexibility/Nonlinear/N01.lean`（节点组织目标；实际已存在的证明文件见下方，整个节点尚未完成）

**验收条件：**

- n_s包含未乘q的u−Φ*
- 量词∃b₀,ε₀,d*∀s∃C_s
- 不得每个s重选邻域半径

**已经完成的子结果：**

- 在每个实际负径向分量内已构造光滑紧支撑控制，其对数扰动光学行程的一阶导数精确为 1；证明包含实际微分、积分分部和符号小区间。

**仍待闭合的义务：**

- 获得统一根尺度、各阶控制 jets 与单元归属，构造同一个参考状态。
- 完成特征流与整体共同域的定量 tame 条件。

**优先核查程度：** high（任务风险标记，不是已发现错误）

**现有 Lean 证明：**

[NegativeComponentOpticalControl.lean](../ContinuousFlexibility/Analysis/NegativeComponentOpticalControl.lean)：

- [`ContinuousFlexibility.Statements.exists_opticalInverseFlux_negative_collar`](../ContinuousFlexibility/Analysis/NegativeComponentOpticalControl.lean#L21)
- [`ContinuousFlexibility.Statements.exists_normalized_opticalControl_of_negativeRadialComponent`](../ContinuousFlexibility/Analysis/NegativeComponentOpticalControl.lean#L86)

[OpticalTravelVariation.lean](../ContinuousFlexibility/Analysis/OpticalTravelVariation.lean)：

- [`ContinuousFlexibility.Statements.hasDerivAt_opticalTravel_logPerturbation`](../ContinuousFlexibility/Analysis/OpticalTravelVariation.lean#L48)
- [`ContinuousFlexibility.Statements.contDiffOn_opticalInverseFlux`](../ContinuousFlexibility/Analysis/OpticalTravelVariation.lean#L167)
- [`ContinuousFlexibility.Statements.opticalTravel_variation_integral_by_parts`](../ContinuousFlexibility/Analysis/OpticalTravelVariation.lean#L204)
- [`ContinuousFlexibility.Statements.exists_normalized_opticalControl`](../ContinuousFlexibility/Analysis/OpticalTravelVariation.lean#L243)


<a id="n02"></a>
## N02 圆返回残差与小除数逆

**状态：** 待形式化。**分支：** 非线性存在性。主定理必要节点。

**数学陈述：** 从真实特征流构造边界chart和返回残差e；e=0等价于两支返回均为固定旋转。证明D_he=M_T+Q_h，及正偶频零均值sector上的M_T逆和固定损失估计。

**证明提纲：** 分离角均值和非零频率；用真实旅行角的小除数界求Fourier逆，保留chart的奇性和π-equivariance。

**直接依赖：** [R12](#r12), [N01](#n01), [W02](#w02)

**论文定位：** [07-fixed-geometry.tex:341–389](../paper/flexible-surface-rewrite/07-fixed-geometry.tex#L341)，`eq:rewrite-circle-inverse`

**目标文件：** `ContinuousFlexibility/Nonlinear/N02.lean`（拟建，尚无此证明）

**验收条件：**

- 常数频率由径向控制处理
- 返回等式包含两支特征
- chart增加性及组合路径的smooth tame性

<a id="n03"></a>
## N03 固定特征返回的残差修正

**状态：** 待形式化。**分支：** 非线性存在性。主定理必要节点。

**数学陈述：** 构造对称散度算子L̂，与L̄同法向主系数a、同根点germs及界面通量，正区间不变，返回精确固定。内部混合系数b一般改变，不声称全局法向通量相同。L̄−L̂=E_x(e)，对独立(e,η)为smooth tame双线性映射且输出兼容源。

**证明提纲：** 冻结实际state的流和复合路径，只替换显式残差因子；验证a不变、修正支持外及界面通量不变和两端积分。

**直接依赖：** [N01](#n01), [N02](#n02), [W02](#w02), [S05](#s05)

**论文定位：** [07-fixed-geometry.tex:391–458](../paper/flexible-surface-rewrite/07-fixed-geometry.tex#L391)，`prop:optical-residual-completion`

**目标文件：** `ContinuousFlexibility/Nonlinear/N03.lean`（拟建，尚无此证明）

**验收条件：**

- 独立残差变量的线性不是只在e=e(state)成立
- 正区间及根germ不动
- 返回精确固定而非仅一阶近似

**优先核查程度：** high（任务风险标记，不是已发现错误）

<a id="n04"></a>
## N04 根坐标、正区间拼接与固定transmission

**状态：** 待形式化。**分支：** 非线性存在性。主定理必要节点。

**数学陈述：** 证明根点x^(3/2)的even/odd合成固定损失，得到光滑非退化根坐标、同一strip的可逆chart、配对保持；正区间主密度差可除y³(1−y)³，所有算子共享传递条件。对满足分片规范方程、物理源在缝口光滑匹配且满足value/conormal传递的分片光滑解，由方程递推得到全部物理jets匹配。

**证明提纲：** 分别做根点合成、Airy型规范形式、源/高度因子、三阶Hadamard除法、正区间延拓及缝口全jet识别。

**直接依赖：** [N01](#n01), [N03](#n03), [W01](#w01), [W02](#w02)

**论文定位：** [07-fixed-geometry.tex:462–715](../paper/flexible-surface-rewrite/07-fixed-geometry.tex#L462)，`lem:rewrite-root-composition`

**目标文件：** `ContinuousFlexibility/Nonlinear/N04.lean`（拟建，尚无此证明）

**验收条件：**

- even/odd损失分别按原文精确计数
- 三阶零点除法的连续映射实际证明
- source Jacobian与符号不丢失
- 任意仅满足value/conormal条件的分片field不自动具有高阶jet匹配
- 在此节点证明根正则坐标和三阶除后系数的高阶界，避免N01隐式引用本节点

**优先核查程度：** critical（任务风险标记，不是已发现错误）

<a id="n05"></a>
## N05 增广参考逆和共同闭图域

**状态：** 待形式化。**分支：** 非线性存在性。主定理必要节点。

**数学陈述：** 在固定canonical cylinders定义V_{t,s}和aL,μ,λ三个标量，构造任意源上的双侧逆G*；同一个G*的β±ε估计给固定M损失。D*=G*(V_{0,b})完备图闭，且识别分布transmission、trace并穷尽admissible smooth fields。

**证明提纲：** 用兼容投影加入λ列；双权选择依输出/输入端点尺度方向，Schur估计后证明物理域识别。

**直接依赖：** [R12](#r12), [N04](#n04), [W02](#w02)

**论文定位：** [08-stable-inverse.tex:14–171](../paper/flexible-surface-rewrite/08-stable-inverse.tex#L14)，`lem:two-weights-closed-domain`

**目标文件：** `ContinuousFlexibility/Nonlinear/N05.lean`（拟建，尚无此证明）

**验收条件：**

- 逆在两指数交叠上确为同一个
- image-domain完备性不替代分布域识别
- 全部光滑admissible fields都在域中

**优先核查程度：** critical（任务风险标记，不是已发现错误）

<a id="n06"></a>
## N06 同一Banach空间的相对小扰动

**状态：** 待形式化。**分支：** 非线性存在性。主定理必要节点。

**数学陈述：** R_x=(P_x−P*)G*是同一个V_{0,b}上的有界自同态，范数<1/2；在D*上有分布意义的P_x=(I+R_x)P*。

**证明提纲：** 用额外H_k^β系数因子支付固定M损失，先证bounded endomorphism与小范数，再使用Neumann逆。

**直接依赖：** [N01](#n01), [N04](#n04), [N05](#n05), [W01](#w01)

**论文定位：** [08-stable-inverse.tex:194–340](../paper/flexible-surface-rewrite/08-stable-inverse.tex#L194)，`eq:current-fixed-domain-factorization`

**目标文件：** `ContinuousFlexibility/Nonlinear/N06.lean`（拟建，尚无此证明）

**验收条件：**

- 不得直接对带导数损失的逆用Neumann级数
- 因式分解在共同域上成立
- 低阶邻域不随输出阶数缩小

**优先核查程度：** critical（任务风险标记，不是已发现错误）

<a id="h02"></a>
## H02 逆族smooth tame定理

**状态：** 待形式化。**分支：** 分析基础与加权空间。主定理必要节点。

**数学陈述：** 对smooth tame线性族L_x，若每个源有唯一解且逆族已连续、tame，则逆族smooth tame。

**证明提纲：** 证明Hamilton II 3.1.1所需版本，或在同一scale中用resolvent、DV=−V(DL)V和归纳给出充分版本。

**直接依赖：** [H01](#h01)

**论文定位：** [08-stable-inverse.tex:523–550](../paper/flexible-surface-rewrite/08-stable-inverse.tex#L523)，`prop:rewrite-volume-inverse`

**目标文件：** `ContinuousFlexibility/Analysis/H02.lean`（拟建，尚无此证明）

**验收条件：**

- 连续性和tame界是须验证的前提
- 无新公理
- 实际采用的方向微积分与H01一致

**外部原始定理：** Hamilton 1982, Part II, Theorem 3.1.1

**优先核查程度：** high（任务风险标记，不是已发现错误）

<a id="n07"></a>
## N07 扰动标量逆及高阶恢复

**状态：** 待形式化。**分支：** 非线性存在性。主定理必要节点。

**数学陈述：** 先在基本Banach空间反演，再从方程恢复全部角向/法向混合正则性，得到固定损失tame逆G_xf=(η,μ)，η∈Xβ∩kerℓ*；兼容源上λ=0，右端归零、左端常数自由。

**证明提纲：** 用基本解的唯一性保持同一高阶解；法向递推与commutator逐阶估计；最后应用H02。

**直接依赖：** [N05](#n05), [N06](#n06), [H02](#h02), [W02](#w02)

**论文定位：** [08-stable-inverse.tex:342–550](../paper/flexible-surface-rewrite/08-stable-inverse.tex#L342)，`prop:rewrite-volume-inverse`

**目标文件：** `ContinuousFlexibility/Nonlinear/N07.lean`（拟建，尚无此证明）

**验收条件：**

- 高阶常数可变而邻域固定
- 积分守恒实际消去λ
- 逆族对state/source smooth tame

<a id="n08"></a>
## N08 联合残差、真实控制列与smoothing

**状态：** 待形式化。**分支：** 非线性存在性。主定理必要节点。

**数学陈述：** 构造R=(A,e):X×ℝ→Y、证明q=0可去且参考state为零；真实k=DνA、K=DκA包含h_w变化；J=⟨Dκe⟩对角一致可逆，K及GK取得所需控制权的smoothing。

**证明提纲：** 把四未知量和归一化slice写成实际空间；分开均值控制行和非零频chart行，证明全部映射的兼容性。

**直接依赖：** [S04](#s04), [N01](#n01), [N02](#n02), [N07](#n07), [W02](#w02)

**论文定位：** [09-solving-the-equation.tex:13–137](../paper/flexible-surface-rewrite/09-solving-the-equation.tex#L13)，`eq:readable-joint-residual`

**目标文件：** `ContinuousFlexibility/Nonlinear/N08.lean`（拟建，尚无此证明）

**验收条件：**

- state为(u,ν,κ,hL)，q为独立参数
- 不能忘记控制对h_w的贡献
- J和smoothing在同一Bβ上使用

<a id="n09"></a>
## N09 耦合高度与圆方程的逆

**状态：** 待形式化。**分支：** 非线性存在性。主定理必要节点。

**数学陈述：** 在同一个Bβ上证明qJ⁻¹R°GK的小范数，构造ξ、(η,μ)、v三条解公式；最终圆源零均值，使M_T逆合法，得到对源线性且对state smooth tame的V。

**证明提纲：** 先做基本空间Schur消元及第二次Neumann反演，再恢复高阶界；真实chart增量为v∘hL。

**直接依赖：** [N02](#n02), [N07](#n07), [N08](#n08), [H02](#h02)

**论文定位：** [09-solving-the-equation.tex:139–181](../paper/flexible-surface-rewrite/09-solving-the-equation.tex#L139)，`eq:joint-height-circle-inverse`

**目标文件：** `ContinuousFlexibility/Nonlinear/N09.lean`（拟建，尚无此证明）

**验收条件：**

- 第二次Neumann仍是同空间有界逆
- 零均值须由方程证明
- 全部高阶估计对应同一基本解

<a id="n10"></a>
## N10 两个独立残差的精确二次误差

**状态：** 待形式化。**分支：** 非线性存在性。主定理必要节点。

**数学陈述：** 构造对任意独立r=(r₁,r₂)、y=(f,g)双线性且smooth tame的Q_x,q(r,y)，证明D_xR·Vy=y+Q_x,q(R,y)，并证明输出源兼容。

**证明提纲：** 固定实际state路径，只替换显式残差因子；分别核对scalar散度误差和chart误差。

**直接依赖：** [N03](#n03), [N08](#n08), [N09](#n09), [S05](#s05), [W02](#w02)

**论文定位：** [09-solving-the-equation.tex:183–227](../paper/flexible-surface-rewrite/09-solving-the-equation.tex#L183)，`eq:joint-height-circle-quadratic-error`

**目标文件：** `ContinuousFlexibility/Nonlinear/N10.lean`（拟建，尚无此证明）

**验收条件：**

- 不能用O(‖R‖‖y‖)估计替代精确恒等式
- 真正双线性且定义在全部独立残差上
- source积分和奇偶条件闭合

**优先核查程度：** high（任务风险标记，不是已发现错误）

<a id="h03"></a>
## H03 带二次误差的Nash–Moser隐函数定理

**状态：** 已有部分已编译子结果。**分支：** 分析基础与加权空间。主定理必要节点。

**数学陈述：** 在真实tame空间开集上，smooth tame的R,V,Q满足上述精确二次误差恒等式且初值为零，则存在同一参数开邻域上的解；须得到本工程需要的正则性和参数依赖。

**证明提纲：** 优先证明Hamilton III 3.3.1的适用版本；若采用专用smoothing迭代，则完整证明其收敛、导数损失预算及参数正则性，并与N10接口逐条对照。

**直接依赖：** [H01](#h01)

**论文定位：** [09-solving-the-equation.tex:183–196](../paper/flexible-surface-rewrite/09-solving-the-equation.tex#L183)，`eq:rewrite-hamilton-hypothesis`

**目标文件：** `ContinuousFlexibility/Analysis/H03.lean`（节点组织目标；实际已存在的证明文件见下方，整个节点尚未完成）

**验收条件：**

- 不能用普通Banach隐函数定理代替
- 不能只把Hamilton结论作为假设/公理
- 换实现路线前必须保留相同的解存在结论

**已经完成的子结果：**

- 固定参数的实际二阶 Taylor 余项、二次 Newton 步及其平滑缺陷、同一局部球上的一二阶 tame 界已验证。
- 已证固定参数下的实际 Taylor 界、右逆及其二次误差的局部 tame 界，以及同一平滑族的低阶、高阶、尾项和一步残差界。同一实际平滑 Newton 步的两阶残差与高阶状态递推已验证。
- 实际统一 tame 数据、数值步长与前缀估计、以及从原固定参数假设得到的同一个真实平滑 Newton 序列已验证。在共同非零参数邻域内，所有有限前缀位于定义域并满足低残差、高状态界。

**仍待闭合的义务：**

- 从同一真实迭代证明全阶修正可和、全阶参数正则性，并完成实际物理应用。

**外部原始定理：** Hamilton 1982, Part III, Theorem 3.3.1

**优先核查程度：** critical（任务风险标记，不是已发现错误）

**现有 Lean 证明：**

[ProjectiveNewtonEstimate.lean](../ContinuousFlexibility/Analysis/ProjectiveNewtonEstimate.lean)：

- [`ContinuousFlexibility.Analysis.projectiveTaylorRemainder_le`](../ContinuousFlexibility/Analysis/ProjectiveNewtonEstimate.lean#L90)
- [`ContinuousFlexibility.Analysis.projectiveNewtonStep_residual_le`](../ContinuousFlexibility/Analysis/ProjectiveNewtonEstimate.lean#L124)
- [`ContinuousFlexibility.Analysis.projectiveSmoothedNewtonStep_residual_le`](../ContinuousFlexibility/Analysis/ProjectiveNewtonEstimate.lean#L151)

[ProjectiveNewtonTameBounds.lean](../ContinuousFlexibility/Analysis/ProjectiveNewtonTameBounds.lean)：

- [`ContinuousFlexibility.Analysis.exists_common_newton_tame_bounds`](../ContinuousFlexibility/Analysis/ProjectiveNewtonTameBounds.lean#L70)
- [`ContinuousFlexibility.Analysis.uniform_secondJet_le_on_segment`](../ContinuousFlexibility/Analysis/ProjectiveNewtonTameBounds.lean#L128)
- [`ContinuousFlexibility.Analysis.projectiveSmoothedNewtonStep_tame_residual_le`](../ContinuousFlexibility/Analysis/ProjectiveNewtonTameBounds.lean#L154)

[ProjectiveNewtonCorrectionBounds.lean](../ContinuousFlexibility/Analysis/ProjectiveNewtonCorrectionBounds.lean)：

- [`ContinuousFlexibility.Analysis.linearFamilyTame_on_ball_of_smoothTame`](../ContinuousFlexibility/Analysis/ProjectiveNewtonCorrectionBounds.lean#L93)
- [`ContinuousFlexibility.Analysis.exists_bilinear_tame_bounds_on_ball_of_smoothTame`](../ContinuousFlexibility/Analysis/ProjectiveNewtonCorrectionBounds.lean#L124)
- [`ContinuousFlexibility.Analysis.exists_common_newton_correction_tame_bounds`](../ContinuousFlexibility/Analysis/ProjectiveNewtonCorrectionBounds.lean#L160)

[ProjectiveNewtonRecurrence.lean](../ContinuousFlexibility/Analysis/ProjectiveNewtonRecurrence.lean)：

- [`ContinuousFlexibility.Analysis.exists_zero_tame_bound`](../ContinuousFlexibility/Analysis/ProjectiveNewtonRecurrence.lean#L21)
- [`ContinuousFlexibility.Analysis.seminorm_le_of_smoothing_bounds`](../ContinuousFlexibility/Analysis/ProjectiveNewtonRecurrence.lean#L42)
- [`ContinuousFlexibility.Analysis.projectiveSmoothedNewtonIterates_parameter`](../ContinuousFlexibility/Analysis/ProjectiveNewtonRecurrence.lean#L69)
- [`ContinuousFlexibility.Analysis.projectiveSmoothedNewtonIterates_displacement_le`](../ContinuousFlexibility/Analysis/ProjectiveNewtonRecurrence.lean#L80)
- [`ContinuousFlexibility.Analysis.projectiveSmoothedNewtonStep_twoGradeRecurrence`](../ContinuousFlexibility/Analysis/ProjectiveNewtonRecurrence.lean#L187)
- [`ContinuousFlexibility.Analysis.newton_correction_bounds_of_tame`](../ContinuousFlexibility/Analysis/ProjectiveNewtonRecurrence.lean#L357)
- [`ContinuousFlexibility.Analysis.exists_twoGradeNewtonSmoothingBounds`](../ContinuousFlexibility/Analysis/ProjectiveNewtonRecurrence.lean#L413)

[ProjectiveNewtonSmoothing.lean](../ContinuousFlexibility/Analysis/ProjectiveNewtonSmoothing.lean)：

- [`ContinuousFlexibility.Analysis.exists_newton_smoothing_bounds`](../ContinuousFlexibility/Analysis/ProjectiveNewtonSmoothing.lean#L26)
- [`ContinuousFlexibility.Analysis.newton_segment_mem_of_seminorm_margin`](../ContinuousFlexibility/Analysis/ProjectiveNewtonSmoothing.lean#L71)
- [`ContinuousFlexibility.Analysis.projectiveSmoothedNewtonStep_residual_le_of_bounds`](../ContinuousFlexibility/Analysis/ProjectiveNewtonSmoothing.lean#L96)
- [`ContinuousFlexibility.Analysis.projectiveSmoothedNewtonStep_scaled_residual_le`](../ContinuousFlexibility/Analysis/ProjectiveNewtonSmoothing.lean#L168)

[ProjectiveNewtonSchedule.lean](../ContinuousFlexibility/Analysis/ProjectiveNewtonSchedule.lean)：

- [`ContinuousFlexibility.Analysis.newtonSmoothingIndex_succ_bounds`](../ContinuousFlexibility/Analysis/ProjectiveNewtonSchedule.lean#L23)
- [`ContinuousFlexibility.Analysis.newtonSmoothingIndex_ge_add`](../ContinuousFlexibility/Analysis/ProjectiveNewtonSchedule.lean#L39)
- [`ContinuousFlexibility.Analysis.newton_budget_rate_identities`](../ContinuousFlexibility/Analysis/ProjectiveNewtonSchedule.lean#L48)
- [`ContinuousFlexibility.Analysis.newton_budget_induction`](../ContinuousFlexibility/Analysis/ProjectiveNewtonSchedule.lean#L184)
- [`ContinuousFlexibility.Analysis.newton_exponential_prefix_le`](../ContinuousFlexibility/Analysis/ProjectiveNewtonSchedule.lean#L239)
- [`ContinuousFlexibility.Analysis.exists_newton_starting_index`](../ContinuousFlexibility/Analysis/ProjectiveNewtonSchedule.lean#L272)
- [`ContinuousFlexibility.Analysis.exists_newton_high_grade_for_rate`](../ContinuousFlexibility/Analysis/ProjectiveNewtonSchedule.lean#L297)
- [`ContinuousFlexibility.Analysis.newton_residual_rate_improvement`](../ContinuousFlexibility/Analysis/ProjectiveNewtonSchedule.lean#L313)
- [`ContinuousFlexibility.Analysis.newtonImprovedRate_zero`](../ContinuousFlexibility/Analysis/ProjectiveNewtonSchedule.lean#L344)
- [`ContinuousFlexibility.Analysis.newtonImprovedRate_succ`](../ContinuousFlexibility/Analysis/ProjectiveNewtonSchedule.lean#L348)
- [`ContinuousFlexibility.Analysis.tendsto_newtonImprovedRate_atTop`](../ContinuousFlexibility/Analysis/ProjectiveNewtonSchedule.lean#L353)

[ProjectiveNewtonSeed.lean](../ContinuousFlexibility/Analysis/ProjectiveNewtonSeed.lean)：

- [`ContinuousFlexibility.Analysis.projectiveNewton_prefix_control`](../ContinuousFlexibility/Analysis/ProjectiveNewtonSeed.lean#L68)
- [`ContinuousFlexibility.Analysis.exists_initial_residual_radius`](../ContinuousFlexibility/Analysis/ProjectiveNewtonSeed.lean#L115)
- [`ContinuousFlexibility.Analysis.projectiveNewton_seed_of_common_bounds`](../ContinuousFlexibility/Analysis/ProjectiveNewtonSeed.lean#L146)
- [`ContinuousFlexibility.Analysis.exists_projectiveNewton_seed`](../ContinuousFlexibility/Analysis/ProjectiveNewtonSeed.lean#L403)

[ProjectiveNewtonTameData.lean](../ContinuousFlexibility/Analysis/ProjectiveNewtonTameData.lean)：

- [`ContinuousFlexibility.Analysis.pairGrading_monotone`](../ContinuousFlexibility/Analysis/ProjectiveNewtonTameData.lean#L20)
- [`ContinuousFlexibility.Analysis.exists_common_newton_tame_data`](../ContinuousFlexibility/Analysis/ProjectiveNewtonTameData.lean#L36)


<a id="n11"></a>
## N11 弱权非线性解支

**状态：** 待形式化。**分支：** 非线性存在性。主定理必要节点。

**数学陈述：** 得到一个共同q₀>0及|q|<q₀上的解x(q)，满足R=0、ℓ*u_q=1、u_q=Φ*+O(q)，全部阶seminorm在同一个区间受控。

**证明提纲：** 逐条实例化H03的真实空间、开集、参考零点、逆和双线性误差。主定理只需其中一个非零q。

**直接依赖：** [H03](#h03), [N08](#n08), [N09](#n09), [N10](#n10)

**论文定位：** [09-solving-the-equation.tex:229–238](../paper/flexible-surface-rewrite/09-solving-the-equation.tex#L229)，`eq:rewrite-weak-branch`

**目标文件：** `ContinuousFlexibility/Nonlinear/N11.lean`（拟建，尚无此证明）

**验收条件：**

- 不得每个阶数各得一个q_s
- q是构造参数，尚非弯曲相位τ
- 最终必须实际实例化所有分析前提

<a id="n12"></a>
## N12 最小平坦环带核心

**状态：** 已有部分已编译子结果。**分支：** 非线性存在性。主定理必要节点。

**数学陈述：** 取固定0<|q|<q₀，构造w_q,z_q，证明Nres=0、余度量正定且局部欧氏、半转对称和非径向；w_q各阶零延拓、z_q两端分别常值平坦延拓。

**证明提纲：** 从弱控制和参考轮廓jet界证明w_q的实际零延拓；ℓ*u_q=1保证非径向；真实Cartan公式给平坦性。输出FlatAnnularCore供G01扩大为开领圈。

**直接依赖：** [N11](#n11), [W03](#w03), [N01](#n01), [R12](#r12), [S03](#s03)

**论文定位：** [10-endpoint-and-sphere.tex:250–317](../paper/flexible-surface-rewrite/10-endpoint-and-sphere.tex#L250)，`thm:new-annular-height`

**目标文件：** `ContinuousFlexibility/Nonlinear/N12.lean`（节点组织目标；实际已存在的证明文件见下方，整个节点尚未完成）

**验收条件：**

- 不能因强估计后置而省掉w_q的延拓证明
- 左右常数允许不同
- 输出不携带未证明的存在性前提

**已经完成的子结果：**

- 实际非零弱分支若有全局光滑的径向状态轮廓，已可用 HeightMember 的正权推出实际高度光滑并构造 FlatAnnularCore。实际局部有限控制和的全阶端点延拓及角取样系数界已验证。
- 实际同一个非零弱分支若满足控制开区间位于指定径向单元，两端受控轮廓和解码高度的全阶平坦延拓均已验证，从该分支直接得到 FlatAnnularCore。

**仍待闭合的义务：**

- 按实际径向参考的负分量构造光学控制及单元归属。
- 构造实际弱分支和允许的非零参数，再实例化环带核心。

**现有 Lean 证明：**

[MaterialHeightRegularity.lean](../ContinuousFlexibility/Analysis/MaterialHeightRegularity.lean)：

- [`ContinuousFlexibility.Statements.IsWeakBranch.nonempty_flatAnnularCore_of_profile_smooth`](../ContinuousFlexibility/Analysis/MaterialHeightRegularity.lean#L43)

[StateControlDecay.lean](../ContinuousFlexibility/Analysis/StateControlDecay.lean)：

- [`ContinuousFlexibility.Statements.abs_iteratedDeriv_stateControlSum_le`](../ContinuousFlexibility/Analysis/StateControlDecay.lean#L52)
- [`ContinuousFlexibility.Statements.contDiff_stateProfile_of_control_jet_bounds`](../ContinuousFlexibility/Analysis/StateControlDecay.lean#L99)

[StateKappaBounds.lean](../ContinuousFlexibility/Analysis/StateKappaBounds.lean)：

- [`ContinuousFlexibility.Statements.integral_abs_le_angleL2`](../ContinuousFlexibility/Analysis/StateKappaBounds.lean#L28)
- [`ContinuousFlexibility.Statements.abs_angularMean_le_angleL2`](../ContinuousFlexibility/Analysis/StateKappaBounds.lean#L50)
- [`ContinuousFlexibility.Statements.circleMember_angleL2_le_weight`](../ContinuousFlexibility/Analysis/StateKappaBounds.lean#L65)
- [`ContinuousFlexibility.Statements.circleMember_angularMean_bound`](../ContinuousFlexibility/Analysis/StateKappaBounds.lean#L96)
- [`ContinuousFlexibility.Statements.materialSample_mem_radialCore`](../ContinuousFlexibility/Analysis/StateKappaBounds.lean#L110)
- [`ContinuousFlexibility.Statements.stateKappa_weight_bound`](../ContinuousFlexibility/Analysis/StateKappaBounds.lean#L116)
- [`ContinuousFlexibility.Statements.stateKappa_weight_bound_of_accumulatingProfile`](../ContinuousFlexibility/Analysis/StateKappaBounds.lean#L128)

[StateProfileRegularity.lean](../ContinuousFlexibility/Analysis/StateProfileRegularity.lean)：

- [`ContinuousFlexibility.Statements.contDiffOn_stateControlSum`](../ContinuousFlexibility/Analysis/StateProfileRegularity.lean#L24)
- [`ContinuousFlexibility.Statements.stateControlSum_zero_off_core`](../ContinuousFlexibility/Analysis/StateProfileRegularity.lean#L51)
- [`ContinuousFlexibility.Statements.contDiffOn_stateProfile`](../ContinuousFlexibility/Analysis/StateProfileRegularity.lean#L61)
- [`ContinuousFlexibility.Statements.contDiff_stateProfile_of_flat_control_sum`](../ContinuousFlexibility/Analysis/StateProfileRegularity.lean#L74)

[WeakBranchCore.lean](../ContinuousFlexibility/Analysis/WeakBranchCore.lean)：

- [`ContinuousFlexibility.Statements.referenceRow_eq_zero_of_angle_constant`](../ContinuousFlexibility/Analysis/WeakBranchCore.lean#L22)
- [`ContinuousFlexibility.Statements.stateHeight_nonradial_of_referenceRow`](../ContinuousFlexibility/Analysis/WeakBranchCore.lean#L45)
- [`ContinuousFlexibility.Statements.polarCoordinateResidual_eq_zero_of_scalarResidualField`](../ContinuousFlexibility/Analysis/WeakBranchCore.lean#L68)
- [`ContinuousFlexibility.Statements.IsWeakBranch.nonempty_flatAnnularCore_of_smooth`](../ContinuousFlexibility/Analysis/WeakBranchCore.lean#L138)

[ControlCellEndpointBounds.lean](../ContinuousFlexibility/Analysis/ControlCellEndpointBounds.lean)：

- [`ContinuousFlexibility.Statements.materialSample_endpoint_weight_bound`](../ContinuousFlexibility/Analysis/ControlCellEndpointBounds.lean#L66)
- [`ContinuousFlexibility.Statements.stateKappa_controlJet_endpoint_bound`](../ContinuousFlexibility/Analysis/ControlCellEndpointBounds.lean#L160)

[StateControlEndpointClosure.lean](../ContinuousFlexibility/Analysis/StateControlEndpointClosure.lean)：

- [`ContinuousFlexibility.Statements.contDiff_stateProfile_of_endpoint_control_jet_bounds`](../ContinuousFlexibility/Analysis/StateControlEndpointClosure.lean#L22)
- [`ContinuousFlexibility.Statements.contDiff_stateProfile_of_controlCellLocations`](../ContinuousFlexibility/Analysis/StateControlEndpointClosure.lean#L71)
- [`ContinuousFlexibility.Statements.IsWeakBranch.nonempty_flatAnnularCore_at_of_controlCellLocations`](../ContinuousFlexibility/Analysis/StateControlEndpointClosure.lean#L89)
- [`ContinuousFlexibility.Statements.IsWeakBranch.nonempty_flatAnnularCore_of_controlCellLocations`](../ContinuousFlexibility/Analysis/StateControlEndpointClosure.lean#L100)


<a id="d01"></a>
## D01 曲面二阶几何与刚体运动自然性

**状态：** 已有部分已编译子结果。**分支：** 几何闭合。主定理必要节点。

**数学陈述：** 对实际光滑曲面嵌入定义诱导度量、单位法向、第二基本形式、形算子、Gaussian曲率及H=tr(S)/2；证明图公式和在欧氏仿射等距/重参数化下的变换律。

**证明提纲：** 采用欧氏坐标和有限图册建立所需曲面几何特例，适配既有流形与向量丛基础；记录法向符号约定。

**直接依赖：** [C00](#c00)

**论文定位：** [01-introduction.tex:33–39](../paper/flexible-surface-rewrite/01-introduction.tex#L33)；[02-geometry.tex:146–190](../paper/flexible-surface-rewrite/02-geometry.tex#L146)，`eq:marker-curvature`

**目标文件：** `ContinuousFlexibility/Geometry/D01.lean`（节点组织目标；实际已存在的证明文件见下方，整个节点尚未完成）

**验收条件：**

- 曲率marker使用真正Gaussian曲率
- 覆盖环境反射及向外法向的运输
- 主方向线与形算子特征空间的对应

**已经完成的子结果：**

- 本检查点包含同一标准球面族的真实联合光滑单位法向、切丛形算子、Weingarten等式、自伴性，以及形算子同物理chart矩阵的实际共轭和trace/det识别；法向尚未识别为完整标记内部的向外法向。

**仍待闭合的义务：**

- 完整标记inside上的全局向外识别及其与任意实际outward normal的对应，由G15后续完成。

**优先核查程度：** high（任务风险标记，不是已发现错误）

**现有 Lean 证明：**

[GraphSurfaceGeometry.lean](../ContinuousFlexibility/Geometry/GraphSurfaceGeometry.lean)：

- [`ContinuousFlexibility.graphAreaSq_pos`](../ContinuousFlexibility/Geometry/GraphSurfaceGeometry.lean#L34)
- [`ContinuousFlexibility.graphAreaDensity_pos`](../ContinuousFlexibility/Geometry/GraphSurfaceGeometry.lean#L39)
- [`ContinuousFlexibility.graphAreaDensity_sq`](../ContinuousFlexibility/Geometry/GraphSurfaceGeometry.lean#L42)
- [`ContinuousFlexibility.graphUpwardNormal_zero`](../ContinuousFlexibility/Geometry/GraphSurfaceGeometry.lean#L46)
- [`ContinuousFlexibility.graphUpwardNormal_one`](../ContinuousFlexibility/Geometry/GraphSurfaceGeometry.lean#L50)
- [`ContinuousFlexibility.graphUpwardNormal_two`](../ContinuousFlexibility/Geometry/GraphSurfaceGeometry.lean#L54)
- [`ContinuousFlexibility.graphUpwardNormal_inner_self`](../ContinuousFlexibility/Geometry/GraphSurfaceGeometry.lean#L58)
- [`ContinuousFlexibility.graphUpwardNormal_norm`](../ContinuousFlexibility/Geometry/GraphSurfaceGeometry.lean#L68)
- [`ContinuousFlexibility.height_fderiv_coordinates`](../ContinuousFlexibility/Geometry/GraphSurfaceGeometry.lean#L74)
- [`ContinuousFlexibility.graphUpwardNormal_orthogonal`](../ContinuousFlexibility/Geometry/GraphSurfaceGeometry.lean#L82)
- [`ContinuousFlexibility.inner_heightGraph_fderiv`](../ContinuousFlexibility/Geometry/GraphSurfaceGeometry.lean#L92)
- [`ContinuousFlexibility.heightGraph_fderiv_injective`](../ContinuousFlexibility/Geometry/GraphSurfaceGeometry.lean#L99)
- [`ContinuousFlexibility.heightGraph_second_fderiv`](../ContinuousFlexibility/Geometry/GraphSurfaceGeometry.lean#L106)
- [`ContinuousFlexibility.graphUpwardNormal_isUnitSurfaceNormal`](../ContinuousFlexibility/Geometry/GraphSurfaceGeometry.lean#L131)
- [`ContinuousFlexibility.contDiff_graphAreaDensity`](../ContinuousFlexibility/Geometry/GraphSurfaceGeometry.lean#L136)
- [`ContinuousFlexibility.contDiff_graphUpwardNormal`](../ContinuousFlexibility/Geometry/GraphSurfaceGeometry.lean#L144)
- [`ContinuousFlexibility.surfaceGram_heightGraph`](../ContinuousFlexibility/Geometry/GraphSurfaceGeometry.lean#L152)
- [`ContinuousFlexibility.surfaceGram_heightGraph_det`](../ContinuousFlexibility/Geometry/GraphSurfaceGeometry.lean#L165)
- [`ContinuousFlexibility.graphAreaDensity_eq_sqrt_gram_det`](../ContinuousFlexibility/Geometry/GraphSurfaceGeometry.lean#L172)
- [`ContinuousFlexibility.surfaceSecondForm_heightGraph`](../ContinuousFlexibility/Geometry/GraphSurfaceGeometry.lean#L178)
- [`ContinuousFlexibility.graphHessian_symm`](../ContinuousFlexibility/Geometry/GraphSurfaceGeometry.lean#L189)
- [`ContinuousFlexibility.surfaceSecondMatrix_heightGraph`](../ContinuousFlexibility/Geometry/GraphSurfaceGeometry.lean#L193)
- [`ContinuousFlexibility.surfaceGaussianCurvature_heightGraph`](../ContinuousFlexibility/Geometry/GraphSurfaceGeometry.lean#L202)
- [`ContinuousFlexibility.surfaceGaussianCurvature_heightGraph_coordinates`](../ContinuousFlexibility/Geometry/GraphSurfaceGeometry.lean#L217)
- [`ContinuousFlexibility.surfaceMeanCurvature_heightGraph`](../ContinuousFlexibility/Geometry/GraphSurfaceGeometry.lean#L227)
- [`ContinuousFlexibility.surfaceShapeMatrix_heightGraph_critical`](../ContinuousFlexibility/Geometry/GraphSurfaceGeometry.lean#L245)

[SurfaceGeometry.lean](../ContinuousFlexibility/Geometry/SurfaceGeometry.lean)：

- [`ContinuousFlexibility.surfaceBasis_zero`](../ContinuousFlexibility/Geometry/SurfaceGeometry.lean#L32)
- [`ContinuousFlexibility.surfaceBasis_one`](../ContinuousFlexibility/Geometry/SurfaceGeometry.lean#L33)
- [`ContinuousFlexibility.surfaceBasis_linearIndependent`](../ContinuousFlexibility/Geometry/SurfaceGeometry.lean#L62)
- [`ContinuousFlexibility.surfaceGram_dotProduct`](../ContinuousFlexibility/Geometry/SurfaceGeometry.lean#L72)
- [`ContinuousFlexibility.surfaceGram_posDef`](../ContinuousFlexibility/Geometry/SurfaceGeometry.lean#L83)
- [`ContinuousFlexibility.surfaceGram_det_pos`](../ContinuousFlexibility/Geometry/SurfaceGeometry.lean#L99)
- [`ContinuousFlexibility.surfaceGram_mul_shape`](../ContinuousFlexibility/Geometry/SurfaceGeometry.lean#L103)
- [`ContinuousFlexibility.surfaceShapeMatrix_unique`](../ContinuousFlexibility/Geometry/SurfaceGeometry.lean#L109)
- [`ContinuousFlexibility.surfaceFirstForm_symm`](../ContinuousFlexibility/Geometry/SurfaceGeometry.lean#L119)
- [`ContinuousFlexibility.surfaceSecondForm_symm`](../ContinuousFlexibility/Geometry/SurfaceGeometry.lean#L122)
- [`ContinuousFlexibility.surfaceSecondForm_eq_neg_normal_derivative`](../ContinuousFlexibility/Geometry/SurfaceGeometry.lean#L129)
- [`ContinuousFlexibility.surfaceSecondMatrix_neg_normal`](../ContinuousFlexibility/Geometry/SurfaceGeometry.lean#L147)
- [`ContinuousFlexibility.surfaceShapeMatrix_neg_normal`](../ContinuousFlexibility/Geometry/SurfaceGeometry.lean#L152)
- [`ContinuousFlexibility.surfaceGaussianCurvature_neg_normal`](../ContinuousFlexibility/Geometry/SurfaceGeometry.lean#L156)
- [`ContinuousFlexibility.surfaceMeanCurvature_neg_normal`](../ContinuousFlexibility/Geometry/SurfaceGeometry.lean#L160)
- [`ContinuousFlexibility.fderiv_rigidSurfaceMap`](../ContinuousFlexibility/Geometry/SurfaceGeometry.lean#L168)
- [`ContinuousFlexibility.secondFDeriv_rigidSurfaceMap`](../ContinuousFlexibility/Geometry/SurfaceGeometry.lean#L174)
- [`ContinuousFlexibility.surfaceFirstForm_rigidSurfaceMap`](../ContinuousFlexibility/Geometry/SurfaceGeometry.lean#L186)
- [`ContinuousFlexibility.surfaceSecondForm_rigidSurfaceMap`](../ContinuousFlexibility/Geometry/SurfaceGeometry.lean#L192)
- [`ContinuousFlexibility.IsUnitSurfaceNormal.rigidSurfaceMap`](../ContinuousFlexibility/Geometry/SurfaceGeometry.lean#L198)
- [`ContinuousFlexibility.surfaceGram_rigidSurfaceMap`](../ContinuousFlexibility/Geometry/SurfaceGeometry.lean#L205)
- [`ContinuousFlexibility.surfaceSecondMatrix_rigidSurfaceMap`](../ContinuousFlexibility/Geometry/SurfaceGeometry.lean#L211)
- [`ContinuousFlexibility.surfaceShapeMatrix_rigidSurfaceMap`](../ContinuousFlexibility/Geometry/SurfaceGeometry.lean#L217)
- [`ContinuousFlexibility.surfaceGaussianCurvature_rigidSurfaceMap`](../ContinuousFlexibility/Geometry/SurfaceGeometry.lean#L223)
- [`ContinuousFlexibility.surfaceMeanCurvature_rigidSurfaceMap`](../ContinuousFlexibility/Geometry/SurfaceGeometry.lean#L229)
- [`ContinuousFlexibility.affineSurfaceMap_eq_rigidSurfaceMap`](../ContinuousFlexibility/Geometry/SurfaceGeometry.lean#L235)
- [`ContinuousFlexibility.surfaceShapeMatrix_affineIsometry`](../ContinuousFlexibility/Geometry/SurfaceGeometry.lean#L243)
- [`ContinuousFlexibility.surfaceGaussianCurvature_affineIsometry`](../ContinuousFlexibility/Geometry/SurfaceGeometry.lean#L250)
- [`ContinuousFlexibility.surfaceMeanCurvature_affineIsometry`](../ContinuousFlexibility/Geometry/SurfaceGeometry.lean#L256)

[GraphFamilyCurvature.lean](../ContinuousFlexibility/Contracts/GraphFamilyCurvature.lean)：

- [`ContinuousFlexibility.IsometricGraphDevelopment.contDiff_physicalHeight`](../ContinuousFlexibility/Contracts/GraphFamilyCurvature.lean#L27)
- [`ContinuousFlexibility.IsometricGraphDevelopment.map_eq_physical_graph`](../ContinuousFlexibility/Contracts/GraphFamilyCurvature.lean#L31)
- [`ContinuousFlexibility.IsometricGraphDevelopment.fderiv_map_physical_graph`](../ContinuousFlexibility/Contracts/GraphFamilyCurvature.lean#L39)
- [`ContinuousFlexibility.IsometricGraphDevelopment.contDiff_upwardGraphNormal`](../ContinuousFlexibility/Contracts/GraphFamilyCurvature.lean#L55)
- [`ContinuousFlexibility.IsometricGraphDevelopment.upwardGraphNormal_isUnitSurfaceNormal`](../ContinuousFlexibility/Contracts/GraphFamilyCurvature.lean#L60)
- [`ContinuousFlexibility.IsometricGraphDevelopment.upwardGraphNormal_height_pos`](../ContinuousFlexibility/Contracts/GraphFamilyCurvature.lean#L70)
- [`ContinuousFlexibility.IsometricGraphDevelopment.rotationNormal_joint_smooth`](../ContinuousFlexibility/Contracts/GraphFamilyCurvature.lean#L81)
- [`ContinuousFlexibility.IsometricGraphDevelopment.fderiv_rotationFamily`](../ContinuousFlexibility/Contracts/GraphFamilyCurvature.lean#L104)
- [`ContinuousFlexibility.IsometricGraphDevelopment.rotationNormal_isUnitSurfaceNormal`](../ContinuousFlexibility/Contracts/GraphFamilyCurvature.lean#L117)
- [`ContinuousFlexibility.IsometricGraphDevelopment.rotationNormal_height_pos`](../ContinuousFlexibility/Contracts/GraphFamilyCurvature.lean#L130)
- [`ContinuousFlexibility.axialRotation_neg_add_one`](../ContinuousFlexibility/Contracts/GraphFamilyCurvature.lean#L137)
- [`ContinuousFlexibility.IsometricGraphDevelopment.rotationNormal_periodic`](../ContinuousFlexibility/Contracts/GraphFamilyCurvature.lean#L144)
- [`ContinuousFlexibility.IsometricGraphDevelopment.rotationNormal_zero`](../ContinuousFlexibility/Contracts/GraphFamilyCurvature.lean#L152)
- [`ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_eq_rigid_comp`](../ContinuousFlexibility/Contracts/GraphFamilyCurvature.lean#L157)
- [`ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_gaussianCurvature`](../ContinuousFlexibility/Contracts/GraphFamilyCurvature.lean#L166)
- [`ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_meanCurvature`](../ContinuousFlexibility/Contracts/GraphFamilyCurvature.lean#L188)
- [`ContinuousFlexibility.IsometricGraphDevelopment.gaussianCurvature_physical_graph`](../ContinuousFlexibility/Contracts/GraphFamilyCurvature.lean#L208)
- [`ContinuousFlexibility.IsometricGraphDevelopment.meanCurvature_physical_graph`](../ContinuousFlexibility/Contracts/GraphFamilyCurvature.lean#L229)

[SurfaceReparametrization.lean](../ContinuousFlexibility/Geometry/SurfaceReparametrization.lean)：

- [`ContinuousFlexibility.surfaceCLM_apply_decompose`](../ContinuousFlexibility/Geometry/SurfaceReparametrization.lean#L30)
- [`ContinuousFlexibility.surfaceLinearMatrix_mulVec`](../ContinuousFlexibility/Geometry/SurfaceReparametrization.lean#L37)
- [`ContinuousFlexibility.surfaceLinearMatrix_isUnit`](../ContinuousFlexibility/Geometry/SurfaceReparametrization.lean#L44)
- [`ContinuousFlexibility.surfaceJacobian_isUnit`](../ContinuousFlexibility/Geometry/SurfaceReparametrization.lean#L59)
- [`ContinuousFlexibility.surfaceJacobian_det_ne_zero`](../ContinuousFlexibility/Geometry/SurfaceReparametrization.lean#L63)
- [`ContinuousFlexibility.secondFDeriv_surface_comp`](../ContinuousFlexibility/Geometry/SurfaceReparametrization.lean#L68)
- [`ContinuousFlexibility.surfaceFirstForm_comp`](../ContinuousFlexibility/Geometry/SurfaceReparametrization.lean#L95)
- [`ContinuousFlexibility.IsUnitSurfaceNormal.comp`](../ContinuousFlexibility/Geometry/SurfaceReparametrization.lean#L103)
- [`ContinuousFlexibility.surfaceSecondForm_comp`](../ContinuousFlexibility/Geometry/SurfaceReparametrization.lean#L111)
- [`ContinuousFlexibility.surfaceFirstForm_coordinates`](../ContinuousFlexibility/Geometry/SurfaceReparametrization.lean#L120)
- [`ContinuousFlexibility.surfaceSecondForm_coordinates`](../ContinuousFlexibility/Geometry/SurfaceReparametrization.lean#L131)
- [`ContinuousFlexibility.surfaceGram_comp`](../ContinuousFlexibility/Geometry/SurfaceReparametrization.lean#L147)
- [`ContinuousFlexibility.surfaceGram_det_comp`](../ContinuousFlexibility/Geometry/SurfaceReparametrization.lean#L160)
- [`ContinuousFlexibility.surfaceSecondMatrix_comp`](../ContinuousFlexibility/Geometry/SurfaceReparametrization.lean#L168)
- [`ContinuousFlexibility.surfaceShapeMatrix_comp`](../ContinuousFlexibility/Geometry/SurfaceReparametrization.lean#L181)
- [`ContinuousFlexibility.surfaceGaussianCurvature_comp`](../ContinuousFlexibility/Geometry/SurfaceReparametrization.lean#L210)
- [`ContinuousFlexibility.surfaceMeanCurvature_comp`](../ContinuousFlexibility/Geometry/SurfaceReparametrization.lean#L220)

[SphereNormals.lean](../ContinuousFlexibility/Geometry/SphereNormals.lean)：

- [`ContinuousFlexibility.IsometricGraphDevelopment.rotationNormal_outside`](../ContinuousFlexibility/Geometry/SphereNormals.lean#L43)
- [`ContinuousFlexibility.markedCapNormal_eq_vertical_of_top_inner`](../ContinuousFlexibility/Geometry/SphereNormals.lean#L77)
- [`ContinuousFlexibility.markedCapNormal_rim_germ`](../ContinuousFlexibility/Geometry/SphereNormals.lean#L90)
- [`ContinuousFlexibility.markedCapNormal_capSphereRadialMap_rim_germ`](../ContinuousFlexibility/Geometry/SphereNormals.lean#L109)
- [`ContinuousFlexibility.contMDiffAt_sphereNorthNormal`](../ContinuousFlexibility/Geometry/SphereNormals.lean#L130)
- [`ContinuousFlexibility.sphereNorthNormal_equator_germ`](../ContinuousFlexibility/Geometry/SphereNormals.lean#L155)
- [`ContinuousFlexibility.sphereSouthNormal_equator_germ`](../ContinuousFlexibility/Geometry/SphereNormals.lean#L171)
- [`ContinuousFlexibility.sphereMarkedNormal_equator_germ`](../ContinuousFlexibility/Geometry/SphereNormals.lean#L183)
- [`ContinuousFlexibility.contMDiff_sphereMarkedNormal`](../ContinuousFlexibility/Geometry/SphereNormals.lean#L195)
- [`ContinuousFlexibility.sphereMarkedNormal_norm`](../ContinuousFlexibility/Geometry/SphereNormals.lean#L220)
- [`ContinuousFlexibility.sphereMarkedNormal_orthogonal`](../ContinuousFlexibility/Geometry/SphereNormals.lean#L230)
- [`ContinuousFlexibility.sphereMarkedNormal_periodic`](../ContinuousFlexibility/Geometry/SphereNormals.lean#L275)
- [`ContinuousFlexibility.sphereMarkedNormal_fixed_south`](../ContinuousFlexibility/Geometry/SphereNormals.lean#L284)
- [`ContinuousFlexibility.sphereMarkedNormal_north`](../ContinuousFlexibility/Geometry/SphereNormals.lean#L290)
- [`ContinuousFlexibility.sphereMarkedNormal_south`](../ContinuousFlexibility/Geometry/SphereNormals.lean#L299)
- [`ContinuousFlexibility.sphereMarkedNormal_fixed_closed_south`](../ContinuousFlexibility/Geometry/SphereNormals.lean#L312)
- [`ContinuousFlexibility.sphereMarkedNormal_smooth_unit`](../ContinuousFlexibility/Geometry/SphereNormals.lean#L321)

[SphereShapeCurvature.lean](../ContinuousFlexibility/Geometry/SphereShapeCurvature.lean)：

- [`ContinuousFlexibility.surfaceShapeMatrix_eq_matrix_of_weingarten`](../ContinuousFlexibility/Geometry/SphereShapeCurvature.lean#L37)
- [`ContinuousFlexibility.surfaceMeanCurvature_eq_trace_of_weingarten`](../ContinuousFlexibility/Geometry/SphereShapeCurvature.lean#L74)
- [`ContinuousFlexibility.surfaceGaussianCurvature_eq_det_of_weingarten`](../ContinuousFlexibility/Geometry/SphereShapeCurvature.lean#L86)
- [`ContinuousFlexibility.sphere_fderiv_comp_param`](../ContinuousFlexibility/Geometry/SphereShapeCurvature.lean#L106)
- [`ContinuousFlexibility.sphereParametricTangentEquiv_toContinuousLinearMap`](../ContinuousFlexibility/Geometry/SphereShapeCurvature.lean#L130)
- [`ContinuousFlexibility.sphereShapeOperator_matrix_in_chart`](../ContinuousFlexibility/Geometry/SphereShapeCurvature.lean#L141)
- [`ContinuousFlexibility.sphereShapeOperator_trace_in_chart`](../ContinuousFlexibility/Geometry/SphereShapeCurvature.lean#L180)
- [`ContinuousFlexibility.sphereShapeOperator_det_in_chart`](../ContinuousFlexibility/Geometry/SphereShapeCurvature.lean#L211)
- [`ContinuousFlexibility.contMDiff_sphereMeanCurvature`](../ContinuousFlexibility/Geometry/SphereShapeCurvature.lean#L243)
- [`ContinuousFlexibility.sphereMeanCurvature_north`](../ContinuousFlexibility/Geometry/SphereShapeCurvature.lean#L252)
- [`ContinuousFlexibility.sphereMeanCurvature_south`](../ContinuousFlexibility/Geometry/SphereShapeCurvature.lean#L272)
- [`ContinuousFlexibility.sphereShapeOperator_det_north`](../ContinuousFlexibility/Geometry/SphereShapeCurvature.lean#L292)
- [`ContinuousFlexibility.sphereShapeOperator_det_south`](../ContinuousFlexibility/Geometry/SphereShapeCurvature.lean#L312)
- [`ContinuousFlexibility.sphereShapeOperator_det_eq_gaussian`](../ContinuousFlexibility/Geometry/SphereShapeCurvature.lean#L334)
- [`ContinuousFlexibility.contMDiff_sphereGaussianCurvature`](../ContinuousFlexibility/Geometry/SphereShapeCurvature.lean#L349)

[SphereShapeOperator.lean](../ContinuousFlexibility/Geometry/SphereShapeOperator.lean)：

- [`ContinuousFlexibility.sphere_mvfderiv_normal_inner_zero`](../ContinuousFlexibility/Geometry/SphereShapeOperator.lean#L94)
- [`ContinuousFlexibility.sphereDifferential_range_eq_normal`](../ContinuousFlexibility/Geometry/SphereShapeOperator.lean#L117)
- [`ContinuousFlexibility.sphereShapeOperator_weingarten`](../ContinuousFlexibility/Geometry/SphereShapeOperator.lean#L135)
- [`ContinuousFlexibility.sphereShapeOperator_contMDiff`](../ContinuousFlexibility/Geometry/SphereShapeOperator.lean#L172)
- [`ContinuousFlexibility.sphereShapeOperator_self_adjoint`](../ContinuousFlexibility/Geometry/SphereShapeOperator.lean#L327)
- [`ContinuousFlexibility.sphereEnd_trace_half_contMDiff`](../ContinuousFlexibility/Geometry/SphereShapeOperator.lean#L342)
- [`ContinuousFlexibility.sphereEnd_det_contMDiff`](../ContinuousFlexibility/Geometry/SphereShapeOperator.lean#L378)
- [`ContinuousFlexibility.sphereShapeOperator_trace_contMDiff`](../ContinuousFlexibility/Geometry/SphereShapeOperator.lean#L422)
- [`ContinuousFlexibility.sphereShapeOperator_det_contMDiff`](../ContinuousFlexibility/Geometry/SphereShapeOperator.lean#L433)


<a id="d02"></a>
## D02 曲面面积和有向积分接口

**状态：** 已有部分已编译子结果。**分支：** 几何闭合。主定理必要节点。

**数学陈述：** 建立参数化/像曲面面积对应、有限图册积分独立性、分块拼接及重参数/环境等距换元，并定义实际的∫H_out dA。

**证明提纲：** 以诱导黎曼面积密度在图册中积分，证明与像曲面面积的一致性；法向由实际内部区域识别后应用。

**直接依赖：** [D01](#d01)

**论文定位：** [02-geometry.tex:258–268](../paper/flexible-surface-rewrite/02-geometry.tex#L258)；[01-introduction.tex:33–39](../paper/flexible-surface-rewrite/01-introduction.tex#L33)

**目标文件：** `ContinuousFlexibility/Geometry/D02.lean`（节点组织目标；实际已存在的证明文件见下方，整个节点尚未完成）

**验收条件：**

- 面积不是任意常值别名
- 有向平均曲率不是|H|
- 重叠/缝口不被重复计数

**已经完成的子结果：**

- 真实图盘Gram密度积分、实际Hausdorff图像测度、旋转测度换元及构造法向下的整球有向平均曲率积分均已编译；包括ambient代表独立性和实际可积性。

**仍待闭合的义务：**

- 将已证明的真实整球积分接到同一完整标记inside的向外法向及最终ClosedBending见证。

**优先核查程度：** high（任务风险标记，不是已发现错误）

**现有 Lean 证明：**

[GraphDiskIntegrals.lean](../ContinuousFlexibility/Contracts/GraphDiskIntegrals.lean)：

- [`ContinuousFlexibility.linearMap_det_eq_surfaceLinearMatrix`](../ContinuousFlexibility/Contracts/GraphDiskIntegrals.lean#L31)
- [`ContinuousFlexibility.planarRotation_surfaceJacobian_det`](../ContinuousFlexibility/Contracts/GraphDiskIntegrals.lean#L40)
- [`ContinuousFlexibility.planarRotation_linearMap_det`](../ContinuousFlexibility/Contracts/GraphDiskIntegrals.lean#L49)
- [`ContinuousFlexibility.measurePreserving_planarRotation`](../ContinuousFlexibility/Contracts/GraphDiskIntegrals.lean#L54)
- [`ContinuousFlexibility.integral_comp_planarRotation_closedDisk`](../ContinuousFlexibility/Contracts/GraphDiskIntegrals.lean#L64)
- [`ContinuousFlexibility.IsometricGraphDevelopment.surfaceGram_rotationFamily`](../ContinuousFlexibility/Contracts/GraphDiskIntegrals.lean#L73)
- [`ContinuousFlexibility.IsometricGraphDevelopment.surfaceGram_comp_planarRotation`](../ContinuousFlexibility/Contracts/GraphDiskIntegrals.lean#L82)
- [`ContinuousFlexibility.IsometricGraphDevelopment.areaDensity_rotationFamily`](../ContinuousFlexibility/Contracts/GraphDiskIntegrals.lean#L99)
- [`ContinuousFlexibility.IsometricGraphDevelopment.areaDensity_planarRotation`](../ContinuousFlexibility/Contracts/GraphDiskIntegrals.lean#L104)
- [`ContinuousFlexibility.continuous_surfaceParamAreaDensity`](../ContinuousFlexibility/Contracts/GraphDiskIntegrals.lean#L116)
- [`ContinuousFlexibility.continuous_heightGraph_meanCurvature`](../ContinuousFlexibility/Contracts/GraphDiskIntegrals.lean#L126)
- [`ContinuousFlexibility.IsometricGraphDevelopment.continuous_upwardMeanCurvature`](../ContinuousFlexibility/Contracts/GraphDiskIntegrals.lean#L157)
- [`ContinuousFlexibility.IsometricGraphDevelopment.areaDensity_integrableOn_closedDisk`](../ContinuousFlexibility/Contracts/GraphDiskIntegrals.lean#L168)
- [`ContinuousFlexibility.IsometricGraphDevelopment.upwardMeanIntegrand_integrableOn_closedDisk`](../ContinuousFlexibility/Contracts/GraphDiskIntegrals.lean#L175)
- [`ContinuousFlexibility.IsometricGraphDevelopment.graphDiskArea_eq_zeroPhase`](../ContinuousFlexibility/Contracts/GraphDiskIntegrals.lean#L199)
- [`ContinuousFlexibility.IsometricGraphDevelopment.graphDiskUpwardMeanIntegral_eq_zeroPhase`](../ContinuousFlexibility/Contracts/GraphDiskIntegrals.lean#L207)


<a id="g01"></a>
## G01 平坦端点扩大为真实开领圈

**状态：** 已有部分已编译子结果。**分支：** 几何闭合。主定理必要节点。

**数学陈述：** 扩大环带，把w以零、z以各自端常数延拓，得到光滑半转对称数据，保留正定平坦余度量，并在两端实际开领圈上w=0,z=c_L/c_R。

**证明提纲：** 处理全部角向混合jets，证明扩展区为欧氏余度量；实例化AnnularSolution。

**直接依赖：** [N12](#n12), [W03](#w03), [S03](#s03)

**论文定位：** [02-geometry.tex:9–17](../paper/flexible-surface-rewrite/02-geometry.tex#L9)，`def:flat-endpoint`；[10-endpoint-and-sphere.tex:304–317](../paper/flexible-surface-rewrite/10-endpoint-and-sphere.tex#L304)

**目标文件：** `ContinuousFlexibility/Geometry/G01.lean`（节点组织目标；实际已存在的证明文件见下方，整个节点尚未完成）

**验收条件：**

- 真实开集相等，不只是边界jets趋零
- c_L与c_R独立
- 平坦和正性在拼接点也成立

**已经完成的子结果：**

- 实际constant/zero germs推出真实height jets、D=1和residual=0
- 从全局光滑平坦延拓的同一Core，将界扩大为a/2与b+1；真实open flat collars、正性、残差与非径向witness均保留

**仍待闭合的义务：**

- 由N12与加权空间实际产出这里所需的全局联合光滑Core延拓；Core存在性未证明

**现有 Lean 证明：**

[FlatCollar.lean](../ContinuousFlexibility/Scalar/FlatCollar.lean)：

- [`ContinuousFlexibility.height_jets_eq_zero_of_constant_germ`](../ContinuousFlexibility/Scalar/FlatCollar.lean#L21)
- [`ContinuousFlexibility.profileEnergy_eq_one_of_zero_germ`](../ContinuousFlexibility/Scalar/FlatCollar.lean#L39)
- [`ContinuousFlexibility.flat_germ_discriminant_eq_one`](../ContinuousFlexibility/Scalar/FlatCollar.lean#L47)
- [`ContinuousFlexibility.flat_germ_curvatureNumerator_eq_zero`](../ContinuousFlexibility/Scalar/FlatCollar.lean#L55)
- [`ContinuousFlexibility.flat_germ_residual_eq_zero`](../ContinuousFlexibility/Scalar/FlatCollar.lean#L64)

[Annular.lean](../ContinuousFlexibility/Contracts/Annular.lean)：

- [`ContinuousFlexibility.FlatAnnularCore.enlarge_w`](../ContinuousFlexibility/Contracts/Annular.lean#L125)
- [`ContinuousFlexibility.FlatAnnularCore.enlarge_z`](../ContinuousFlexibility/Contracts/Annular.lean#L126)
- [`ContinuousFlexibility.AnnularSolution.left_collar`](../ContinuousFlexibility/Contracts/Annular.lean#L128)
- [`ContinuousFlexibility.AnnularSolution.right_collar`](../ContinuousFlexibility/Contracts/Annular.lean#L133)
- [`ContinuousFlexibility.AnnularSolution.left_collar_nonempty`](../ContinuousFlexibility/Contracts/Annular.lean#L138)
- [`ContinuousFlexibility.AnnularSolution.right_collar_nonempty`](../ContinuousFlexibility/Contracts/Annular.lean#L141)
- [`ContinuousFlexibility.AnnularSolution.nonradial_on_annulus`](../ContinuousFlexibility/Contracts/Annular.lean#L144)


<a id="g02"></a>
## G02 填盘后的归一化平面发展

**状态：** 已有部分已编译子结果。**分支：** 几何闭合。主定理必要节点。

**数学陈述：** 对任意AnnularSolution A，填内圈为平盘，在其光滑正定平坦余度量下构造定向局部等距P，外领圈P=id。后续几何节点共享同一A及其选择的P、cap、Fτ。

**证明提纲：** 构造全局Cartesian余标架，闭连接取primitive旋转为闭余标架，再积分得到P。利用填盘凸性适配Poincaré引理。

**直接依赖：** [C00](#c00), [S03](#s03)

**论文定位：** [02-geometry.tex:69–94](../paper/flexible-surface-rewrite/02-geometry.tex#L69)，`lem:disk-development`

**目标文件：** `ContinuousFlexibility/Geometry/G02.lean`（节点组织目标；实际已存在的证明文件见下方，整个节点尚未完成）

**验收条件：**

- 中心处光滑性不以极坐标公式冒充
- global coframe与外圈归一化实际证明
- 闭连接到全局primitive没有残留holonomy

**已经完成的子结果：**

- 由π周期极坐标高度实际构造全局Cartesian高度，支割线与原点均C∞；保留源同半径非径向witness
- 实际Cartesian余度量全局C∞正定、内外标准，真实polar微分拉回等于原g-dz²
- 全局Cholesky coframe与真实Cartan连接，由same metric/SO2与实际拉回证明Cartesian连接闭；没有新增flatness输入
- 从Core实际积分构造外域归一化P、全局双向C∞逆、圆盘保持、完整双线性余度量拉回；实际Jacobian全域为正

**仍待闭合的义务：**

- 尚未在已构造的analytic Core见证上实例化，因为Core存在性属于N12未完成

**现有 Lean 证明：**

[RotatedCoframe.lean](../ContinuousFlexibility/Geometry/RotatedCoframe.lean)：

- [`ContinuousFlexibility.exteriorCoefficient_coordinateDifferential`](../ContinuousFlexibility/Geometry/RotatedCoframe.lean#L57)
- [`ContinuousFlexibility.contDiffAt_rotatedCoframeOne_radial`](../ContinuousFlexibility/Geometry/RotatedCoframe.lean#L61)
- [`ContinuousFlexibility.contDiffAt_rotatedCoframeOne_angular`](../ContinuousFlexibility/Geometry/RotatedCoframe.lean#L67)
- [`ContinuousFlexibility.contDiffAt_rotatedCoframeTwo_radial`](../ContinuousFlexibility/Geometry/RotatedCoframe.lean#L73)
- [`ContinuousFlexibility.contDiffAt_rotatedCoframeTwo_angular`](../ContinuousFlexibility/Geometry/RotatedCoframe.lean#L79)
- [`ContinuousFlexibility.radialPartial_cos`](../ContinuousFlexibility/Geometry/RotatedCoframe.lean#L85)
- [`ContinuousFlexibility.angularPartial_cos`](../ContinuousFlexibility/Geometry/RotatedCoframe.lean#L92)
- [`ContinuousFlexibility.radialPartial_sin`](../ContinuousFlexibility/Geometry/RotatedCoframe.lean#L99)
- [`ContinuousFlexibility.angularPartial_sin`](../ContinuousFlexibility/Geometry/RotatedCoframe.lean#L106)
- [`ContinuousFlexibility.exteriorCoefficient_rotatedCoframeOne`](../ContinuousFlexibility/Geometry/RotatedCoframe.lean#L114)
- [`ContinuousFlexibility.exteriorCoefficient_rotatedCoframeTwo`](../ContinuousFlexibility/Geometry/RotatedCoframe.lean#L136)
- [`ContinuousFlexibility.rotatedCoframeOne_closed`](../ContinuousFlexibility/Geometry/RotatedCoframe.lean#L158)
- [`ContinuousFlexibility.rotatedCoframeTwo_closed`](../ContinuousFlexibility/Geometry/RotatedCoframe.lean#L171)
- [`ContinuousFlexibility.rotatedCoframe_square_sum`](../ContinuousFlexibility/Geometry/RotatedCoframe.lean#L184)
- [`ContinuousFlexibility.rotatedCoframe_wedge_eq`](../ContinuousFlexibility/Geometry/RotatedCoframe.lean#L197)
- [`ContinuousFlexibility.rotatedCoframe_wedge_ne_zero`](../ContinuousFlexibility/Geometry/RotatedCoframe.lean#L207)
- [`ContinuousFlexibility.rotatedCoframe_wedge_pos`](../ContinuousFlexibility/Geometry/RotatedCoframe.lean#L213)

[GaugeConnection.lean](../ContinuousFlexibility/Geometry/GaugeConnection.lean)：

- [`ContinuousFlexibility.exteriorCoefficient_subtractPlaneOneForm`](../ContinuousFlexibility/Geometry/GaugeConnection.lean#L27)
- [`ContinuousFlexibility.rotatedCoframeOne_cartan_gauge`](../ContinuousFlexibility/Geometry/GaugeConnection.lean#L40)
- [`ContinuousFlexibility.rotatedCoframeTwo_cartan_gauge`](../ContinuousFlexibility/Geometry/GaugeConnection.lean#L55)
- [`ContinuousFlexibility.exteriorCoefficient_gaugeConnection`](../ContinuousFlexibility/Geometry/GaugeConnection.lean#L71)
- [`ContinuousFlexibility.gaugeConnection_closed_iff`](../ContinuousFlexibility/Geometry/GaugeConnection.lean#L82)
- [`ContinuousFlexibility.gaugeConnection_angle_radial`](../ContinuousFlexibility/Geometry/GaugeConnection.lean#L90)
- [`ContinuousFlexibility.gaugeConnection_angle_angular`](../ContinuousFlexibility/Geometry/GaugeConnection.lean#L95)
- [`ContinuousFlexibility.exteriorCoefficient_gaugeConnection_angle`](../ContinuousFlexibility/Geometry/GaugeConnection.lean#L100)

[Primitive.lean](../ContinuousFlexibility/Geometry/Primitive.lean)：

- [`ContinuousFlexibility.PlaneOneForm.toCLM_apply`](../ContinuousFlexibility/Geometry/Primitive.lean#L29)
- [`ContinuousFlexibility.PlaneOneForm.hasFDerivAt_toCLM`](../ContinuousFlexibility/Geometry/Primitive.lean#L35)
- [`ContinuousFlexibility.PlaneOneForm.differentiableAt_toCLM`](../ContinuousFlexibility/Geometry/Primitive.lean#L43)
- [`ContinuousFlexibility.PlaneOneForm.fderiv_toCLM_apply`](../ContinuousFlexibility/Geometry/Primitive.lean#L48)
- [`ContinuousFlexibility.polarCLM_apply_decompose`](../ContinuousFlexibility/Geometry/Primitive.lean#L57)
- [`ContinuousFlexibility.PlaneOneForm.fderiv_toCLM_skew`](../ContinuousFlexibility/Geometry/Primitive.lean#L66)
- [`ContinuousFlexibility.exteriorCoefficient_eq_zero_iff_fderiv_toCLM_symmetric`](../ContinuousFlexibility/Geometry/Primitive.lean#L79)
- [`ContinuousFlexibility.PlaneOneForm.contDiffAt_toCLM`](../ContinuousFlexibility/Geometry/Primitive.lean#L92)
- [`ContinuousFlexibility.exists_primitive_of_closed`](../ContinuousFlexibility/Geometry/Primitive.lean#L98)
- [`ContinuousFlexibility.exists_primitive_of_closed_eq_zero`](../ContinuousFlexibility/Geometry/Primitive.lean#L112)
- [`ContinuousFlexibility.contDiffAt_of_primitive`](../ContinuousFlexibility/Geometry/Primitive.lean#L124)
- [`ContinuousFlexibility.contDiffAt_of_primitive_infty`](../ContinuousFlexibility/Geometry/Primitive.lean#L133)
- [`ContinuousFlexibility.exists_development_of_closed_coframe`](../ContinuousFlexibility/Geometry/Primitive.lean#L145)
- [`ContinuousFlexibility.exists_smooth_development_of_closed_coframe`](../ContinuousFlexibility/Geometry/Primitive.lean#L160)
- [`ContinuousFlexibility.development_fderiv_apply`](../ContinuousFlexibility/Geometry/Primitive.lean#L182)
- [`ContinuousFlexibility.development_derivative_square_sum`](../ContinuousFlexibility/Geometry/Primitive.lean#L189)

[LocalInverse.lean](../ContinuousFlexibility/Geometry/LocalInverse.lean)：

- [`ContinuousFlexibility.linear_injective_of_remainder_metric`](../ContinuousFlexibility/Geometry/LocalInverse.lean#L24)
- [`ContinuousFlexibility.linear_bijective_of_remainder_metric`](../ContinuousFlexibility/Geometry/LocalInverse.lean#L49)
- [`ContinuousFlexibility.planeLinearEquivOfBijective_coe`](../ContinuousFlexibility/Geometry/LocalInverse.lean#L62)
- [`ContinuousFlexibility.fderiv_injective_of_remainder_metric`](../ContinuousFlexibility/Geometry/LocalInverse.lean#L69)
- [`ContinuousFlexibility.fderiv_bijective_of_remainder_metric`](../ContinuousFlexibility/Geometry/LocalInverse.lean#L77)
- [`ContinuousFlexibility.exists_fderiv_linearEquiv_of_remainder_metric`](../ContinuousFlexibility/Geometry/LocalInverse.lean#L85)
- [`ContinuousFlexibility.exists_localInverse_of_fderiv_bijective`](../ContinuousFlexibility/Geometry/LocalInverse.lean#L98)
- [`ContinuousFlexibility.exists_localInverse_of_remainder_metric`](../ContinuousFlexibility/Geometry/LocalInverse.lean#L118)
- [`ContinuousFlexibility.exists_smooth_localInverse_of_remainder_metric`](../ContinuousFlexibility/Geometry/LocalInverse.lean#L132)
- [`ContinuousFlexibility.exists_open_injOn_of_remainder_metric`](../ContinuousFlexibility/Geometry/LocalInverse.lean#L144)

[FlatDevelopment.lean](../ContinuousFlexibility/Geometry/FlatDevelopment.lean)：

- [`ContinuousFlexibility.contDiffAt_heightConnection`](../ContinuousFlexibility/Geometry/FlatDevelopment.lean#L26)
- [`ContinuousFlexibility.contDiffAt_heightCoframe`](../ContinuousFlexibility/Geometry/FlatDevelopment.lean#L55)
- [`ContinuousFlexibility.exists_smooth_remainder_development`](../ContinuousFlexibility/Geometry/FlatDevelopment.lean#L70)
- [`ContinuousFlexibility.exists_locally_invertible_remainder_development`](../ContinuousFlexibility/Geometry/FlatDevelopment.lean#L142)
- [`ContinuousFlexibility.coordinate_pair_eq_remainder_of_square_sum`](../ContinuousFlexibility/Geometry/FlatDevelopment.lean#L176)
- [`ContinuousFlexibility.development_pullback_bilinear`](../ContinuousFlexibility/Geometry/FlatDevelopment.lean#L190)

[FormPullback.lean](../ContinuousFlexibility/Scalar/FormPullback.lean)：

- [`ContinuousFlexibility.toCLM_pullbackPlaneOneForm`](../ContinuousFlexibility/Scalar/FormPullback.lean#L33)
- [`ContinuousFlexibility.formValue_pullbackPlaneOneForm`](../ContinuousFlexibility/Scalar/FormPullback.lean#L43)
- [`ContinuousFlexibility.wedgeCoefficient_pullbackPlaneOneForm`](../ContinuousFlexibility/Scalar/FormPullback.lean#L52)
- [`ContinuousFlexibility.fderiv_pullbackPlaneOneForm_coefficient`](../ContinuousFlexibility/Scalar/FormPullback.lean#L63)
- [`ContinuousFlexibility.exteriorCoefficient_pullbackPlaneOneForm`](../ContinuousFlexibility/Scalar/FormPullback.lean#L92)
- [`ContinuousFlexibility.exteriorCoefficient_pullback_closed_iff`](../ContinuousFlexibility/Scalar/FormPullback.lean#L112)
- [`ContinuousFlexibility.contDiffAt_pullbackPlaneOneForm`](../ContinuousFlexibility/Scalar/FormPullback.lean#L124)

[CartesianHeight.lean](../ContinuousFlexibility/Contracts/CartesianHeight.lean)：

- [`ContinuousFlexibility.contDiffAt_complexArg_real`](../ContinuousFlexibility/Contracts/CartesianHeight.lean#L26)
- [`ContinuousFlexibility.polarHeightOnComplex_neg`](../ContinuousFlexibility/Contracts/CartesianHeight.lean#L33)
- [`ContinuousFlexibility.contDiffAt_polarHeightOnComplex_slit`](../ContinuousFlexibility/Contracts/CartesianHeight.lean#L63)
- [`ContinuousFlexibility.contDiffAt_polarHeightOnComplex_of_ne_zero`](../ContinuousFlexibility/Contracts/CartesianHeight.lean#L71)
- [`ContinuousFlexibility.FlatAnnularCore.complexHeight_left`](../ContinuousFlexibility/Contracts/CartesianHeight.lean#L89)
- [`ContinuousFlexibility.FlatAnnularCore.complexHeight_right`](../ContinuousFlexibility/Contracts/CartesianHeight.lean#L93)
- [`ContinuousFlexibility.FlatAnnularCore.contDiff_complexHeight`](../ContinuousFlexibility/Contracts/CartesianHeight.lean#L97)
- [`ContinuousFlexibility.FlatAnnularCore.contDiff_cartesianHeight`](../ContinuousFlexibility/Contracts/CartesianHeight.lean#L111)
- [`ContinuousFlexibility.FlatAnnularCore.cartesianHeight_left`](../ContinuousFlexibility/Contracts/CartesianHeight.lean#L115)
- [`ContinuousFlexibility.FlatAnnularCore.cartesianHeight_right`](../ContinuousFlexibility/Contracts/CartesianHeight.lean#L119)
- [`ContinuousFlexibility.FlatAnnularCore.cartesianHeight_even`](../ContinuousFlexibility/Contracts/CartesianHeight.lean#L123)
- [`ContinuousFlexibility.complex_polarPosition`](../ContinuousFlexibility/Contracts/CartesianHeight.lean#L132)
- [`ContinuousFlexibility.norm_polarToComplex`](../ContinuousFlexibility/Contracts/CartesianHeight.lean#L136)
- [`ContinuousFlexibility.cartesianRadius_polarPosition`](../ContinuousFlexibility/Contracts/CartesianHeight.lean#L140)
- [`ContinuousFlexibility.polarHeightOnComplex_polarToComplex`](../ContinuousFlexibility/Contracts/CartesianHeight.lean#L146)
- [`ContinuousFlexibility.FlatAnnularCore.cartesianHeight_polarPosition`](../ContinuousFlexibility/Contracts/CartesianHeight.lean#L161)
- [`ContinuousFlexibility.FlatAnnularCore.cartesianHeight_nonradial`](../ContinuousFlexibility/Contracts/CartesianHeight.lean#L169)

[CartesianMetric.lean](../ContinuousFlexibility/Contracts/CartesianMetric.lean)：

- [`ContinuousFlexibility.polarJacobian_apply`](../ContinuousFlexibility/Contracts/CartesianMetric.lean#L31)
- [`ContinuousFlexibility.hasFDerivAt_polarMap`](../ContinuousFlexibility/Contracts/CartesianMetric.lean#L37)
- [`ContinuousFlexibility.polarJacobian_bijective`](../ContinuousFlexibility/Contracts/CartesianMetric.lean#L54)
- [`ContinuousFlexibility.coordinate_pair_polarJacobian`](../ContinuousFlexibility/Contracts/CartesianMetric.lean#L93)
- [`ContinuousFlexibility.coordinate_pair_position_polarJacobian`](../ContinuousFlexibility/Contracts/CartesianMetric.lean#L104)
- [`ContinuousFlexibility.cartesianMetric_polar_pullback`](../ContinuousFlexibility/Contracts/CartesianMetric.lean#L113)
- [`ContinuousFlexibility.FlatAnnularCore.cartesianHeight_polar_derivative`](../ContinuousFlexibility/Contracts/CartesianMetric.lean#L125)
- [`ContinuousFlexibility.FlatAnnularCore.cartesianRemainder_polar_pullback`](../ContinuousFlexibility/Contracts/CartesianMetric.lean#L139)

[CartesianMetricRegularity.lean](../ContinuousFlexibility/Contracts/CartesianMetricRegularity.lean)：

- [`ContinuousFlexibility.continuous_cartesianRadius`](../ContinuousFlexibility/Contracts/CartesianMetricRegularity.lean#L22)
- [`ContinuousFlexibility.cartesianRadius_pos`](../ContinuousFlexibility/Contracts/CartesianMetricRegularity.lean#L25)
- [`ContinuousFlexibility.contDiffAt_cartesianRadius`](../ContinuousFlexibility/Contracts/CartesianMetricRegularity.lean#L32)
- [`ContinuousFlexibility.polarMap_cartesianCoordinates`](../ContinuousFlexibility/Contracts/CartesianMetricRegularity.lean#L37)
- [`ContinuousFlexibility.FlatAnnularCore.cartesianHeight_germ_left`](../ContinuousFlexibility/Contracts/CartesianMetricRegularity.lean#L47)
- [`ContinuousFlexibility.FlatAnnularCore.cartesianHeight_germ_right`](../ContinuousFlexibility/Contracts/CartesianMetricRegularity.lean#L54)
- [`ContinuousFlexibility.cartesianRemainder_eq_euclidean_of_zero_jets`](../ContinuousFlexibility/Contracts/CartesianMetricRegularity.lean#L61)
- [`ContinuousFlexibility.FlatAnnularCore.cartesianRemainder_left`](../ContinuousFlexibility/Contracts/CartesianMetricRegularity.lean#L67)
- [`ContinuousFlexibility.FlatAnnularCore.cartesianRemainder_right`](../ContinuousFlexibility/Contracts/CartesianMetricRegularity.lean#L74)
- [`ContinuousFlexibility.coordinateEuclideanPair_self_pos`](../ContinuousFlexibility/Contracts/CartesianMetricRegularity.lean#L81)
- [`ContinuousFlexibility.remainderBilinear_self`](../ContinuousFlexibility/Contracts/CartesianMetricRegularity.lean#L89)
- [`ContinuousFlexibility.FlatAnnularCore.cartesianRemainder_pos`](../ContinuousFlexibility/Contracts/CartesianMetricRegularity.lean#L94)
- [`ContinuousFlexibility.FlatAnnularCore.contDiff_cartesianProfileFactor`](../ContinuousFlexibility/Contracts/CartesianMetricRegularity.lean#L122)
- [`ContinuousFlexibility.cartesianRemainderA_eq`](../ContinuousFlexibility/Contracts/CartesianMetricRegularity.lean#L138)
- [`ContinuousFlexibility.cartesianRemainderB_eq`](../ContinuousFlexibility/Contracts/CartesianMetricRegularity.lean#L145)
- [`ContinuousFlexibility.cartesianRemainderC_eq`](../ContinuousFlexibility/Contracts/CartesianMetricRegularity.lean#L151)
- [`ContinuousFlexibility.cartesianRemainder_matrix`](../ContinuousFlexibility/Contracts/CartesianMetricRegularity.lean#L158)
- [`ContinuousFlexibility.FlatAnnularCore.cartesianRemainderA_pos`](../ContinuousFlexibility/Contracts/CartesianMetricRegularity.lean#L171)
- [`ContinuousFlexibility.FlatAnnularCore.cartesianRemainder_det_pos`](../ContinuousFlexibility/Contracts/CartesianMetricRegularity.lean#L175)
- [`ContinuousFlexibility.FlatAnnularCore.contDiff_cartesianRemainder_entries`](../ContinuousFlexibility/Contracts/CartesianMetricRegularity.lean#L193)
- [`ContinuousFlexibility.FlatAnnularCore.cartesianRemainder_standard_right`](../ContinuousFlexibility/Contracts/CartesianMetricRegularity.lean#L221)
- [`ContinuousFlexibility.FlatAnnularCore.cartesianRemainder_standard_left`](../ContinuousFlexibility/Contracts/CartesianMetricRegularity.lean#L229)

[CartesianFlatness.lean](../ContinuousFlexibility/Contracts/CartesianFlatness.lean)：

- [`ContinuousFlexibility.contDiff_polarMap`](../ContinuousFlexibility/Contracts/CartesianFlatness.lean#L23)
- [`ContinuousFlexibility.planeJacobian_polarMap`](../ContinuousFlexibility/Contracts/CartesianFlatness.lean#L28)
- [`ContinuousFlexibility.FlatAnnularCore.contDiff_cartesianRemainderCoframe`](../ContinuousFlexibility/Contracts/CartesianFlatness.lean#L39)
- [`ContinuousFlexibility.FlatAnnularCore.contDiff_cartesianRemainderConnection`](../ContinuousFlexibility/Contracts/CartesianFlatness.lean#L53)
- [`ContinuousFlexibility.FlatAnnularCore.cartesianCoframe_polar_same_metric`](../ContinuousFlexibility/Contracts/CartesianFlatness.lean#L63)
- [`ContinuousFlexibility.FlatAnnularCore.cartesianRemainder_entries_germ_left`](../ContinuousFlexibility/Contracts/CartesianFlatness.lean#L85)
- [`ContinuousFlexibility.FlatAnnularCore.cartesianRemainderConnection_zero_left`](../ContinuousFlexibility/Contracts/CartesianFlatness.lean#L100)
- [`ContinuousFlexibility.FlatAnnularCore.cartesianRemainderConnection_germ_zero_left`](../ContinuousFlexibility/Contracts/CartesianFlatness.lean#L107)
- [`ContinuousFlexibility.FlatAnnularCore.cartesianRemainderConnection_closed_left`](../ContinuousFlexibility/Contracts/CartesianFlatness.lean#L119)
- [`ContinuousFlexibility.FlatAnnularCore.cartesianRemainderConnection_closed_polar`](../ContinuousFlexibility/Contracts/CartesianFlatness.lean#L129)
- [`ContinuousFlexibility.FlatAnnularCore.cartesianRemainderConnection_closed`](../ContinuousFlexibility/Contracts/CartesianFlatness.lean#L170)

[PlanarDevelopment.lean](../ContinuousFlexibility/Contracts/PlanarDevelopment.lean)：

- [`ContinuousFlexibility.coordinate_pair_eq_matrix_of_square_sum`](../ContinuousFlexibility/Contracts/PlanarDevelopment.lean#L20)
- [`ContinuousFlexibility.FlatAnnularCore.exists_planarDevelopment`](../ContinuousFlexibility/Contracts/PlanarDevelopment.lean#L36)
- [`ContinuousFlexibility.image_larger_disk_of_normalized_homeomorph`](../ContinuousFlexibility/Contracts/PlanarDevelopment.lean#L66)

[CartesianCoframe.lean](../ContinuousFlexibility/Geometry/CartesianCoframe.lean)：

- [`ContinuousFlexibility.PlaneOneForm.ext_components`](../ContinuousFlexibility/Geometry/CartesianCoframe.lean#L16)
- [`ContinuousFlexibility.PlaneOneForm.toCLM_eq_zero_of_components`](../ContinuousFlexibility/Geometry/CartesianCoframe.lean#L29)
- [`ContinuousFlexibility.coframeLinearMap_eq_id_of_standard`](../ContinuousFlexibility/Geometry/CartesianCoframe.lean#L34)
- [`ContinuousFlexibility.coframeLinearMap_injective`](../ContinuousFlexibility/Geometry/CartesianCoframe.lean#L43)
- [`ContinuousFlexibility.coframeLinearMap_bijective`](../ContinuousFlexibility/Geometry/CartesianCoframe.lean#L76)
- [`ContinuousFlexibility.fderiv_bijective_of_hasFDerivAt_coframe`](../ContinuousFlexibility/Geometry/CartesianCoframe.lean#L84)

[CartesianDevelopment.lean](../ContinuousFlexibility/Geometry/CartesianDevelopment.lean)：

- [`ContinuousFlexibility.exists_global_smooth_primitive`](../ContinuousFlexibility/Geometry/CartesianDevelopment.lean#L38)
- [`ContinuousFlexibility.exists_global_smooth_primitive_zero_on_exterior`](../ContinuousFlexibility/Geometry/CartesianDevelopment.lean#L53)
- [`ContinuousFlexibility.exists_normalized_map_of_fderiv_eq_id_on_exterior`](../ContinuousFlexibility/Geometry/CartesianDevelopment.lean#L78)
- [`ContinuousFlexibility.exists_normalized_development_of_closed_cartesian_coframe`](../ContinuousFlexibility/Geometry/CartesianDevelopment.lean#L99)
- [`ContinuousFlexibility.exists_global_development_of_closed_cartesian_coframe`](../ContinuousFlexibility/Geometry/CartesianDevelopment.lean#L134)
- [`ContinuousFlexibility.exists_global_development_of_flat_cartesian_coframe`](../ContinuousFlexibility/Geometry/CartesianDevelopment.lean#L167)

[CartesianExterior.lean](../ContinuousFlexibility/Geometry/CartesianExterior.lean)：

- [`ContinuousFlexibility.isPreconnected_norm_exterior`](../ContinuousFlexibility/Geometry/CartesianExterior.lean#L20)
- [`ContinuousFlexibility.isPreconnected_complex_radius_exterior`](../ContinuousFlexibility/Geometry/CartesianExterior.lean#L42)
- [`ContinuousFlexibility.isOpen_complex_radius_exterior`](../ContinuousFlexibility/Geometry/CartesianExterior.lean#L57)
- [`ContinuousFlexibility.isCompact_complex_radius_sublevel`](../ContinuousFlexibility/Geometry/CartesianExterior.lean#L61)
- [`ContinuousFlexibility.exists_global_development_of_flat_cartesian_coframe_on_disk`](../ContinuousFlexibility/Geometry/CartesianExterior.lean#L77)

[CartesianMetricCoframe.lean](../ContinuousFlexibility/Geometry/CartesianMetricCoframe.lean)：

- [`ContinuousFlexibility.cholesky_square_sum`](../ContinuousFlexibility/Geometry/CartesianMetricCoframe.lean#L41)
- [`ContinuousFlexibility.matrixCoframe_square_sum`](../ContinuousFlexibility/Geometry/CartesianMetricCoframe.lean#L52)
- [`ContinuousFlexibility.matrixCoframe_wedge`](../ContinuousFlexibility/Geometry/CartesianMetricCoframe.lean#L60)
- [`ContinuousFlexibility.matrixCoframe_wedge_pos`](../ContinuousFlexibility/Geometry/CartesianMetricCoframe.lean#L67)
- [`ContinuousFlexibility.contDiffAt_matrixCoframe`](../ContinuousFlexibility/Geometry/CartesianMetricCoframe.lean#L73)
- [`ContinuousFlexibility.triangularCoframeConnection_cartan`](../ContinuousFlexibility/Geometry/CartesianMetricCoframe.lean#L87)
- [`ContinuousFlexibility.matrixCoframe_cartan`](../ContinuousFlexibility/Geometry/CartesianMetricCoframe.lean#L100)
- [`ContinuousFlexibility.contDiffAt_triangularCoframeConnection`](../ContinuousFlexibility/Geometry/CartesianMetricCoframe.lean#L109)
- [`ContinuousFlexibility.contDiffAt_matrixCoframeConnection`](../ContinuousFlexibility/Geometry/CartesianMetricCoframe.lean#L124)
- [`ContinuousFlexibility.matrixCoframe_standard`](../ContinuousFlexibility/Geometry/CartesianMetricCoframe.lean#L135)
- [`ContinuousFlexibility.triangularCoframeConnection_zero_of_eventually_standard`](../ContinuousFlexibility/Geometry/CartesianMetricCoframe.lean#L143)
- [`ContinuousFlexibility.matrixCoframeConnection_zero_of_eventually_standard`](../ContinuousFlexibility/Geometry/CartesianMetricCoframe.lean#L163)

[MatrixDevelopment.lean](../ContinuousFlexibility/Geometry/MatrixDevelopment.lean)：

- [`ContinuousFlexibility.exists_global_development_of_flat_matrix_on_disk`](../ContinuousFlexibility/Geometry/MatrixDevelopment.lean#L39)

[CoframeRotationAlgebra.lean](../ContinuousFlexibility/Geometry/CoframeRotationAlgebra.lean)：

- [`ContinuousFlexibility.oriented_coframe_rotation_algebra`](../ContinuousFlexibility/Geometry/CoframeRotationAlgebra.lean#L18)
- [`ContinuousFlexibility.relativeCoframe_rotation`](../ContinuousFlexibility/Geometry/CoframeRotationAlgebra.lean#L72)

[CoframeSO2.lean](../ContinuousFlexibility/Geometry/CoframeSO2.lean)：

- [`ContinuousFlexibility.so2_tangent_identity`](../ContinuousFlexibility/Geometry/CoframeSO2.lean#L33)
- [`ContinuousFlexibility.so2_unit_tangent`](../ContinuousFlexibility/Geometry/CoframeSO2.lean#L40)
- [`ContinuousFlexibility.exteriorCoefficient_so2Connection`](../ContinuousFlexibility/Geometry/CoframeSO2.lean#L60)
- [`ContinuousFlexibility.so2Connection_closed`](../ContinuousFlexibility/Geometry/CoframeSO2.lean#L82)
- [`ContinuousFlexibility.exteriorCoefficient_so2CoframeOne`](../ContinuousFlexibility/Geometry/CoframeSO2.lean#L103)
- [`ContinuousFlexibility.exteriorCoefficient_so2CoframeTwo`](../ContinuousFlexibility/Geometry/CoframeSO2.lean#L122)
- [`ContinuousFlexibility.contDiffAt_so2Connection`](../ContinuousFlexibility/Geometry/CoframeSO2.lean#L141)
- [`ContinuousFlexibility.so2Coframe_cartan`](../ContinuousFlexibility/Geometry/CoframeSO2.lean#L150)

[CoframeCurvature.lean](../ContinuousFlexibility/Geometry/CoframeCurvature.lean)：

- [`ContinuousFlexibility.exteriorCoefficient_congr_germ`](../ContinuousFlexibility/Geometry/CoframeCurvature.lean#L20)
- [`ContinuousFlexibility.cartan_connection_unique`](../ContinuousFlexibility/Geometry/CoframeCurvature.lean#L26)
- [`ContinuousFlexibility.contDiffAt_relativeCoframeRotation`](../ContinuousFlexibility/Geometry/CoframeCurvature.lean#L40)
- [`ContinuousFlexibility.coframe_curvature_eq_of_same_metric`](../ContinuousFlexibility/Geometry/CoframeCurvature.lean#L56)

[PullbackCurvature.lean](../ContinuousFlexibility/Geometry/PullbackCurvature.lean)：

- [`ContinuousFlexibility.cartan_equations_pullback`](../ContinuousFlexibility/Geometry/PullbackCurvature.lean#L19)
- [`ContinuousFlexibility.cartan_curvature_pullback_eq_of_same_metric`](../ContinuousFlexibility/Geometry/PullbackCurvature.lean#L42)

[PlanarOrientation.lean](../ContinuousFlexibility/Geometry/PlanarOrientation.lean)：

- [`ContinuousFlexibility.planeCLM_apply_decompose`](../ContinuousFlexibility/Geometry/PlanarOrientation.lean#L25)
- [`ContinuousFlexibility.planeJacobian_comp`](../ContinuousFlexibility/Geometry/PlanarOrientation.lean#L35)
- [`ContinuousFlexibility.fderiv_bijective_of_homeomorph_smooth_inverse`](../ContinuousFlexibility/Geometry/PlanarOrientation.lean#L48)
- [`ContinuousFlexibility.planeJacobian_inverse_mul`](../ContinuousFlexibility/Geometry/PlanarOrientation.lean#L66)
- [`ContinuousFlexibility.planeJacobian_ne_zero_of_homeomorph_smooth_inverse`](../ContinuousFlexibility/Geometry/PlanarOrientation.lean#L78)
- [`ContinuousFlexibility.continuous_planeJacobian`](../ContinuousFlexibility/Geometry/PlanarOrientation.lean#L88)
- [`ContinuousFlexibility.planeJacobian_pos_of_normalized_homeomorph`](../ContinuousFlexibility/Geometry/PlanarOrientation.lean#L98)
- [`ContinuousFlexibility.IsometricGraphDevelopment.planar_orientation`](../ContinuousFlexibility/Geometry/PlanarOrientation.lean#L129)
- [`ContinuousFlexibility.FlatAnnularCore.graphDevelopment_orientation`](../ContinuousFlexibility/Geometry/PlanarOrientation.lean#L135)


<a id="g03"></a>
## G03 发展唯一性和内盘中心定位

**状态：** 已有部分已编译子结果。**分支：** 几何闭合。主定理必要节点。

**数学陈述：** 归一化平面发展唯一；半转对称推出P为奇映射，因此内平盘上P是绕原点旋转，无平移项。

**证明提纲：** 证明两个定向发展相差固定欧氏运动，由外圈归一化消掉；奇性消掉内盘平移。

**直接依赖：** [G02](#g02)

**论文定位：** [02-geometry.tex:96–102](../paper/flexible-surface-rewrite/02-geometry.tex#L96)

**目标文件：** `ContinuousFlexibility/Geometry/G03.lean`（节点组织目标；实际已存在的证明文件见下方，整个节点尚未完成）

**验收条件：**

- 不得只证明内盘是某个欧氏运动
- 半转对称落实到实际P

**已经完成的子结果：**

- 实际欧氏坐标metric与正Jacobian经混合偏导推导固定SO2线性部和平移，不使用product max norm充当欧氏度量
- 两个同一实际拉回度量的发展由非空open identity normalization全局唯一，定向自动由归一化推出
- 由实际高度偶性和真实微分构造反射发展-P(-x)，唯一性给P奇性和P(0)=0
- 内圆盘实际Euclidean remainder推出中心固定旋转，闭盘边界由真实连续性延拓

**仍待闭合的义务：**

- 给定Core的发展唯一性/奇性/中心旋转已全部证明；主链尚待N12构造实际非空Core并用于同一球面组装

**现有 Lean 证明：**

[CenteredDevelopment.lean](../ContinuousFlexibility/Contracts/CenteredDevelopment.lean)：

- [`ContinuousFlexibility.IsometricGraphDevelopment.planar_unique`](../ContinuousFlexibility/Contracts/CenteredDevelopment.lean#L23)
- [`ContinuousFlexibility.IsometricGraphDevelopment.planar_odd`](../ContinuousFlexibility/Contracts/CenteredDevelopment.lean#L39)
- [`ContinuousFlexibility.IsometricGraphDevelopment.planar_zero`](../ContinuousFlexibility/Contracts/CenteredDevelopment.lean#L46)
- [`ContinuousFlexibility.convex_cartesianDisk`](../ContinuousFlexibility/Contracts/CenteredDevelopment.lean#L54)
- [`ContinuousFlexibility.closure_cartesianDisk`](../ContinuousFlexibility/Contracts/CenteredDevelopment.lean#L64)
- [`ContinuousFlexibility.IsometricGraphDevelopment.exists_centered_inner_rotation`](../ContinuousFlexibility/Contracts/CenteredDevelopment.lean#L82)

[DevelopmentSymmetry.lean](../ContinuousFlexibility/Contracts/DevelopmentSymmetry.lean)：

- [`ContinuousFlexibility.cartesianRadius_neg`](../ContinuousFlexibility/Contracts/DevelopmentSymmetry.lean#L22)
- [`ContinuousFlexibility.coordinateEuclideanPair_neg_neg`](../ContinuousFlexibility/Contracts/DevelopmentSymmetry.lean#L25)
- [`ContinuousFlexibility.cartesianMetric_neg_neg`](../ContinuousFlexibility/Contracts/DevelopmentSymmetry.lean#L29)
- [`ContinuousFlexibility.fderiv_even_apply_neg`](../ContinuousFlexibility/Contracts/DevelopmentSymmetry.lean#L34)
- [`ContinuousFlexibility.FlatAnnularCore.cartesianRemainder_neg_neg`](../ContinuousFlexibility/Contracts/DevelopmentSymmetry.lean#L47)
- [`ContinuousFlexibility.reflectedPlaneHomeomorph_apply`](../ContinuousFlexibility/Contracts/DevelopmentSymmetry.lean#L61)
- [`ContinuousFlexibility.reflectedPlaneHomeomorph_symm_apply`](../ContinuousFlexibility/Contracts/DevelopmentSymmetry.lean#L64)
- [`ContinuousFlexibility.contDiff_reflectedPlaneHomeomorph`](../ContinuousFlexibility/Contracts/DevelopmentSymmetry.lean#L67)
- [`ContinuousFlexibility.fderiv_reflectedPlaneHomeomorph_apply`](../ContinuousFlexibility/Contracts/DevelopmentSymmetry.lean#L72)
- [`ContinuousFlexibility.IsometricGraphDevelopment.reflected_planar_apply`](../ContinuousFlexibility/Contracts/DevelopmentSymmetry.lean#L125)

[EuclideanRigidity.lean](../ContinuousFlexibility/Geometry/EuclideanRigidity.lean)：

- [`ContinuousFlexibility.exists_rotation_affine_of_euclidean_derivative`](../ContinuousFlexibility/Geometry/EuclideanRigidity.lean#L23)
- [`ContinuousFlexibility.exists_affine_of_euclidean_derivative`](../ContinuousFlexibility/Geometry/EuclideanRigidity.lean#L60)
- [`ContinuousFlexibility.contDiffAt_planeJacobian`](../ContinuousFlexibility/Geometry/EuclideanRigidity.lean#L85)
- [`ContinuousFlexibility.planeJacobian_sq_of_euclidean_derivative`](../ContinuousFlexibility/Geometry/EuclideanRigidity.lean#L92)
- [`ContinuousFlexibility.planeJacobian_pos_of_euclidean_derivative_at`](../ContinuousFlexibility/Geometry/EuclideanRigidity.lean#L111)
- [`ContinuousFlexibility.eq_id_of_euclidean_derivative_of_identity_germ`](../ContinuousFlexibility/Geometry/EuclideanRigidity.lean#L129)
- [`ContinuousFlexibility.normalized_developments_unique`](../ContinuousFlexibility/Geometry/EuclideanRigidity.lean#L153)

[EuclideanRigidityCoordinates.lean](../ContinuousFlexibility/Geometry/EuclideanRigidityCoordinates.lean)：

- [`ContinuousFlexibility.planeRotationLinearMap_apply`](../ContinuousFlexibility/Geometry/EuclideanRigidityCoordinates.lean#L26)
- [`ContinuousFlexibility.planeRotationLinearMap_metric`](../ContinuousFlexibility/Geometry/EuclideanRigidityCoordinates.lean#L30)
- [`ContinuousFlexibility.planeRotationLinearMap_bijective`](../ContinuousFlexibility/Geometry/EuclideanRigidityCoordinates.lean#L39)
- [`ContinuousFlexibility.fderiv_plane_coordinates`](../ContinuousFlexibility/Geometry/EuclideanRigidityCoordinates.lean#L63)
- [`ContinuousFlexibility.derivative_rotation_of_metric`](../ContinuousFlexibility/Geometry/EuclideanRigidityCoordinates.lean#L76)
- [`ContinuousFlexibility.fderiv_eq_planeRotation_of_metric`](../ContinuousFlexibility/Geometry/EuclideanRigidityCoordinates.lean#L102)
- [`ContinuousFlexibility.derivative_rotation_fderiv_zero`](../ContinuousFlexibility/Geometry/EuclideanRigidityCoordinates.lean#L118)


<a id="g04"></a>
## G04 局部发展成为全局微分同胚

**状态：** 已有部分已编译子结果。**分支：** 几何闭合。主定理必要节点。

**数学陈述：** P恒等延拓为R²上的proper local diffeomorphism，由有限纤维covering和外部单层推出全局双射，限制为圆盘自微分同胚。

**证明提纲：** 组合proper→closed、compact discrete fibers有限、closed local homeomorphism→covering及连通纤维层数；最后适配光滑逆。

**直接依赖：** [G02](#g02)

**论文定位：** [02-geometry.tex:104–108](../paper/flexible-surface-rewrite/02-geometry.tex#L104)

**目标文件：** `ContinuousFlexibility/Geometry/G04.lean`（节点组织目标；实际已存在的证明文件见下方，整个节点尚未完成）

**验收条件：**

- 局部等距不直接等于嵌入
- 证明像圆盘恰为同一圆盘
- 边界附近的恒等延拓光滑

**已经完成的子结果：**

- 紧集外恒等的连续全平面映射proper、闭映射且纤维紧
- proper局部homeomorphism经真实covering lift得到全局双侧逆
- 在实际fderiv处处双射及C∞条件下，得到全局homeomorphism及其逆逐点C∞，并保持原区域像

**仍待闭合的义务：**

- G02实际构造的归一化发展必须扩成全平面映射并核对所有前提
- 与同一个填盘高度、标记补帽及后续相位族统一见证

**现有 Lean 证明：**

[GlobalInverse.lean](../ContinuousFlexibility/Geometry/GlobalInverse.lean)：

- [`ContinuousFlexibility.isCompact_preimage_of_eq_id_outside_compact`](../ContinuousFlexibility/Geometry/GlobalInverse.lean#L19)
- [`ContinuousFlexibility.isProperMap_of_eq_id_outside_compact`](../ContinuousFlexibility/Geometry/GlobalInverse.lean#L33)
- [`ContinuousFlexibility.isClosedMap_of_eq_id_outside_compact`](../ContinuousFlexibility/Geometry/GlobalInverse.lean#L40)
- [`ContinuousFlexibility.isCompact_fiber_of_eq_id_outside_compact`](../ContinuousFlexibility/Geometry/GlobalInverse.lean#L46)
- [`ContinuousFlexibility.image_eq_self_of_bijective_eq_id_outside`](../ContinuousFlexibility/Geometry/GlobalInverse.lean#L54)

[GlobalCovering.lean](../ContinuousFlexibility/Geometry/GlobalCovering.lean)：

- [`ContinuousFlexibility.finite_fiber_of_proper_localHomeomorph`](../ContinuousFlexibility/Geometry/GlobalCovering.lean#L27)
- [`ContinuousFlexibility.isCoveringMap_of_proper_localHomeomorph`](../ContinuousFlexibility/Geometry/GlobalCovering.lean#L36)
- [`ContinuousFlexibility.exists_globalInverse_of_plane_covering`](../ContinuousFlexibility/Geometry/GlobalCovering.lean#L45)
- [`ContinuousFlexibility.isHomeomorph_of_plane_covering`](../ContinuousFlexibility/Geometry/GlobalCovering.lean#L62)
- [`ContinuousFlexibility.isHomeomorph_of_proper_localHomeomorph_plane`](../ContinuousFlexibility/Geometry/GlobalCovering.lean#L67)
- [`ContinuousFlexibility.isHomeomorph_of_eq_id_outside_compact`](../ContinuousFlexibility/Geometry/GlobalCovering.lean#L71)
- [`ContinuousFlexibility.exists_homeomorph_of_eq_id_outside_compact`](../ContinuousFlexibility/Geometry/GlobalCovering.lean#L77)
- [`ContinuousFlexibility.image_compact_region_eq_self_of_localHomeomorph`](../ContinuousFlexibility/Geometry/GlobalCovering.lean#L84)
- [`ContinuousFlexibility.contDiffAt_homeomorph_symm_of_fderiv_bijective`](../ContinuousFlexibility/Geometry/GlobalCovering.lean#L93)
- [`ContinuousFlexibility.exists_smooth_homeomorph_of_eq_id_outside_compact`](../ContinuousFlexibility/Geometry/GlobalCovering.lean#L111)


<a id="g05"></a>
## G05 等距图盘

**状态：** 已有部分已编译子结果。**分支：** 几何闭合。主定理必要节点。

**数学陈述：** F=(P,z)是光滑嵌入圆盘且F*δ=g；外领圈为水平恒等盘，内盘为水平中心旋转盘。

**证明提纲：** 用P的全局逆证明图嵌入，逐项证明拉回度量等式及两端图公式。

**直接依赖：** [G03](#g03), [G04](#g04)

**论文定位：** [02-geometry.tex:69–81](../paper/flexible-surface-rewrite/02-geometry.tex#L69)，`lem:disk-development`；[02-geometry.tex:107–108](../paper/flexible-surface-rewrite/02-geometry.tex#L107)

**目标文件：** `ContinuousFlexibility/Geometry/G05.lean`（节点组织目标；实际已存在的证明文件见下方，整个节点尚未完成）

**验收条件：**

- smooth immersion和topological embedding均证明
- 保持内外领圈的精确公式

**已经完成的子结果：**

- 真正E3=EuclideanSpace ℝ(Fin3)的graphMap，全局C∞、topological embedding和实际微分单射
- 实际Euclidean inner拉回等于cartesianMetric，不是ambient Isometry
- 同一个Core与P给IsometricGraphDevelopment；扩大后R>b闭盘图像嵌入且内部有真实水平identity collar
- 同一D的实际内闭盘已证明为中心旋转，平移由发展奇性消除

**仍待闭合的义务：**

- 同一标记帽及球面组装尚未构造；图盘结论不含闭球面族或非全等
- 尚未证明analytic Core存在

**现有 Lean 证明：**

[IsometricGraph.lean](../ContinuousFlexibility/Contracts/IsometricGraph.lean)：

- [`ContinuousFlexibility.FlatAnnularCore.exists_isometricGraphDevelopment`](../ContinuousFlexibility/Contracts/IsometricGraph.lean#L37)
- [`ContinuousFlexibility.IsometricGraphDevelopment.embedding_restrict`](../ContinuousFlexibility/Contracts/IsometricGraph.lean#L61)
- [`ContinuousFlexibility.graphBaseProjection_image_graphMap`](../ContinuousFlexibility/Contracts/IsometricGraph.lean#L66)
- [`ContinuousFlexibility.IsometricGraphDevelopment.graph_projects_onto_disk`](../ContinuousFlexibility/Contracts/IsometricGraph.lean#L74)
- [`ContinuousFlexibility.IsometricGraphDevelopment.map_standard_outside`](../ContinuousFlexibility/Contracts/IsometricGraph.lean#L81)
- [`ContinuousFlexibility.AnnularSolution.exists_isometricGraphDisk`](../ContinuousFlexibility/Contracts/IsometricGraph.lean#L91)

[GraphEmbedding.lean](../ContinuousFlexibility/Geometry/GraphEmbedding.lean)：

- [`ContinuousFlexibility.graphMap_zero`](../ContinuousFlexibility/Geometry/GraphEmbedding.lean#L36)
- [`ContinuousFlexibility.graphMap_one`](../ContinuousFlexibility/Geometry/GraphEmbedding.lean#L40)
- [`ContinuousFlexibility.graphMap_two`](../ContinuousFlexibility/Geometry/GraphEmbedding.lean#L44)
- [`ContinuousFlexibility.graphBaseProjection_graphMap`](../ContinuousFlexibility/Geometry/GraphEmbedding.lean#L48)
- [`ContinuousFlexibility.graphDifferential_apply_zero`](../ContinuousFlexibility/Geometry/GraphEmbedding.lean#L52)
- [`ContinuousFlexibility.graphDifferential_apply_one`](../ContinuousFlexibility/Geometry/GraphEmbedding.lean#L57)
- [`ContinuousFlexibility.graphDifferential_apply_two`](../ContinuousFlexibility/Geometry/GraphEmbedding.lean#L62)
- [`ContinuousFlexibility.e3_inner_coordinates`](../ContinuousFlexibility/Geometry/GraphEmbedding.lean#L67)
- [`ContinuousFlexibility.continuous_graphBaseProjection`](../ContinuousFlexibility/Geometry/GraphEmbedding.lean#L72)
- [`ContinuousFlexibility.continuous_graphMap`](../ContinuousFlexibility/Geometry/GraphEmbedding.lean#L76)
- [`ContinuousFlexibility.contDiff_graphMap`](../ContinuousFlexibility/Geometry/GraphEmbedding.lean#L81)
- [`ContinuousFlexibility.contDiffAt_graphMap`](../ContinuousFlexibility/Geometry/GraphEmbedding.lean#L86)
- [`ContinuousFlexibility.hasFDerivAt_graphMap`](../ContinuousFlexibility/Geometry/GraphEmbedding.lean#L93)
- [`ContinuousFlexibility.fderiv_graphMap`](../ContinuousFlexibility/Geometry/GraphEmbedding.lean#L100)
- [`ContinuousFlexibility.inner_graphDifferential`](../ContinuousFlexibility/Geometry/GraphEmbedding.lean#L105)
- [`ContinuousFlexibility.isEmbedding_graphMap`](../ContinuousFlexibility/Geometry/GraphEmbedding.lean#L112)
- [`ContinuousFlexibility.graphMap_pullback_metric`](../ContinuousFlexibility/Geometry/GraphEmbedding.lean#L121)
- [`ContinuousFlexibility.graph_cartesianMetric_self_pos`](../ContinuousFlexibility/Geometry/GraphEmbedding.lean#L132)
- [`ContinuousFlexibility.graphMap_fderiv_injective_of_metric`](../ContinuousFlexibility/Geometry/GraphEmbedding.lean#L146)
- [`ContinuousFlexibility.graphMap_fderiv_injective_of_planar`](../ContinuousFlexibility/Geometry/GraphEmbedding.lean#L164)
- [`ContinuousFlexibility.graphMap_fderiv_injective_of_smooth_inverse`](../ContinuousFlexibility/Geometry/GraphEmbedding.lean#L175)
- [`ContinuousFlexibility.isEmbedding_graphMap_restrict`](../ContinuousFlexibility/Geometry/GraphEmbedding.lean#L194)
- [`ContinuousFlexibility.graphMap_smooth_embedding_with_metric`](../ContinuousFlexibility/Geometry/GraphEmbedding.lean#L201)


<a id="g06"></a>
## G06 隔离的固定标记补帽

**状态：** 已有部分已编译子结果。**分支：** 几何闭合。主定理必要节点。

**数学陈述：** 对给定图盘构造光滑嵌入补帽，与该图盘的全部轴向旋转像除公共领圈外分离；在中央圆柱内补帽仅为底平盘c_B且c_B<min Z。补帽含唯一全局Gaussian曲率最大点p，其两主曲率不同。

**证明提纲：** 构造外侧下降径线及下平盘；严格验证axis/rim光滑。放入椭圆bump，证明支持边界光滑、曲率公式和严格最大值，按顺序选k、ρ。

**直接依赖：** [G05](#g05), [D01](#d01)

**论文定位：** [02-geometry.tex:146–190](../paper/flexible-surface-rewrite/02-geometry.tex#L146)，`lem:fixed-cap`

**目标文件：** `ContinuousFlexibility/Geometry/G06.lean`（节点组织目标；实际已存在的证明文件见下方，整个节点尚未完成）

**验收条件：**

- 对整个相位族的统一分离
- 最大点是整个闭曲面的唯一最大点
- 主曲率不等，不仅坐标Hessian不等

**已经完成的子结果：**

- 实际expNegInvGlue核和真实积分构造全局C∞椭圆marker，紧支撑、0≤u≤kρ²/2、全点一二阶导及支持边界Hessian=0
- 真实图K等于论文表达式；中心为全图唯一严格Gaussian曲率峰，实际shape中心为diag(-kA,-kB)且具有不同eigenvalues及对应坐标eigenvectors
- 实际闭图盘compact，所有相位具有同一真实高度上下界，为隔离bottom cap提供统一空间
- 真实积分子午线、整个闭帽盘的光滑嵌入和单位法向、只作用于顶平环的实际marker、完整帽盘唯一曲率峰和同Core图族的统一曲率界已编译。
- 精确 markedCap_G06_statement 已通过：一次实际长度选择、真实闭补帽光滑嵌入、统一分离/底盘/开放领圈、同一标记的严格曲率峰和两真实单位正交主方向。

**仍待闭合的义务：**

- 精确 G06Statement 已证明；主蓝图节点的前置 G05/D01 的较强通用验收另行保留。

**优先核查程度：** high（任务风险标记，不是已发现错误）

**现有 Lean 证明：**

[GraphFamilyImage.lean](../ContinuousFlexibility/Contracts/GraphFamilyImage.lean)：

- [`ContinuousFlexibility.isCompact_closedCartesianDisk`](../ContinuousFlexibility/Contracts/GraphFamilyImage.lean#L186)
- [`ContinuousFlexibility.IsometricGraphDevelopment.exists_rotationFamily_height_bounds`](../ContinuousFlexibility/Contracts/GraphFamilyImage.lean#L208)

[MarkedCap.lean](../ContinuousFlexibility/Geometry/MarkedCap.lean)：

- [`ContinuousFlexibility.markerCurvatureExpression_zero`](../ContinuousFlexibility/Geometry/MarkedCap.lean#L32)
- [`ContinuousFlexibility.markerCurvatureExpression_support`](../ContinuousFlexibility/Geometry/MarkedCap.lean#L37)
- [`ContinuousFlexibility.positive_ellipticQuadratic_of_ne_zero`](../ContinuousFlexibility/Geometry/MarkedCap.lean#L42)
- [`ContinuousFlexibility.markerCurvatureExpression_lt_peak`](../ContinuousFlexibility/Geometry/MarkedCap.lean#L53)
- [`ContinuousFlexibility.markerCurvatureExpression_le_peak`](../ContinuousFlexibility/Geometry/MarkedCap.lean#L97)
- [`ContinuousFlexibility.markerCurvatureExpression_eq_peak_iff`](../ContinuousFlexibility/Geometry/MarkedCap.lean#L105)
- [`ContinuousFlexibility.graphHessian_markerBump_apply`](../ContinuousFlexibility/Geometry/MarkedCap.lean#L116)
- [`ContinuousFlexibility.graphHessian_markerBump_det`](../ContinuousFlexibility/Geometry/MarkedCap.lean#L130)
- [`ContinuousFlexibility.graphAreaSq_markerBump`](../ContinuousFlexibility/Geometry/MarkedCap.lean#L141)
- [`ContinuousFlexibility.surfaceGaussianCurvature_markerBump_kernel`](../ContinuousFlexibility/Geometry/MarkedCap.lean#L149)
- [`ContinuousFlexibility.surfaceGaussianCurvature_markerBump`](../ContinuousFlexibility/Geometry/MarkedCap.lean#L162)
- [`ContinuousFlexibility.surfaceGaussianCurvature_markerBump_zero`](../ContinuousFlexibility/Geometry/MarkedCap.lean#L189)
- [`ContinuousFlexibility.surfaceGaussianCurvature_markerBump_lt_peak`](../ContinuousFlexibility/Geometry/MarkedCap.lean#L194)
- [`ContinuousFlexibility.surfaceGaussianCurvature_markerBump_eq_peak_iff`](../ContinuousFlexibility/Geometry/MarkedCap.lean#L202)
- [`ContinuousFlexibility.graphHessian_markerBump_zero`](../ContinuousFlexibility/Geometry/MarkedCap.lean#L209)
- [`ContinuousFlexibility.surfaceShapeMatrix_markerBump_zero`](../ContinuousFlexibility/Geometry/MarkedCap.lean#L215)
- [`ContinuousFlexibility.surfaceShapeMatrix_markerBump_center_eigenvectors`](../ContinuousFlexibility/Geometry/MarkedCap.lean#L223)

[MarkerBump.lean](../ContinuousFlexibility/Geometry/MarkerBump.lean)：

- [`ContinuousFlexibility.contDiff_markerKernel`](../ContinuousFlexibility/Geometry/MarkerBump.lean#L34)
- [`ContinuousFlexibility.markerKernel_nonneg`](../ContinuousFlexibility/Geometry/MarkerBump.lean#L38)
- [`ContinuousFlexibility.markerKernel_eq_zero`](../ContinuousFlexibility/Geometry/MarkerBump.lean#L41)
- [`ContinuousFlexibility.markerKernel_eq_exp`](../ContinuousFlexibility/Geometry/MarkerBump.lean#L50)
- [`ContinuousFlexibility.markerKernel_zero`](../ContinuousFlexibility/Geometry/MarkerBump.lean#L62)
- [`ContinuousFlexibility.markerKernel_le_one`](../ContinuousFlexibility/Geometry/MarkerBump.lean#L65)
- [`ContinuousFlexibility.hasDerivAt_markerPrimitive`](../ContinuousFlexibility/Geometry/MarkerBump.lean#L73)
- [`ContinuousFlexibility.deriv_markerPrimitive`](../ContinuousFlexibility/Geometry/MarkerBump.lean#L82)
- [`ContinuousFlexibility.contDiff_markerPrimitive`](../ContinuousFlexibility/Geometry/MarkerBump.lean#L86)
- [`ContinuousFlexibility.markerPrimitive_eq_zero`](../ContinuousFlexibility/Geometry/MarkerBump.lean#L93)
- [`ContinuousFlexibility.markerPrimitive_nonneg`](../ContinuousFlexibility/Geometry/MarkerBump.lean#L102)
- [`ContinuousFlexibility.markerPrimitive_le`](../ContinuousFlexibility/Geometry/MarkerBump.lean#L109)
- [`ContinuousFlexibility.contDiff_markerQuadratic`](../ContinuousFlexibility/Geometry/MarkerBump.lean#L123)
- [`ContinuousFlexibility.contDiff_markerBump`](../ContinuousFlexibility/Geometry/MarkerBump.lean#L127)
- [`ContinuousFlexibility.markerBump_eq_zero`](../ContinuousFlexibility/Geometry/MarkerBump.lean#L130)
- [`ContinuousFlexibility.markerBump_bounds`](../ContinuousFlexibility/Geometry/MarkerBump.lean#L135)
- [`ContinuousFlexibility.hasCompactSupport_markerBump`](../ContinuousFlexibility/Geometry/MarkerBump.lean#L142)
- [`ContinuousFlexibility.hasFDerivAt_markerQuadratic`](../ContinuousFlexibility/Geometry/MarkerBump.lean#L171)
- [`ContinuousFlexibility.hasFDerivAt_markerBump`](../ContinuousFlexibility/Geometry/MarkerBump.lean#L183)
- [`ContinuousFlexibility.fderiv_markerBump_apply`](../ContinuousFlexibility/Geometry/MarkerBump.lean#L189)
- [`ContinuousFlexibility.fderiv_markerBump_zero`](../ContinuousFlexibility/Geometry/MarkerBump.lean#L196)
- [`ContinuousFlexibility.markerBump_secondDerivative_zero`](../ContinuousFlexibility/Geometry/MarkerBump.lean#L202)
- [`ContinuousFlexibility.hasDerivAt_markerKernel`](../ContinuousFlexibility/Geometry/MarkerBump.lean#L225)
- [`ContinuousFlexibility.deriv_markerKernel`](../ContinuousFlexibility/Geometry/MarkerBump.lean#L235)
- [`ContinuousFlexibility.deriv_markerKernel_eq_zero`](../ContinuousFlexibility/Geometry/MarkerBump.lean#L240)
- [`ContinuousFlexibility.deriv_markerKernel_of_lt`](../ContinuousFlexibility/Geometry/MarkerBump.lean#L244)
- [`ContinuousFlexibility.markerBump_secondDerivative`](../ContinuousFlexibility/Geometry/MarkerBump.lean#L251)
- [`ContinuousFlexibility.markerBump_secondDerivative_of_lt`](../ContinuousFlexibility/Geometry/MarkerBump.lean#L276)
- [`ContinuousFlexibility.markerBump_secondDerivative_eq_zero`](../ContinuousFlexibility/Geometry/MarkerBump.lean#L286)

[GraphCurvatureBounds.lean](../ContinuousFlexibility/Contracts/GraphCurvatureBounds.lean)：

- [`ContinuousFlexibility.continuous_heightGraph_gaussianCurvature`](../ContinuousFlexibility/Contracts/GraphCurvatureBounds.lean#L21)
- [`ContinuousFlexibility.IsometricGraphDevelopment.continuous_upwardGaussianCurvature`](../ContinuousFlexibility/Contracts/GraphCurvatureBounds.lean#L43)
- [`ContinuousFlexibility.IsometricGraphDevelopment.exists_rotationFamily_curvature_bounds`](../ContinuousFlexibility/Contracts/GraphCurvatureBounds.lean#L54)

[CapDisk.lean](../ContinuousFlexibility/Geometry/CapDisk.lean)：

- [`ContinuousFlexibility.capDiskMap_zero`](../ContinuousFlexibility/Geometry/CapDisk.lean#L34)
- [`ContinuousFlexibility.capDiskMap_one`](../ContinuousFlexibility/Geometry/CapDisk.lean#L37)
- [`ContinuousFlexibility.capDiskMap_two`](../ContinuousFlexibility/Geometry/CapDisk.lean#L40)
- [`ContinuousFlexibility.capDisk_radius_nonneg`](../ContinuousFlexibility/Geometry/CapDisk.lean#L43)
- [`ContinuousFlexibility.capDisk_radius_eq_zero_iff`](../ContinuousFlexibility/Geometry/CapDisk.lean#L45)
- [`ContinuousFlexibility.capDisk_radius_smul`](../ContinuousFlexibility/Geometry/CapDisk.lean#L53)
- [`ContinuousFlexibility.capDisk_axis_parameter`](../ContinuousFlexibility/Geometry/CapDisk.lean#L57)
- [`ContinuousFlexibility.capDisk_axis_base`](../ContinuousFlexibility/Geometry/CapDisk.lean#L64)
- [`ContinuousFlexibility.capDisk_axis_height`](../ContinuousFlexibility/Geometry/CapDisk.lean#L76)
- [`ContinuousFlexibility.capDisk_axis_formula`](../ContinuousFlexibility/Geometry/CapDisk.lean#L81)
- [`ContinuousFlexibility.capDisk_axis_germ`](../ContinuousFlexibility/Geometry/CapDisk.lean#L89)
- [`ContinuousFlexibility.contDiff_capDiskMap`](../ContinuousFlexibility/Geometry/CapDisk.lean#L98)
- [`ContinuousFlexibility.capDiskParameter_mem`](../ContinuousFlexibility/Geometry/CapDisk.lean#L116)
- [`ContinuousFlexibility.capDisk_meridian_radius_pos`](../ContinuousFlexibility/Geometry/CapDisk.lean#L124)
- [`ContinuousFlexibility.capDiskBase_radius`](../ContinuousFlexibility/Geometry/CapDisk.lean#L134)
- [`ContinuousFlexibility.capDiskMap_injOn`](../ContinuousFlexibility/Geometry/CapDisk.lean#L150)
- [`ContinuousFlexibility.isCompact_capDiskDomain_set`](../ContinuousFlexibility/Geometry/CapDisk.lean#L180)
- [`ContinuousFlexibility.isEmbedding_capDiskEmbeddingMap`](../ContinuousFlexibility/Geometry/CapDisk.lean#L198)
- [`ContinuousFlexibility.hasFDerivAt_capDiskMap_axis`](../ContinuousFlexibility/Geometry/CapDisk.lean#L208)
- [`ContinuousFlexibility.capDiskMap_axis_fderiv_injective`](../ContinuousFlexibility/Geometry/CapDisk.lean#L217)
- [`ContinuousFlexibility.capDiskMap_polarMap`](../ContinuousFlexibility/Geometry/CapDisk.lean#L231)
- [`ContinuousFlexibility.capDiskMap_polar_germ`](../ContinuousFlexibility/Geometry/CapDisk.lean#L262)
- [`ContinuousFlexibility.capDiskMap_fderiv_injective_nonaxis`](../ContinuousFlexibility/Geometry/CapDisk.lean#L273)
- [`ContinuousFlexibility.capDiskMap_fderiv_injective`](../ContinuousFlexibility/Geometry/CapDisk.lean#L329)
- [`ContinuousFlexibility.capDisk_outer_collar`](../ContinuousFlexibility/Geometry/CapDisk.lean#L338)
- [`ContinuousFlexibility.capDisk_boundary`](../ContinuousFlexibility/Geometry/CapDisk.lean#L346)
- [`ContinuousFlexibility.capDisk_inside_cylinder_bottom`](../ContinuousFlexibility/Geometry/CapDisk.lean#L353)
- [`ContinuousFlexibility.capDisk_inside_cylinder_below`](../ContinuousFlexibility/Geometry/CapDisk.lean#L370)
- [`ContinuousFlexibility.capDiskMap_smooth_embedding`](../ContinuousFlexibility/Geometry/CapDisk.lean#L378)
- [`ContinuousFlexibility.capDiskRimScale_pos`](../ContinuousFlexibility/Geometry/CapDisk.lean#L395)
- [`ContinuousFlexibility.capDiskRimChart_radius`](../ContinuousFlexibility/Geometry/CapDisk.lean#L404)
- [`ContinuousFlexibility.capDiskRimChart_parameter`](../ContinuousFlexibility/Geometry/CapDisk.lean#L412)
- [`ContinuousFlexibility.capDiskBase_rimChart`](../ContinuousFlexibility/Geometry/CapDisk.lean#L420)
- [`ContinuousFlexibility.capDiskMap_rimChart`](../ContinuousFlexibility/Geometry/CapDisk.lean#L437)
- [`ContinuousFlexibility.contDiffAt_capDiskRimChart`](../ContinuousFlexibility/Geometry/CapDisk.lean#L449)
- [`ContinuousFlexibility.capDiskMap_rim_germ`](../ContinuousFlexibility/Geometry/CapDisk.lean#L456)
- [`ContinuousFlexibility.capDiskRimChart_fderiv_injective`](../ContinuousFlexibility/Geometry/CapDisk.lean#L468)
- [`ContinuousFlexibility.capDisk_meridian_at_rim`](../ContinuousFlexibility/Geometry/CapDisk.lean#L489)
- [`ContinuousFlexibility.capDisk_upper_cylinder_meeting`](../ContinuousFlexibility/Geometry/CapDisk.lean#L505)

[CapDiskNormal.lean](../ContinuousFlexibility/Geometry/CapDiskNormal.lean)：

- [`ContinuousFlexibility.capRevolutionNormal_zero`](../ContinuousFlexibility/Geometry/CapDiskNormal.lean#L35)
- [`ContinuousFlexibility.capRevolutionNormal_one`](../ContinuousFlexibility/Geometry/CapDiskNormal.lean#L39)
- [`ContinuousFlexibility.capRevolutionNormal_two`](../ContinuousFlexibility/Geometry/CapDiskNormal.lean#L43)
- [`ContinuousFlexibility.capDiskNormal_zero`](../ContinuousFlexibility/Geometry/CapDiskNormal.lean#L47)
- [`ContinuousFlexibility.capDiskNormal_one`](../ContinuousFlexibility/Geometry/CapDiskNormal.lean#L52)
- [`ContinuousFlexibility.capDiskNormal_two`](../ContinuousFlexibility/Geometry/CapDiskNormal.lean#L57)
- [`ContinuousFlexibility.contDiff_capRevolutionNormal`](../ContinuousFlexibility/Geometry/CapDiskNormal.lean#L61)
- [`ContinuousFlexibility.capRevolutionNormal_inner_self`](../ContinuousFlexibility/Geometry/CapDiskNormal.lean#L67)
- [`ContinuousFlexibility.capRevolutionNormal_norm`](../ContinuousFlexibility/Geometry/CapDiskNormal.lean#L77)
- [`ContinuousFlexibility.capRevolutionNormal_orthogonal`](../ContinuousFlexibility/Geometry/CapDiskNormal.lean#L83)
- [`ContinuousFlexibility.isUnitSurfaceNormal_capRevolution`](../ContinuousFlexibility/Geometry/CapDiskNormal.lean#L91)
- [`ContinuousFlexibility.capDiskNormal_top_collar`](../ContinuousFlexibility/Geometry/CapDiskNormal.lean#L96)
- [`ContinuousFlexibility.capDiskNormal_bottom_collar`](../ContinuousFlexibility/Geometry/CapDiskNormal.lean#L103)
- [`ContinuousFlexibility.capDiskNormal_axis_neighborhood`](../ContinuousFlexibility/Geometry/CapDiskNormal.lean#L110)
- [`ContinuousFlexibility.capDiskNormal_axis`](../ContinuousFlexibility/Geometry/CapDiskNormal.lean#L115)
- [`ContinuousFlexibility.capDiskNormal_axis_germ`](../ContinuousFlexibility/Geometry/CapDiskNormal.lean#L119)
- [`ContinuousFlexibility.contDiff_capDiskNormal`](../ContinuousFlexibility/Geometry/CapDiskNormal.lean#L127)
- [`ContinuousFlexibility.capDiskNormal_polarMap`](../ContinuousFlexibility/Geometry/CapDiskNormal.lean#L142)
- [`ContinuousFlexibility.capDiskNormal_norm`](../ContinuousFlexibility/Geometry/CapDiskNormal.lean#L168)
- [`ContinuousFlexibility.capDiskNormal_orthogonal`](../ContinuousFlexibility/Geometry/CapDiskNormal.lean#L179)
- [`ContinuousFlexibility.isUnitSurfaceNormal_capDisk`](../ContinuousFlexibility/Geometry/CapDiskNormal.lean#L224)
- [`ContinuousFlexibility.contDiffAt_capDiskShapeMatrix`](../ContinuousFlexibility/Geometry/CapDiskNormal.lean#L268)
- [`ContinuousFlexibility.contDiffAt_capDiskGaussianCurvature`](../ContinuousFlexibility/Geometry/CapDiskNormal.lean#L279)
- [`ContinuousFlexibility.contDiffAt_capDiskMeanCurvature`](../ContinuousFlexibility/Geometry/CapDiskNormal.lean#L288)
- [`ContinuousFlexibility.contDiffOn_capDiskGaussianCurvature`](../ContinuousFlexibility/Geometry/CapDiskNormal.lean#L297)
- [`ContinuousFlexibility.contDiffOn_capDiskMeanCurvature`](../ContinuousFlexibility/Geometry/CapDiskNormal.lean#L302)
- [`ContinuousFlexibility.capDisk_curvature_uniform_bound`](../ContinuousFlexibility/Geometry/CapDiskNormal.lean#L309)

[CapMeridian.lean](../ContinuousFlexibility/Geometry/CapMeridian.lean)：

- [`ContinuousFlexibility.contDiff_capTurn`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L48)
- [`ContinuousFlexibility.capTurn_nonneg`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L52)
- [`ContinuousFlexibility.capTurn_le_one`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L54)
- [`ContinuousFlexibility.monotone_capTurn`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L56)
- [`ContinuousFlexibility.capTurn_eq_zero`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L60)
- [`ContinuousFlexibility.capTurn_eq_one`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L63)
- [`ContinuousFlexibility.capTurn_reflection`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L74)
- [`ContinuousFlexibility.capTurn_half`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L79)
- [`ContinuousFlexibility.capTurn_pos`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L84)
- [`ContinuousFlexibility.capTurn_lt_one`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L87)
- [`ContinuousFlexibility.contDiff_capRadialVelocity`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L90)
- [`ContinuousFlexibility.contDiff_capDownwardVelocity`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L93)
- [`ContinuousFlexibility.capRadialVelocity_reflection`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L96)
- [`ContinuousFlexibility.capDownwardVelocity_reflection`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L101)
- [`ContinuousFlexibility.capRadialVelocity_eq_one`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L106)
- [`ContinuousFlexibility.capDownwardVelocity_eq_zero_left`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L109)
- [`ContinuousFlexibility.capRadialVelocity_eq_neg_one`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L112)
- [`ContinuousFlexibility.capDownwardVelocity_eq_zero_right`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L115)
- [`ContinuousFlexibility.capRadialVelocity_nonneg`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L118)
- [`ContinuousFlexibility.capDownwardVelocity_nonneg`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L127)
- [`ContinuousFlexibility.capDownwardVelocity_pos`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L133)
- [`ContinuousFlexibility.capDownwardVelocity_half`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L139)
- [`ContinuousFlexibility.hasDerivAt_capRadialOffset`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L143)
- [`ContinuousFlexibility.hasDerivAt_capHeightDrop`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L150)
- [`ContinuousFlexibility.contDiff_capRadialOffset`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L157)
- [`ContinuousFlexibility.contDiff_capHeightDrop`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L165)
- [`ContinuousFlexibility.capRadialOffset_eq_left`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L173)
- [`ContinuousFlexibility.capHeightDrop_eq_left`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L179)
- [`ContinuousFlexibility.capRadialOffset_zero`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L185)
- [`ContinuousFlexibility.capHeightDrop_zero`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L187)
- [`ContinuousFlexibility.capRadialOffset_one`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L189)
- [`ContinuousFlexibility.capRadialOffset_reflection`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L196)
- [`ContinuousFlexibility.capHeightDrop_reflection`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L208)
- [`ContinuousFlexibility.capRadialOffset_eq_right`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L219)
- [`ContinuousFlexibility.capHeightDrop_eq_right`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L223)
- [`ContinuousFlexibility.capDrop_pos`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L229)
- [`ContinuousFlexibility.capRadialOffset_pos_left`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L236)
- [`ContinuousFlexibility.capRadialOffset_pos`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L243)
- [`ContinuousFlexibility.capRadialOffset_nonneg`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L249)
- [`ContinuousFlexibility.monotone_capHeightDrop`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L258)
- [`ContinuousFlexibility.strictMonoOn_capHeightDrop`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L261)
- [`ContinuousFlexibility.capHeightDrop_lt`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L268)
- [`ContinuousFlexibility.capNormalizedMeridian_ne_of_lt`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L286)
- [`ContinuousFlexibility.capNormalizedMeridian_injective`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L300)
- [`ContinuousFlexibility.contDiff_capMeridianRadius`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L308)
- [`ContinuousFlexibility.contDiff_capMeridianHeight`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L311)
- [`ContinuousFlexibility.contDiff_capMeridian`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L314)
- [`ContinuousFlexibility.hasDerivAt_capMeridianRadius`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L317)
- [`ContinuousFlexibility.hasDerivAt_capMeridianHeight`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L324)
- [`ContinuousFlexibility.capMeridian_unit_speed`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L332)
- [`ContinuousFlexibility.capMeridian_injective`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L339)
- [`ContinuousFlexibility.capMeridianRadius_eq_left`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L350)
- [`ContinuousFlexibility.capMeridianHeight_eq_left`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L356)
- [`ContinuousFlexibility.capMeridianRadius_eq_right`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L361)
- [`ContinuousFlexibility.capMeridianHeight_eq_right`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L368)
- [`ContinuousFlexibility.capMeridianRadius_core_le`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L373)
- [`ContinuousFlexibility.capMeridianRadius_core_lt`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L380)
- [`ContinuousFlexibility.capMeridian_top_axis`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L387)
- [`ContinuousFlexibility.capMeridian_bottom_axis`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L392)
- [`ContinuousFlexibility.capMeridianRadius_pos`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L399)
- [`ContinuousFlexibility.capMeridianRadius_zero_iff`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L409)
- [`ContinuousFlexibility.capMeridianRadius_nonneg`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L428)
- [`ContinuousFlexibility.capLength_pos`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L440)
- [`ContinuousFlexibility.capLength_bottom_le`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L443)
- [`ContinuousFlexibility.capLength_bottom_lt`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L448)
- [`ContinuousFlexibility.capMeridianHeight_capLength_below`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L452)
- [`ContinuousFlexibility.capMeridian_zero`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L458)
- [`ContinuousFlexibility.capMeridian_length`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L461)
- [`ContinuousFlexibility.capMeridian_left_collar`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L465)
- [`ContinuousFlexibility.capMeridian_right_collar`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L469)
- [`ContinuousFlexibility.hasDerivAt_capMeridian`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L473)
- [`ContinuousFlexibility.capMeridian_deriv_ne_zero`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L478)
- [`ContinuousFlexibility.antitone_capMeridianHeight`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L487)
- [`ContinuousFlexibility.capMeridianHeight_strict`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L495)
- [`ContinuousFlexibility.capHeightDrop_bounds`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L505)
- [`ContinuousFlexibility.capMeridianHeight_bounds`](../ContinuousFlexibility/Geometry/CapMeridian.lean#L515)

[CapRevolution.lean](../ContinuousFlexibility/Geometry/CapRevolution.lean)：

- [`ContinuousFlexibility.capRevolution_zero`](../ContinuousFlexibility/Geometry/CapRevolution.lean#L30)
- [`ContinuousFlexibility.capRevolution_one`](../ContinuousFlexibility/Geometry/CapRevolution.lean#L34)
- [`ContinuousFlexibility.capRevolution_two`](../ContinuousFlexibility/Geometry/CapRevolution.lean#L38)
- [`ContinuousFlexibility.contDiff_capRevolution`](../ContinuousFlexibility/Geometry/CapRevolution.lean#L41)
- [`ContinuousFlexibility.capRevolution_fderiv`](../ContinuousFlexibility/Geometry/CapRevolution.lean#L48)
- [`ContinuousFlexibility.capRevolution_pullback_metric`](../ContinuousFlexibility/Geometry/CapRevolution.lean#L72)
- [`ContinuousFlexibility.capRevolution_fderiv_injective`](../ContinuousFlexibility/Geometry/CapRevolution.lean#L88)
- [`ContinuousFlexibility.capRevolution_left_collar`](../ContinuousFlexibility/Geometry/CapRevolution.lean#L103)
- [`ContinuousFlexibility.capRevolution_right_collar`](../ContinuousFlexibility/Geometry/CapRevolution.lean#L111)
- [`ContinuousFlexibility.capCylinderMap_zero`](../ContinuousFlexibility/Geometry/CapRevolution.lean#L125)
- [`ContinuousFlexibility.capCylinderMap_one`](../ContinuousFlexibility/Geometry/CapRevolution.lean#L129)
- [`ContinuousFlexibility.capCylinderMap_two`](../ContinuousFlexibility/Geometry/CapRevolution.lean#L133)
- [`ContinuousFlexibility.continuous_capCylinderMap`](../ContinuousFlexibility/Geometry/CapRevolution.lean#L137)
- [`ContinuousFlexibility.capCylinderMap_radial_sq`](../ContinuousFlexibility/Geometry/CapRevolution.lean#L148)
- [`ContinuousFlexibility.capCylinderMap_injOn`](../ContinuousFlexibility/Geometry/CapRevolution.lean#L161)
- [`ContinuousFlexibility.continuous_capClosedCylinderMap`](../ContinuousFlexibility/Geometry/CapRevolution.lean#L196)
- [`ContinuousFlexibility.capClosedCylinderMap_injective`](../ContinuousFlexibility/Geometry/CapRevolution.lean#L201)
- [`ContinuousFlexibility.isEmbedding_capClosedCylinderMap`](../ContinuousFlexibility/Geometry/CapRevolution.lean#L211)
- [`ContinuousFlexibility.capCylinderMap_core_outside`](../ContinuousFlexibility/Geometry/CapRevolution.lean#L216)
- [`ContinuousFlexibility.capCylinderMap_inside_cylinder_bottom`](../ContinuousFlexibility/Geometry/CapRevolution.lean#L225)

[GraphCapAttachment.lean](../ContinuousFlexibility/Geometry/GraphCapAttachment.lean)：

- [`ContinuousFlexibility.capDisk_physical_boundary`](../ContinuousFlexibility/Geometry/GraphCapAttachment.lean#L35)
- [`ContinuousFlexibility.IsometricGraphDevelopment.phase_flat_outside`](../ContinuousFlexibility/Geometry/GraphCapAttachment.lean#L45)
- [`ContinuousFlexibility.IsometricGraphDevelopment.phase_disk_projection_bound`](../ContinuousFlexibility/Geometry/GraphCapAttachment.lean#L52)
- [`ContinuousFlexibility.IsometricGraphDevelopment.graph_cap_intersection`](../ContinuousFlexibility/Geometry/GraphCapAttachment.lean#L64)
- [`ContinuousFlexibility.IsometricGraphDevelopment.graph_cap_open_collar`](../ContinuousFlexibility/Geometry/GraphCapAttachment.lean#L104)
- [`ContinuousFlexibility.IsometricGraphDevelopment.exists_fixed_cap_attachment`](../ContinuousFlexibility/Geometry/GraphCapAttachment.lean#L113)

[MarkedCapDisk.lean](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean)：

- [`ContinuousFlexibility.markedCapCutoff_bounds`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L41)
- [`ContinuousFlexibility.markedCapCutoff_eq_zero`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L48)
- [`ContinuousFlexibility.markedCapCutoff_eq_one`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L54)
- [`ContinuousFlexibility.markedCapCutoff_axis_germ`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L60)
- [`ContinuousFlexibility.contDiff_markedCapCutoff`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L68)
- [`ContinuousFlexibility.markedCap_contDiff_base`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L80)
- [`ContinuousFlexibility.markedCap_contDiff_height`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L89)
- [`ContinuousFlexibility.contDiff_markedCapBump`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L97)
- [`ContinuousFlexibility.contDiff_markedCapMap`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L103)
- [`ContinuousFlexibility.markedCapBump_nonneg`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L108)
- [`ContinuousFlexibility.markedCapBump_eq_zero_bottom`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L113)
- [`ContinuousFlexibility.markedCap_meridian_middle_lower`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L140)
- [`ContinuousFlexibility.markedCapCenter_radius`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L150)
- [`ContinuousFlexibility.markedCap_marker_support_radius`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L163)
- [`ContinuousFlexibility.markedCapBump_nonzero_top`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L180)
- [`ContinuousFlexibility.markedCapBump_nonzero_height`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L195)
- [`ContinuousFlexibility.markedCapBump_eq_zero_of_not_top`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L201)
- [`ContinuousFlexibility.markedCapMap_base`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L208)
- [`ContinuousFlexibility.markedCapMap_height`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L212)
- [`ContinuousFlexibility.markedCapMap_injOn`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L216)
- [`ContinuousFlexibility.markedCap_top_height_germ`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L247)
- [`ContinuousFlexibility.markedCap_base_fderiv_injective_top`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L257)
- [`ContinuousFlexibility.markedCapBump_fderiv_eq_zero`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L272)
- [`ContinuousFlexibility.markedCapMap_fderiv_injective`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L281)
- [`ContinuousFlexibility.isEmbedding_markedCapEmbeddingMap`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L303)
- [`ContinuousFlexibility.markedCap_smooth_embedding`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L314)
- [`ContinuousFlexibility.markedCap_marker_support_distance`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L324)
- [`ContinuousFlexibility.markedCap_marker_support_lower`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L335)
- [`ContinuousFlexibility.markedCapBump_eq_zero_of_inner`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L348)
- [`ContinuousFlexibility.markedCapMap_eq_capDiskMap_of_inner`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L357)
- [`ContinuousFlexibility.markedCapMap_rimChart`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L366)
- [`ContinuousFlexibility.markedCapMap_rimChart_germ`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L380)
- [`ContinuousFlexibility.markedCapMap_rim_germ`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L390)
- [`ContinuousFlexibility.markedCap_marker_center_positive`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L406)
- [`ContinuousFlexibility.markedCapCenterParameter_mem`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L418)
- [`ContinuousFlexibility.markedCapBump_center_positive`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L430)
- [`ContinuousFlexibility.markedCapBump_bounds`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L444)
- [`ContinuousFlexibility.markedCapHeight_bounds`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L456)
- [`ContinuousFlexibility.markedCapBump_zero_germ_of_quadratic`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L466)
- [`ContinuousFlexibility.markedCapBump_zero_germ_of_not_top`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L480)
- [`ContinuousFlexibility.markedCapMap_germ_of_not_top`](../ContinuousFlexibility/Geometry/MarkedCapDisk.lean#L502)

[MarkedCapDiskCurvature.lean](../ContinuousFlexibility/Geometry/MarkedCapDiskCurvature.lean)：

- [`ContinuousFlexibility.contDiff_markedCapCoordinates`](../ContinuousFlexibility/Geometry/MarkedCapDiskCurvature.lean#L38)
- [`ContinuousFlexibility.contDiff_markedCapNormal`](../ContinuousFlexibility/Geometry/MarkedCapDiskCurvature.lean#L42)
- [`ContinuousFlexibility.markedCapNormal_eq_top`](../ContinuousFlexibility/Geometry/MarkedCapDiskCurvature.lean#L48)
- [`ContinuousFlexibility.markedCapNormal_eq_capDiskNormal`](../ContinuousFlexibility/Geometry/MarkedCapDiskCurvature.lean#L91)
- [`ContinuousFlexibility.isUnitSurfaceNormal_markedCap`](../ContinuousFlexibility/Geometry/MarkedCapDiskCurvature.lean#L135)
- [`ContinuousFlexibility.markedCapNormal_norm`](../ContinuousFlexibility/Geometry/MarkedCapDiskCurvature.lean#L155)
- [`ContinuousFlexibility.markedCapNormal_orthogonal`](../ContinuousFlexibility/Geometry/MarkedCapDiskCurvature.lean#L160)
- [`ContinuousFlexibility.markedCapCoordinates_fderiv_injective_top`](../ContinuousFlexibility/Geometry/MarkedCapDiskCurvature.lean#L178)
- [`ContinuousFlexibility.surfaceShapeMatrix_markedCap_top`](../ContinuousFlexibility/Geometry/MarkedCapDiskCurvature.lean#L187)
- [`ContinuousFlexibility.surfaceGaussianCurvature_markedCap_top`](../ContinuousFlexibility/Geometry/MarkedCapDiskCurvature.lean#L207)
- [`ContinuousFlexibility.surfaceShapeMatrix_markedCap_of_not_top`](../ContinuousFlexibility/Geometry/MarkedCapDiskCurvature.lean#L218)
- [`ContinuousFlexibility.surfaceGaussianCurvature_markedCap_of_not_top`](../ContinuousFlexibility/Geometry/MarkedCapDiskCurvature.lean#L227)
- [`ContinuousFlexibility.surfaceMeanCurvature_markedCap_of_not_top`](../ContinuousFlexibility/Geometry/MarkedCapDiskCurvature.lean#L234)
- [`ContinuousFlexibility.markedCapCenterParameter_parameter`](../ContinuousFlexibility/Geometry/MarkedCapDiskCurvature.lean#L241)
- [`ContinuousFlexibility.markedCapCoordinates_center`](../ContinuousFlexibility/Geometry/MarkedCapDiskCurvature.lean#L251)
- [`ContinuousFlexibility.markedCapCoordinates_eq_zero_iff`](../ContinuousFlexibility/Geometry/MarkedCapDiskCurvature.lean#L259)
- [`ContinuousFlexibility.markedCapNormal_center`](../ContinuousFlexibility/Geometry/MarkedCapDiskCurvature.lean#L277)
- [`ContinuousFlexibility.surfaceShapeMatrix_markedCap_center`](../ContinuousFlexibility/Geometry/MarkedCapDiskCurvature.lean#L285)
- [`ContinuousFlexibility.surfaceShapeMatrix_markedCap_center_eigenvectors`](../ContinuousFlexibility/Geometry/MarkedCapDiskCurvature.lean#L316)
- [`ContinuousFlexibility.surfaceGaussianCurvature_markedCap_center`](../ContinuousFlexibility/Geometry/MarkedCapDiskCurvature.lean#L353)
- [`ContinuousFlexibility.exists_markedCap_unique_peak`](../ContinuousFlexibility/Geometry/MarkedCapDiskCurvature.lean#L393)

[MarkedCapSpecification.lean](../ContinuousFlexibility/Geometry/MarkedCapSpecification.lean)：

- [`ContinuousFlexibility.markedCap_hasDistinctPrincipalDirections`](../ContinuousFlexibility/Geometry/MarkedCapSpecification.lean#L93)
- [`ContinuousFlexibility.IsometricGraphDevelopment.exists_markedCapSpecification_given_length`](../ContinuousFlexibility/Geometry/MarkedCapSpecification.lean#L238)
- [`ContinuousFlexibility.markedCap_G06_statement`](../ContinuousFlexibility/Geometry/MarkedCapSpecification.lean#L267)


<a id="g07"></a>
## G07 标准球面参数化和固定度量

**状态：** 已有部分已编译子结果。**分支：** 几何闭合。主定理必要节点。

**数学陈述：** 在标准S²上拼出光滑嵌入F₀，北侧为图盘、南侧为补帽，并定义光滑正定gΣ=F₀*δ。

**证明提纲：** 用立体投影的扩大半球圆盘坐标及共同开领圈拼接；显式参数化补帽的axis和rim。

**直接依赖：** [G05](#g05), [G06](#g06), [D01](#d01)

**论文定位：** [02-geometry.tex:146–168](../paper/flexible-surface-rewrite/02-geometry.tex#L146)；[02-geometry.tex:230–239](../paper/flexible-surface-rewrite/02-geometry.tex#L230)

**目标文件：** `ContinuousFlexibility/Geometry/G07.lean`（节点组织目标；实际已存在的证明文件见下方，整个节点尚未完成）

**验收条件：**

- 不用equator处退化的xy半球投影
- 直接标准S²避免另造曲面后偷用分类定理
- metric是实际F₀的拉回

**已经完成的子结果：**

- 同一标准S²南北图、真实帽盘径向拼接，以及实际内盘/图盘/补帽的闭圆盘同胚、非空内部、正规闭性和精确补集关系已编译。
- 真实图盘/内盘/补帽拓扑和逐点固定已组装成同一个标记球面族的正式 FixedDiskRegions。

**仍待闭合的义务：**

- 任意合约帽的 InitialSphereData 全规格桥接仍需独立验收。

**现有 Lean 证明：**

[CapSphereProfile.lean](../ContinuousFlexibility/Geometry/CapSphereProfile.lean)：

- [`ContinuousFlexibility.contDiff_capSphereCutoff`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L44)
- [`ContinuousFlexibility.capSphereCutoff_nonneg`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L47)
- [`ContinuousFlexibility.capSphereCutoff_le_one`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L50)
- [`ContinuousFlexibility.capSphereCutoff_eq_zero`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L53)
- [`ContinuousFlexibility.capSphereCutoff_eq_one`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L56)
- [`ContinuousFlexibility.capSphereHead_nonneg`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L59)
- [`ContinuousFlexibility.capSphereTail_nonneg`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L62)
- [`ContinuousFlexibility.capSphereHead_eq_one`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L65)
- [`ContinuousFlexibility.capSphereTail_eq_zero`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L68)
- [`ContinuousFlexibility.capSphereTail_zero_germ`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L71)
- [`ContinuousFlexibility.contDiff_capSphereHead`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L77)
- [`ContinuousFlexibility.contDiff_capSphereTail`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L80)
- [`ContinuousFlexibility.capSphereHeadIntegral_pos`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L89)
- [`ContinuousFlexibility.capSphereTailIntegral_nonneg`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L96)
- [`ContinuousFlexibility.capSphereTailIntegral_le_one`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L119)
- [`ContinuousFlexibility.capSphereSlope_pos`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L139)
- [`ContinuousFlexibility.contDiff_capSphereSpeed`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L145)
- [`ContinuousFlexibility.capSphereSpeed_eq_left`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L148)
- [`ContinuousFlexibility.capSphereSpeed_eq_right`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L152)
- [`ContinuousFlexibility.capSphereSpeed_pos`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L156)
- [`ContinuousFlexibility.hasDerivAt_capSphereProfile`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L171)
- [`ContinuousFlexibility.contDiff_capSphereProfile`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L178)
- [`ContinuousFlexibility.capSphereProfile_zero`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L186)
- [`ContinuousFlexibility.capSphereProfile_one`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L189)
- [`ContinuousFlexibility.capSphereProfile_eq_left`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L200)
- [`ContinuousFlexibility.capSphereProfile_eq_right`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L207)
- [`ContinuousFlexibility.strictMono_capSphereProfile`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L230)
- [`ContinuousFlexibility.capSphereRatio_mem`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L237)
- [`ContinuousFlexibility.capSphereProfile_pos`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L243)
- [`ContinuousFlexibility.capSphereProfile_nonneg`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L247)
- [`ContinuousFlexibility.capSphereRadialMap_zero`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L251)
- [`ContinuousFlexibility.capSphereRadialMap_boundary`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L254)
- [`ContinuousFlexibility.capSphereRadialMap_eq_left`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L258)
- [`ContinuousFlexibility.capSphereRadialMap_zero_germ`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L267)
- [`ContinuousFlexibility.contDiff_capSphereRadialMap`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L275)
- [`ContinuousFlexibility.capSphereRadialMap_radius`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L287)
- [`ContinuousFlexibility.capSphereRadialMap_injective`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L297)
- [`ContinuousFlexibility.capSphereRadialMap_mapsTo_disk`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L314)
- [`ContinuousFlexibility.capSphereRadialMap_surjOn_disk`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L322)
- [`ContinuousFlexibility.capSphereRadialMap_bijOn_disk`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L357)
- [`ContinuousFlexibility.hasFDerivAt_capSphereRadialMap_zero`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L363)
- [`ContinuousFlexibility.capSphereRadialMap_polarMap`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L371)
- [`ContinuousFlexibility.capSphereRadialMap_polar_germ`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L386)
- [`ContinuousFlexibility.capSphereRadialMap_fderiv_injective`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L394)
- [`ContinuousFlexibility.capDiskParameter_capSphereRadialMap`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L445)
- [`ContinuousFlexibility.capDiskMap_capSphereRadialMap_collar`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L457)
- [`ContinuousFlexibility.capDiskMap_capSphereRadialMap_rim_germ`](../ContinuousFlexibility/Geometry/CapSphereProfile.lean#L478)

[SphereFixedDisks.lean](../ContinuousFlexibility/Geometry/SphereFixedDisks.lean)：

- [`ContinuousFlexibility.sphereNorthClosedDisk_eq_image`](../ContinuousFlexibility/Geometry/SphereFixedDisks.lean#L40)
- [`ContinuousFlexibility.sphereGraphDisk_eq_northClosedDisk`](../ContinuousFlexibility/Geometry/SphereFixedDisks.lean#L88)
- [`ContinuousFlexibility.sphereInnerDisk_eq_northClosedDisk`](../ContinuousFlexibility/Geometry/SphereFixedDisks.lean#L122)
- [`ContinuousFlexibility.isCompact_sphereNorthClosedDisk`](../ContinuousFlexibility/Geometry/SphereFixedDisks.lean#L196)
- [`ContinuousFlexibility.isClosed_sphereGraphDisk`](../ContinuousFlexibility/Geometry/SphereFixedDisks.lean#L200)
- [`ContinuousFlexibility.isClosed_sphereComplementaryCap`](../ContinuousFlexibility/Geometry/SphereFixedDisks.lean#L204)
- [`ContinuousFlexibility.isCompact_sphereInnerDisk`](../ContinuousFlexibility/Geometry/SphereFixedDisks.lean#L208)
- [`ContinuousFlexibility.isClosed_sphereInnerDisk`](../ContinuousFlexibility/Geometry/SphereFixedDisks.lean#L213)
- [`ContinuousFlexibility.interior_closedCartesianDisk`](../ContinuousFlexibility/Geometry/SphereFixedDisks.lean#L216)
- [`ContinuousFlexibility.interior_sphereNorthClosedDisk`](../ContinuousFlexibility/Geometry/SphereFixedDisks.lean#L228)
- [`ContinuousFlexibility.closure_openCartesianDisk`](../ContinuousFlexibility/Geometry/SphereFixedDisks.lean#L237)
- [`ContinuousFlexibility.sphereNorthClosedDisk_interior_nonempty`](../ContinuousFlexibility/Geometry/SphereFixedDisks.lean#L248)
- [`ContinuousFlexibility.closure_interior_sphereNorthClosedDisk`](../ContinuousFlexibility/Geometry/SphereFixedDisks.lean#L255)
- [`ContinuousFlexibility.sphereGraphDisk_interior_nonempty`](../ContinuousFlexibility/Geometry/SphereFixedDisks.lean#L276)
- [`ContinuousFlexibility.closure_interior_sphereGraphDisk`](../ContinuousFlexibility/Geometry/SphereFixedDisks.lean#L280)
- [`ContinuousFlexibility.closure_interior_sphereInnerDisk`](../ContinuousFlexibility/Geometry/SphereFixedDisks.lean#L284)
- [`ContinuousFlexibility.sphereNorthChart_radius_lt_one_iff`](../ContinuousFlexibility/Geometry/SphereFixedDisks.lean#L289)
- [`ContinuousFlexibility.interior_sphereGraphDisk`](../ContinuousFlexibility/Geometry/SphereFixedDisks.lean#L313)
- [`ContinuousFlexibility.sphereComplementaryCap_eq_compl_interior`](../ContinuousFlexibility/Geometry/SphereFixedDisks.lean#L324)
- [`ContinuousFlexibility.sphereComplementaryCap_eq_diff_interior`](../ContinuousFlexibility/Geometry/SphereFixedDisks.lean#L330)
- [`ContinuousFlexibility.closure_interior_sphereComplementaryCap`](../ContinuousFlexibility/Geometry/SphereFixedDisks.lean#L334)
- [`ContinuousFlexibility.sphereGraphDisk_union_complementaryCap`](../ContinuousFlexibility/Geometry/SphereFixedDisks.lean#L339)
- [`ContinuousFlexibility.sphereGraphDisk_inter_complementaryCap`](../ContinuousFlexibility/Geometry/SphereFixedDisks.lean#L345)
- [`ContinuousFlexibility.sphereInnerDisk_subset_interior_graphDisk`](../ContinuousFlexibility/Geometry/SphereFixedDisks.lean#L351)
- [`ContinuousFlexibility.sphereInnerDisk_interior_nonempty`](../ContinuousFlexibility/Geometry/SphereFixedDisks.lean#L358)
- [`ContinuousFlexibility.sphereComplementaryCap_interior_nonempty`](../ContinuousFlexibility/Geometry/SphereFixedDisks.lean#L365)
- [`ContinuousFlexibility.disjoint_sphereInnerDisk_complementaryCap`](../ContinuousFlexibility/Geometry/SphereFixedDisks.lean#L380)
- [`ContinuousFlexibility.sphereGraphDiskPhysicalHomeomorph_apply`](../ContinuousFlexibility/Geometry/SphereFixedDisks.lean#L386)
- [`ContinuousFlexibility.sphereComplementaryCapHomeomorph_apply`](../ContinuousFlexibility/Geometry/SphereFixedDisks.lean#L390)
- [`ContinuousFlexibility.sphereGraphCapFamily_image_graphDisk`](../ContinuousFlexibility/Geometry/SphereFixedDisks.lean#L393)
- [`ContinuousFlexibility.sphereGraphCapFamily_image_complementaryCap`](../ContinuousFlexibility/Geometry/SphereFixedDisks.lean#L411)
- [`ContinuousFlexibility.sphereGraphCapFamily_fixed_innerDisk`](../ContinuousFlexibility/Geometry/SphereFixedDisks.lean#L437)
- [`ContinuousFlexibility.sphereGraphCapFamily_image_innerDisk`](../ContinuousFlexibility/Geometry/SphereFixedDisks.lean#L445)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphereFamily_fixed_disks`](../ContinuousFlexibility/Geometry/SphereFixedDisks.lean#L470)

[SphereFixedDiskBridges.lean](../ContinuousFlexibility/Geometry/SphereFixedDiskBridges.lean)：

- [`ContinuousFlexibility.sphereDiskRegions_inner_region`](../ContinuousFlexibility/Geometry/SphereFixedDiskBridges.lean#L54)


<a id="g08"></a>
## G08 相位族联合光滑、周期与固定区域

**状态：** 已有部分已编译子结果。**分支：** 几何闭合。主定理必要节点。

**数学陈述：** 图盘上Fτ=R_(-2πτ)F₀R_(2πτ)，补帽固定；证明联合光滑、Fτ+1=Fτ，以及内盘和补帽逐点固定。

**证明提纲：** 在开领圈上两旋转精确抵消，因此两变量拼接光滑；分别证明内盘和外帽公式。

**直接依赖：** [G03](#g03), [G07](#g07)

**论文定位：** [01-introduction.tex:172–174](../paper/flexible-surface-rewrite/01-introduction.tex#L172)，`eq:phase-family`；[02-geometry.tex:230–239](../paper/flexible-surface-rewrite/02-geometry.tex#L230)

**目标文件：** `ContinuousFlexibility/Geometry/G08.lean`（节点组织目标；实际已存在的证明文件见下方，整个节点尚未完成）

**验收条件：**

- 逐参数光滑不替代联合光滑
- 两个固定区域具有非空内部和规定圆盘拓扑
- q已固定，τ是独立相位

**已经完成的子结果：**

- 实际R_t的群律、period1、联合C∞、真正Euclidean radius和cartesianMetric不变
- 按论文外R_-t内R_t构造同一个D的图族，真实联合C∞、period1和t=0原图
- 内闭盘≤a与外域>b逐点固定，真实E3轴LinearIsometryEquiv及其联合C∞；没有将逐参数smooth冒充联合smooth
- 同一实际Core的标准S²拼接族已证明联合C∞、一周期、内区和补帽点值固定、完整像等于实际图盘与实际帽的并。

**仍待闭合的义务：**

- 实际联合光滑/周期/固定值定理已齐；尚待C00/G07完整接口验收和同一见证组装。

**现有 Lean 证明：**

[GraphFamilyImage.lean](../ContinuousFlexibility/Contracts/GraphFamilyImage.lean)：

- [`ContinuousFlexibility.axialRotationMap_base`](../ContinuousFlexibility/Contracts/GraphFamilyImage.lean#L24)
- [`ContinuousFlexibility.axialRotationMap_height`](../ContinuousFlexibility/Contracts/GraphFamilyImage.lean#L28)
- [`ContinuousFlexibility.e3_eq_of_base_height`](../ContinuousFlexibility/Contracts/GraphFamilyImage.lean#L32)
- [`ContinuousFlexibility.axialRotationMap_zero`](../ContinuousFlexibility/Contracts/GraphFamilyImage.lean#L40)
- [`ContinuousFlexibility.axialRotationMap_add`](../ContinuousFlexibility/Contracts/GraphFamilyImage.lean#L45)
- [`ContinuousFlexibility.axialRotationMap_inner`](../ContinuousFlexibility/Contracts/GraphFamilyImage.lean#L51)
- [`ContinuousFlexibility.axialRotation_apply`](../ContinuousFlexibility/Contracts/GraphFamilyImage.lean#L101)
- [`ContinuousFlexibility.contDiff_axialRotation_joint`](../ContinuousFlexibility/Contracts/GraphFamilyImage.lean#L104)
- [`ContinuousFlexibility.axialRotation_periodic`](../ContinuousFlexibility/Contracts/GraphFamilyImage.lean#L121)
- [`ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_eq_axialRotation`](../ContinuousFlexibility/Contracts/GraphFamilyImage.lean#L129)
- [`ContinuousFlexibility.planarRotation_image_closedCartesianDisk`](../ContinuousFlexibility/Contracts/GraphFamilyImage.lean#L139)

[GraphRotationFamily.lean](../ContinuousFlexibility/Geometry/GraphRotationFamily.lean)：

- [`ContinuousFlexibility.rotationConjugate_apply`](../ContinuousFlexibility/Geometry/GraphRotationFamily.lean#L31)
- [`ContinuousFlexibility.contDiff_rotationConjugate`](../ContinuousFlexibility/Geometry/GraphRotationFamily.lean#L38)
- [`ContinuousFlexibility.contDiff_rotatedHeight`](../ContinuousFlexibility/Geometry/GraphRotationFamily.lean#L43)
- [`ContinuousFlexibility.contDiff_rotationConjugate_joint`](../ContinuousFlexibility/Geometry/GraphRotationFamily.lean#L46)
- [`ContinuousFlexibility.fderiv_rotationConjugate`](../ContinuousFlexibility/Geometry/GraphRotationFamily.lean#L102)
- [`ContinuousFlexibility.fderiv_rotatedHeight`](../ContinuousFlexibility/Geometry/GraphRotationFamily.lean#L112)

[PlanarRotations.lean](../ContinuousFlexibility/Geometry/PlanarRotations.lean)：

- [`ContinuousFlexibility.planeRotationLinearMap_commute`](../ContinuousFlexibility/Geometry/PlanarRotations.lean#L22)
- [`ContinuousFlexibility.planarRotation_metric`](../ContinuousFlexibility/Geometry/PlanarRotations.lean#L28)
- [`ContinuousFlexibility.planarRotation_zero`](../ContinuousFlexibility/Geometry/PlanarRotations.lean#L33)
- [`ContinuousFlexibility.planarRotation_add`](../ContinuousFlexibility/Geometry/PlanarRotations.lean#L36)
- [`ContinuousFlexibility.planarRotation_neg_cancel`](../ContinuousFlexibility/Geometry/PlanarRotations.lean#L42)
- [`ContinuousFlexibility.planarRotation_cancel_neg`](../ContinuousFlexibility/Geometry/PlanarRotations.lean#L46)
- [`ContinuousFlexibility.planarRotation_commute`](../ContinuousFlexibility/Geometry/PlanarRotations.lean#L50)
- [`ContinuousFlexibility.planarRotation_add_one`](../ContinuousFlexibility/Geometry/PlanarRotations.lean#L55)
- [`ContinuousFlexibility.planarRotation_neg_add_one`](../ContinuousFlexibility/Geometry/PlanarRotations.lean#L59)
- [`ContinuousFlexibility.planarRotationHomeomorph_apply`](../ContinuousFlexibility/Geometry/PlanarRotations.lean#L74)
- [`ContinuousFlexibility.planarRotationHomeomorph_symm_apply`](../ContinuousFlexibility/Geometry/PlanarRotations.lean#L77)
- [`ContinuousFlexibility.contDiff_planarRotation_joint`](../ContinuousFlexibility/Geometry/PlanarRotations.lean#L80)
- [`ContinuousFlexibility.cartesianRadius_sq_coordinates`](../ContinuousFlexibility/Geometry/PlanarRotations.lean#L89)
- [`ContinuousFlexibility.cartesianRadius_planarRotation`](../ContinuousFlexibility/Geometry/PlanarRotations.lean#L94)
- [`ContinuousFlexibility.cartesianMetric_planarRotation`](../ContinuousFlexibility/Geometry/PlanarRotations.lean#L100)

[SphereCapGluing.lean](../ContinuousFlexibility/Geometry/SphereCapGluing.lean)：

- [`ContinuousFlexibility.contMDiffAt_sphereNorthFamily`](../ContinuousFlexibility/Geometry/SphereCapGluing.lean#L40)
- [`ContinuousFlexibility.contMDiffAt_sphereSouthCap`](../ContinuousFlexibility/Geometry/SphereCapGluing.lean#L67)
- [`ContinuousFlexibility.sphere_equator_sources`](../ContinuousFlexibility/Geometry/SphereCapGluing.lean#L74)
- [`ContinuousFlexibility.sphere_equator_chart_radii`](../ContinuousFlexibility/Geometry/SphereCapGluing.lean#L84)
- [`ContinuousFlexibility.sphere_chart_physical_inversion`](../ContinuousFlexibility/Geometry/SphereCapGluing.lean#L96)
- [`ContinuousFlexibility.markedCapMap_capSphereRadialMap_rim_germ`](../ContinuousFlexibility/Geometry/SphereCapGluing.lean#L103)
- [`ContinuousFlexibility.sphereGraphCap_equator_germ`](../ContinuousFlexibility/Geometry/SphereCapGluing.lean#L125)
- [`ContinuousFlexibility.contMDiff_sphereGraphCapFamily`](../ContinuousFlexibility/Geometry/SphereCapGluing.lean#L158)
- [`ContinuousFlexibility.IsometricGraphDevelopment.contMDiff_unmarkedSphereFamily`](../ContinuousFlexibility/Geometry/SphereCapGluing.lean#L196)
- [`ContinuousFlexibility.IsometricGraphDevelopment.contMDiff_markedSphereFamily`](../ContinuousFlexibility/Geometry/SphereCapGluing.lean#L204)
- [`ContinuousFlexibility.sphereGraphCapFamily_periodic`](../ContinuousFlexibility/Geometry/SphereCapGluing.lean#L214)
- [`ContinuousFlexibility.sphereGraphCapFamily_fixed_south`](../ContinuousFlexibility/Geometry/SphereCapGluing.lean#L223)
- [`ContinuousFlexibility.sphereGraphCapFamily_fixed_inner`](../ContinuousFlexibility/Geometry/SphereCapGluing.lean#L229)
- [`ContinuousFlexibility.sphereGraphCapFamily_north`](../ContinuousFlexibility/Geometry/SphereCapGluing.lean#L237)
- [`ContinuousFlexibility.sphereGraphCapFamily_south`](../ContinuousFlexibility/Geometry/SphereCapGluing.lean#L243)
- [`ContinuousFlexibility.sphereGraphCapFamily_fixed_closed_south`](../ContinuousFlexibility/Geometry/SphereCapGluing.lean#L258)
- [`ContinuousFlexibility.sphereGraphCapFamily_range`](../ContinuousFlexibility/Geometry/SphereCapGluing.lean#L270)
- [`ContinuousFlexibility.sphereNorthInverse_eq_southInverse_of_radius_one`](../ContinuousFlexibility/Geometry/SphereCapGluing.lean#L326)
- [`ContinuousFlexibility.sphereGraphCap_cross_eq`](../ContinuousFlexibility/Geometry/SphereCapGluing.lean#L339)
- [`ContinuousFlexibility.sphereGraphCapFamily_injective`](../ContinuousFlexibility/Geometry/SphereCapGluing.lean#L388)
- [`ContinuousFlexibility.isEmbedding_sphereGraphCapFamily`](../ContinuousFlexibility/Geometry/SphereCapGluing.lean#L427)
- [`ContinuousFlexibility.markedCap_boundary`](../ContinuousFlexibility/Geometry/SphereCapGluing.lean#L445)
- [`ContinuousFlexibility.IsometricGraphDevelopment.marked_cap_meeting_subset`](../ContinuousFlexibility/Geometry/SphereCapGluing.lean#L455)
- [`ContinuousFlexibility.IsometricGraphDevelopment.exists_markedSphereFamily`](../ContinuousFlexibility/Geometry/SphereCapGluing.lean#L478)
- [`ContinuousFlexibility.sphereGraphCapFamily_north_germ`](../ContinuousFlexibility/Geometry/SphereCapGluing.lean#L498)
- [`ContinuousFlexibility.sphereGraphCapFamily_south_germ`](../ContinuousFlexibility/Geometry/SphereCapGluing.lean#L519)
- [`ContinuousFlexibility.mdifferentiable_sphereNorthCoordinates`](../ContinuousFlexibility/Geometry/SphereCapGluing.lean#L530)
- [`ContinuousFlexibility.mdifferentiable_sphereSouthCoordinates`](../ContinuousFlexibility/Geometry/SphereCapGluing.lean#L538)
- [`ContinuousFlexibility.mfderiv_sphereNorthChart_bijective`](../ContinuousFlexibility/Geometry/SphereCapGluing.lean#L546)
- [`ContinuousFlexibility.mfderiv_sphereSouthChart_bijective`](../ContinuousFlexibility/Geometry/SphereCapGluing.lean#L550)
- [`ContinuousFlexibility.sphereGraphCapFamily_mfderiv_injective`](../ContinuousFlexibility/Geometry/SphereCapGluing.lean#L567)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphereFamily_mfderiv_injective`](../ContinuousFlexibility/Geometry/SphereCapGluing.lean#L629)
- [`ContinuousFlexibility.IsometricGraphDevelopment.exists_markedSphereFamily_regular`](../ContinuousFlexibility/Geometry/SphereCapGluing.lean#L641)


<a id="g09"></a>
## G09 每一相位均为同度量嵌入

**状态：** 已有部分已编译子结果。**分支：** 几何闭合。主定理必要节点。

**数学陈述：** 每个Fτ是光滑嵌入且Fτ*δ=gΣ。

**证明提纲：** 图盘像是环境旋转的同一图、补帽保持分离；度量等式由径向内禀角旋转保持g得到，并在领圈拼合。

**直接依赖：** [G05](#g05), [G06](#g06), [G08](#g08)

**论文定位：** [02-geometry.tex:230–239](../paper/flexible-surface-rewrite/02-geometry.tex#L230)，`thm:geometric-closure`

**目标文件：** `ContinuousFlexibility/Geometry/G09.lean`（节点组织目标；实际已存在的证明文件见下方，整个节点尚未完成）

**验收条件：**

- 覆盖所有实τ
- 不能仅证明immersion或局部单射
- 嵌入是全球结论

**已经完成的子结果：**

- 每个实相位的真实全平面图和任意限制均topological embedding，实际微分单射且完整pullback tensor等于同一个cartesianMetric
- 每个闭图盘像确为原闭图盘像的真实环境轴旋转，并投影满射同一圆盘
- 通过实际逆函数定理和固定一维补空间取得库中的真IsImmersion/IsSmoothEmbedding；实际mfderiv拉回给出正定光滑bundle metric并证明所有实相位具有同一metric。

**仍待闭合的义务：**

- 实际同L的smooth embedding和fixed metric定理已齐；尚待C00正式接口的逐字段组装。
- 非全等及几何积分是其它节点，不能由embedding/metric结论推出。

**现有 Lean 证明：**

[GraphFamilyImage.lean](../ContinuousFlexibility/Contracts/GraphFamilyImage.lean)：

- [`ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_image_closedDisk`](../ContinuousFlexibility/Contracts/GraphFamilyImage.lean#L149)
- [`ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_projects_onto_disk`](../ContinuousFlexibility/Contracts/GraphFamilyImage.lean#L168)

[GraphRotationFamily.lean](../ContinuousFlexibility/Geometry/GraphRotationFamily.lean)：

- [`ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_joint_smooth`](../ContinuousFlexibility/Geometry/GraphRotationFamily.lean#L61)
- [`ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_smooth`](../ContinuousFlexibility/Geometry/GraphRotationFamily.lean#L70)
- [`ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_periodic`](../ContinuousFlexibility/Geometry/GraphRotationFamily.lean#L76)
- [`ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_zero`](../ContinuousFlexibility/Geometry/GraphRotationFamily.lean#L84)
- [`ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_embedding`](../ContinuousFlexibility/Geometry/GraphRotationFamily.lean#L90)
- [`ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_embedding_restrict`](../ContinuousFlexibility/Geometry/GraphRotationFamily.lean#L96)
- [`ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_remainder_metric`](../ContinuousFlexibility/Geometry/GraphRotationFamily.lean#L119)
- [`ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_metric`](../ContinuousFlexibility/Geometry/GraphRotationFamily.lean#L132)
- [`ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_immersion`](../ContinuousFlexibility/Geometry/GraphRotationFamily.lean#L141)
- [`ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_fixed_outside`](../ContinuousFlexibility/Geometry/GraphRotationFamily.lean#L149)
- [`ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_fixed_inside`](../ContinuousFlexibility/Geometry/GraphRotationFamily.lean#L161)

[SphereImmersion.lean](../ContinuousFlexibility/Geometry/SphereImmersion.lean)：

- [`ContinuousFlexibility.isImmersion_sphere_of_mfderiv_injective`](../ContinuousFlexibility/Geometry/SphereImmersion.lean#L192)
- [`ContinuousFlexibility.isSmoothEmbedding_sphere_of_mfderiv_injective`](../ContinuousFlexibility/Geometry/SphereImmersion.lean#L218)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphereFamily_isImmersion`](../ContinuousFlexibility/Geometry/SphereImmersion.lean#L227)
- [`ContinuousFlexibility.IsometricGraphDevelopment.exists_markedSphereFamily_smoothEmbedding`](../ContinuousFlexibility/Geometry/SphereImmersion.lean#L239)

[SphereMetric.lean](../ContinuousFlexibility/Geometry/SphereMetric.lean)：

- [`ContinuousFlexibility.spherePullbackForm_apply`](../ContinuousFlexibility/Geometry/SphereMetric.lean#L34)
- [`ContinuousFlexibility.spherePullbackForm_symm`](../ContinuousFlexibility/Geometry/SphereMetric.lean#L39)
- [`ContinuousFlexibility.spherePullbackForm_pos`](../ContinuousFlexibility/Geometry/SphereMetric.lean#L45)
- [`ContinuousFlexibility.spherePullbackForm_isVonNBounded`](../ContinuousFlexibility/Geometry/SphereMetric.lean#L57)
- [`ContinuousFlexibility.spherePullbackForm_contMDiff`](../ContinuousFlexibility/Geometry/SphereMetric.lean#L78)
- [`ContinuousFlexibility.sphere_mvfderiv_congr`](../ContinuousFlexibility/Geometry/SphereMetric.lean#L137)
- [`ContinuousFlexibility.sphere_mvfderiv_comp`](../ContinuousFlexibility/Geometry/SphereMetric.lean#L143)
- [`ContinuousFlexibility.contMDiffAt_sphereNorthPlanarMap`](../ContinuousFlexibility/Geometry/SphereMetric.lean#L153)
- [`ContinuousFlexibility.sphereFamilyForm_phase_invariant`](../ContinuousFlexibility/Geometry/SphereMetric.lean#L169)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphereFamilyForm_phase_invariant`](../ContinuousFlexibility/Geometry/SphereMetric.lean#L206)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphereFamilyForm_pos`](../ContinuousFlexibility/Geometry/SphereMetric.lean#L215)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphereFamily_slice_contMDiff`](../ContinuousFlexibility/Geometry/SphereMetric.lean#L222)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphereMetric_inner`](../ContinuousFlexibility/Geometry/SphereMetric.lean#L241)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphereFamily_pullback_metric`](../ContinuousFlexibility/Geometry/SphereMetric.lean#L248)
- [`ContinuousFlexibility.IsometricGraphDevelopment.exists_markedSphereFamily_fixedMetric`](../ContinuousFlexibility/Geometry/SphereMetric.lean#L265)


<a id="g10"></a>
## G10 径向盘的边界等距刚性

**状态：** 已有部分已编译子结果。**分支：** 几何闭合。主定理必要节点。

**数学陈述：** 对本构造的径向盘度量，光滑内禀等距自微分同胚H若在外领圈等于Rθ，则全盘等于Rθ。

**证明提纲：** 采用Cartesian一阶jet的实际ODE传播：从真实metric identity及二阶偏导对称推导Hessian/Christoffel变换式，沿盘内直线比较(H∘γ,DH∘γ)与(γ,Id)，由紧管道导数界得到统一Lipschitz常数并应用实际ODE唯一性；闭盘由连续性推广。径向距离路线保留作后备。

**直接依赖：** [C00](#c00)

**论文定位：** [02-geometry.tex:241–248](../paper/flexible-surface-rewrite/02-geometry.tex#L241)

**目标文件：** `ContinuousFlexibility/Geometry/G10.lean`（节点组织目标；实际已存在的证明文件见下方，整个节点尚未完成）

**验收条件：**

- 实际微分等距方程，不能把连接保持或1jet刚性作为新前提
- 严格构造光滑Christoffel系数、两条真实ODE解和同一紧管道Lipschitz界
- 开盘传播及闭盘连续延拓全部实际证明；不能暗用未经实现的测地线刚性

**已经完成的子结果：**

- 真实metric/Koszul导数导出Γ/Hessian与一阶jet ODE，由共同紧管道Lipschitz和实际ODE唯一性得到刚性，再绑定Core径向度量和闭盘领圈旋转。

**仍待闭合的义务：**

- 与仅在盘上定义的内禀自微分同胚陈述精确对齐（必要的领圈外延拓）并完成整节点验收。

**路线决策：** 已只读调查本地Mathlib.Analysis.ODE.ExistUnique与MeanValue，选择Cartesian 1jet ODE路线；对应依赖尚未构建，Hessian变换式/传播尚未证明。路径距离路线缺实际metric bundle及距离积分上下界，暂作后备。

**优先核查程度：** high（任务风险标记，不是已发现错误）

**现有 Lean 证明：**

[MetricIsometryRigidity.lean](../ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean)：

- [`ContinuousFlexibility.fderiv_metric_pullback_apply`](../ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean#L39)
- [`ContinuousFlexibility.fderiv_metric_evaluation_apply`](../ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean#L64)
- [`ContinuousFlexibility.differentiated_metric_identity`](../ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean#L74)
- [`ContinuousFlexibility.metric_hessian_koszul`](../ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean#L93)
- [`ContinuousFlexibility.planeMetricInverse_apply`](../ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean#L130)
- [`ContinuousFlexibility.planeMetricTensor_coordinates`](../ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean#L138)
- [`ContinuousFlexibility.inverse_metric_pairing_algebra`](../ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean#L154)
- [`ContinuousFlexibility.planeMetricInverse_pairing`](../ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean#L162)
- [`ContinuousFlexibility.planeMetricTensor_left_injective`](../ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean#L169)
- [`ContinuousFlexibility.metricKoszulValue_decompose_last`](../ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean#L195)
- [`ContinuousFlexibility.metricChristoffel_pairing`](../ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean#L207)
- [`ContinuousFlexibility.metric_hessian_transformation`](../ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean#L218)
- [`ContinuousFlexibility.metric_derivative_bijective`](../ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean#L251)
- [`ContinuousFlexibility.metricKoszulValue_decompose_second`](../ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean#L270)
- [`ContinuousFlexibility.metricChristoffel_decompose_second`](../ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean#L283)
- [`ContinuousFlexibility.metricChristoffelLinear_apply`](../ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean#L302)
- [`ContinuousFlexibility.contDiffAt_metricKoszulValue`](../ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean#L310)
- [`ContinuousFlexibility.contDiffAt_planeMetricInverse_apply`](../ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean#L323)
- [`ContinuousFlexibility.contDiffAt_metricChristoffel`](../ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean#L341)
- [`ContinuousFlexibility.contDiffAt_metricChristoffelLinear`](../ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean#L353)
- [`ContinuousFlexibility.contDiff_metricLine`](../ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean#L374)
- [`ContinuousFlexibility.hasDerivAt_metricLine`](../ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean#L377)
- [`ContinuousFlexibility.contDiff_metricJetRHS`](../ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean#L390)
- [`ContinuousFlexibility.hasDerivAt_metricJet_along_line`](../ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean#L409)
- [`ContinuousFlexibility.hasDerivAt_identityMetricJet`](../ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean#L445)
- [`ContinuousFlexibility.smooth_ode_unique_on_unit_interval`](../ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean#L453)
- [`ContinuousFlexibility.metric_isometry_oneJet_rigidity_on_convex`](../ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean#L482)
- [`ContinuousFlexibility.metric_isometry_eq_id_of_identity_germ_on_convex`](../ContinuousFlexibility/Geometry/MetricIsometryRigidity.lean#L531)

[RadialMetricRigidity.lean](../ContinuousFlexibility/Geometry/RadialMetricRigidity.lean)：

- [`ContinuousFlexibility.rankOnePlaneMetric_apply`](../ContinuousFlexibility/Geometry/RadialMetricRigidity.lean#L42)
- [`ContinuousFlexibility.rankOnePlaneMetric_symmetric`](../ContinuousFlexibility/Geometry/RadialMetricRigidity.lean#L49)
- [`ContinuousFlexibility.planeMetricDet_rankOne`](../ContinuousFlexibility/Geometry/RadialMetricRigidity.lean#L55)
- [`ContinuousFlexibility.planeMetricDet_rankOne_pos`](../ContinuousFlexibility/Geometry/RadialMetricRigidity.lean#L61)
- [`ContinuousFlexibility.contDiff_coordinateMetricCovector`](../ContinuousFlexibility/Geometry/RadialMetricRigidity.lean#L67)
- [`ContinuousFlexibility.contDiff_rankOnePlaneMetric`](../ContinuousFlexibility/Geometry/RadialMetricRigidity.lean#L71)
- [`ContinuousFlexibility.cartesianMetricTensor_apply`](../ContinuousFlexibility/Geometry/RadialMetricRigidity.lean#L79)
- [`ContinuousFlexibility.contDiff_cartesianMetricTensor`](../ContinuousFlexibility/Geometry/RadialMetricRigidity.lean#L83)
- [`ContinuousFlexibility.FlatAnnularCore.contDiff_metricTensor`](../ContinuousFlexibility/Geometry/RadialMetricRigidity.lean#L87)
- [`ContinuousFlexibility.cartesianMetricTensor_pos`](../ContinuousFlexibility/Geometry/RadialMetricRigidity.lean#L91)
- [`ContinuousFlexibility.FlatAnnularCore.metricTensor_inner`](../ContinuousFlexibility/Geometry/RadialMetricRigidity.lean#L99)
- [`ContinuousFlexibility.contDiff_cartesianMetricInverse`](../ContinuousFlexibility/Geometry/RadialMetricRigidity.lean#L105)
- [`ContinuousFlexibility.cartesianMetric_isometry_eq_id_on_convex`](../ContinuousFlexibility/Geometry/RadialMetricRigidity.lean#L139)
- [`ContinuousFlexibility.cartesianMetric_isometry_eq_rotation_on_convex`](../ContinuousFlexibility/Geometry/RadialMetricRigidity.lean#L154)
- [`ContinuousFlexibility.cartesianMetric_isometry_eq_rotation_on_closed_disk`](../ContinuousFlexibility/Geometry/RadialMetricRigidity.lean#L191)
- [`ContinuousFlexibility.FlatAnnularCore.metric_isometry_eq_rotation_on_closed_disk`](../ContinuousFlexibility/Geometry/RadialMetricRigidity.lean#L241)


<a id="g11"></a>
## G11 移动盘像不恒定

**状态：** 已有部分已编译子结果。**分支：** 几何闭合。主定理必要节点。

**数学陈述：** 非径向z蕴含存在两个相位使移动圆盘像不同。

**证明提纲：** 若像恒定，Hθ=P⁻¹RθP且zHθ=z，故Hθ保持g并在外圈等于Rθ；G10推出z对所有旋转不变，矛盾。

**直接依赖：** [G04](#g04), [G05](#g05), [G08](#g08), [G10](#g10)

**论文定位：** [02-geometry.tex:241–248](../paper/flexible-surface-rewrite/02-geometry.tex#L241)

**目标文件：** `ContinuousFlexibility/Geometry/G11.lean`（节点组织目标；实际已存在的证明文件见下方，整个节点尚未完成）

**验收条件：**

- 比较像集而非参数化映射
- Hθ确实是全盘等距自微分同胚
- 非径向用存在两个角值不等的明确谓词

**已经完成的子结果：**

- 由真实P^-1 R_t P、图高度唯一性及实际径向metric刚性，证明同一Core的闭图盘相位像确实不恒定；未把它升级为封帽闭像非全等。

**仍待闭合的义务：**

- 实际Core版本的本节点数学结论已有证明；按依赖验收规则仍待前置G10整节点闭合与接口组装。
- 完整封帽闭像的非全等仍属G12/G13，不由盘像不同直接替代。

**现有 Lean 证明：**

[GraphOrbitVariation.lean](../ContinuousFlexibility/Geometry/GraphOrbitVariation.lean)：

- [`ContinuousFlexibility.IsometricGraphDevelopment.intrinsicRotationLift_apply`](../ContinuousFlexibility/Geometry/GraphOrbitVariation.lean#L33)
- [`ContinuousFlexibility.IsometricGraphDevelopment.intrinsicRotationLift_planar`](../ContinuousFlexibility/Geometry/GraphOrbitVariation.lean#L37)
- [`ContinuousFlexibility.IsometricGraphDevelopment.intrinsicRotationLift_smooth`](../ContinuousFlexibility/Geometry/GraphOrbitVariation.lean#L42)
- [`ContinuousFlexibility.IsometricGraphDevelopment.intrinsicRotationLift_inverse_smooth`](../ContinuousFlexibility/Geometry/GraphOrbitVariation.lean#L47)
- [`ContinuousFlexibility.IsometricGraphDevelopment.intrinsicRotationLift_outside`](../ContinuousFlexibility/Geometry/GraphOrbitVariation.lean#L52)
- [`ContinuousFlexibility.IsometricGraphDevelopment.intrinsicRotationLift_image_disk`](../ContinuousFlexibility/Geometry/GraphOrbitVariation.lean#L61)
- [`ContinuousFlexibility.IsometricGraphDevelopment.map_intrinsicRotationLift_of_disk_invariant`](../ContinuousFlexibility/Geometry/GraphOrbitVariation.lean#L79)
- [`ContinuousFlexibility.IsometricGraphDevelopment.height_intrinsicRotationLift_of_disk_invariant`](../ContinuousFlexibility/Geometry/GraphOrbitVariation.lean#L108)
- [`ContinuousFlexibility.IsometricGraphDevelopment.metric_intrinsicRotationLift_of_disk_invariant`](../ContinuousFlexibility/Geometry/GraphOrbitVariation.lean#L120)
- [`ContinuousFlexibility.IsometricGraphDevelopment.intrinsicRotationLift_eq_rotation_of_disk_invariant`](../ContinuousFlexibility/Geometry/GraphOrbitVariation.lean#L168)
- [`ContinuousFlexibility.planarRotation_polarPosition`](../ContinuousFlexibility/Geometry/GraphOrbitVariation.lean#L182)
- [`ContinuousFlexibility.IsometricGraphDevelopment.exists_rotationFamily_image_ne`](../ContinuousFlexibility/Geometry/GraphOrbitVariation.lean#L188)
- [`ContinuousFlexibility.IsometricGraphDevelopment.exists_distinct_rotationFamily_images`](../ContinuousFlexibility/Geometry/GraphOrbitVariation.lean#L224)


<a id="g12"></a>
## G12 全等变换的有限候选集

**状态：** 已有部分已编译子结果。**分支：** 几何闭合。主定理必要节点。

**数学陈述：** 任意联系两个闭像的欧氏仿射等距变换，固定共同marker p、向外法向和两条不同主方向线，故候选至多四个。

**证明提纲：** 用真实内部区域识别外法向，D01自然性输运形算子；在主方向基中线性部分为diag(±1,±1,1)，平移由固定p决定。

**直接依赖：** [G06](#g06), [G09](#g09), [G15](#g15), [D01](#d01)

**论文定位：** [02-geometry.tex:250–253](../paper/flexible-surface-rewrite/02-geometry.tex#L250)

**目标文件：** `ContinuousFlexibility/Geometry/G12.lean`（节点组织目标；实际已存在的证明文件见下方，整个节点尚未完成）

**验收条件：**

- 量化所有仿射等距，包括环境反射
- 有限集合与相位无关
- 不得只证明orientation-preserving congruence有限

**已经完成的子结果：**

- 真实整球闭像全等推出高斯曲率运输和唯一峰固定；用实际非零H排除normal翻转，再由真实shape的不同特征线构造实际DF eigenframe，得到同一marker处全欧氏仿射等距候选统一至多四个，包含反射。

**仍待闭合的义务：**

- 同一L输入的最终公开统一装配与后续细分独立验收。
- 历史细分合同的normalized orthonormal frame及显式四符号枚举尚未自动验收；当前实际eigenframe已足够证明统一至多四个。

**现有 Lean 证明：**

[LocalSurfaceReparametrization.lean](../ContinuousFlexibility/Geometry/LocalSurfaceReparametrization.lean)：

- [`ContinuousFlexibility.exists_continuousLinearMap_leftInverse`](../ContinuousFlexibility/Geometry/LocalSurfaceReparametrization.lean#L29)
- [`ContinuousFlexibility.eventually_mem_image_of_embedded_chart`](../ContinuousFlexibility/Geometry/LocalSurfaceReparametrization.lean#L41)
- [`ContinuousFlexibility.contDiffAt_projected_inverse`](../ContinuousFlexibility/Geometry/LocalSurfaceReparametrization.lean#L69)
- [`ContinuousFlexibility.fderiv_bijective_of_surface_identity`](../ContinuousFlexibility/Geometry/LocalSurfaceReparametrization.lean#L90)
- [`ContinuousFlexibility.exists_smooth_local_reparametrization_of_image_germ`](../ContinuousFlexibility/Geometry/LocalSurfaceReparametrization.lean#L111)
- [`ContinuousFlexibility.contDiffAt_affineSurfaceMap`](../ContinuousFlexibility/Geometry/LocalSurfaceReparametrization.lean#L201)
- [`ContinuousFlexibility.fderiv_affineSurfaceMap`](../ContinuousFlexibility/Geometry/LocalSurfaceReparametrization.lean#L211)
- [`ContinuousFlexibility.exists_smooth_local_reparametrization`](../ContinuousFlexibility/Geometry/LocalSurfaceReparametrization.lean#L222)
- [`ContinuousFlexibility.exists_smooth_local_reparametrization_germ`](../ContinuousFlexibility/Geometry/LocalSurfaceReparametrization.lean#L247)
- [`ContinuousFlexibility.fderiv_surface_reparametrization`](../ContinuousFlexibility/Geometry/LocalSurfaceReparametrization.lean#L269)
- [`ContinuousFlexibility.IsUnitSurfaceNormal.of_affine_reparametrization`](../ContinuousFlexibility/Geometry/LocalSurfaceReparametrization.lean#L282)
- [`ContinuousFlexibility.surfaceShapeMatrix_congr_germ`](../ContinuousFlexibility/Geometry/LocalSurfaceReparametrization.lean#L303)
- [`ContinuousFlexibility.surfaceGaussianCurvature_congr_germ`](../ContinuousFlexibility/Geometry/LocalSurfaceReparametrization.lean#L317)
- [`ContinuousFlexibility.surfaceMeanCurvature_congr_germ`](../ContinuousFlexibility/Geometry/LocalSurfaceReparametrization.lean#L322)

[MarkerStabilizer.lean](../ContinuousFlexibility/Geometry/MarkerStabilizer.lean)：

- [`ContinuousFlexibility.linearIsometry_eq_or_eq_neg_of_mem_span`](../ContinuousFlexibility/Geometry/MarkerStabilizer.lean#L25)
- [`ContinuousFlexibility.markerStabilizerEncoding_injOn`](../ContinuousFlexibility/Geometry/MarkerStabilizer.lean#L52)
- [`ContinuousFlexibility.markerStabilizerEncoding_mapsTo`](../ContinuousFlexibility/Geometry/MarkerStabilizer.lean#L76)
- [`ContinuousFlexibility.markerStabilizers_encard_le_four`](../ContinuousFlexibility/Geometry/MarkerStabilizer.lean#L88)
- [`ContinuousFlexibility.markerStabilizers_finite`](../ContinuousFlexibility/Geometry/MarkerStabilizer.lean#L103)
- [`ContinuousFlexibility.marker_diagonal_operator_coordinate`](../ContinuousFlexibility/Geometry/MarkerStabilizer.lean#L108)
- [`ContinuousFlexibility.marker_mem_line_of_eigenvector`](../ContinuousFlexibility/Geometry/MarkerStabilizer.lean#L120)
- [`ContinuousFlexibility.marker_line_preserved_of_commute`](../ContinuousFlexibility/Geometry/MarkerStabilizer.lean#L141)
- [`ContinuousFlexibility.markerOperatorStabilizers_subset`](../ContinuousFlexibility/Geometry/MarkerStabilizer.lean#L155)
- [`ContinuousFlexibility.markerOperatorStabilizers_encard_le_four`](../ContinuousFlexibility/Geometry/MarkerStabilizer.lean#L164)
- [`ContinuousFlexibility.marker_center_eigenvalues_injective`](../ContinuousFlexibility/Geometry/MarkerStabilizer.lean#L173)

[MarkerFrame.lean](../ContinuousFlexibility/Geometry/MarkerFrame.lean)：

- [`ContinuousFlexibility.eigenvectors_linearIndependent_two`](../ContinuousFlexibility/Geometry/MarkerFrame.lean#L24)
- [`ContinuousFlexibility.markerPlaneEigenbasis_apply`](../ContinuousFlexibility/Geometry/MarkerFrame.lean#L61)
- [`ContinuousFlexibility.principalFrameVectors_linearIndependent`](../ContinuousFlexibility/Geometry/MarkerFrame.lean#L70)
- [`ContinuousFlexibility.principalFrame_apply`](../ContinuousFlexibility/Geometry/MarkerFrame.lean#L103)
- [`ContinuousFlexibility.markerPlane_operator_coordinate`](../ContinuousFlexibility/Geometry/MarkerFrame.lean#L109)
- [`ContinuousFlexibility.markerPlane_mem_line_of_eigenvector`](../ContinuousFlexibility/Geometry/MarkerFrame.lean#L120)
- [`ContinuousFlexibility.principal_line_preserved_of_shape_commute`](../ContinuousFlexibility/Geometry/MarkerFrame.lean#L142)
- [`ContinuousFlexibility.mem_markerStabilizers_of_shape_commute`](../ContinuousFlexibility/Geometry/MarkerFrame.lean#L159)

[SphereCongruenceCurvature.lean](../ContinuousFlexibility/Geometry/SphereCongruenceCurvature.lean)：

- [`ContinuousFlexibility.IsUnitSurfaceNormal.eq_or_eq_neg`](../ContinuousFlexibility/Geometry/SphereCongruenceCurvature.lean#L28)
- [`ContinuousFlexibility.sphereCanonicalCoordinates_mem_source`](../ContinuousFlexibility/Geometry/SphereCongruenceCurvature.lean#L75)
- [`ContinuousFlexibility.sphereCanonicalCoordinates_target`](../ContinuousFlexibility/Geometry/SphereCongruenceCurvature.lean#L86)
- [`ContinuousFlexibility.sphereCanonicalCoordinates_left_inv`](../ContinuousFlexibility/Geometry/SphereCongruenceCurvature.lean#L91)
- [`ContinuousFlexibility.sphereCanonicalCoordinates_mdiff`](../ContinuousFlexibility/Geometry/SphereCongruenceCurvature.lean#L95)
- [`ContinuousFlexibility.contMDiff_sphereCanonicalInverse`](../ContinuousFlexibility/Geometry/SphereCongruenceCurvature.lean#L102)
- [`ContinuousFlexibility.isOpenEmbedding_sphereCanonicalInverse`](../ContinuousFlexibility/Geometry/SphereCongruenceCurvature.lean#L109)
- [`ContinuousFlexibility.sphereCanonicalInverse_range`](../ContinuousFlexibility/Geometry/SphereCongruenceCurvature.lean#L113)
- [`ContinuousFlexibility.contDiff_sphereCanonicalSurfaceChart`](../ContinuousFlexibility/Geometry/SphereCongruenceCurvature.lean#L121)
- [`ContinuousFlexibility.sphereCanonicalSurfaceChart_fderiv_injective`](../ContinuousFlexibility/Geometry/SphereCongruenceCurvature.lean#L126)
- [`ContinuousFlexibility.isUnitSurfaceNormal_sphereCanonicalSurfaceChart`](../ContinuousFlexibility/Geometry/SphereCongruenceCurvature.lean#L151)
- [`ContinuousFlexibility.sphereGaussianCurvature_eq_canonical`](../ContinuousFlexibility/Geometry/SphereCongruenceCurvature.lean#L175)
- [`ContinuousFlexibility.eventually_mem_open_chart_image`](../ContinuousFlexibility/Geometry/SphereCongruenceCurvature.lean#L183)
- [`ContinuousFlexibility.exists_sphere_congruence_reparametrization`](../ContinuousFlexibility/Geometry/SphereCongruenceCurvature.lean#L203)
- [`ContinuousFlexibility.normal_sign_of_affine_surface_germ`](../ContinuousFlexibility/Geometry/SphereCongruenceCurvature.lean#L241)
- [`ContinuousFlexibility.gaussianCurvature_of_affine_surface_germ`](../ContinuousFlexibility/Geometry/SphereCongruenceCurvature.lean#L258)
- [`ContinuousFlexibility.sphereGaussianCurvature_congruence`](../ContinuousFlexibility/Geometry/SphereCongruenceCurvature.lean#L284)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphereGaussianCurvature_congruence`](../ContinuousFlexibility/Geometry/SphereCongruenceCurvature.lean#L312)

[SphereCurvature.lean](../ContinuousFlexibility/Geometry/SphereCurvature.lean)：

- [`ContinuousFlexibility.sphereGraphCapFamily_south_closed_germ`](../ContinuousFlexibility/Geometry/SphereCurvature.lean#L52)
- [`ContinuousFlexibility.markedSphereNorthSurfaceChart_germ`](../ContinuousFlexibility/Geometry/SphereCurvature.lean#L67)
- [`ContinuousFlexibility.markedSphereSouthSurfaceChart_germ`](../ContinuousFlexibility/Geometry/SphereCurvature.lean#L88)
- [`ContinuousFlexibility.markedSphereNorthSurfaceChart_gaussian`](../ContinuousFlexibility/Geometry/SphereCurvature.lean#L123)
- [`ContinuousFlexibility.markedSphereSouthSurfaceChart_gaussian`](../ContinuousFlexibility/Geometry/SphereCurvature.lean#L144)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphereGaussianCurvature_north`](../ContinuousFlexibility/Geometry/SphereCurvature.lean#L172)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphereGaussianCurvature_south`](../ContinuousFlexibility/Geometry/SphereCurvature.lean#L183)
- [`ContinuousFlexibility.markedSphereSouthSurfaceChart_mean`](../ContinuousFlexibility/Geometry/SphereCurvature.lean#L198)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphereGaussianCurvature_periodic`](../ContinuousFlexibility/Geometry/SphereCurvature.lean#L226)
- [`ContinuousFlexibility.surfaceGaussianCurvature_horizontal`](../ContinuousFlexibility/Geometry/SphereCurvature.lean#L247)
- [`ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_gaussianCurvature_outside`](../ContinuousFlexibility/Geometry/SphereCurvature.lean#L258)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphereGaussianCurvature_equator`](../ContinuousFlexibility/Geometry/SphereCurvature.lean#L269)
- [`ContinuousFlexibility.exists_markedSphereCenterParameter`](../ContinuousFlexibility/Geometry/SphereCurvature.lean#L281)
- [`ContinuousFlexibility.markedSphereCenterParameter_south`](../ContinuousFlexibility/Geometry/SphereCurvature.lean#L309)
- [`ContinuousFlexibility.markedSphereCenterParameter_coordinates`](../ContinuousFlexibility/Geometry/SphereCurvature.lean#L313)
- [`ContinuousFlexibility.markedSphereCenterParameter_coordinates_eq_iff`](../ContinuousFlexibility/Geometry/SphereCurvature.lean#L319)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphereCenter_image`](../ContinuousFlexibility/Geometry/SphereCurvature.lean#L334)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphereCenter_normal`](../ContinuousFlexibility/Geometry/SphereCurvature.lean#L344)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphereGaussianCurvature_center`](../ContinuousFlexibility/Geometry/SphereCurvature.lean#L354)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphereCenter_mean`](../ContinuousFlexibility/Geometry/SphereCurvature.lean#L367)
- [`ContinuousFlexibility.IsometricGraphDevelopment.exists_markedSphere_unique_peak`](../ContinuousFlexibility/Geometry/SphereCurvature.lean#L390)
- [`ContinuousFlexibility.IsometricGraphDevelopment.exists_markedSphere_unique_peak_iff`](../ContinuousFlexibility/Geometry/SphereCurvature.lean#L426)

[SphereMarkerRigidity.lean](../ContinuousFlexibility/Geometry/SphereMarkerRigidity.lean)：

- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphere_congruence_fixes_marker_of_peak`](../ContinuousFlexibility/Geometry/SphereMarkerRigidity.lean#L36)
- [`ContinuousFlexibility.meanCurvature_of_affine_surface_germ`](../ContinuousFlexibility/Geometry/SphereMarkerRigidity.lean#L70)
- [`ContinuousFlexibility.normal_fixed_of_affine_surface_germ`](../ContinuousFlexibility/Geometry/SphereMarkerRigidity.lean#L90)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphereCanonicalCenter_mean`](../ContinuousFlexibility/Geometry/SphereMarkerRigidity.lean#L108)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphere_congruence_fixes_normal_of_peak`](../ContinuousFlexibility/Geometry/SphereMarkerRigidity.lean#L130)
- [`ContinuousFlexibility.IsometricGraphDevelopment.exists_markedSphere_fixed_marker_normal`](../ContinuousFlexibility/Geometry/SphereMarkerRigidity.lean#L183)
- [`ContinuousFlexibility.markerChartPoint_eq_south`](../ContinuousFlexibility/Geometry/SphereMarkerRigidity.lean#L218)
- [`ContinuousFlexibility.markerChartPoint_cap_coordinates`](../ContinuousFlexibility/Geometry/SphereMarkerRigidity.lean#L224)
- [`ContinuousFlexibility.IsometricGraphDevelopment.contDiff_markerCapComposite`](../ContinuousFlexibility/Geometry/SphereMarkerRigidity.lean#L229)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markerCapComposite_immersion`](../ContinuousFlexibility/Geometry/SphereMarkerRigidity.lean#L234)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markerCapComposite_normal`](../ContinuousFlexibility/Geometry/SphereMarkerRigidity.lean#L247)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphereCanonicalCenter_germ`](../ContinuousFlexibility/Geometry/SphereMarkerRigidity.lean#L259)
- [`ContinuousFlexibility.IsometricGraphDevelopment.exists_markerCapComposite_eigenbasis`](../ContinuousFlexibility/Geometry/SphereMarkerRigidity.lean#L286)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphere_congruences_in_stabilizers_of_peak`](../ContinuousFlexibility/Geometry/SphereMarkerRigidity.lean#L376)
- [`ContinuousFlexibility.IsometricGraphDevelopment.exists_markedSphere_finite_congruences_given_length`](../ContinuousFlexibility/Geometry/SphereMarkerRigidity.lean#L468)
- [`ContinuousFlexibility.IsometricGraphDevelopment.exists_markedSphere_finite_congruences`](../ContinuousFlexibility/Geometry/SphereMarkerRigidity.lean#L499)


<a id="g13"></a>
## G13 闭球面像确实非全等

**状态：** 已有部分已编译子结果。**分支：** 几何闭合。主定理必要节点。

**数学陈述：** 存在τ₁,τ₂，对任意欧氏仿射等距A，A''range(Fτ₁)≠range(Fτ₂)。

**证明提纲：** 图高度Zτ在C(D_b)一致拓扑连续；若闭像都全等，G12给有限像，顶部图高度可从闭像恢复，连通参数像有限迫使其恒定，与G11矛盾。

**直接依赖：** [G08](#g08), [G11](#g11), [G12](#g12)

**论文定位：** [02-geometry.tex:250–256](../paper/flexible-surface-rewrite/02-geometry.tex#L250)，`thm:geometric-closure`

**目标文件：** `ContinuousFlexibility/Geometry/G13.lean`（节点组织目标；实际已存在的证明文件见下方，整个节点尚未完成）

**验收条件：**

- 连续性载体和从闭像恢复顶部图均明确
- 不是仅排除绕轴旋转
- 从不恒定到非全等的有限候选论证完整

**已经完成的子结果：**

- 给定同一L的实际regularity和统一bottom gap，已实际选择marker并从有限仿射候选、紧像族连续性和真实图盘像变化推出两个封闭球面像对所有AffineIsometryEquiv不全等。
- 已对同一高度界一次选择实际长度并选择同一个标记，实际闭像族有至少两个成员在全欧氏仿射等距群下非全等。

**仍待闭合的义务：**

- 任意满足 FixedMarkedCap 的帽与实际选取帽之间的量词区别仍保留；本结果足以供完整主定理几何组装。

**现有 Lean 证明：**

[GraphCapAttachment.lean](../ContinuousFlexibility/Geometry/GraphCapAttachment.lean)：

- [`ContinuousFlexibility.isCompact_graphPhaseDiskImage`](../ContinuousFlexibility/Geometry/GraphCapAttachment.lean#L135)
- [`ContinuousFlexibility.isCompact_capDiskImage`](../ContinuousFlexibility/Geometry/GraphCapAttachment.lean#L139)
- [`ContinuousFlexibility.coe_graphPhaseCompact`](../ContinuousFlexibility/Geometry/GraphCapAttachment.lean#L149)
- [`ContinuousFlexibility.continuous_graphPhaseCompact`](../ContinuousFlexibility/Geometry/GraphCapAttachment.lean#L154)
- [`ContinuousFlexibility.coe_cappedGraphCompact`](../ContinuousFlexibility/Geometry/GraphCapAttachment.lean#L167)
- [`ContinuousFlexibility.continuous_cappedGraphCompact`](../ContinuousFlexibility/Geometry/GraphCapAttachment.lean#L172)
- [`ContinuousFlexibility.continuous_finite_compact_family_constant`](../ContinuousFlexibility/Geometry/GraphCapAttachment.lean#L177)
- [`ContinuousFlexibility.cappedGraphCompact_constant_of_finite_range`](../ContinuousFlexibility/Geometry/GraphCapAttachment.lean#L186)

[SphereNoncongruence.lean](../ContinuousFlexibility/Geometry/SphereNoncongruence.lean)：

- [`ContinuousFlexibility.IsometricGraphDevelopment.continuous_markedSphereCompact`](../ContinuousFlexibility/Geometry/SphereNoncongruence.lean#L37)
- [`ContinuousFlexibility.IsometricGraphDevelopment.coe_markedSphereCompact`](../ContinuousFlexibility/Geometry/SphereNoncongruence.lean#L42)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedCap_in_recoveryCylinder_subset_graph`](../ContinuousFlexibility/Geometry/SphereNoncongruence.lean#L56)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphere_recovers_graph`](../ContinuousFlexibility/Geometry/SphereNoncongruence.lean#L84)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphere_noncongruent_of_finite_congruences`](../ContinuousFlexibility/Geometry/SphereNoncongruence.lean#L108)
- [`ContinuousFlexibility.IsometricGraphDevelopment.exists_markedSphere_noncongruent_given_length`](../ContinuousFlexibility/Geometry/SphereNoncongruence.lean#L149)

[SphereCommonCapLength.lean](../ContinuousFlexibility/Geometry/SphereCommonCapLength.lean)：

- [`ContinuousFlexibility.IsometricGraphDevelopment.physical_height_gap_of_source_height_gap`](../ContinuousFlexibility/Geometry/SphereCommonCapLength.lean#L30)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphere_regular_of_cap_meeting`](../ContinuousFlexibility/Geometry/SphereCommonCapLength.lean#L49)
- [`ContinuousFlexibility.IsometricGraphDevelopment.exists_markedSphere_common_cap_length`](../ContinuousFlexibility/Geometry/SphereCommonCapLength.lean#L75)
- [`ContinuousFlexibility.IsometricGraphDevelopment.exists_common_cap_markedSphere_noncongruent`](../ContinuousFlexibility/Geometry/SphereCommonCapLength.lean#L111)


<a id="g14"></a>
## G14 面积不变

**状态：** 已有部分已编译子结果。**分支：** 几何闭合。主定理必要节点。

**数学陈述：** 实际闭像曲面面积Area(Fτ(S²))与τ无关。

**证明提纲：** 由同一拉回度量及参数化面积/像面积识别，或分块旋转换元。

**直接依赖：** [G09](#g09), [D02](#d02)

**论文定位：** [02-geometry.tex:258–260](../paper/flexible-surface-rewrite/02-geometry.tex#L258)

**目标文件：** `ContinuousFlexibility/Geometry/G14.lean`（节点组织目标；实际已存在的证明文件见下方，整个节点尚未完成）

**验收条件：**

- 像面积与参数化积分有已证桥接
- 不是只把同一gΣ的形式面积记作结论

**已经完成的子结果：**

- 同一实际标准球面族的归一化Euclidean Hausdorff二维面积已证明严格正、有限且相位不变；使用真实图盘与固定marked cap图像及零面积rim。

**仍待闭合的义务：**

- 将实际面积见证与同一L、同一marker、同一metric及全部其它主定理字段合并。

**现有 Lean 证明：**

[SphereArea.lean](../ContinuousFlexibility/Geometry/SphereArea.lean)：

- [`ContinuousFlexibility.euclideanArea_zero_iff_hausdorff`](../ContinuousFlexibility/Geometry/SphereArea.lean#L31)
- [`ContinuousFlexibility.euclideanArea_lt_top_of_hausdorff`](../ContinuousFlexibility/Geometry/SphereArea.lean#L39)
- [`ContinuousFlexibility.smooth_compact_planar_image_area_lt_top`](../ContinuousFlexibility/Geometry/SphereArea.lean#L45)
- [`ContinuousFlexibility.IsometricGraphDevelopment.graphPhaseDiskImage_area_invariant`](../ContinuousFlexibility/Geometry/SphereArea.lean#L57)
- [`ContinuousFlexibility.IsometricGraphDevelopment.graphPhaseDiskImage_areaMeasure_map`](../ContinuousFlexibility/Geometry/SphereArea.lean#L68)
- [`ContinuousFlexibility.IsometricGraphDevelopment.graphPhaseDiskImage_area_lt_top`](../ContinuousFlexibility/Geometry/SphereArea.lean#L85)
- [`ContinuousFlexibility.IsometricGraphDevelopment.graphPhaseDiskImage_integral_rotate`](../ContinuousFlexibility/Geometry/SphereArea.lean#L94)
- [`ContinuousFlexibility.IsometricGraphDevelopment.graphPhaseDiskImage_area_pos`](../ContinuousFlexibility/Geometry/SphereArea.lean#L111)
- [`ContinuousFlexibility.isCompact_markedCapImage`](../ContinuousFlexibility/Geometry/SphereArea.lean#L144)
- [`ContinuousFlexibility.markedCapImage_area_lt_top`](../ContinuousFlexibility/Geometry/SphereArea.lean#L148)
- [`ContinuousFlexibility.smooth_compact_curve_area_eq_zero`](../ContinuousFlexibility/Geometry/SphereArea.lean#L154)
- [`ContinuousFlexibility.capAttachingRim_area_eq_zero`](../ContinuousFlexibility/Geometry/SphereArea.lean#L170)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphereFamily_area_add`](../ContinuousFlexibility/Geometry/SphereArea.lean#L188)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphereFamily_areaMeasure_add`](../ContinuousFlexibility/Geometry/SphereArea.lean#L209)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphereFamily_area_invariant`](../ContinuousFlexibility/Geometry/SphereArea.lean#L228)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphereFamily_integral_add`](../ContinuousFlexibility/Geometry/SphereArea.lean#L245)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphereFamily_integral_invariant`](../ContinuousFlexibility/Geometry/SphereArea.lean#L267)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphereFamily_area_lt_top`](../ContinuousFlexibility/Geometry/SphereArea.lean#L302)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphereFamily_area_pos`](../ContinuousFlexibility/Geometry/SphereArea.lean#L314)
- [`ContinuousFlexibility.integrable_surfaceArea_of_continuous_comp`](../ContinuousFlexibility/Geometry/SphereArea.lean#L327)
- [`ContinuousFlexibility.IsometricGraphDevelopment.exists_markedSphereFamily_area`](../ContinuousFlexibility/Geometry/SphereArea.lean#L340)


<a id="g15"></a>
## G15 显式围成区域及体积不变

**状态：** 已有部分已编译子结果。**分支：** 几何闭合。主定理必要节点。

**数学陈述：** 构造有界开内部区域Ωτ，证明边界恰为闭像、内外连通关系足以识别其围成区域，并证明Lebesgue体积恒定。

**证明提纲：** 中央圆柱内在底高c_B与顶部图Zτ之间，其余固定；证明边界/内部/外部性质后，用Fubini和旋转换元。

**直接依赖：** [G06](#g06), [G08](#g08), [G09](#g09)

**论文定位：** [02-geometry.tex:260–268](../paper/flexible-surface-rewrite/02-geometry.tex#L260)

**目标文件：** `ContinuousFlexibility/Geometry/G15.lean`（节点组织目标；实际已存在的证明文件见下方，整个节点尚未完成）

**验收条件：**

- 不能直接把∫(Zτ−cB)定义成围成体积而跳过区域识别
- 底帽与上图分离用于所有τ
- 为G12/G16给真实向外法向

**已经完成的子结果：**

- 实际帽体的闭高度逆、全局球同胚、精确closure/frontier与内外连通/外部无界均已编译；移动图面通过真实ambient homeomorphism插入，所得未标记body的完整frontier等于实际图盘与帽盘，且体积有限正并相位不变。
- 同一标记环境变形给出实际开有界内域、完整球面边界、连通内域与无界连通外域、正且有限并相位不变的 Lebesgue 体积；全部球面点的真实向外射线和正式 EnclosedRegionFamily 已编译。

**仍待闭合的义务：**

- 任意 FixedMarkedCap 的 G15Statement 另需通用区域构造；已选定的实际帽满足主定理所需全部字段。

**优先核查程度：** high（任务风险标记，不是已发现错误）

**现有 Lean 证明：**

[CapInteriorProfile.lean](../ContinuousFlexibility/Contracts/CapInteriorProfile.lean)：

- [`ContinuousFlexibility.capHeightDrop_mem_open_iff`](../ContinuousFlexibility/Contracts/CapInteriorProfile.lean#L25)
- [`ContinuousFlexibility.exists_capHeightDrop_preimage`](../ContinuousFlexibility/Contracts/CapInteriorProfile.lean#L41)
- [`ContinuousFlexibility.capHeightDrop_parameter`](../ContinuousFlexibility/Contracts/CapInteriorProfile.lean#L53)
- [`ContinuousFlexibility.capHeightParameter_mem`](../ContinuousFlexibility/Contracts/CapInteriorProfile.lean#L58)
- [`ContinuousFlexibility.capHeightParameter_drop`](../ContinuousFlexibility/Contracts/CapInteriorProfile.lean#L63)
- [`ContinuousFlexibility.hasStrictDerivAt_capHeightParameter_drop`](../ContinuousFlexibility/Contracts/CapInteriorProfile.lean#L76)
- [`ContinuousFlexibility.contDiffAt_capHeightParameter_drop`](../ContinuousFlexibility/Contracts/CapInteriorProfile.lean#L84)
- [`ContinuousFlexibility.contDiffAt_capHeightParameter`](../ContinuousFlexibility/Contracts/CapInteriorProfile.lean#L104)
- [`ContinuousFlexibility.hasDerivAt_capHeightParameter`](../ContinuousFlexibility/Contracts/CapInteriorProfile.lean#L109)
- [`ContinuousFlexibility.cap_normalized_height_mem`](../ContinuousFlexibility/Contracts/CapInteriorProfile.lean#L117)
- [`ContinuousFlexibility.capWallRadius_gt`](../ContinuousFlexibility/Contracts/CapInteriorProfile.lean#L121)
- [`ContinuousFlexibility.contDiffAt_capWallRadius`](../ContinuousFlexibility/Contracts/CapInteriorProfile.lean#L129)
- [`ContinuousFlexibility.capWallRadius_at_meridian`](../ContinuousFlexibility/Contracts/CapInteriorProfile.lean#L135)
- [`ContinuousFlexibility.hasDerivAt_capWallRadius`](../ContinuousFlexibility/Contracts/CapInteriorProfile.lean#L144)
- [`ContinuousFlexibility.capRadialOffset_le_self`](../ContinuousFlexibility/Contracts/CapInteriorProfile.lean#L157)
- [`ContinuousFlexibility.capWallRadius_le`](../ContinuousFlexibility/Contracts/CapInteriorProfile.lean#L164)
- [`ContinuousFlexibility.isOpen_capRevolutionInterior`](../ContinuousFlexibility/Contracts/CapInteriorProfile.lean#L177)
- [`ContinuousFlexibility.capRevolutionInterior_subset_compact`](../ContinuousFlexibility/Contracts/CapInteriorProfile.lean#L191)
- [`ContinuousFlexibility.capRevolutionInterior_volume_lt_top`](../ContinuousFlexibility/Contracts/CapInteriorProfile.lean#L202)
- [`ContinuousFlexibility.capRevolutionInterior_volume_pos`](../ContinuousFlexibility/Contracts/CapInteriorProfile.lean#L207)

[GraphBoundaryNormals.lean](../ContinuousFlexibility/Contracts/GraphBoundaryNormals.lean)：

- [`ContinuousFlexibility.positive_derivative_two_sided_sign`](../ContinuousFlexibility/Contracts/GraphBoundaryNormals.lean#L22)
- [`ContinuousFlexibility.continuous_graphDefiningFunction`](../ContinuousFlexibility/Contracts/GraphBoundaryNormals.lean#L48)
- [`ContinuousFlexibility.graphDefiningFunction_graph`](../ContinuousFlexibility/Contracts/GraphBoundaryNormals.lean#L53)
- [`ContinuousFlexibility.graph_normal_defining_derivative_pos`](../ContinuousFlexibility/Contracts/GraphBoundaryNormals.lean#L57)
- [`ContinuousFlexibility.hasDerivAt_graphNormalRayLevel`](../ContinuousFlexibility/Contracts/GraphBoundaryNormals.lean#L78)
- [`ContinuousFlexibility.graphNormalRayLevel_eq_defining`](../ContinuousFlexibility/Contracts/GraphBoundaryNormals.lean#L91)
- [`ContinuousFlexibility.graph_normal_pointsOutwardFrom`](../ContinuousFlexibility/Contracts/GraphBoundaryNormals.lean#L103)
- [`ContinuousFlexibility.PointsOutwardFrom.mem_frontier`](../ContinuousFlexibility/Contracts/GraphBoundaryNormals.lean#L142)
- [`ContinuousFlexibility.IsUnitSurfaceNormal.of_comp`](../ContinuousFlexibility/Contracts/GraphBoundaryNormals.lean#L166)
- [`ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_eq_physical_graph`](../ContinuousFlexibility/Contracts/GraphBoundaryNormals.lean#L177)
- [`ContinuousFlexibility.IsometricGraphDevelopment.rotationNormal_physical_graph`](../ContinuousFlexibility/Contracts/GraphBoundaryNormals.lean#L186)
- [`ContinuousFlexibility.IsometricGraphDevelopment.rotationNormal_pointsOutwardFrom`](../ContinuousFlexibility/Contracts/GraphBoundaryNormals.lean#L208)
- [`ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_base_radius_lt`](../ContinuousFlexibility/Contracts/GraphBoundaryNormals.lean#L224)
- [`ContinuousFlexibility.IsometricGraphDevelopment.exists_bottom_outward_graphDisk`](../ContinuousFlexibility/Contracts/GraphBoundaryNormals.lean#L240)

[GraphCapInterior.lean](../ContinuousFlexibility/Contracts/GraphCapInterior.lean)：

- [`ContinuousFlexibility.IsometricGraphDevelopment.physicalHeight_outside`](../ContinuousFlexibility/Contracts/GraphCapInterior.lean#L23)
- [`ContinuousFlexibility.IsometricGraphDevelopment.rotated_physicalHeight_outside`](../ContinuousFlexibility/Contracts/GraphCapInterior.lean#L33)
- [`ContinuousFlexibility.IsometricGraphDevelopment.isOpen_graphCapInterior`](../ContinuousFlexibility/Contracts/GraphCapInterior.lean#L47)
- [`ContinuousFlexibility.IsometricGraphDevelopment.graphCapInterior_partition`](../ContinuousFlexibility/Contracts/GraphCapInterior.lean#L54)
- [`ContinuousFlexibility.disjoint_graphCylinder_fixedOutside`](../ContinuousFlexibility/Contracts/GraphCapInterior.lean#L78)
- [`ContinuousFlexibility.measurableSet_graphCapFixedOutside`](../ContinuousFlexibility/Contracts/GraphCapInterior.lean#L86)
- [`ContinuousFlexibility.IsometricGraphDevelopment.graphCapInterior_volume`](../ContinuousFlexibility/Contracts/GraphCapInterior.lean#L92)
- [`ContinuousFlexibility.IsometricGraphDevelopment.exists_compact_graphCapInterior_bound`](../ContinuousFlexibility/Contracts/GraphCapInterior.lean#L103)
- [`ContinuousFlexibility.IsometricGraphDevelopment.graphCapInterior_volume_lt_top`](../ContinuousFlexibility/Contracts/GraphCapInterior.lean#L113)
- [`ContinuousFlexibility.IsometricGraphDevelopment.exists_cap_bottom_below_physical_graph`](../ContinuousFlexibility/Contracts/GraphCapInterior.lean#L119)
- [`ContinuousFlexibility.IsometricGraphDevelopment.graphCapInterior_volume_pos`](../ContinuousFlexibility/Contracts/GraphCapInterior.lean#L129)
- [`ContinuousFlexibility.IsometricGraphDevelopment.rotationNormal_pointsOutwardFrom_graphCapInterior`](../ContinuousFlexibility/Contracts/GraphCapInterior.lean#L148)
- [`ContinuousFlexibility.IsometricGraphDevelopment.exists_graphCapInterior_family`](../ContinuousFlexibility/Contracts/GraphCapInterior.lean#L179)

[GraphCylinderVolume.lean](../ContinuousFlexibility/Contracts/GraphCylinderVolume.lean)：

- [`ContinuousFlexibility.IsometricGraphDevelopment.rotationFamily_physical_height`](../ContinuousFlexibility/Contracts/GraphCylinderVolume.lean#L28)
- [`ContinuousFlexibility.IsometricGraphDevelopment.isOpen_graphCylinderInterior`](../ContinuousFlexibility/Contracts/GraphCylinderVolume.lean#L36)
- [`ContinuousFlexibility.IsometricGraphDevelopment.graphCylinderInterior_eq_axial_image`](../ContinuousFlexibility/Contracts/GraphCylinderVolume.lean#L46)
- [`ContinuousFlexibility.IsometricGraphDevelopment.graphCylinderInterior_volume`](../ContinuousFlexibility/Contracts/GraphCylinderVolume.lean#L64)
- [`ContinuousFlexibility.continuous_euclideanVectorOfCoordinates`](../ContinuousFlexibility/Contracts/GraphCylinderVolume.lean#L77)
- [`ContinuousFlexibility.euclideanVectorOfCoordinates_of_vector`](../ContinuousFlexibility/Contracts/GraphCylinderVolume.lean#L81)
- [`ContinuousFlexibility.IsometricGraphDevelopment.exists_compact_graphCylinder_bound`](../ContinuousFlexibility/Contracts/GraphCylinderVolume.lean#L88)
- [`ContinuousFlexibility.IsometricGraphDevelopment.graphCylinderInterior_volume_lt_top`](../ContinuousFlexibility/Contracts/GraphCylinderVolume.lean#L107)
- [`ContinuousFlexibility.IsometricGraphDevelopment.exists_bottom_with_positive_graphCylinder_volume`](../ContinuousFlexibility/Contracts/GraphCylinderVolume.lean#L113)

[CapInteriorClosure.lean](../ContinuousFlexibility/Contracts/CapInteriorClosure.lean)：

- [`ContinuousFlexibility.bijective_capHeightDropClosedMap`](../ContinuousFlexibility/Contracts/CapInteriorClosure.lean#L32)
- [`ContinuousFlexibility.continuous_capHeightDropClosedEquiv`](../ContinuousFlexibility/Contracts/CapInteriorClosure.lean#L47)
- [`ContinuousFlexibility.continuous_capClampedDrop`](../ContinuousFlexibility/Contracts/CapInteriorClosure.lean#L58)
- [`ContinuousFlexibility.continuous_capClosedHeightParameter`](../ContinuousFlexibility/Contracts/CapInteriorClosure.lean#L64)
- [`ContinuousFlexibility.capClosedHeightParameter_mem`](../ContinuousFlexibility/Contracts/CapInteriorClosure.lean#L68)
- [`ContinuousFlexibility.capHeightDrop_closedParameter`](../ContinuousFlexibility/Contracts/CapInteriorClosure.lean#L72)
- [`ContinuousFlexibility.capClosedHeightParameter_eq`](../ContinuousFlexibility/Contracts/CapInteriorClosure.lean#L78)
- [`ContinuousFlexibility.capClosedHeightParameter_zero`](../ContinuousFlexibility/Contracts/CapInteriorClosure.lean#L84)
- [`ContinuousFlexibility.capClosedHeightParameter_capDrop`](../ContinuousFlexibility/Contracts/CapInteriorClosure.lean#L89)
- [`ContinuousFlexibility.continuous_capExtendedWallRadius`](../ContinuousFlexibility/Contracts/CapInteriorClosure.lean#L97)
- [`ContinuousFlexibility.capExtendedWallRadius_eq`](../ContinuousFlexibility/Contracts/CapInteriorClosure.lean#L102)
- [`ContinuousFlexibility.capExtendedWallRadius_top`](../ContinuousFlexibility/Contracts/CapInteriorClosure.lean#L108)
- [`ContinuousFlexibility.capExtendedWallRadius_bottom`](../ContinuousFlexibility/Contracts/CapInteriorClosure.lean#L114)
- [`ContinuousFlexibility.capExtendedWallRadius_gt`](../ContinuousFlexibility/Contracts/CapInteriorClosure.lean#L120)
- [`ContinuousFlexibility.closure_capRevolutionInterior_subset`](../ContinuousFlexibility/Contracts/CapInteriorClosure.lean#L129)
- [`ContinuousFlexibility.capRevolutionInterior_eq_preimage_cylinder`](../ContinuousFlexibility/Contracts/CapInteriorClosure.lean#L182)
- [`ContinuousFlexibility.closure_openCartesianUnitDisk`](../ContinuousFlexibility/Contracts/CapInteriorClosure.lean#L203)
- [`ContinuousFlexibility.closure_capRevolutionInterior`](../ContinuousFlexibility/Contracts/CapInteriorClosure.lean#L219)
- [`ContinuousFlexibility.frontier_capRevolutionInterior`](../ContinuousFlexibility/Contracts/CapInteriorClosure.lean#L235)

[CapInteriorFrontier.lean](../ContinuousFlexibility/Contracts/CapInteriorFrontier.lean)：

- [`ContinuousFlexibility.capClosedHeightParameter_drop`](../ContinuousFlexibility/Contracts/CapInteriorFrontier.lean#L21)
- [`ContinuousFlexibility.capExtendedWallRadius_at_meridian`](../ContinuousFlexibility/Contracts/CapInteriorFrontier.lean#L28)
- [`ContinuousFlexibility.mem_capDiskImage_of_meridian`](../ContinuousFlexibility/Contracts/CapInteriorFrontier.lean#L37)
- [`ContinuousFlexibility.capDiskImage_subset_frontier_capRevolutionInterior`](../ContinuousFlexibility/Contracts/CapInteriorFrontier.lean#L90)
- [`ContinuousFlexibility.topDisk_subset_frontier_capRevolutionInterior`](../ContinuousFlexibility/Contracts/CapInteriorFrontier.lean#L126)
- [`ContinuousFlexibility.frontier_capRevolutionInterior_eq_topDisk_union_capDisk`](../ContinuousFlexibility/Contracts/CapInteriorFrontier.lean#L137)

[CapInteriorTopology.lean](../ContinuousFlexibility/Contracts/CapInteriorTopology.lean)：

- [`ContinuousFlexibility.cap_normalized_height_abs_lt`](../ContinuousFlexibility/Contracts/CapInteriorTopology.lean#L49)
- [`ContinuousFlexibility.capRevolutionInterior_eq_preimage_ball`](../ContinuousFlexibility/Contracts/CapInteriorTopology.lean#L64)
- [`ContinuousFlexibility.isConnected_compl_unitClosedBall`](../ContinuousFlexibility/Contracts/CapInteriorTopology.lean#L79)
- [`ContinuousFlexibility.isConnected_capRevolutionInterior`](../ContinuousFlexibility/Contracts/CapInteriorTopology.lean#L108)
- [`ContinuousFlexibility.isConnected_capRevolutionExterior`](../ContinuousFlexibility/Contracts/CapInteriorTopology.lean#L115)
- [`ContinuousFlexibility.unbounded_capRevolutionExterior`](../ContinuousFlexibility/Contracts/CapInteriorTopology.lean#L126)

[GraphCapFrontier.lean](../ContinuousFlexibility/Contracts/GraphCapFrontier.lean)：

- [`ContinuousFlexibility.IsometricGraphDevelopment.graphCapHomeomorph_fixes_bottom`](../ContinuousFlexibility/Contracts/GraphCapFrontier.lean#L21)
- [`ContinuousFlexibility.IsometricGraphDevelopment.graphCapHomeomorph_fixes_cap`](../ContinuousFlexibility/Contracts/GraphCapFrontier.lean#L31)
- [`ContinuousFlexibility.IsometricGraphDevelopment.graphCapHomeomorph_image_cap`](../ContinuousFlexibility/Contracts/GraphCapFrontier.lean#L44)
- [`ContinuousFlexibility.IsometricGraphDevelopment.graphCapHomeomorph_image_topDisk`](../ContinuousFlexibility/Contracts/GraphCapFrontier.lean#L58)
- [`ContinuousFlexibility.IsometricGraphDevelopment.frontier_graphCapInterior`](../ContinuousFlexibility/Contracts/GraphCapFrontier.lean#L97)

[GraphCapHomeomorph.lean](../ContinuousFlexibility/Contracts/GraphCapHomeomorph.lean)：

- [`ContinuousFlexibility.vertical_height_interval_iff`](../ContinuousFlexibility/Contracts/GraphCapHomeomorph.lean#L46)
- [`ContinuousFlexibility.IsometricGraphDevelopment.physical_graph_above_bottom`](../ContinuousFlexibility/Contracts/GraphCapHomeomorph.lean#L69)
- [`ContinuousFlexibility.IsometricGraphDevelopment.graphCapHomeomorph_base`](../ContinuousFlexibility/Contracts/GraphCapHomeomorph.lean#L97)
- [`ContinuousFlexibility.IsometricGraphDevelopment.graphCapHomeomorph_height`](../ContinuousFlexibility/Contracts/GraphCapHomeomorph.lean#L106)
- [`ContinuousFlexibility.IsometricGraphDevelopment.graphCapHomeomorph_outside`](../ContinuousFlexibility/Contracts/GraphCapHomeomorph.lean#L116)
- [`ContinuousFlexibility.capRevolutionInterior_mem_of_radius_lt`](../ContinuousFlexibility/Contracts/GraphCapHomeomorph.lean#L132)
- [`ContinuousFlexibility.IsometricGraphDevelopment.graphCapHomeomorph_mem`](../ContinuousFlexibility/Contracts/GraphCapHomeomorph.lean#L140)
- [`ContinuousFlexibility.IsometricGraphDevelopment.graphCapInterior_eq_preimage`](../ContinuousFlexibility/Contracts/GraphCapHomeomorph.lean#L168)
- [`ContinuousFlexibility.IsometricGraphDevelopment.isConnected_graphCapInterior`](../ContinuousFlexibility/Contracts/GraphCapHomeomorph.lean#L179)
- [`ContinuousFlexibility.IsometricGraphDevelopment.isConnected_graphCapExterior`](../ContinuousFlexibility/Contracts/GraphCapHomeomorph.lean#L189)
- [`ContinuousFlexibility.IsometricGraphDevelopment.unbounded_graphCapExterior`](../ContinuousFlexibility/Contracts/GraphCapHomeomorph.lean#L200)

[MarkedCapInterior.lean](../ContinuousFlexibility/Contracts/MarkedCapInterior.lean)：

- [`ContinuousFlexibility.IsometricGraphDevelopment.markedCapInterior_eq_preimage`](../ContinuousFlexibility/Contracts/MarkedCapInterior.lean#L29)
- [`ContinuousFlexibility.IsometricGraphDevelopment.isOpen_markedCapInterior`](../ContinuousFlexibility/Contracts/MarkedCapInterior.lean#L37)
- [`ContinuousFlexibility.IsometricGraphDevelopment.isConnected_markedCapInterior`](../ContinuousFlexibility/Contracts/MarkedCapInterior.lean#L44)
- [`ContinuousFlexibility.IsometricGraphDevelopment.isConnected_markedCapExterior`](../ContinuousFlexibility/Contracts/MarkedCapInterior.lean#L53)
- [`ContinuousFlexibility.IsometricGraphDevelopment.exists_compact_markedCapInterior_bound`](../ContinuousFlexibility/Contracts/MarkedCapInterior.lean#L65)
- [`ContinuousFlexibility.IsometricGraphDevelopment.isBounded_markedCapInterior`](../ContinuousFlexibility/Contracts/MarkedCapInterior.lean#L74)
- [`ContinuousFlexibility.IsometricGraphDevelopment.unbounded_markedCapExterior`](../ContinuousFlexibility/Contracts/MarkedCapInterior.lean#L81)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedCapInterior_volume_lt_top`](../ContinuousFlexibility/Contracts/MarkedCapInterior.lean#L90)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedCapInterior_volume_pos`](../ContinuousFlexibility/Contracts/MarkedCapInterior.lean#L97)
- [`ContinuousFlexibility.markerAmbientHomeomorph_image_capDisk`](../ContinuousFlexibility/Contracts/MarkedCapInterior.lean#L106)
- [`ContinuousFlexibility.IsometricGraphDevelopment.frontier_markedCapInterior`](../ContinuousFlexibility/Contracts/MarkedCapInterior.lean#L119)
- [`ContinuousFlexibility.IsometricGraphDevelopment.frontier_markedCapInterior_eq_sphereRange`](../ContinuousFlexibility/Contracts/MarkedCapInterior.lean#L134)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markerAmbientHomeomorph_image_graphCylinder`](../ContinuousFlexibility/Contracts/MarkedCapInterior.lean#L150)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedCapInterior_partition`](../ContinuousFlexibility/Contracts/MarkedCapInterior.lean#L169)
- [`ContinuousFlexibility.measurableSet_markedCapFixedOutside`](../ContinuousFlexibility/Contracts/MarkedCapInterior.lean#L180)
- [`ContinuousFlexibility.disjoint_graphCylinder_markedOutside`](../ContinuousFlexibility/Contracts/MarkedCapInterior.lean#L186)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedCapInterior_volume`](../ContinuousFlexibility/Contracts/MarkedCapInterior.lean#L199)

[MarkedCapOutward.lean](../ContinuousFlexibility/Contracts/MarkedCapOutward.lean)：

- [`ContinuousFlexibility.IsometricGraphDevelopment.graphCapInterior_mem_below_turning_radius`](../ContinuousFlexibility/Contracts/MarkedCapOutward.lean#L28)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedCapInterior_mem_below_turning_radius`](../ContinuousFlexibility/Contracts/MarkedCapOutward.lean#L56)
- [`ContinuousFlexibility.IsometricGraphDevelopment.rotationNormal_pointsOutwardFrom_markedCapInterior`](../ContinuousFlexibility/Contracts/MarkedCapOutward.lean#L114)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedCapNormal_pointsOutwardFrom_markedCapInterior`](../ContinuousFlexibility/Contracts/MarkedCapOutward.lean#L193)
- [`ContinuousFlexibility.IsometricGraphDevelopment.sphereMarkedNormal_pointsOutwardFrom`](../ContinuousFlexibility/Contracts/MarkedCapOutward.lean#L239)

[CapDiskOutward.lean](../ContinuousFlexibility/Geometry/CapDiskOutward.lean)：

- [`ContinuousFlexibility.capRadialOffset_gt_quarter`](../ContinuousFlexibility/Geometry/CapDiskOutward.lean#L21)
- [`ContinuousFlexibility.capWallRadius_gt_rim`](../ContinuousFlexibility/Geometry/CapDiskOutward.lean#L44)
- [`ContinuousFlexibility.capDiskNormal_pointsOutwardFrom`](../ContinuousFlexibility/Geometry/CapDiskOutward.lean#L207)

[EnclosedRegionUniqueness.lean](../ContinuousFlexibility/Geometry/EnclosedRegionUniqueness.lean)：

- [`ContinuousFlexibility.bounded_region_subset_of_frontier_eq`](../ContinuousFlexibility/Geometry/EnclosedRegionUniqueness.lean#L26)
- [`ContinuousFlexibility.bounded_regions_eq_of_frontier_eq`](../ContinuousFlexibility/Geometry/EnclosedRegionUniqueness.lean#L60)
- [`ContinuousFlexibility.sphere_outward_normals_eq`](../ContinuousFlexibility/Geometry/EnclosedRegionUniqueness.lean#L78)

[GraphCapOutward.lean](../ContinuousFlexibility/Geometry/GraphCapOutward.lean)：

- [`ContinuousFlexibility.IsometricGraphDevelopment.graphCapInterior_outside_germ`](../ContinuousFlexibility/Geometry/GraphCapOutward.lean#L31)
- [`ContinuousFlexibility.IsometricGraphDevelopment.graphCapInterior_capDisk_germ`](../ContinuousFlexibility/Geometry/GraphCapOutward.lean#L49)
- [`ContinuousFlexibility.IsometricGraphDevelopment.capDiskNormal_pointsOutwardFrom_graphCapInterior`](../ContinuousFlexibility/Geometry/GraphCapOutward.lean#L94)
- [`ContinuousFlexibility.IsometricGraphDevelopment.rotationNormal_pointsOutwardFrom_graphCapInterior_closed`](../ContinuousFlexibility/Geometry/GraphCapOutward.lean#L107)

[MarkedCapPhysicalNormals.lean](../ContinuousFlexibility/Geometry/MarkedCapPhysicalNormals.lean)：

- [`ContinuousFlexibility.markedCapMap_physical_top_germ`](../ContinuousFlexibility/Geometry/MarkedCapPhysicalNormals.lean#L25)
- [`ContinuousFlexibility.markedCapMap_physical_top`](../ContinuousFlexibility/Geometry/MarkedCapPhysicalNormals.lean#L40)
- [`ContinuousFlexibility.markedCapNormal_physical_top`](../ContinuousFlexibility/Geometry/MarkedCapPhysicalNormals.lean#L49)
- [`ContinuousFlexibility.markedCapNormal_top_height_pos`](../ContinuousFlexibility/Geometry/MarkedCapPhysicalNormals.lean#L73)
- [`ContinuousFlexibility.markedCapMap_top_defining_eq_zero`](../ContinuousFlexibility/Geometry/MarkedCapPhysicalNormals.lean#L79)
- [`ContinuousFlexibility.markedCapNormal_top_defining_derivative_pos`](../ContinuousFlexibility/Geometry/MarkedCapPhysicalNormals.lean#L88)

[MarkerAmbientDeformation.lean](../ContinuousFlexibility/Geometry/MarkerAmbientDeformation.lean)：

- [`ContinuousFlexibility.contDiff_markerAmbientBump`](../ContinuousFlexibility/Geometry/MarkerAmbientDeformation.lean#L33)
- [`ContinuousFlexibility.contDiff_markerAmbientScale`](../ContinuousFlexibility/Geometry/MarkerAmbientDeformation.lean#L37)
- [`ContinuousFlexibility.markerAmbientBump_nonneg`](../ContinuousFlexibility/Geometry/MarkerAmbientDeformation.lean#L41)
- [`ContinuousFlexibility.markerAmbientScale_pos`](../ContinuousFlexibility/Geometry/MarkerAmbientDeformation.lean#L45)
- [`ContinuousFlexibility.markerAmbientBump_support_bounds`](../ContinuousFlexibility/Geometry/MarkerAmbientDeformation.lean#L55)
- [`ContinuousFlexibility.markerAmbientBump_eq_zero_of_inner`](../ContinuousFlexibility/Geometry/MarkerAmbientDeformation.lean#L70)
- [`ContinuousFlexibility.markerAmbientBump_eq_zero_of_outer`](../ContinuousFlexibility/Geometry/MarkerAmbientDeformation.lean#L77)
- [`ContinuousFlexibility.markerAmbientHomeomorph_base`](../ContinuousFlexibility/Geometry/MarkerAmbientDeformation.lean#L93)
- [`ContinuousFlexibility.markerAmbientHomeomorph_height`](../ContinuousFlexibility/Geometry/MarkerAmbientDeformation.lean#L100)
- [`ContinuousFlexibility.markerAmbientHomeomorph_symm_base`](../ContinuousFlexibility/Geometry/MarkerAmbientDeformation.lean#L107)
- [`ContinuousFlexibility.markerAmbientHomeomorph_symm_height`](../ContinuousFlexibility/Geometry/MarkerAmbientDeformation.lean#L114)
- [`ContinuousFlexibility.markerAmbientHomeomorph_fixes_bottom`](../ContinuousFlexibility/Geometry/MarkerAmbientDeformation.lean#L122)
- [`ContinuousFlexibility.markerAmbientHomeomorph_eq_self_of_bump_eq_zero`](../ContinuousFlexibility/Geometry/MarkerAmbientDeformation.lean#L129)
- [`ContinuousFlexibility.markerAmbientHomeomorph_eq_self_of_inner`](../ContinuousFlexibility/Geometry/MarkerAmbientDeformation.lean#L139)
- [`ContinuousFlexibility.markerAmbientHomeomorph_eq_self_of_outer`](../ContinuousFlexibility/Geometry/MarkerAmbientDeformation.lean#L146)
- [`ContinuousFlexibility.markerAmbientHomeomorph_inner_germ`](../ContinuousFlexibility/Geometry/MarkerAmbientDeformation.lean#L153)
- [`ContinuousFlexibility.markerAmbientHomeomorph_outer_germ`](../ContinuousFlexibility/Geometry/MarkerAmbientDeformation.lean#L163)
- [`ContinuousFlexibility.markerAmbientHomeomorph_capDiskMap`](../ContinuousFlexibility/Geometry/MarkerAmbientDeformation.lean#L175)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markerAmbientHomeomorph_rotationFamily`](../ContinuousFlexibility/Geometry/MarkerAmbientDeformation.lean#L214)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markerAmbientHomeomorph_image_graphDisk`](../ContinuousFlexibility/Geometry/MarkerAmbientDeformation.lean#L224)

[OutwardNormalRays.lean](../ContinuousFlexibility/Geometry/OutwardNormalRays.lean)：

- [`ContinuousFlexibility.closure_eventuallyEq_of_eventuallyEq`](../ContinuousFlexibility/Geometry/OutwardNormalRays.lean#L23)
- [`ContinuousFlexibility.PointsOutwardFrom.congr_germ`](../ContinuousFlexibility/Geometry/OutwardNormalRays.lean#L33)
- [`ContinuousFlexibility.PointsOutwardFrom.not_neg`](../ContinuousFlexibility/Geometry/OutwardNormalRays.lean#L57)
- [`ContinuousFlexibility.PointsOutwardFrom.eq_of_eq_or_eq_neg`](../ContinuousFlexibility/Geometry/OutwardNormalRays.lean#L70)
- [`ContinuousFlexibility.PointsOutwardFrom.of_defining_function`](../ContinuousFlexibility/Geometry/OutwardNormalRays.lean#L79)


<a id="g16"></a>
## G16 总向外有向平均曲率不变

**状态：** 已有部分已编译子结果。**分支：** 几何闭合。主定理必要节点。

**数学陈述：** 向外法向、H=(k₁+k₂)/2约定下，∫_{Fτ(S²)}H_out dA与τ无关。

**证明提纲：** 移动盘是环境旋转加内禀重参数化，补帽固定；用D01/D02变换律和分块积分，平领圈H=0。

**直接依赖：** [G06](#g06), [G08](#g08), [G09](#g09), [G15](#g15), [D02](#d02)

**论文定位：** [02-geometry.tex:258–260](../paper/flexible-surface-rewrite/02-geometry.tex#L258)；[01-introduction.tex:33–39](../paper/flexible-surface-rewrite/01-introduction.tex#L33)

**目标文件：** `ContinuousFlexibility/Geometry/G16.lean`（节点组织目标；实际已存在的证明文件见下方，整个节点尚未完成）

**验收条件：**

- 明确向外方向而非任选参数法向
- 不是∫|H|
- 交接领圈和图册重叠积分无遗漏

**已经完成的子结果：**

- 同一给定L/hmeet族的真实Hausdorff图像积分、实际TS形算子trace/2与ambient代表识别、可积性及有向平均曲率积分相位不变已编译；当前使用构造的法向，不把它静默称为outward。
- 同一实际球面上的 EnclosedRegionFamily、向外真法向、光滑切空间形算子、同一固定度量下自伴、ambient trace/2 识别和真实有向 H 积分已组装；对同一实际球面族的任意 oriented enclosure 已证识别与不变性。

**仍待闭合的义务：**

- G16Statement 对任意满足合约的帽 C 量化，不能从已选定的实际标记帽直接推出此更强规格。

**现有 Lean 证明：**

[SphereMeanIntegral.lean](../ContinuousFlexibility/Geometry/SphereMeanIntegral.lean)：

- [`ContinuousFlexibility.sphereImageScalar_apply`](../ContinuousFlexibility/Geometry/SphereMeanIntegral.lean#L32)
- [`ContinuousFlexibility.integrable_sphereImageScalar`](../ContinuousFlexibility/Geometry/SphereMeanIntegral.lean#L36)
- [`ContinuousFlexibility.integrable_and_integral_eq_sphereImageScalar`](../ContinuousFlexibility/Geometry/SphereMeanIntegral.lean#L49)
- [`ContinuousFlexibility.sphereShapeOperator_unique`](../ContinuousFlexibility/Geometry/SphereMeanIntegral.lean#L69)
- [`ContinuousFlexibility.sphereMeanCurvature_eq_trace_of_weingarten`](../ContinuousFlexibility/Geometry/SphereMeanIntegral.lean#L82)
- [`ContinuousFlexibility.IsometricGraphDevelopment.contMDiff_markedSpherePhaseMap`](../ContinuousFlexibility/Geometry/SphereMeanIntegral.lean#L112)
- [`ContinuousFlexibility.IsometricGraphDevelopment.contMDiff_markedSpherePhaseNormal`](../ContinuousFlexibility/Geometry/SphereMeanIntegral.lean#L118)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSpherePhaseMap_isEmbedding`](../ContinuousFlexibility/Geometry/SphereMeanIntegral.lean#L126)
- [`ContinuousFlexibility.IsometricGraphDevelopment.contMDiff_markedSphereMeanCurvature`](../ContinuousFlexibility/Geometry/SphereMeanIntegral.lean#L141)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphereMeanCurvature_north`](../ContinuousFlexibility/Geometry/SphereMeanIntegral.lean#L165)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphereMeanCurvature_south`](../ContinuousFlexibility/Geometry/SphereMeanIntegral.lean#L197)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphereAmbientMean_on_image`](../ContinuousFlexibility/Geometry/SphereMeanIntegral.lean#L217)
- [`ContinuousFlexibility.IsometricGraphDevelopment.integrable_markedSphereAmbientMean`](../ContinuousFlexibility/Geometry/SphereMeanIntegral.lean#L227)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphereAmbientMean_on_graph`](../ContinuousFlexibility/Geometry/SphereMeanIntegral.lean#L243)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphereAmbientMean_on_cap`](../ContinuousFlexibility/Geometry/SphereMeanIntegral.lean#L281)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphereTotalMean_invariant`](../ContinuousFlexibility/Geometry/SphereMeanIntegral.lean#L325)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphereMean_integral_eq_of_identification`](../ContinuousFlexibility/Geometry/SphereMeanIntegral.lean#L356)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphereMean_integral_invariant_of_identification`](../ContinuousFlexibility/Geometry/SphereMeanIntegral.lean#L375)
- [`ContinuousFlexibility.IsometricGraphDevelopment.exists_markedSphereTotalMean`](../ContinuousFlexibility/Geometry/SphereMeanIntegral.lean#L398)

[SphereOrientedEnclosed.lean](../ContinuousFlexibility/Geometry/SphereOrientedEnclosed.lean)：

- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphereEnclosure_unique`](../ContinuousFlexibility/Geometry/SphereOrientedEnclosed.lean#L82)
- [`ContinuousFlexibility.IsometricGraphDevelopment.markedSphereOrientedMean_invariant`](../ContinuousFlexibility/Geometry/SphereOrientedEnclosed.lean#L127)


<a id="main"></a>
## MAIN 闭球面光滑周期等距弯曲主定理

**状态：** 已有部分已编译子结果。**分支：** 主定理。主定理必要节点。

**数学陈述：** 实例化C00的全部结论：标准S²上的一个固定光滑正定度量、联合光滑一周期等距嵌入族、两个非全等闭像、固定内盘及补帽，以及三项几何积分不变量。

**证明提纲：** 从实际N12/G01数据沿几何链组装所有见证。最终导出不带RadialReference/AnnularSolution/Hamilton结论假设的无条件存在定理。

**直接依赖：** [G01](#g01), [G07](#g07), [G08](#g08), [G09](#g09), [G13](#g13), [G14](#g14), [G15](#g15), [G16](#g16)

**论文定位：** [01-introduction.tex:18–39](../paper/flexible-surface-rewrite/01-introduction.tex#L18)，`thm:main`；[10-endpoint-and-sphere.tex:320–339](../paper/flexible-surface-rewrite/10-endpoint-and-sphere.tex#L320)

**目标文件：** `ContinuousFlexibility/Main.lean`（节点组织目标；实际已存在的证明文件见下方，整个节点尚未完成）

**验收条件：**

- 最终Lean声明类型逐条覆盖原thm:main
- 全部主链节点有实际证明且主定理通过内核和公理审计
- 不得以条件性闭合定理或蓝图验收器代替完成

**已经完成的子结果：**

- 从任意实际 FlatAnnularCore 出发，已编译主定理的完整几何组装；同一 L,k,ρ 和同一标准 S² 族同时满足全部字段。

**仍待闭合的义务：**

- 构造 Nonempty FlatAnnularCore：完成积聚径向参考、实际加权空间和非线性逆及弱分支。
- 实例化无条件 MainStatement 并通过完整源码和所有必要依赖的最终验收。

**现有 Lean 证明：**

[SphereClosedBending.lean](../ContinuousFlexibility/Contracts/SphereClosedBending.lean)：

- [`ContinuousFlexibility.IsometricGraphDevelopment.nonempty_closedBending`](../ContinuousFlexibility/Contracts/SphereClosedBending.lean#L23)
- [`ContinuousFlexibility.mainStatement_of_flatAnnularCore`](../ContinuousFlexibility/Contracts/SphereClosedBending.lean#L59)


<a id="x01"></a>
## X01 所有端点指数的同一几何加强

**状态：** 待形式化。**分支：** 主定理之后的加强。主定理之后的加强旁支。

**数学陈述：** 将同一径向几何的逆估计加强到全部紧区间[γ₋,γ₊]⊂(0,1)，几何本身不随区间变化。

**证明提纲：** 展开原文统一参数选择次序和尾部求和量词。

**直接依赖：** [R05](#r05), [R10](#r10), [R11](#r11), [R12](#r12)

**论文定位：** [04-designing-the-profile.tex:99–106](../paper/flexible-surface-rewrite/04-designing-the-profile.tex#L99)，`prop:rad-fixed-theorem`；[06-global-reference-inverse.tex:707–764](../paper/flexible-surface-rewrite/06-global-reference-inverse.tex#L707)，`lem:radial-uniform-exponents`

**目标文件：** `ContinuousFlexibility/Extensions/X01.lean`（拟建，尚无此证明）

**验收条件：**

- 这是原参考命题的加强范围；主定理仅需固定β及邻近指数
- 不能逐γ另造几何

<a id="x02"></a>
## X02 双倍端点权和二次控制加强

**状态：** 待形式化。**分支：** 主定理之后的加强。主定理之后的加强旁支。

**数学陈述：** 二次余项进入2β权；mean primitive不损失指数，恢复ν_q,κ_q=O(q²)、强拓扑光滑性及H^(1−ε)端点估计。

**证明提纲：** 分别证明双弱因子的乘积、平均方程恢复和控制恢复；不再进行新的非线性迭代。

**直接依赖：** [N11](#n11), [S04](#s04), [W02](#w02), [W03](#w03), [N01](#n01)

**论文定位：** [10-endpoint-and-sphere.tex:19–299](../paper/flexible-surface-rewrite/10-endpoint-and-sphere.tex#L19)，`lem:posterior-two-weight`

**目标文件：** `ContinuousFlexibility/Extensions/X02.lean`（拟建，尚无此证明）

**验收条件：**

- 不阻挡首次MAIN闭合
- 仍保留N12必需的弱空间延拓证明

<a id="x03"></a>
## X03 有限角向截断的障碍

**状态：** 待形式化。**分支：** 主定理之后的加强。主定理之后的加强旁支。

**数学陈述：** 形式化附录prop:obs-finite-square的完整原陈述及其有限Fourier最高频、复平方根ODE和延拓论证。

**证明提纲：** 最高模系数计算、非零分支平方根、Gronwall、零点拼接和有限降阶分别处理。

**直接依赖：** [S03](#s03)

**论文定位：** [appendix-shortcuts.tex:11–109](../paper/flexible-surface-rewrite/appendix-shortcuts.tex#L11)，`prop:obs-finite-square`

**目标文件：** `ContinuousFlexibility/Extensions/X03.lean`（拟建，尚无此证明）

**验收条件：**

- 独立于主存在性链
- 复平方根和零点累积延拓不能只靠代数检查
