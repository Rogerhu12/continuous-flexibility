import ContinuousFlexibility.Analysis.N07bNormalizedSourceChainCalculus
import ContinuousFlexibility.Analysis.N07bAngularChainExpansion
import ContinuousFlexibility.Analysis.N07bActualCanonicalSourceLift

/-!
# The actual normalized source-coefficient recursion

The material-coordinate Jacobian density is `Omega = ell * |J|`. Multiplying
each actual path coefficient by `sqrt Omega * (H/H_m)^beta` removes every
derivative of the material height from the unchanged-jet branch. Its new
zeroth-order coefficient is exactly `-D(Omega)/(2*Omega)`.

All fields in this module depend only on the material data and actual
chart geometry. They have no physical source argument. Positivity and
local smoothness are consequences of the existing actual geometry.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

def n07bSourceMaterialJacobian {S : PhysicalSpacesData} (T : MaterialData)
    (K : CanonicalData S) (z : AnnularState S × ℝ) (m : ℕ) (x : PolarPoint) : ℝ :=
  T.ell x.1 * |planeJacobian (K.chart z m) x|

def n07bSourceHeightRatio {S : PhysicalSpacesData} (T : MaterialData)
    (K : CanonicalData S) (m : ℕ) (x : PolarPoint) : ℝ :=
  T.H x.1 / T.H (T.sample (K.cell m))

def n07bSourceNormalizer {S : PhysicalSpacesData} (T : MaterialData)
    (K : CanonicalData S) (z : AnnularState S × ℝ) (m : ℕ) (β : ℝ)
    (x : PolarPoint) : ℝ :=
  Real.sqrt (n07bSourceMaterialJacobian T K z m x) *
    n07bSourceHeightRatio T K m x ^ β

def n07bSourceMaterialAngleVector {S : PhysicalSpacesData} (T : MaterialData)
    (K : CanonicalData S) (z : AnnularState S × ℝ) (m : ℕ) (x : PolarPoint) : PolarPoint :=
  ((n07bInverseAngleVector (K.chart z m) x).1 / T.ell x.1,
    (n07bInverseAngleVector (K.chart z m) x).2)

def n07bSourceNormalizationDrift {S : PhysicalSpacesData} (T : MaterialData)
    (K : CanonicalData S) (z : AnnularState S × ℝ) (m : ℕ) (x : PolarPoint) : ℝ :=
  -n07bInverseAngleDerivative (K.chart z m) (n07bSourceMaterialJacobian T K z m) x /
    (2 * n07bSourceMaterialJacobian T K z m x)

def n07bNormalizedSourceCoefficient {S : PhysicalSpacesData} (T : MaterialData)
    (K : CanonicalData S) (z : AnnularState S × ℝ) (m : ℕ) (β : ℝ)
    (j : ℕ) (i : n07bAngularChainIndex j) (x : PolarPoint) : ℝ :=
  n07bSourceNormalizer T K z m β x * n07bAngularChainCoefficient T K z m β j i x

/-- The ratio normalization is the product normalization with a constant
sample factor. This identity is used only at genuine positive heights. -/
theorem n07bSourceNormalizer_eq_product {S : PhysicalSpacesData}
    (T : MaterialData) (K : CanonicalData S) (z : AnnularState S × ℝ)
    (m : ℕ) (β : ℝ) (x : PolarPoint)
    (hx : 0 < T.H x.1) (hm : 0 < T.H (T.sample (K.cell m))) :
    n07bSourceNormalizer T K z m β x =
      Real.sqrt (n07bSourceMaterialJacobian T K z m x) *
        (T.H (T.sample (K.cell m)) ^ β)⁻¹ * T.H x.1 ^ β := by
  rw [n07bSourceNormalizer, n07bSourceHeightRatio, Real.div_rpow hx.le hm.le]
  simp only [div_eq_mul_inv]
  ring

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
  {z : AnnularState S × ℝ}

theorem n07bSourceMaterialJacobian_pos (hT : IsMaterialData D T)
    (hK : N04PartA D S C K base ε) (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {x : PolarPoint}
    (hx : x ∈ physicalPieceOpen S K m) :
    0 < n07bSourceMaterialJacobian T K z m x := by
  have hxcore := (hK.2.2.2.1 m).2.2 hx.1
  have hclosed := hK.2.2.2.2.2.2.2.2.1 z hz hs m x ⟨hx.1.1.le, hx.1.2.le⟩
  exact mul_pos (hT.2.1 x.1 hxcore).1 (abs_pos.mpr hclosed.2.2.1)

theorem n07bSourceMaterialJacobian_contDiffAt (hT : IsMaterialData D T)
    (hK : N04PartA D S C K base ε) (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {x : PolarPoint}
    (hx : x ∈ physicalPieceOpen S K m) :
    ContDiffAt ℝ ∞ (n07bSourceMaterialJacobian T K z m) x := by
  have hxcore := (hK.2.2.2.1 m).2.2 hx.1
  have hclosed := hK.2.2.2.2.2.2.2.2.1 z hz hs m x ⟨hx.1.1.le, hx.1.2.le⟩
  have hell : ContDiffAt ℝ ∞ (fun y : PolarPoint => T.ell y.1) x :=
    ((hT.1 T.ell (by simp)).contDiffAt (isOpen_Ioo.mem_nhds hxcore)).comp x contDiffAt_fst
  exact hell.mul ((ContinuousFlexibility.contDiffAt_planeJacobian hclosed.1).abs hclosed.2.2.1)

private theorem sampleHeight_pos (hD : IsAccumulatingProfile D)
    (hT : IsMaterialData D T) (K : CanonicalData S) (m : ℕ) :
    0 < T.H (T.sample (K.cell m)) := by
  simpa only [n07bCanonicalSourceFactor, neg_zero, Real.rpow_zero,
    Real.rpow_one, one_mul] using
      (n07bCanonicalSourceFactor_pos_of_material (K := K) hD hT 1 0 m)

theorem n07bSourceHeightRatio_pos (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hK : N04PartA D S C K base ε) (m : ℕ) {x : PolarPoint}
    (hx : x ∈ physicalPieceOpen S K m) : 0 < n07bSourceHeightRatio T K m x :=
  div_pos (hT.2.1 x.1 ((hK.2.2.2.1 m).2.2 hx.1)).2.1 (sampleHeight_pos hD hT K m)

theorem n07bSourceNormalizer_pos (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hK : N04PartA D S C K base ε) (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (β : ℝ) {x : PolarPoint}
    (hx : x ∈ physicalPieceOpen S K m) : 0 < n07bSourceNormalizer T K z m β x :=
  mul_pos (Real.sqrt_pos.mpr (n07bSourceMaterialJacobian_pos hT hK hz hs m hx))
    (Real.rpow_pos_of_pos (n07bSourceHeightRatio_pos hD hT hK m hx) β)

/-- The density, normalizer, material inverse direction, and drift are
actual smooth geometric fields on the actual physical piece. -/
theorem n07b_sourceNormalizationFields_contDiffAt
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hK : N04PartA D S C K base ε) (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (β : ℝ) {x : PolarPoint}
    (hx : x ∈ physicalPieceOpen S K m) :
    ContDiffAt ℝ ∞ (n07bSourceMaterialJacobian T K z m) x ∧
      ContDiffAt ℝ ∞ (n07bSourceNormalizer T K z m β) x ∧
      ContDiffAt ℝ ∞ (n07bSourceMaterialAngleVector T K z m) x ∧
      ContDiffAt ℝ ∞ (n07bSourceNormalizationDrift T K z m) x := by
  have hxcore := (hK.2.2.2.1 m).2.2 hx.1
  have hclosed := hK.2.2.2.2.2.2.2.2.1 z hz hs m x ⟨hx.1.1.le, hx.1.2.le⟩
  have hΩ := n07bSourceMaterialJacobian_contDiffAt hT hK hz hs m hx
  have hΩpos := n07bSourceMaterialJacobian_pos hT hK hz hs m hx
  have hH : ContDiffAt ℝ ∞ (fun y : PolarPoint => T.H y.1) x :=
    ((hT.1 T.H (by simp)).contDiffAt (isOpen_Ioo.mem_nhds hxcore)).comp x contDiffAt_fst
  have hell : ContDiffAt ℝ ∞ (fun y : PolarPoint => T.ell y.1) x :=
    ((hT.1 T.ell (by simp)).contDiffAt (isOpen_Ioo.mem_nhds hxcore)).comp x contDiffAt_fst
  have hR : ContDiffAt ℝ ∞ (n07bSourceHeightRatio T K m) x :=
    hH.div contDiffAt_const (sampleHeight_pos hD hT K m).ne'
  have hV := n07b_contDiffAt_inverseAngleVector hclosed.1 hclosed.2.2.1
  have hDΩ := n07b_contDiffAt_inverseAngleDerivative hclosed.1 hclosed.2.2.1 hΩ
  refine ⟨hΩ, ?_, ?_, ?_⟩
  · exact (hΩ.sqrt hΩpos.ne').mul
      (hR.rpow_const_of_ne (n07bSourceHeightRatio_pos hD hT hK m hx).ne')
  · exact (hV.fst.div hell (hT.2.1 x.1 hxcore).1.ne').prodMk hV.snd
  · exact hDΩ.neg.div (contDiffAt_const.mul hΩ) (mul_ne_zero (by norm_num) hΩpos.ne')

/-- The squared normalizer is the actual material Jacobian density times
the squared material-height ratio. -/
theorem n07bSourceNormalizer_sq (hT : IsMaterialData D T)
    (hK : N04PartA D S C K base ε) (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (β : ℝ) {x : PolarPoint}
    (hx : x ∈ physicalPieceOpen S K m) :
    n07bSourceNormalizer T K z m β x ^ 2 =
      n07bSourceMaterialJacobian T K z m x * (n07bSourceHeightRatio T K m x ^ β) ^ 2 := by
  rw [n07bSourceNormalizer, mul_pow,
    Real.sq_sqrt (n07bSourceMaterialJacobian_pos hT hK hz hs m hx).le]

/-- The actual path energy is exactly the square of its normalized
coefficient. No source function occurs on either side. -/
theorem n07bNormalizedSourceCoefficient_sq (hT : IsMaterialData D T)
    (hK : N04PartA D S C K base ε) (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (β : ℝ) (j : ℕ) (i : n07bAngularChainIndex j)
    {x : PolarPoint} (hx : x ∈ physicalPieceOpen S K m) :
    n07bNormalizedSourceCoefficient T K z m β j i x ^ 2 =
      (n07bSourceMaterialJacobian T K z m x * (n07bSourceHeightRatio T K m x ^ β) ^ 2) *
        n07bAngularChainCoefficient T K z m β j i x ^ 2 := by
  rw [n07bNormalizedSourceCoefficient, mul_pow, n07bSourceNormalizer_sq hT hK hz hs m β hx]

/-- Exact normalization of the unchanged-jet branch. Material-height
derivatives cancel; the only added coefficient is the actual drift. -/
theorem n07b_normalizedSource_stay
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hK : N04PartA D S C K base ε) (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (β : ℝ) {c : PolarPoint → ℝ} {x : PolarPoint}
    (hx : x ∈ physicalPieceOpen S K m) (hc : ContDiffAt ℝ ∞ c x) :
    n07bSourceNormalizer T K z m β x * n07bMaterialCoeffStay T β (K.chart z m) c x =
      n07bInverseAngleDerivative (K.chart z m)
        (fun y => n07bSourceNormalizer T K z m β y * c y) x +
      n07bSourceNormalizationDrift T K z m x * (n07bSourceNormalizer T K z m β x * c x) := by
  let Ω : PolarPoint → ℝ := n07bSourceMaterialJacobian T K z m
  let k : ℝ := (T.H (T.sample (K.cell m)) ^ β)⁻¹
  let u : PolarPoint → ℝ := fun y => T.H y.1 ^ β * c y
  let g : PolarPoint → ℝ := fun y => k * u y
  have hxcore := (hK.2.2.2.1 m).2.2 hx.1
  have hHpos : 0 < T.H x.1 := (hT.2.1 x.1 hxcore).2.1
  have hmpos := sampleHeight_pos hD hT K m
  have hΩ := n07bSourceMaterialJacobian_contDiffAt hT hK hz hs m hx
  have hΩpos := n07bSourceMaterialJacobian_pos hT hK hz hs m hx
  have hu : ContDiffAt ℝ ∞ u x := (n07b_contDiffAt_physicalMaterialWeight hT hxcore β).mul hc
  have hg : ContDiffAt ℝ ∞ g x := contDiffAt_const.mul hu
  have hW : n07bSourceNormalizer T K z m β x = Real.sqrt (Ω x) * k * T.H x.1 ^ β :=
    n07bSourceNormalizer_eq_product T K z m β x hHpos hmpos
  have hcancel : T.H x.1 ^ β * T.H x.1 ^ (-β) = 1 := by
    rw [← Real.rpow_add hHpos, add_neg_cancel, Real.rpow_zero]
  have heq : (fun y => n07bSourceNormalizer T K z m β y * c y) =ᶠ[𝓝 x]
      (fun y => Real.sqrt (Ω y) * g y) := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hx] with y hy
    change n07bSourceNormalizer T K z m β y * c y = Real.sqrt (Ω y) * g y
    rw [n07bSourceNormalizer_eq_product T K z m β y
      (hT.2.1 y.1 ((hK.2.2.2.1 m).2.2 hy.1)).2.1 hmpos]
    dsimp only [Ω, g, k, u]
    ring
  have hderiv : n07bInverseAngleDerivative (K.chart z m)
      (fun y => n07bSourceNormalizer T K z m β y * c y) x =
        n07bInverseAngleDerivative (K.chart z m) (fun y => Real.sqrt (Ω y) * g y) x := by
    rw [n07b_inverseAngle_eq_fderiv, n07b_inverseAngle_eq_fderiv]
    exact congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (n07bInverseAngleVector (K.chart z m) x))
      (heq.fderiv_eq (𝕜 := ℝ))
  calc
    _ = Real.sqrt (Ω x) * k * n07bInverseAngleDerivative (K.chart z m) u x := by
      change n07bSourceNormalizer T K z m β x *
        (T.H x.1 ^ (-β) * n07bInverseAngleDerivative (K.chart z m) u x) = _
      rw [hW]
      calc
        _ = Real.sqrt (Ω x) * k * (T.H x.1 ^ β * T.H x.1 ^ (-β)) *
            n07bInverseAngleDerivative (K.chart z m) u x := by ring
        _ = _ := by rw [hcancel, mul_one]
    _ = Real.sqrt (Ω x) * n07bInverseAngleDerivative (K.chart z m) g x := by
      dsimp only [g]
      rw [n07b_inverseAngle_const_mul (K.chart z m) k (hu.differentiableAt (by simp))]
      ring
    _ = n07bInverseAngleDerivative (K.chart z m) (fun y => Real.sqrt (Ω y) * g y) x +
        n07bSourceNormalizationDrift T K z m x * (Real.sqrt (Ω x) * g x) :=
      n07b_inverseAngle_sqrt_conjugation (K.chart z m)
        (hΩ.differentiableAt (by simp)) hΩpos (hg.differentiableAt (by simp))
    _ = _ := by rw [← hderiv, ← heq.eq_of_nhds]

/-- Every actual normalized path coefficient is smooth on the piece. -/
theorem n07bNormalizedSourceCoefficient_contDiffAt
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hK : N04PartA D S C K base ε) (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (β : ℝ) (j : ℕ) (i : n07bAngularChainIndex j)
    {x : PolarPoint} (hx : x ∈ physicalPieceOpen S K m) :
    ContDiffAt ℝ ∞ (n07bNormalizedSourceCoefficient T K z m β j i) x :=
  (n07b_sourceNormalizationFields_contDiffAt hD hT hK hz hs m β hx).2.1.mul
    (n07b_angularChainCoefficient_contDiffAt hT hK hz hs m β j i hx)

theorem n07bNormalizedSourceCoefficient_stay
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hK : N04PartA D S C K base ε) (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (β : ℝ) (j : ℕ) (i : n07bAngularChainIndex j)
    {x : PolarPoint} (hx : x ∈ physicalPieceOpen S K m) :
    n07bNormalizedSourceCoefficient T K z m β (j + 1) (i, 0) x =
      n07bInverseAngleDerivative (K.chart z m) (n07bNormalizedSourceCoefficient T K z m β j i) x +
        n07bSourceNormalizationDrift T K z m x * n07bNormalizedSourceCoefficient T K z m β j i x := by
  simpa [n07bNormalizedSourceCoefficient, n07bAngularChainCoefficient] using
    n07b_normalizedSource_stay hD hT hK hz hs m β hx
      (n07b_angularChainCoefficient_contDiffAt hT hK hz hs m β j i hx)

theorem n07bNormalizedSourceCoefficient_radial (T : MaterialData) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (β : ℝ) (j : ℕ) (i : n07bAngularChainIndex j)
    (x : PolarPoint) :
    n07bNormalizedSourceCoefficient T K z m β (j + 1) (i, 1) x =
      (n07bSourceMaterialAngleVector T K z m x).1 * n07bNormalizedSourceCoefficient T K z m β j i x := by
  simp only [n07bNormalizedSourceCoefficient, n07bAngularChainCoefficient,
    n07bSourceMaterialAngleVector, n07bMaterialCoeffRadial]
  norm_num <;> ring

theorem n07bNormalizedSourceCoefficient_angular (T : MaterialData) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (β : ℝ) (j : ℕ) (i : n07bAngularChainIndex j)
    (x : PolarPoint) :
    n07bNormalizedSourceCoefficient T K z m β (j + 1) (i, 2) x =
      (n07bSourceMaterialAngleVector T K z m x).2 * n07bNormalizedSourceCoefficient T K z m β j i x := by
  simp only [n07bNormalizedSourceCoefficient, n07bAngularChainCoefficient,
    n07bSourceMaterialAngleVector, n07bMaterialCoeffAngular]
  norm_num <;> ring

theorem n07bNormalizedSourceCoefficient_zero (T : MaterialData) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (β : ℝ) (x : PolarPoint) :
    n07bNormalizedSourceCoefficient T K z m β 0 () x =
      n07bSourceNormalizer T K z m β x * (K.height z m x / |planeJacobian (K.chart z m) x|) := rfl

end ContinuousFlexibility.Analysis
