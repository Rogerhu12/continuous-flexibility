module

public import ContinuousFlexibility.Analysis.N07bMaterialDirection
public import ContinuousFlexibility.Analysis.N07bNormalizedSourceMaterial

/-!
# The same density normalization for arbitrary actual directions

The normalizer is the one already used by the current canonical source.
An arbitrary geometric direction has the same exact conjugation rule;
only its two material components and its actual density drift change.
Every identity is proved from the genuine differential, not postulated.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

def n07bDirectionMaterialVector (T : MaterialData)
    (Y : PolarPoint → PolarPoint) (x : PolarPoint) : PolarPoint :=
  ((Y x).1 / T.ell x.1, (Y x).2)

def n07bDirectionNormalizationDrift {S : PhysicalSpacesData} (T : MaterialData)
    (K : CanonicalData S) (z : AnnularState S × ℝ) (m : ℕ)
    (Y : PolarPoint → PolarPoint) (x : PolarPoint) : ℝ :=
  -n07bDirectionalDerivative Y (n07bSourceMaterialJacobian T K z m) x /
    (2 * n07bSourceMaterialJacobian T K z m x)

theorem n07b_directional_const_mul (Y : PolarPoint → PolarPoint) (a : ℝ)
    {g : PolarPoint → ℝ} {x : PolarPoint} (hg : DifferentiableAt ℝ g x) :
    n07bDirectionalDerivative Y (fun y => a * g y) x =
      a * n07bDirectionalDerivative Y g x := by
  rw [n07bDirectionalDerivative_mul Y (differentiableAt_const a) hg]
  simp [n07bDirectionalDerivative, radialPartial, angularPartial]

/-- The actual derivative of the square root in any geometric direction. -/
theorem n07b_directional_sqrt (Y : PolarPoint → PolarPoint)
    {Ω : PolarPoint → ℝ} {x : PolarPoint}
    (hΩ : DifferentiableAt ℝ Ω x) (hpos : 0 < Ω x) :
    n07bDirectionalDerivative Y (fun y => Real.sqrt (Ω y)) x =
      n07bDirectionalDerivative Y Ω x / (2 * Real.sqrt (Ω x)) := by
  have hs := hΩ.sqrt hpos.ne'
  have heq : (fun y => Real.sqrt (Ω y) * Real.sqrt (Ω y)) =ᶠ[𝓝 x] Ω := by
    filter_upwards [hΩ.continuousAt.eventually (isOpen_Ioi.mem_nhds hpos)] with y hy
    exact Real.mul_self_sqrt hy.le
  have hd := n07bDirectionalDerivative_congr Y heq
  rw [n07bDirectionalDerivative_mul Y hs hs] at hd
  apply (eq_div_iff (mul_ne_zero (by norm_num) (Real.sqrt_pos.mpr hpos).ne')).mpr
  calc
    _ = n07bDirectionalDerivative Y (fun y => Real.sqrt (Ω y)) x * Real.sqrt (Ω x) +
        Real.sqrt (Ω x) * n07bDirectionalDerivative Y (fun y => Real.sqrt (Ω y)) x := by ring
    _ = _ := hd

/-- The half-density conjugation uses the same density for every direction. -/
theorem n07b_directional_sqrt_conjugation (Y : PolarPoint → PolarPoint)
    {Ω g : PolarPoint → ℝ} {x : PolarPoint}
    (hΩ : DifferentiableAt ℝ Ω x) (hpos : 0 < Ω x)
    (hg : DifferentiableAt ℝ g x) :
    Real.sqrt (Ω x) * n07bDirectionalDerivative Y g x =
      n07bDirectionalDerivative Y (fun y => Real.sqrt (Ω y) * g y) x +
        (-n07bDirectionalDerivative Y Ω x / (2 * Ω x)) *
          (Real.sqrt (Ω x) * g x) := by
  rw [n07bDirectionalDerivative_mul Y (hΩ.sqrt hpos.ne') hg,
    n07b_directional_sqrt Y hΩ hpos]
  let s : ℝ := Real.sqrt (Ω x)
  have hs : s ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hsquare : s ^ 2 = Ω x := Real.sq_sqrt hpos.le
  change s * n07bDirectionalDerivative Y g x =
    n07bDirectionalDerivative Y Ω x / (2 * s) * g x +
      s * n07bDirectionalDerivative Y g x +
        (-n07bDirectionalDerivative Y Ω x / (2 * Ω x)) * (s * g x)
  rw [← hsquare]
  field_simp [hs] <;> ring

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
  {z : AnnularState S × ℝ}

/-- The actual material components and density drift are smooth where the
chosen physical direction and chart are smooth. -/
theorem n07b_directionNormalizationFields_contDiffAt
    (hT : IsMaterialData D T) (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {Y : PolarPoint → PolarPoint} {x : PolarPoint}
    (hx : x ∈ physicalPieceOpen S K z m) (hY : ContDiffAt ℝ ∞ Y x) :
    ContDiffAt ℝ ∞ (n07bDirectionMaterialVector T Y) x ∧
      ContDiffAt ℝ ∞ (n07bDirectionNormalizationDrift T K z m Y) x := by
  have hxcore := ((hK.domains z hz hs m).2.2.1 hx).1
  have hΩ := n07bSourceMaterialJacobian_contDiffAt hT hK hz hs m hx
  have hΩpos := n07bSourceMaterialJacobian_pos hT hK hz hs m hx
  have hell : ContDiffAt ℝ ∞ (fun y : PolarPoint => T.ell y.1) x :=
    ((hT.1 T.ell (by simp)).contDiffAt (isOpen_Ioo.mem_nhds hxcore)).comp x contDiffAt_fst
  exact ⟨(hY.fst.div hell (hT.2.1 x.1 hxcore).1.ne').prodMk hY.snd,
    (n07b_contDiffAt_directionalDerivative hY hΩ).neg.div (contDiffAt_const.mul hΩ)
      (mul_ne_zero (by norm_num) hΩpos.ne')⟩

/-- The unchanged-material-jet branch has the actual drift
`-D_Y Omega/(2 Omega)`, with no material-height derivative left over. -/
theorem n07b_normalizedDirection_stay
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hK : N04PartA D S C K base ε) (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (β : ℝ) (Y : PolarPoint → PolarPoint)
    {c : PolarPoint → ℝ} {x : PolarPoint}
    (hx : x ∈ physicalPieceOpen S K z m) (hc : ContDiffAt ℝ ∞ c x) :
    n07bSourceNormalizer T K z m β x * n07bDirectionCoeffStay T β Y c x =
      n07bDirectionalDerivative Y (fun y => n07bSourceNormalizer T K z m β y * c y) x +
        n07bDirectionNormalizationDrift T K z m Y x *
          (n07bSourceNormalizer T K z m β x * c x) := by
  let Ω : PolarPoint → ℝ := n07bSourceMaterialJacobian T K z m
  let k : ℝ := (T.H (T.sample (K.cell m)) ^ β)⁻¹
  let u : PolarPoint → ℝ := fun y => T.H y.1 ^ β * c y
  let g : PolarPoint → ℝ := fun y => k * u y
  have hxcore := ((hK.domains z hz hs m).2.2.1 hx).1
  have hHpos : 0 < T.H x.1 := (hT.2.1 x.1 hxcore).2.1
  have hmpos : 0 < T.H (T.sample (K.cell m)) := by
    simpa only [n07bCanonicalSourceFactor, neg_zero, Real.rpow_zero,
      Real.rpow_one, one_mul] using
        (n07bCanonicalSourceFactor_pos_of_material (K := K) hD hT 1 0 m)
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
    filter_upwards [(hK.domains z hz hs m).1.mem_nhds hx] with y hy
    change n07bSourceNormalizer T K z m β y * c y = Real.sqrt (Ω y) * g y
    rw [n07bSourceNormalizer_eq_product T K z m β y
      (hT.2.1 y.1 (((hK.domains z hz hs m).2.2.1 hy).1)).2.1 hmpos]
    dsimp only [Ω, g, k, u]
    ring
  have hderiv := n07bDirectionalDerivative_congr Y heq
  calc
    _ = Real.sqrt (Ω x) * k * n07bDirectionalDerivative Y u x := by
      change n07bSourceNormalizer T K z m β x * (T.H x.1 ^ (-β) * n07bDirectionalDerivative Y u x) = _
      rw [hW]
      calc
        _ = Real.sqrt (Ω x) * k * (T.H x.1 ^ β * T.H x.1 ^ (-β)) *
            n07bDirectionalDerivative Y u x := by ring
        _ = _ := by rw [hcancel, mul_one]
    _ = Real.sqrt (Ω x) * n07bDirectionalDerivative Y g x := by
      dsimp only [g]
      rw [n07b_directional_const_mul Y k (hu.differentiableAt (by simp))]
      ring
    _ = n07bDirectionalDerivative Y (fun y => Real.sqrt (Ω y) * g y) x +
        n07bDirectionNormalizationDrift T K z m Y x * (Real.sqrt (Ω x) * g x) :=
      n07b_directional_sqrt_conjugation Y (hΩ.differentiableAt (by simp))
        hΩpos (hg.differentiableAt (by simp))
    _ = _ := by rw [← hderiv, ← heq.eq_of_nhds]

/-- Transport of an actual physical directional derivative by the actual
material coordinate inverse, proved on a full neighborhood of the point. -/
theorem n07b_directional_materialized (hT : IsMaterialData D T)
    (Y : PolarPoint → PolarPoint) {c : PolarPoint → ℝ} {x : PolarPoint}
    (hx : x.1 ∈ Ioo D.a D.b) (hc : DifferentiableAt ℝ c x) :
    n07bDirectionalDerivative Y c x =
      (n07bDirectionMaterialVector T Y x).1 *
          radialPartial (c ∘ n07bMaterialRadiusChart T) (n07bMaterialChart T x) +
        (n07bDirectionMaterialVector T Y x).2 *
          angularPartial (c ∘ n07bMaterialRadiusChart T) (n07bMaterialChart T x) := by
  have heq : c =ᶠ[𝓝 x] ((c ∘ n07bMaterialRadiusChart T) ∘ n07bMaterialChart T) := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hx, mem_univ x.2⟩] with y hy
    change c y = c (n07bMaterialRadiusChart T (n07bMaterialChart T y))
    rw [n07bMaterialRadiusChart_materialChart hT hy.1]
  have hinner : DifferentiableAt ℝ c (n07bMaterialRadiusChart T (n07bMaterialChart T x)) := by
    rw [n07bMaterialRadiusChart_materialChart hT hx]
    exact hc
  have hu : DifferentiableAt ℝ (c ∘ n07bMaterialRadiusChart T) (n07bMaterialChart T x) :=
    hinner.comp _ ((n07bMaterialRadiusChart_contDiff hT).differentiable (by simp) _)
  exact (n07bDirectionalDerivative_congr Y heq).trans
    (n07b_directional_material_comp hT Y hx hu)

end ContinuousFlexibility.Analysis
