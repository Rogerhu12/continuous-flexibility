module

public import ContinuousFlexibility.Analysis.N07bNormalizedSourceChain

/-!
# Actual normalized coefficients in material coordinates

The physical normalized recursion is transported by the prescribed radius
map. On the actual material preimage of each piece it is the usual scalar
first-order recurrence with two coordinate partials and one drift term.
All identities use the genuine inverse relation of `rho` and `radius`.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

def n07bMaterialRadiusChart (T : MaterialData) (y : PolarPoint) : PolarPoint :=
  (T.radius y.1, y.2)

def n07bSourceMaterialPiece {S : PhysicalSpacesData} (T : MaterialData)
    (K : CanonicalData S) (z : AnnularState S × ℝ) (m : ℕ) : Set PolarPoint :=
  n07bMaterialRadiusChart T ⁻¹' physicalPieceOpen S K z m

def n07bMaterialSourceV1 {S : PhysicalSpacesData} (T : MaterialData)
    (K : CanonicalData S) (z : AnnularState S × ℝ) (m : ℕ) (y : PolarPoint) : ℝ :=
  (n07bSourceMaterialAngleVector T K z m (n07bMaterialRadiusChart T y)).1

def n07bMaterialSourceV2 {S : PhysicalSpacesData} (T : MaterialData)
    (K : CanonicalData S) (z : AnnularState S × ℝ) (m : ℕ) (y : PolarPoint) : ℝ :=
  (n07bSourceMaterialAngleVector T K z m (n07bMaterialRadiusChart T y)).2

def n07bMaterialSourceDrift {S : PhysicalSpacesData} (T : MaterialData)
    (K : CanonicalData S) (z : AnnularState S × ℝ) (m : ℕ) (y : PolarPoint) : ℝ :=
  n07bSourceNormalizationDrift T K z m (n07bMaterialRadiusChart T y)

def n07bMaterialNormalizedSourceCoefficient {S : PhysicalSpacesData} (T : MaterialData)
    (K : CanonicalData S) (z : AnnularState S × ℝ) (m : ℕ) (β : ℝ)
    (j : ℕ) (i : n07bAngularChainIndex j) : PolarPoint → ℝ :=
  n07bNormalizedSourceCoefficient T K z m β j i ∘ n07bMaterialRadiusChart T

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
  {z : AnnularState S × ℝ}

theorem n07bMaterialRadiusChart_contDiff (hT : IsMaterialData D T) :
    ContDiff ℝ ∞ (n07bMaterialRadiusChart T) := by
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, hr, _⟩ := hdata
  exact (hr.comp contDiff_fst).prodMk contDiff_snd

theorem n07bMaterialChart_radiusChart (hT : IsMaterialData D T) (y : PolarPoint) :
    n07bMaterialChart T (n07bMaterialRadiusChart T y) = y := by
  apply Prod.ext
  · change T.rho (T.radius y.1) = y.1
    exact (hT.2.2.2.2.2.2.2.1 y.1).2
  · rfl

theorem n07bMaterialRadiusChart_materialChart (hT : IsMaterialData D T)
    {x : PolarPoint} (hx : x.1 ∈ Ioo D.a D.b) :
    n07bMaterialRadiusChart T (n07bMaterialChart T x) = x := by
  apply Prod.ext
  · change T.radius (T.rho x.1) = x.1
    exact hT.2.2.2.2.2.2.2.2.1 x.1 hx
  · rfl

theorem n07bSourceMaterialPiece_isOpen (hT : IsMaterialData D T)
    (hK : N04PartA D S C K base ε) (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) : IsOpen (n07bSourceMaterialPiece T K z m) :=
  (hK.domains z hz hs m).1.preimage (n07bMaterialRadiusChart_contDiff hT).continuous

/-- The actual inverse angular derivative becomes its two material
coordinate coefficients after the genuine radius pullback. -/
theorem n07b_inverseAngle_materialized (hT : IsMaterialData D T)
    (Ψ : PolarPoint → PolarPoint) {c : PolarPoint → ℝ} {x : PolarPoint}
    (hx : x.1 ∈ Ioo D.a D.b) (hc : DifferentiableAt ℝ c x) :
    n07bInverseAngleDerivative Ψ c x =
      (n07bInverseAngleVector Ψ x).1 / T.ell x.1 *
        radialPartial (c ∘ n07bMaterialRadiusChart T) (n07bMaterialChart T x) +
      (n07bInverseAngleVector Ψ x).2 *
        angularPartial (c ∘ n07bMaterialRadiusChart T) (n07bMaterialChart T x) := by
  have heq : c =ᶠ[𝓝 x] ((c ∘ n07bMaterialRadiusChart T) ∘ n07bMaterialChart T) := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hx, mem_univ x.2⟩] with y hy
    change c y = c (n07bMaterialRadiusChart T (n07bMaterialChart T y))
    rw [n07bMaterialRadiusChart_materialChart hT hy.1]
  have hinner : DifferentiableAt ℝ c
      (n07bMaterialRadiusChart T (n07bMaterialChart T x)) := by
    rw [n07bMaterialRadiusChart_materialChart hT hx]
    exact hc
  have hu : DifferentiableAt ℝ (c ∘ n07bMaterialRadiusChart T) (n07bMaterialChart T x) :=
    hinner.comp _ ((n07bMaterialRadiusChart_contDiff hT).differentiable (by simp) _)
  have hd : n07bInverseAngleDerivative Ψ c x =
      n07bInverseAngleDerivative Ψ ((c ∘ n07bMaterialRadiusChart T) ∘ n07bMaterialChart T) x := by
    rw [n07b_inverseAngle_eq_fderiv, n07b_inverseAngle_eq_fderiv]
    exact congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (n07bInverseAngleVector Ψ x))
      (heq.fderiv_eq (𝕜 := ℝ))
  exact hd.trans (n07b_inverseAngle_material_comp hT Ψ hx hu)

theorem n07bMaterialNormalizedSourceCoefficient_contDiffOn
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hK : N04PartA D S C K base ε) (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (β : ℝ) (j : ℕ) (i : n07bAngularChainIndex j) :
    ContDiffOn ℝ ∞ (n07bMaterialNormalizedSourceCoefficient T K z m β j i)
      (n07bSourceMaterialPiece T K z m) := by
  intro y hy
  have hx : n07bMaterialRadiusChart T y ∈ physicalPieceOpen S K z m := hy
  exact ((n07bNormalizedSourceCoefficient_contDiffAt hD hT hK hz hs m β j i hx).comp y
    (n07bMaterialRadiusChart_contDiff hT).contDiffAt).contDiffWithinAt

theorem n07b_materialSourceFields_contDiffOn
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hK : N04PartA D S C K base ε) (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) :
    ContDiffOn ℝ ∞ (n07bMaterialSourceV1 T K z m) (n07bSourceMaterialPiece T K z m) ∧
      ContDiffOn ℝ ∞ (n07bMaterialSourceV2 T K z m) (n07bSourceMaterialPiece T K z m) ∧
      ContDiffOn ℝ ∞ (n07bMaterialSourceDrift T K z m) (n07bSourceMaterialPiece T K z m) := by
  have hX := (n07bMaterialRadiusChart_contDiff hT)
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    have hx : n07bMaterialRadiusChart T y ∈ physicalPieceOpen S K z m := hy
    exact (((n07b_sourceNormalizationFields_contDiffAt hD hT hK hz hs m 0 hx).2.2.1.fst).comp
      y hX.contDiffAt).contDiffWithinAt
  · intro y hy
    have hx : n07bMaterialRadiusChart T y ∈ physicalPieceOpen S K z m := hy
    exact (((n07b_sourceNormalizationFields_contDiffAt hD hT hK hz hs m 0 hx).2.2.1.snd).comp
      y hX.contDiffAt).contDiffWithinAt
  · intro y hy
    have hx : n07bMaterialRadiusChart T y ∈ physicalPieceOpen S K z m := hy
    exact ((n07b_sourceNormalizationFields_contDiffAt hD hT hK hz hs m 0 hx).2.2.2.comp
      y hX.contDiffAt).contDiffWithinAt

theorem n07bMaterialNormalizedSourceCoefficient_stay
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hK : N04PartA D S C K base ε) (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (β : ℝ) (j : ℕ) (i : n07bAngularChainIndex j)
    {y : PolarPoint} (hy : y ∈ n07bSourceMaterialPiece T K z m) :
    n07bMaterialNormalizedSourceCoefficient T K z m β (j + 1) (i, 0) y =
      n07bMaterialSourceV1 T K z m y * radialPartial (n07bMaterialNormalizedSourceCoefficient T K z m β j i) y +
      n07bMaterialSourceV2 T K z m y * angularPartial (n07bMaterialNormalizedSourceCoefficient T K z m β j i) y +
      n07bMaterialSourceDrift T K z m y * n07bMaterialNormalizedSourceCoefficient T K z m β j i y := by
  have hx : n07bMaterialRadiusChart T y ∈ physicalPieceOpen S K z m := hy
  have hc := (n07bNormalizedSourceCoefficient_contDiffAt hD hT hK hz hs m β j i hx).differentiableAt
    (by simp)
  have hd := n07b_inverseAngle_materialized hT (K.chart z m)
    (((hK.domains z hz hs m).2.2.1 hx).1) hc
  rw [n07bMaterialChart_radiusChart hT y] at hd
  change n07bNormalizedSourceCoefficient T K z m β (j + 1) (i, 0) (n07bMaterialRadiusChart T y) = _
  rw [n07bNormalizedSourceCoefficient_stay hD hT hK hz hs m β j i hx, hd]
  rfl

theorem n07bMaterialNormalizedSourceCoefficient_radial (T : MaterialData) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (β : ℝ) (j : ℕ) (i : n07bAngularChainIndex j) (y : PolarPoint) :
    n07bMaterialNormalizedSourceCoefficient T K z m β (j + 1) (i, 1) y =
      n07bMaterialSourceV1 T K z m y * n07bMaterialNormalizedSourceCoefficient T K z m β j i y :=
  n07bNormalizedSourceCoefficient_radial T K z m β j i (n07bMaterialRadiusChart T y)

theorem n07bMaterialNormalizedSourceCoefficient_angular (T : MaterialData) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (β : ℝ) (j : ℕ) (i : n07bAngularChainIndex j) (y : PolarPoint) :
    n07bMaterialNormalizedSourceCoefficient T K z m β (j + 1) (i, 2) y =
      n07bMaterialSourceV2 T K z m y * n07bMaterialNormalizedSourceCoefficient T K z m β j i y :=
  n07bNormalizedSourceCoefficient_angular T K z m β j i (n07bMaterialRadiusChart T y)

end ContinuousFlexibility.Analysis
