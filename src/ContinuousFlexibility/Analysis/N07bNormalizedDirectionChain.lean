import ContinuousFlexibility.Analysis.N07bNormalizedDirectionChainCalculus
import ContinuousFlexibility.Analysis.N07bDirectionChain

/-!
# Actual normalized paths for a sequence of geometric directions

The normalizer stays fixed while the direction may change at each layer.
The resulting material recurrence uses the actual components and actual
density drift of that layer's direction. Its initial coefficient is any
prescribed geometric coefficient, independently of the scalar source.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

def n07bNormalizedDirectionChainCoefficient {S : PhysicalSpacesData} (T : MaterialData)
    (K : CanonicalData S) (z : AnnularState S × ℝ) (m : ℕ) (β : ℝ)
    (X : ℕ → PolarPoint → PolarPoint) (c : PolarPoint → ℝ)
    (j : ℕ) (i : n07bAngularChainIndex j) (x : PolarPoint) : ℝ :=
  n07bSourceNormalizer T K z m β x * n07bDirectionChainCoefficient T β X c j i x

def n07bMaterialNormalizedDirectionChainCoefficient {S : PhysicalSpacesData} (T : MaterialData)
    (K : CanonicalData S) (z : AnnularState S × ℝ) (m : ℕ) (β : ℝ)
    (X : ℕ → PolarPoint → PolarPoint) (c : PolarPoint → ℝ)
    (j : ℕ) (i : n07bAngularChainIndex j) : PolarPoint → ℝ :=
  n07bNormalizedDirectionChainCoefficient T K z m β X c j i ∘ n07bMaterialRadiusChart T

def n07bMaterialDirectionV1 (T : MaterialData) (Y : PolarPoint → PolarPoint)
    (y : PolarPoint) : ℝ :=
  (n07bDirectionMaterialVector T Y (n07bMaterialRadiusChart T y)).1

def n07bMaterialDirectionV2 (T : MaterialData) (Y : PolarPoint → PolarPoint)
    (y : PolarPoint) : ℝ :=
  (n07bDirectionMaterialVector T Y (n07bMaterialRadiusChart T y)).2

def n07bMaterialDirectionDrift {S : PhysicalSpacesData} (T : MaterialData)
    (K : CanonicalData S) (z : AnnularState S × ℝ) (m : ℕ)
    (Y : PolarPoint → PolarPoint) : PolarPoint → ℝ :=
  n07bDirectionNormalizationDrift T K z m Y ∘ n07bMaterialRadiusChart T

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
  {z : AnnularState S × ℝ}

theorem n07bNormalizedDirectionChainCoefficient_contDiffAt
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hK : N04PartA D S C K base ε) (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (β : ℝ)
    {X : ℕ → PolarPoint → PolarPoint} {c : PolarPoint → ℝ} {x : PolarPoint}
    (hx : x ∈ physicalPieceOpen S K z m)
    (hX : ∀ j, ContDiffAt ℝ ∞ (X j) x) (hc : ContDiffAt ℝ ∞ c x)
    (j : ℕ) (i : n07bAngularChainIndex j) :
    ContDiffAt ℝ ∞ (n07bNormalizedDirectionChainCoefficient T K z m β X c j i) x :=
  (n07b_sourceNormalizationFields_contDiffAt hD hT hK hz hs m β hx).2.1.mul
    (n07bDirectionChainCoefficient_contDiffAt hT (((hK.domains z hz hs m).2.2.1 hx).1) β hX hc j i)

theorem n07bMaterialNormalizedDirectionChainCoefficient_contDiffOn
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hK : N04PartA D S C K base ε) (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (β : ℝ)
    {X : ℕ → PolarPoint → PolarPoint} {c : PolarPoint → ℝ}
    (hX : ∀ j, ContDiffOn ℝ ∞ (X j) (physicalPieceOpen S K z m))
    (hc : ContDiffOn ℝ ∞ c (physicalPieceOpen S K z m))
    (j : ℕ) (i : n07bAngularChainIndex j) :
    ContDiffOn ℝ ∞ (n07bMaterialNormalizedDirectionChainCoefficient T K z m β X c j i)
      (n07bSourceMaterialPiece T K z m) := by
  intro y hy
  have hx : n07bMaterialRadiusChart T y ∈ physicalPieceOpen S K z m := hy
  have hU : IsOpen (physicalPieceOpen S K z m) := (hK.domains z hz hs m).1
  exact ((n07bNormalizedDirectionChainCoefficient_contDiffAt hD hT hK hz hs m β hx
    (fun k => (hX k).contDiffAt (hU.mem_nhds hx)) (hc.contDiffAt (hU.mem_nhds hx)) j i).comp y
      (n07bMaterialRadiusChart_contDiff hT).contDiffAt).contDiffWithinAt

theorem n07b_materialDirectionFields_contDiffOn
    (hT : IsMaterialData D T) (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ)
    {Y : PolarPoint → PolarPoint} (hY : ContDiffOn ℝ ∞ Y (physicalPieceOpen S K z m)) :
    ContDiffOn ℝ ∞ (n07bMaterialDirectionV1 T Y) (n07bSourceMaterialPiece T K z m) ∧
      ContDiffOn ℝ ∞ (n07bMaterialDirectionV2 T Y) (n07bSourceMaterialPiece T K z m) ∧
      ContDiffOn ℝ ∞ (n07bMaterialDirectionDrift T K z m Y) (n07bSourceMaterialPiece T K z m) := by
  have hU : IsOpen (physicalPieceOpen S K z m) := (hK.domains z hz hs m).1
  have hfield (y : PolarPoint) (hy : y ∈ n07bSourceMaterialPiece T K z m) :
      ContDiffAt ℝ ∞ (n07bDirectionMaterialVector T Y) (n07bMaterialRadiusChart T y) ∧
        ContDiffAt ℝ ∞ (n07bDirectionNormalizationDrift T K z m Y)
          (n07bMaterialRadiusChart T y) := by
    have hx : n07bMaterialRadiusChart T y ∈ physicalPieceOpen S K z m := hy
    exact n07b_directionNormalizationFields_contDiffAt hT hK hz hs m hx
      (hY.contDiffAt (hU.mem_nhds hx))
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    exact ((hfield y hy).1.fst.comp y (n07bMaterialRadiusChart_contDiff hT).contDiffAt).contDiffWithinAt
  · intro y hy
    exact ((hfield y hy).1.snd.comp y (n07bMaterialRadiusChart_contDiff hT).contDiffAt).contDiffWithinAt
  · intro y hy
    exact ((hfield y hy).2.comp y (n07bMaterialRadiusChart_contDiff hT).contDiffAt).contDiffWithinAt

theorem n07bNormalizedDirectionChainCoefficient_stay
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hK : N04PartA D S C K base ε) (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (β : ℝ)
    {X : ℕ → PolarPoint → PolarPoint} {c : PolarPoint → ℝ} {x : PolarPoint}
    (hx : x ∈ physicalPieceOpen S K z m)
    (hX : ∀ j, ContDiffAt ℝ ∞ (X j) x) (hc : ContDiffAt ℝ ∞ c x)
    (j : ℕ) (i : n07bAngularChainIndex j) :
    n07bNormalizedDirectionChainCoefficient T K z m β X c (j + 1) (i, 0) x =
      n07bDirectionalDerivative (X j) (n07bNormalizedDirectionChainCoefficient T K z m β X c j i) x +
        n07bDirectionNormalizationDrift T K z m (X j) x *
          n07bNormalizedDirectionChainCoefficient T K z m β X c j i x := by
  change n07bSourceNormalizer T K z m β x *
      n07bDirectionCoeffStay T β (X j) (n07bDirectionChainCoefficient T β X c j i) x =
    n07bDirectionalDerivative (X j)
        (fun y => n07bSourceNormalizer T K z m β y * n07bDirectionChainCoefficient T β X c j i y) x +
      n07bDirectionNormalizationDrift T K z m (X j) x *
        (n07bSourceNormalizer T K z m β x * n07bDirectionChainCoefficient T β X c j i x)
  exact n07b_normalizedDirection_stay hD hT hK hz hs m β (X j) hx
    (n07bDirectionChainCoefficient_contDiffAt hT (((hK.domains z hz hs m).2.2.1 hx).1) β hX hc j i)

theorem n07bNormalizedDirectionChainCoefficient_radial
    (T : MaterialData) (K : CanonicalData S) (z : AnnularState S × ℝ) (m : ℕ) (β : ℝ)
    (X : ℕ → PolarPoint → PolarPoint) (c : PolarPoint → ℝ)
    (j : ℕ) (i : n07bAngularChainIndex j) (x : PolarPoint) :
    n07bNormalizedDirectionChainCoefficient T K z m β X c (j + 1) (i, 1) x =
      (n07bDirectionMaterialVector T (X j) x).1 *
        n07bNormalizedDirectionChainCoefficient T K z m β X c j i x := by
  change n07bSourceNormalizer T K z m β x *
      (((X j x).1 / T.ell x.1) * n07bDirectionChainCoefficient T β X c j i x) =
    ((X j x).1 / T.ell x.1) *
      (n07bSourceNormalizer T K z m β x * n07bDirectionChainCoefficient T β X c j i x)
  ring

theorem n07bNormalizedDirectionChainCoefficient_angular
    (T : MaterialData) (K : CanonicalData S) (z : AnnularState S × ℝ) (m : ℕ) (β : ℝ)
    (X : ℕ → PolarPoint → PolarPoint) (c : PolarPoint → ℝ)
    (j : ℕ) (i : n07bAngularChainIndex j) (x : PolarPoint) :
    n07bNormalizedDirectionChainCoefficient T K z m β X c (j + 1) (i, 2) x =
      (n07bDirectionMaterialVector T (X j) x).2 *
        n07bNormalizedDirectionChainCoefficient T K z m β X c j i x := by
  change n07bSourceNormalizer T K z m β x *
      ((X j x).2 * n07bDirectionChainCoefficient T β X c j i x) =
    (X j x).2 *
      (n07bSourceNormalizer T K z m β x * n07bDirectionChainCoefficient T β X c j i x)
  ring

/-- The real recurrence after the prescribed material pullback. -/
theorem n07bMaterialNormalizedDirectionChainCoefficient_stay
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hK : N04PartA D S C K base ε) (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (β : ℝ)
    {X : ℕ → PolarPoint → PolarPoint} {c : PolarPoint → ℝ}
    (hX : ∀ j, ContDiffOn ℝ ∞ (X j) (physicalPieceOpen S K z m))
    (hc : ContDiffOn ℝ ∞ c (physicalPieceOpen S K z m))
    (j : ℕ) (i : n07bAngularChainIndex j) {y : PolarPoint}
    (hy : y ∈ n07bSourceMaterialPiece T K z m) :
    n07bMaterialNormalizedDirectionChainCoefficient T K z m β X c (j + 1) (i, 0) y =
      n07bMaterialDirectionV1 T (X j) y *
          radialPartial (n07bMaterialNormalizedDirectionChainCoefficient T K z m β X c j i) y +
        n07bMaterialDirectionV2 T (X j) y *
          angularPartial (n07bMaterialNormalizedDirectionChainCoefficient T K z m β X c j i) y +
        n07bMaterialDirectionDrift T K z m (X j) y *
          n07bMaterialNormalizedDirectionChainCoefficient T K z m β X c j i y := by
  have hx : n07bMaterialRadiusChart T y ∈ physicalPieceOpen S K z m := hy
  have hU : IsOpen (physicalPieceOpen S K z m) := (hK.domains z hz hs m).1
  have hXp (k : ℕ) := (hX k).contDiffAt (hU.mem_nhds hx)
  have hcp := hc.contDiffAt (hU.mem_nhds hx)
  have hd := n07b_directional_materialized hT (X j) (((hK.domains z hz hs m).2.2.1 hx).1)
    ((n07bNormalizedDirectionChainCoefficient_contDiffAt hD hT hK hz hs m β hx hXp hcp j i).differentiableAt
      (by simp))
  rw [n07bMaterialChart_radiusChart hT y] at hd
  change n07bNormalizedDirectionChainCoefficient T K z m β X c (j + 1) (i, 0)
    (n07bMaterialRadiusChart T y) = _
  rw [n07bNormalizedDirectionChainCoefficient_stay hD hT hK hz hs m β hx hXp hcp j i, hd]
  rfl

theorem n07bMaterialNormalizedDirectionChainCoefficient_radial
    (T : MaterialData) (K : CanonicalData S) (z : AnnularState S × ℝ) (m : ℕ) (β : ℝ)
    (X : ℕ → PolarPoint → PolarPoint) (c : PolarPoint → ℝ)
    (j : ℕ) (i : n07bAngularChainIndex j) (y : PolarPoint) :
    n07bMaterialNormalizedDirectionChainCoefficient T K z m β X c (j + 1) (i, 1) y =
      n07bMaterialDirectionV1 T (X j) y *
        n07bMaterialNormalizedDirectionChainCoefficient T K z m β X c j i y :=
  n07bNormalizedDirectionChainCoefficient_radial T K z m β X c j i (n07bMaterialRadiusChart T y)

theorem n07bMaterialNormalizedDirectionChainCoefficient_angular
    (T : MaterialData) (K : CanonicalData S) (z : AnnularState S × ℝ) (m : ℕ) (β : ℝ)
    (X : ℕ → PolarPoint → PolarPoint) (c : PolarPoint → ℝ)
    (j : ℕ) (i : n07bAngularChainIndex j) (y : PolarPoint) :
    n07bMaterialNormalizedDirectionChainCoefficient T K z m β X c (j + 1) (i, 2) y =
      n07bMaterialDirectionV2 T (X j) y *
        n07bMaterialNormalizedDirectionChainCoefficient T K z m β X c j i y :=
  n07bNormalizedDirectionChainCoefficient_angular T K z m β X c j i (n07bMaterialRadiusChart T y)

/-- Multiplication of the geometric seed is actual multiplication of the
normalized seed, so ordinary finite-product jet bounds apply directly. -/
theorem n07bMaterialNormalizedDirectionChainCoefficient_seed_mul
    (T : MaterialData) (K : CanonicalData S) (z : AnnularState S × ℝ) (m : ℕ) (β : ℝ)
    (X : ℕ → PolarPoint → PolarPoint) (α c : PolarPoint → ℝ) (y : PolarPoint) :
    n07bMaterialNormalizedDirectionChainCoefficient T K z m β X (fun x => α x * c x) 0 () y =
      α (n07bMaterialRadiusChart T y) *
        n07bMaterialNormalizedDirectionChainCoefficient T K z m β X c 0 () y := by
  change n07bSourceNormalizer T K z m β (n07bMaterialRadiusChart T y) *
      (α (n07bMaterialRadiusChart T y) * c (n07bMaterialRadiusChart T y)) = _
  change _ = α (n07bMaterialRadiusChart T y) *
    (n07bSourceNormalizer T K z m β (n07bMaterialRadiusChart T y) * c (n07bMaterialRadiusChart T y))
  ring

end ContinuousFlexibility.Analysis
