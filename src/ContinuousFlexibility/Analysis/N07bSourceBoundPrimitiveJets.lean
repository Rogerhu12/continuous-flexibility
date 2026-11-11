import ContinuousFlexibility.Analysis.N07bNormalizedSourceJetBounds
import ContinuousFlexibility.Analysis.N07bNormalizedSourceMaterial
import ContinuousFlexibility.Analysis.N07bSourceBoundMajorant

/-!
# Actual source coefficients from four primitive geometric jets

The hypothesis concerns only the initial normalized coefficient, the two
material components of the inverse angular direction, and its scalar
drift. No higher path coefficient or source function occurs in it. The
actual recursion proves the higher coefficient estimate, and its squared
normalization is exactly the multiplier used by the source-energy bound.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- A common finite jet bound for the four actual material-coordinate
primitive fields. Only the order-zero path coefficient is primitive. -/
def N07bSourcePrimitiveJetBound {S : PhysicalSpacesData} (T : MaterialData)
    (K : CanonicalData S) (z : AnnularState S × ℝ) (m b : ℕ) (R : ℝ)
    (y : PolarPoint) : Prop :=
  (∀ n : ℕ, n ≤ b →
    ‖iteratedFDeriv ℝ n (n07bMaterialNormalizedSourceCoefficient T K z m (3 / 4 : ℝ) 0 ()) y‖ ≤ R) ∧
  (∀ n : ℕ, n ≤ b → ‖iteratedFDeriv ℝ n (n07bMaterialSourceV1 T K z m) y‖ ≤ R) ∧
  (∀ n : ℕ, n ≤ b → ‖iteratedFDeriv ℝ n (n07bMaterialSourceV2 T K z m) y‖ ≤ R) ∧
  (∀ n : ℕ, n ≤ b → ‖iteratedFDeriv ℝ n (n07bMaterialSourceDrift T K z m) y‖ ≤ R)

theorem N07bSourcePrimitiveJetBound.mono {S : PhysicalSpacesData} {T : MaterialData}
    {K : CanonicalData S} {z : AnnularState S × ℝ} {m b : ℕ} {R R' : ℝ}
    {y : PolarPoint} (h : N07bSourcePrimitiveJetBound T K z m b R y) (hRR : R ≤ R') :
    N07bSourcePrimitiveJetBound T K z m b R' y :=
  ⟨fun n hn => (h.1 n hn).trans hRR,
    fun n hn => (h.2.1 n hn).trans hRR,
    fun n hn => (h.2.2.1 n hn).trans hRR,
    fun n hn => (h.2.2.2 n hn).trans hRR⟩

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
  {z : AnnularState S × ℝ}

/-- The primitive jet bound controls all actual path values. All smoothness
and recursive identities used by the induction come from the actual charts. -/
theorem n07b_sourcePrimitive_value_le
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hK : N04PartA D S C K base ε) (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m b : ℕ) {y : PolarPoint}
    (hy : y ∈ n07bSourceMaterialPiece T K z m) {R : ℝ} (hR : 1 ≤ R)
    (hjets : N07bSourcePrimitiveJetBound T K z m b R y)
    {j : ℕ} (hj : j ≤ b) (i : n07bAngularChainIndex j) :
    |n07bMaterialNormalizedSourceCoefficient T K z m (3 / 4 : ℝ) j i y| ≤
      n07bSourceChainJetConstant b ^ b * R ^ (b + 1) := by
  obtain ⟨hv₁, hv₂, hq⟩ := n07b_materialSourceFields_contDiffOn hD hT hK hz hs m
  exact n07b_threeBranch_value_le (n07bSourceMaterialPiece_isOpen hT hK hz hs m)
    (n07bMaterialNormalizedSourceCoefficient_contDiffOn hD hT hK hz hs m (3 / 4 : ℝ))
    hv₁ hv₂ hq
    (fun j i y hy => n07bMaterialNormalizedSourceCoefficient_stay hD hT hK hz hs m (3 / 4 : ℝ) j i hy)
    (fun j i y _ => n07bMaterialNormalizedSourceCoefficient_radial T K z m (3 / 4 : ℝ) j i y)
    (fun j i y _ => n07bMaterialNormalizedSourceCoefficient_angular T K z m (3 / 4 : ℝ) j i y)
    hy b hR hjets.1 hjets.2.1 hjets.2.2.1 hjets.2.2.2 hj i

/-- The prescribed material chart returns the original actual normalized
coefficient on the physical core. -/
theorem n07bMaterialNormalizedSourceCoefficient_materialChart
    (hT : IsMaterialData D T) (K : CanonicalData S) (z : AnnularState S × ℝ)
    (m : ℕ) (β : ℝ) (j : ℕ) (i : n07bAngularChainIndex j)
    {x : PolarPoint} (hx : x.1 ∈ Ioo D.a D.b) :
    n07bMaterialNormalizedSourceCoefficient T K z m β j i (n07bMaterialChart T x) =
      n07bNormalizedSourceCoefficient T K z m β j i x := by
  change n07bNormalizedSourceCoefficient T K z m β j i
    (n07bMaterialRadiusChart T (n07bMaterialChart T x)) = _
  rw [n07bMaterialRadiusChart_materialChart hT hx]

/-- The source-energy multiplier is exactly the square normalization,
including the actual sampled height in the chosen volume model. -/
theorem n07bNormalizedSourceCoefficient_sq_eq_weight
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hK : N04PartA D S C K base ε) (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m j : ℕ) (i : n07bAngularChainIndex j)
    {x : PolarPoint} (hx : x ∈ physicalPieceOpen S K z m) :
    n07bNormalizedSourceCoefficient T K z m (3 / 4 : ℝ) j i x ^ 2 =
      n07bSourceGeometricWeight T K z m x *
        n07bAngularChainCoefficient T K z m (3 / 4 : ℝ) j i x ^ 2 := by
  have hxcore : x.1 ∈ Ioo D.a D.b := ((hK.domains z hz hs m).2.2.1 hx).1
  have hm : 0 < T.H (T.sample (K.cell m)) := by
    simpa only [n07bCanonicalSourceFactor, neg_zero, Real.rpow_zero,
      Real.rpow_one, one_mul] using
        (n07bCanonicalSourceFactor_pos_of_material (K := K) hD hT 1 0 m)
  have hW := n07bSourceNormalizer_eq_product T K z m (3 / 4 : ℝ) x
    (hT.2.1 x.1 hxcore).2.1 hm
  have hsq : Real.sqrt (T.ell x.1 * |planeJacobian (K.chart z m) x|) ^ 2 =
      T.ell x.1 * |planeJacobian (K.chart z m) x| := by
    apply Real.sq_sqrt
    change 0 ≤ n07bSourceMaterialJacobian T K z m x
    exact (n07bSourceMaterialJacobian_pos hT hK hz hs m hx).le
  simp only [n07bNormalizedSourceCoefficient, hW, mul_pow,
    n07bSourceGeometricWeight, n07bCanonicalSourceFactor, neg_zero,
    Real.rpow_zero, one_mul, n07bSourceMaterialJacobian, canonicalMaterialJacobian]
  rw [hsq]
  ring

/-- This is the actual weighted path estimate obtained from the four
primitive fields, rather than an assumed estimate on the path itself. -/
theorem n07b_sourcePrimitive_weighted_square_le
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hK : N04PartA D S C K base ε) (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m b : ℕ) {x : PolarPoint}
    (hx : x ∈ physicalPieceOpen S K z m) {R : ℝ} (hR : 1 ≤ R)
    (hjets : N07bSourcePrimitiveJetBound T K z m b R (n07bMaterialChart T x))
    {j : ℕ} (hj : j ≤ b) (i : n07bAngularChainIndex j) :
    n07bSourceGeometricWeight T K z m x *
        n07bAngularChainCoefficient T K z m (3 / 4 : ℝ) j i x ^ 2 ≤
      (n07bSourceChainJetConstant b ^ b * R ^ (b + 1)) ^ 2 := by
  have hxcore : x.1 ∈ Ioo D.a D.b := ((hK.domains z hz hs m).2.2.1 hx).1
  have hy : n07bMaterialChart T x ∈ n07bSourceMaterialPiece T K z m := by
    change n07bMaterialRadiusChart T (n07bMaterialChart T x) ∈ physicalPieceOpen S K z m
    rw [n07bMaterialRadiusChart_materialChart hT hxcore]
    exact hx
  have hv := n07b_sourcePrimitive_value_le hD hT hK hz hs m b hy hR hjets hj i
  rw [n07bMaterialNormalizedSourceCoefficient_materialChart hT K z m (3 / 4 : ℝ) j i hxcore] at hv
  have hsquare := pow_le_pow_left₀ (abs_nonneg _) hv 2
  rw [sq_abs, n07bNormalizedSourceCoefficient_sq_eq_weight hD hT hK hz hs m j i hx] at hsquare
  exact hsquare

end ContinuousFlexibility.Analysis
