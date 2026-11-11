import ContinuousFlexibility.Analysis.N07bCanonicalHeightMembership
import ContinuousFlexibility.Analysis.N07bSourceBoundChangeVariables
import ContinuousFlexibility.Analysis.N07bMaterialAngularChain
import ContinuousFlexibility.Analysis.N07bMaterialJetEnergy
import ContinuousFlexibility.Analysis.N07bAtlasEnergy
import ContinuousFlexibility.Analysis.MaterialHeightRegularity

/-!
# Actual canonical height lifts from a geometric density bound

The geometric hypothesis is a pointwise comparison of the actual reciprocal
height density with a fixed material weight. It is independent of the
physical height. The normalized height's zeroth material jet then gives one
integrable density for the whole atlas, and the existing disjoint-atlas
summation theorem supplies genuine square summability.

This is a conditional analytic estimate. No such geometric comparison is
added to or inferred from the frozen canonical geometry conditions.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

/-- A source-independent bound on the actual canonical unknown density. -/
def N07bHeightDensityBound {S : PhysicalSpacesData}
    (T : MaterialData) (K : CanonicalData S) (z : AnnularState S × ℝ)
    (β γ t : ℝ) (c : ℕ) (A : ℝ) : Prop :=
  ∀ m x, x ∈ physicalPieceOpen S K m →
    (n07bCanonicalSourceFactor T K γ t m)⁻¹ ^ 2 *
        T.ell x.1 * |planeJacobian (K.chart z m) x| / K.height z m x ^ 2 *
          T.H x.1 ^ (2 * β) ≤ A * T.M x.1 ^ (2 * c)

/-- The geometric comparison acts on the genuine zeroth material jet. -/
theorem n07b_heightDensity_le_materialJetEnergy
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {K : CanonicalData S} {z : AnnularState S × ℝ}
    (hT : IsMaterialData D T) (β γ t : ℝ) (u : PolarPoint → ℝ)
    (c m : ℕ) {x : PolarPoint} (hx : x.1 ∈ Ioo D.a D.b) {A : ℝ}
    (hbound :
      (n07bCanonicalSourceFactor T K γ t m)⁻¹ ^ 2 *
          T.ell x.1 * |planeJacobian (K.chart z m) x| / K.height z m x ^ 2 *
            T.H x.1 ^ (2 * β) ≤ A * T.M x.1 ^ (2 * c)) :
    (n07bCanonicalSourceFactor T K γ t m)⁻¹ ^ 2 *
        (|planeJacobian (K.chart z m) x| / K.height z m x ^ 2 * u x ^ 2) ≤
      A * n07bMaterialJetEnergyDensity T β 0 0 c u x := by
  let v : ℝ := materialPullback T β u (n07bMaterialChart T x)
  have hell : 0 < T.ell x.1 := (hT.2.1 x.1 hx).1
  have hH : 0 < T.H x.1 := (hT.2.1 x.1 hx).2.1
  have hrestore : T.H x.1 ^ β * v = u x :=
    n07b_materialPullback_restore hT β u hx
  have hHpow : T.H x.1 ^ (2 * β) = (T.H x.1 ^ β) ^ 2 := by
    rw [show (2 : ℝ) * β = β * 2 by ring, Real.rpow_mul hH.le, Real.rpow_two]
  have hMpow : T.M x.1 ^ (2 * c) = (T.M x.1 ^ c) ^ 2 := by
    rw [Nat.mul_comm 2 c, pow_mul]
  rw [hHpow, hMpow] at hbound
  have hmul := mul_le_mul_of_nonneg_right hbound (sq_nonneg v)
  simp only [n07bMaterialJetEnergyDensity, mixedDerivative, iteratedDeriv_zero]
  change (n07bCanonicalSourceFactor T K γ t m)⁻¹ ^ 2 *
      (|planeJacobian (K.chart z m) x| / K.height z m x ^ 2 * u x ^ 2) ≤
    A * ((T.M x.1 ^ c * v) ^ 2 / T.ell x.1)
  calc
    _ ≤ (A * (T.M x.1 ^ c * v) ^ 2) / T.ell x.1 := by
      apply (le_div_iff₀ hell).mpr
      calc
        _ = ((n07bCanonicalSourceFactor T K γ t m)⁻¹ ^ 2 *
              T.ell x.1 * |planeJacobian (K.chart z m) x| / K.height z m x ^ 2 *
                (T.H x.1 ^ β) ^ 2) * v ^ 2 := by
          rw [← hrestore]
          ring
        _ ≤ (A * (T.M x.1 ^ c) ^ 2) * v ^ 2 := hmul
        _ = A * (T.M x.1 ^ c * v) ^ 2 := by ring
    _ = _ := by ring

section Atlas

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
  (hK : N04PartA D S C K base ε)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hs : stateSector S z.1)

include hK hz hs

/-- Local L² membership and actual change of variables give integrability
of the reciprocal physical height density on each prescribed piece. -/
theorem n07b_physicalHeightDensity_integrable (u : PolarPoint → ℝ)
    (hu : Continuous u) (m : ℕ) :
    IntegrableOn (fun p =>
      |planeJacobian (K.chart z m) p| / K.height z m p ^ 2 * u p ^ 2)
      (physicalPieceOpen S K m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi)) := by
  have hcharts := hK.2.2.2.2.2.2.2.1 z hz hs m
  have hcan := n07b_canonicalHeight_memLp hK hz hs m hu.continuousOn
  apply (n07b_sourceBound_square_integrable hK hz hs m hcan).congr
  filter_upwards [ae_restrict_mem
    ((measurableSet_Ioo.prod MeasurableSet.univ).inter
      (MeasurableSet.univ.prod measurableSet_Ioc))] with p hp
  change |planeJacobian (K.chart z m) p| *
      canonicalHeight S K z m u (K.chart z m p) ^ 2 =
    |planeJacobian (K.chart z m) p| / K.height z m p ^ 2 * u p ^ 2
  simp only [canonicalHeight, hcharts.2.2.1 p hp.1, div_pow]
  ring

/-- The actual weighted height-energy series is summable and bounded by
one original material seminorm. -/
theorem n07b_height_energy_summable_of_geometric_bound
    (hT : IsMaterialData D T) {β : ℝ} (hβ : 0 < β)
    {u : PolarPoint → ℝ} (hu : HeightMember D T β u)
    (γ t : ℝ) (c : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hbound : N07bHeightDensityBound T K z β γ t c A) :
    Summable (n07bPhysicalHeightEnergy (T := T) (K := K) γ t z u) ∧
      (∑' m, n07bPhysicalHeightEnergy (T := T) (K := K) γ t z u m) ≤
        A * physicalNorm T β c u ^ 2 := by
  have huc : Continuous u := (heightMember_contDiff_and_flatJets hT hβ hu).1.continuous
  let g : PolarPoint → ℝ := fun p => A * n07bMaterialJetEnergyDensity T β 0 0 c u p
  have hg : IntegrableOn g (Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi) :=
    (n07bMaterialJetEnergyDensity_integrable hT hu 0 0 c).const_mul A
  have hnonneg (m : ℕ) :
      0 ≤ n07bPhysicalHeightEnergy (T := T) (K := K) γ t z u m := by
    apply mul_nonneg (sq_nonneg _)
    exact integral_nonneg (fun p =>
      mul_nonneg (div_nonneg (abs_nonneg _) (sq_nonneg _)) (sq_nonneg _))
  have hpiece (m : ℕ) :
      n07bPhysicalHeightEnergy (T := T) (K := K) γ t z u m ≤
        ∫ p in physicalPieceOpen S K m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi), g p := by
    have hsub : physicalPieceOpen S K m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi) ⊆
        Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi :=
      fun p hp => ⟨(hK.2.2.2.1 m).2.2 hp.1.1, hp.2.2⟩
    change (n07bCanonicalSourceFactor T K γ t m)⁻¹ ^ 2 *
      (∫ p in physicalPieceOpen S K m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi),
        |planeJacobian (K.chart z m) p| / K.height z m p ^ 2 * u p ^ 2) ≤ _
    rw [← integral_const_mul]
    apply integral_mono_ae
      ((n07b_physicalHeightDensity_integrable hK hz hs u huc m).const_mul _)
      (hg.mono_set hsub)
    filter_upwards [ae_restrict_mem
      ((measurableSet_Ioo.prod MeasurableSet.univ).inter
        (MeasurableSet.univ.prod measurableSet_Ioc))] with p hp
    exact n07b_heightDensity_le_materialJetEnergy hT β γ t u c m
      ((hK.2.2.2.1 m).2.2 hp.1.1) (hbound m p hp.1)
  have hsum := n07b_summable_energy_of_piece_integral_bound hK hg hnonneg hpiece
  refine ⟨hsum.1, hsum.2.trans ?_⟩
  change (∫ p in Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi,
    A * n07bMaterialJetEnergyDensity T β 0 0 c u p) ≤ _
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left
    (n07bMaterialJetEnergyDensity_integral_le hT hu 0 0 c c (by simp)) hA

/-- The given geometry constructs an actual element of the already chosen
zeroth-order volume level, with the prescribed height representation. -/
theorem n07b_exists_canonicalHeightLevel_of_geometric_bound
    {V : VolumeModelData S K}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) {β : ℝ} (hβ : 0 < β)
    {u : PolarPoint → ℝ} (hu : HeightMember D T β u)
    (γ t : ℝ) (c : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hbound : N07bHeightDensityBound T K z β γ t c A) :
    ∃ W : V.level γ t 0, ∀ m,
      (V.forget γ t 0 W m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        canonicalHeight S K z m u := by
  have hsum := n07b_height_energy_summable_of_geometric_bound hK hz hs hT hβ hu γ t c hA hbound
  exact n07b_exists_canonicalHeightLevel hK hz hs hD hT hV γ t u
    (heightMember_contDiff_and_flatJets hT hβ hu).1.continuous
    hu.2.1 hu.2.2.1 hsum.1

/-- Positive target height gives a genuine unweighted Hilbert sequence as
well as membership in the prescribed weighted volume level. -/
theorem n07b_exists_canonicalHeightSequence_of_geometric_bound
    {V : VolumeModelData S K}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    {u : PolarPoint → ℝ} (hu : HeightMember D T β u)
    (t : ℝ) (c : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hbound : N07bHeightDensityBound T K z β γ t c A) :
    ∃ U : CanonicalL2Sequence S K,
      VolumeMember S K V γ t 0 (fun m => U m) ∧
      ∀ m, (U m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        canonicalHeight S K z m u := by
  obtain ⟨W, hW⟩ := n07b_exists_canonicalHeightLevel_of_geometric_bound
    hK hz hs hD hT hV hβ hu γ t c hA hbound
  refine ⟨n07bVolumeUnknownSequence hD hT hV hγ t 0 W, ?_, ?_⟩
  · exact ⟨W, rfl⟩
  · intro m
    exact hW m

end Atlas

end ContinuousFlexibility.Analysis
