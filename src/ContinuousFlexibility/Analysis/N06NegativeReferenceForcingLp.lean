module

public import ContinuousFlexibility.Analysis.N06NegativeReferenceEquation
public import ContinuousFlexibility.Analysis.N06NegativeCurrentTestLp
public import ContinuousFlexibility.Analysis.MaterialHeightRegularity

/-!
# The actual negative reference equation has L2 principal forcing

The actual potential is measurable by applying the original operator
identity to the constant canonical test. Its order-zero N04 bound makes
multiplication preserve the original canonical L2 space. The three actual
reference columns are continuous on each physical closed tile, so their
source transforms are L2 there as well.

Subtracting this genuine potential contribution from the genuine N05
forcing gives the weak equation for the radial negative principal part.
The potential is not assumed smooth, periodic or radial.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology ENNReal

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

/-- Constant tests identify the actual negative potential with the
source transform of a measurable genuine physical divergence. -/
theorem n06_negativePotential_aestronglyMeasurable
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (hm : K.positive m = false) :
    AEStronglyMeasurable (K.potential z m) (canonicalMeasure S K m) := by
  obtain ⟨hA, hB⟩ := n06_N04_qualitative_parts h04
  let Φ := n06CanonicalTestPullback S K z m (fun _ => (1 : ℝ))
  let f := divergenceOperator (L.coefficients z) Φ
  have hf : AEStronglyMeasurable (canonicalSource S K z m f)
      (canonicalMeasure S K m) :=
    n06_current_canonicalSource_aestronglyMeasurable h04 hz hs m
      (n06_divergenceOperator_measurable (L.coefficients z) Φ)
  apply hf.congr
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
  have he := n06CanonicalTestPullback_source_divergence (L := L)
    (φ := fun _ => (1 : ℝ)) hA hB hz hs contDiff_const ⟨hp.1, mem_univ _⟩
  simpa only [hm, Bool.false_eq_true, ↓reduceIte, one_mul, mul_one,
    divergenceOperator_const, zero_add] using he

/-- The original order-zero potential bound acts on the original L2
field, without a replacement regularity hypothesis on the potential. -/
theorem n06_negativePotential_mul_memLp
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (hm : K.positive m = false)
    {U : PolarPoint → ℝ} (hU : MemLp U 2 (canonicalMeasure S K m)) :
    MemLp (fun p => K.potential z m p * U p) 2 (canonicalMeasure S K m) := by
  obtain ⟨Q, hQ, hbound⟩ := n06_actual_canonicalPotential_bounded h04 hz m
  apply (hU.const_mul Q).of_le
    ((n06_negativePotential_aestronglyMeasurable h04 hz hs m hm).mul hU.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
  simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg hQ]
  exact mul_le_mul_of_nonneg_right (hbound p ⟨hp.1, mem_univ _⟩) (abs_nonneg _)

/-- The original negative forcing is L2 on each actual canonical piece;
all three scalar columns are the literal physical fields. -/
theorem n06N05_negativeReferenceForcing_memLp
    {V : VolumeModelData S K} {b : ℕ} {B : CanonicalDomainData S K V b}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (u : B.Space) (m : ℕ) :
    MemLp (n06NegativeReferenceForcing D S C K u.val.1
      (V.forget (3 / 4 : ℝ) 0 b u.val.2) m) 2 (canonicalMeasure S K m) := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1.1
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2.1
  have hgeom : RadialProfileGeometry D := h01.1.1.choose_spec.1
  have hb : RadialTrueBorder D := h01.1.2.2.2.1
  have hz := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hs := n05_referenceState_sector h01.2.2.1
  have hχ : Continuous (n06ReferenceTestOperator D (n06ReferenceLeftField S.chiLeft)) :=
    r11b_continuous_radialPDE_test hgeom (n06_referenceLeftField_contDiff hS.2.2.1.1)
  have hν : Continuous (n06ReferenceNuField D) := n06_referenceNuField_continuous hgeom hb
  have hψ : Continuous ((S.height (3 / 4 : ℝ)).decode S.psi) :=
    (physical_height_contDiff_and_flatJets hT hS
      (by norm_num : (0 : ℝ) < 3 / 4) S.psi).1.continuous
  have hχLp := n06_current_canonicalSource_memLp h04 hz hs m hχ.continuousOn
  have hνLp := n06_current_canonicalSource_memLp h04 hz hs m hν.continuousOn
  have hψLp := n06_current_canonicalSource_memLp h04 hz hs m hψ.continuousOn
  unfold n06NegativeReferenceForcing
  exact (((Lp.memLp (V.forget (3 / 4 : ℝ) 0 b u.val.2 m)).sub
      (hχLp.const_mul u.val.1.2.1)).sub (hνLp.const_mul u.val.1.2.2.1)).sub
        (hψLp.const_mul u.val.1.2.2.2)

/-- Removing the literal reference potential leaves the forcing for
`d_yy - y d_theta_theta`. Its radial modal equation uses the opposite
forcing sign in the standard `-d_yy + j^2 c` convention. -/
def n06NegativePrincipalForcing (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (U : CanonicalUnknown S K) (F : CanonicalSequence S K) (m : ℕ) :
    PolarPoint → ℝ := fun p => n06NegativeReferenceForcing D S C K U F m p -
      K.potential (C.referenceState, 0) m p * U.1 m p

theorem n06N05_negativePrincipalForcing_memLp
    {V : VolumeModelData S K} {b : ℕ} {B : CanonicalDomainData S K V b}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (u : B.Space) (m : ℕ) (hm : K.positive m = false) :
    MemLp (n06NegativePrincipalForcing D S C K u.val.1
      (V.forget (3 / 4 : ℝ) 0 b u.val.2) m) 2 (canonicalMeasure S K m) := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1.1
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2.1
  have hz := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hs := n05_referenceState_sector h01.2.2.1
  exact (n06N05_negativeReferenceForcing_memLp hT hS h u m).sub
    (n06_negativePotential_mul_memLp h04 hz hs m hm (Lp.memLp (u.val.1.1 m)))

/-- The principal weak equation follows from the same N05 graph after
an integrable subtraction of the actual potential term. -/
theorem n06N05_negative_principal_pairing
    {V : VolumeModelData S K} {b : ℕ} {B : CanonicalDomainData S K V b}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (u : B.Space) (m : ℕ) (hm : K.positive m = false)
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) :
    (∫ p, u.val.1.1 m p * n06NegativePrincipalTest φ p ∂canonicalMeasure S K m) =
      ∫ p, n06NegativePrincipalForcing D S C K u.val.1
        (V.forget (3 / 4 : ℝ) 0 b u.val.2) m p * φ p ∂canonicalMeasure S K m := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1.1
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2.1
  have hz := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hs := n05_referenceState_sector h01.2.2.1
  let U : PolarPoint → ℝ := u.val.1.1 m
  let F := n06NegativeReferenceForcing D S C K u.val.1
    (V.forget (3 / 4 : ℝ) 0 b u.val.2) m
  let M := K.potential (C.referenceState, 0) m
  have hφLp : MemLp φ 2 (canonicalMeasure S K m) := hφ.n06_memLp
  have hPφ : Continuous (n06NegativePrincipalTest φ) :=
    (contDiff_cylinder_radialPartial (contDiff_cylinder_radialPartial hφ.1)).continuous.sub
      (continuous_fst.mul
        (contDiff_cylinder_angularPartial (contDiff_cylinder_angularPartial hφ.1)).continuous)
  have hI₀ : Integrable (fun p => U p * n06NegativePrincipalTest φ p)
      (canonicalMeasure S K m) :=
    (Lp.memLp (u.val.1.1 m)).integrable_mul (n06_memLp_canonical_of_continuous m hPφ)
  have hI₁ : Integrable (fun p => (M p * U p) * φ p) (canonicalMeasure S K m) :=
    (n06_negativePotential_mul_memLp h04 hz hs m hm (Lp.memLp (u.val.1.1 m))).integrable_mul hφLp
  have hIF : Integrable (fun p => F p * φ p) (canonicalMeasure S K m) :=
    (n06N05_negativeReferenceForcing_memLp hT hS h u m).integrable_mul hφLp
  have hleft : (∫ p, U p * (n06NegativePrincipalTest φ p + M p * φ p)
      ∂canonicalMeasure S K m) =
      (∫ p, U p * n06NegativePrincipalTest φ p ∂canonicalMeasure S K m) +
        ∫ p, (M p * U p) * φ p ∂canonicalMeasure S K m := by
    rw [← integral_add hI₀ hI₁]
    apply integral_congr_ae
    filter_upwards with p
    ring
  have hright : (∫ p, (F p - M p * U p) * φ p ∂canonicalMeasure S K m) =
      (∫ p, F p * φ p ∂canonicalMeasure S K m) -
        ∫ p, (M p * U p) * φ p ∂canonicalMeasure S K m := by
    rw [← integral_sub hIF hI₁]
    apply integral_congr_ae
    filter_upwards with p
    ring
  have he := n06N05_negative_principal_potential_pairing hT hS h u m hm hφ
  change (∫ p, U p * (n06NegativePrincipalTest φ p + M p * φ p)
    ∂canonicalMeasure S K m) = ∫ p, F p * φ p ∂canonicalMeasure S K m at he
  rw [hleft] at he
  change (∫ p, U p * n06NegativePrincipalTest φ p ∂canonicalMeasure S K m) =
    ∫ p, (F p - M p * U p) * φ p ∂canonicalMeasure S K m
  rw [hright]
  linarith only [he]

end ContinuousFlexibility.Analysis
