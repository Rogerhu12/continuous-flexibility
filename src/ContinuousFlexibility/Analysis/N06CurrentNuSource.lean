import ContinuousFlexibility.Analysis.N06ReferenceChartNuSource
import ContinuousFlexibility.Analysis.N06FiniteSourceNormalization
import ContinuousFlexibility.Analysis.N06ScalarColumns

/-!
# The current nu source for a chart fixed on the actual cutoff support

The extra premise in this file is an explicit primitive geometric choice:
the selected normalization region contains tsupport chi. It is not an
output of N04 for an arbitrary witness. Under that choice, the previously
constructed reference-chart source is exactly the actual current nu
column difference. The existing N05 inverse supplies its actual mu scalar
and gives a bounded endomorphism of the same source space.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {base loss : ℕ} {ε : ℝ}

theorem n06_currentNuSourceDifference_eq_referenceChart
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hfixed : tsupport D.chi ⊆ K.normalizationRegion)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m) :
    canonicalSource S K z m (nuColumnField D S C z) p -
        canonicalSource S K (C.referenceState, 0) m
          (nuColumnField D S C (C.referenceState, 0)) p =
      canonicalSource S K (C.referenceState, 0) m
        (fun q => nuColumnField D S C z q - nuColumnField D S C (C.referenceState, 0) q) p := by
  have hsupport : ∀ q, nuColumnField D S C z q ≠ 0 → q.1 ∈ K.normalizationRegion := by
    intro q hq
    apply hfixed
    by_contra hnot
    exact hq (n06_nuColumn_zero_off_tsupport hT hS h01 z hnot)
  have hcurrent := n06_canonicalSource_normalization_fixed h04
    (n05_referenceState_mem h01.2.1) (n05_referenceState_sector h01.2.2.1)
    hz hs hsupport m hp
  rw [hcurrent]
  simp only [canonicalSource, div_eq_mul_inv]
  ring

set_option backward.isDefEq.respectTransparency true

private theorem n06_referenceChartNuDifference_ae_current
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hfixed : tsupport D.chi ⊆ K.normalizationRegion)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) :
    canonicalSource S K (C.referenceState, 0) m
      (fun p => nuColumnField D S C z p - nuColumnField D S C (C.referenceState, 0) p)
      =ᵐ[canonicalMeasure S K m]
    fun p => canonicalSource S K z m (nuColumnField D S C z) p -
      canonicalSource S K (C.referenceState, 0) m
        (nuColumnField D S C (C.referenceState, 0)) p := by
  have hmem : ∀ᵐ p ∂canonicalMeasure S K m,
      p ∈ Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi :=
    ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)
  filter_upwards [hmem] with p hp
  exact (n06_currentNuSourceDifference_eq_referenceChart hT hS h01 h04
    hfixed hz hs m (p := p) ⟨hp.1, mem_univ _⟩).symm

private theorem n06_source_family_ae_transport
    {Z E α : Type*} [Norm E] [MeasurableSpace α]
    (μ : ℕ → Measure α) (decode : E → ℕ → α → ℝ)
    (f g : Z → ℕ → α → ℝ) (size : Z → ℝ) (Ad₁ Ad₂ : Z → Prop)
    (hidentity : ∀ z, Ad₁ z → Ad₂ z → ∀ m, f z m =ᵐ[μ m] g z m)
    (hsource : ∃ Q : ℝ, 0 ≤ Q ∧ ∀ z, Ad₁ z → Ad₂ z → size z ≤ 1 →
      ∃ F : E, (∀ m, decode F m =ᵐ[μ m] f z m) ∧ ‖F‖ ≤ Q * size z) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ z, Ad₁ z → Ad₂ z → size z ≤ 1 →
      ∃ F : E, (∀ m, decode F m =ᵐ[μ m] g z m) ∧ ‖F‖ ≤ Q * size z := by
  obtain ⟨Q, hQ, hconstruct⟩ := hsource
  refine ⟨Q, hQ, ?_⟩
  intro z hz₁ hz₂ hsmall
  obtain ⟨F, hF, hFnorm⟩ := hconstruct z hz₁ hz₂ hsmall
  exact ⟨F, fun m => (hF m).trans (hidentity z hz₁ hz₂ m), hFnorm⟩

def N06CurrentNuDifferenceBound
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (K : CanonicalData S) (V : VolumeModelData S K) (base : ℕ) (ε γ t : ℝ)
    (b : ℕ) (Q : ℝ) : Prop :=
  ∀ z : AnnularState S × ℝ,
    z ∈ stateNeighborhood S C base ε → stateSector S z.1 →
    stateGrading S (b + 4) (z.1 - C.referenceState) + |z.2| ≤ 1 →
    ∃ F : V.level γ t b,
      (∀ m, (V.forget γ t b F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        fun p => canonicalSource S K z m (nuColumnField D S C z) p -
          canonicalSource S K (C.referenceState, 0) m
            (nuColumnField D S C (C.referenceState, 0)) p) ∧
      ‖F‖ ≤ Q * (stateGrading S (b + 4) (z.1 - C.referenceState) + |z.2|)

/-- The same small source element now has the genuine current-minus-
reference source representative. The additional fixed-support geometry
remains a visible input. -/
theorem n06Volume_exists_currentNuDifference_of_fixed_support
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hV : IsVolumeModel T S K V)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (hfixed : tsupport D.chi ⊆ K.normalizationRegion) (γ t : ℝ) (b : ℕ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ N06CurrentNuDifferenceBound D S C K V base ε γ t b Q := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1
  have h04 : N04Properties D T S C L K base loss ε := h.2.2.2.2.1
  have hreference : ∃ Q : ℝ, 0 ≤ Q ∧
      N06ReferenceChartNuDifferenceBound D S C K V base ε γ t b Q :=
    n06Volume_exists_referenceChart_nuDifference hT hS hV h hcoordinates γ t b
  exact n06_source_family_ae_transport
    (Z := AnnularState S × ℝ) (E := V.level γ t b) (α := PolarPoint)
    (canonicalMeasure S K)
    (fun F m => (V.forget γ t b F m : PolarPoint → ℝ))
    (fun z m => canonicalSource S K (C.referenceState, 0) m
      (fun p => nuColumnField D S C z p - nuColumnField D S C (C.referenceState, 0) p))
    (fun z m p => canonicalSource S K z m (nuColumnField D S C z) p -
      canonicalSource S K (C.referenceState, 0) m
        (nuColumnField D S C (C.referenceState, 0)) p)
    (fun z => stateGrading S (b + 4) (z.1 - C.referenceState) + |z.2|)
    (fun z => z ∈ stateNeighborhood S C base ε) (fun z => stateSector S z.1)
    (fun z hz hs m => n06_referenceChartNuDifference_ae_current
      hT hS h01 h04 hfixed (z := z) hz hs m)
    hreference

set_option backward.isDefEq.respectTransparency false

section ScalarColumn

variable {b : ℕ}

private theorem n06_middleScalarColumn_apply (B : CanonicalDomainData S K V b)
    (N X : V.level (3 / 4 : ℝ) 0 b) :
    n06ScalarColumnOperator B 0 N 0 X = (B.inverse X).val.1.2.2.1 • N := by
  simpa only [smul_zero, zero_add, add_zero] using
    n06ScalarColumnOperator_apply B 0 N 0 X

private theorem n06_middleScalarColumn_norm (B : CanonicalDomainData S K V b)
    (N : V.level (3 / 4 : ℝ) 0 b) :
    ‖n06ScalarColumnOperator B 0 N 0‖ ≤ ‖N‖ * ‖n06InverseScalars B‖ := by
  simpa only [norm_zero, zero_add, add_zero] using norm_n06ScalarColumnOperator_le B 0 N 0

private theorem n06_middleScalarColumn_forget (B : CanonicalDomainData S K V b)
    (N X : V.level (3 / 4 : ℝ) 0 b) (m : ℕ) :
    (V.forget (3 / 4 : ℝ) 0 b (n06ScalarColumnOperator B 0 N 0 X) m : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m]
        fun p => (B.inverse X).val.1.2.2.1 * V.forget (3 / 4 : ℝ) 0 b N m p := by
  let μ : ℝ := (B.inverse X).val.1.2.2.1
  have he : V.forget (3 / 4 : ℝ) 0 b (n06ScalarColumnOperator B 0 N 0 X) m =
      μ • V.forget (3 / 4 : ℝ) 0 b N m := by
    have h := congrArg (fun Y : V.level (3 / 4 : ℝ) 0 b =>
      V.forget (3 / 4 : ℝ) 0 b Y m) (n06_middleScalarColumn_apply B N X)
    exact h.trans (congrFun ((V.forget (3 / 4 : ℝ) 0 b).map_smul μ N) m)
  filter_upwards [Lp.coeFn_smul μ (V.forget (3 / 4 : ℝ) 0 b N m)] with p hp
  change (μ • V.forget (3 / 4 : ℝ) 0 b N m : CanonicalL2 S K m) p =
    μ * V.forget (3 / 4 : ℝ) 0 b N m p at hp
  exact (congrArg (fun Y : CanonicalL2 S K m => Y p) he).trans hp

set_option backward.isDefEq.respectTransparency true

private theorem n06_scalarColumn_family_norm_bound
    {Z E O α : Type*} [Norm E] [Norm O] [MeasurableSpace α]
    (μ : ℕ → Measure α) (decode : E → ℕ → α → ℝ)
    (decodeOut : O → E → ℕ → α → ℝ) (scalar : E → ℝ)
    (field : Z → ℕ → α → ℝ) (size : Z → ℝ) (Ad₁ Ad₂ : Z → Prop)
    (column : E → O) (M : ℝ) (hM : 0 ≤ M)
    (hnorm : ∀ N, ‖column N‖ ≤ ‖N‖ * M)
    (hfield : ∀ N X m, decodeOut (column N) X m =ᵐ[μ m]
      fun p => scalar X * decode N m p)
    (hsource : ∃ Q : ℝ, 0 ≤ Q ∧ ∀ z, Ad₁ z → Ad₂ z → size z ≤ 1 →
      ∃ N : E, (∀ m, decode N m =ᵐ[μ m] field z m) ∧ ‖N‖ ≤ Q * size z) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ z, Ad₁ z → Ad₂ z → size z ≤ 1 →
      ∃ P : O, ‖P‖ ≤ Q * size z ∧ ∀ X m,
        decodeOut P X m =ᵐ[μ m] fun p => scalar X * field z m p := by
  obtain ⟨Q, hQ, hconstruct⟩ := hsource
  refine ⟨Q * M, mul_nonneg hQ hM, ?_⟩
  intro z hz₁ hz₂ hsmall
  obtain ⟨N, hN, hNnorm⟩ := hconstruct z hz₁ hz₂ hsmall
  refine ⟨column N, ?_, ?_⟩
  · have hbound := (hnorm N).trans (mul_le_mul_of_nonneg_right hNnorm hM)
    exact hbound.trans_eq (by ring)
  · intro X m
    apply (hfield N X m).trans
    filter_upwards [hN m] with p hp
    exact congrArg (fun a : ℝ => scalar X * a) hp

def N06CurrentNuColumnOperatorBound
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (K : CanonicalData S) (V : VolumeModelData S K) (b : ℕ)
    (B : CanonicalDomainData S K V b) (base : ℕ) (ε Q : ℝ) : Prop :=
  ∀ z : AnnularState S × ℝ,
    z ∈ stateNeighborhood S C base ε → stateSector S z.1 →
    stateGrading S (b + 4) (z.1 - C.referenceState) + |z.2| ≤ 1 →
    ∃ P : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b,
      ‖P‖ ≤ Q * (stateGrading S (b + 4) (z.1 - C.referenceState) + |z.2|) ∧
      ∀ (X : V.level (3 / 4 : ℝ) 0 b) m,
        (V.forget (3 / 4 : ℝ) 0 b (P X) m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
          fun p => (B.inverse X).val.1.2.2.1 *
            (canonicalSource S K z m (nuColumnField D S C z) p -
              canonicalSource S K (C.referenceState, 0) m
                (nuColumnField D S C (C.referenceState, 0)) p)

/-- The selected N05 inverse, including its true mu coordinate, is kept
unchanged. Only the explicit primitive fixed-support geometry is added. -/
theorem n06N05_currentNuColumnOperator_of_fixed_support
    {B : CanonicalDomainData S K V b}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (hfixed : tsupport D.chi ⊆ K.normalizationRegion) :
    ∃ Q : ℝ, 0 ≤ Q ∧ N06CurrentNuColumnOperatorBound D S C K V b B base ε Q := by
  have hV : IsVolumeModel T S K V := h.2.2.1
  have hsource : ∃ Q : ℝ, 0 ≤ Q ∧
      N06CurrentNuDifferenceBound D S C K V base ε (3 / 4 : ℝ) 0 b Q :=
    n06Volume_exists_currentNuDifference_of_fixed_support
      hT hS hV h.1 hcoordinates hfixed (3 / 4 : ℝ) 0 b
  exact n06_scalarColumn_family_norm_bound
    (Z := AnnularState S × ℝ) (E := V.level (3 / 4 : ℝ) 0 b)
    (O := V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b) (α := PolarPoint)
    (canonicalMeasure S K)
    (fun F m => (V.forget (3 / 4 : ℝ) 0 b F m : PolarPoint → ℝ))
    (fun P X m => (V.forget (3 / 4 : ℝ) 0 b (P X) m : PolarPoint → ℝ))
    (fun X => (B.inverse X).val.1.2.2.1)
    (fun z m p => canonicalSource S K z m (nuColumnField D S C z) p -
      canonicalSource S K (C.referenceState, 0) m
        (nuColumnField D S C (C.referenceState, 0)) p)
    (fun z => stateGrading S (b + 4) (z.1 - C.referenceState) + |z.2|)
    (fun z => z ∈ stateNeighborhood S C base ε) (fun z => stateSector S z.1)
    (fun N => n06ScalarColumnOperator B 0 N 0)
    ‖n06InverseScalars B‖ (norm_nonneg (n06InverseScalars B))
    (n06_middleScalarColumn_norm B) (n06_middleScalarColumn_forget B) hsource

end ScalarColumn

end ContinuousFlexibility.Statements
