import ContinuousFlexibility.Analysis.N04bReferenceActualDomains
import ContinuousFlexibility.Analysis.N04bNegativePairDomains
import ContinuousFlexibility.Analysis.N04bNormalizationRegion

/-!
# Actual typed domains, normalization and planar partition

The genuine travel chart supplies every current negative-domain field and
the null moving cuts. Positive subdivisions retain their fixed radial
domains. One arbitrary equivalence transfers the actual typed partition to
the natural-number indices of the final atlas.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Negative domains miss the normalization region for every travel
function. Positive domains are literally unchanged. -/
theorem n04b_typed_normalization_inter
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hC : controlGeometryConditions D S C)
    (Γ₁ Γ₂ : ℕ → PolarPoint → PolarPoint) (i : N04PieceIndex D) :
    n04bTypedPhysicalDomain C Γ₁ i ∩ (n04bNormalizationRegion D ×ˢ univ) =
      n04bTypedPhysicalDomain C Γ₂ i ∩ (n04bNormalizationRegion D ×ˢ univ) := by
  cases i with
  | inl i =>
    have h₁ : ∀ p ∈ n04bTypedPhysicalDomain C Γ₁ (.inl i), deriv D.w p.1 < 0 :=
      fun p hp => n04b_typed_domain_negative hC (.inl i) rfl hp
    have h₂ : ∀ p ∈ n04bTypedPhysicalDomain C Γ₂ (.inl i), deriv D.w p.1 < 0 :=
      fun p hp => n04b_typed_domain_negative hC (.inl i) rfl hp
    exact (n04b_negative_domain_normalization_inter h₁).trans
      (n04b_negative_domain_normalization_inter h₂).symm
  | inr i => rfl

/-- All current domain fields are consequences of the raw corrected field
and the actual travel construction. -/
theorem n04b_actual_typed_domain_fields
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (i : N04PieceIndex D) :
    let Ω := n04bTypedPhysicalDomain C (n04bActualTravelChart S C L z) i
    IsOpen Ω ∧ Ω.Nonempty ∧ Ω ⊆ annularOpen D ∧
      (∀ p : PolarPoint, p + (0, Real.pi) ∈ Ω ↔ p ∈ Ω) ∧
      (∀ p : PolarPoint, (p.1, -p.2) ∈ Ω ↔ p ∈ Ω) ∧
      (n04TypedPiecePositive i = true →
        Ω = n04bTypedPhysicalDomain C
          (n04bActualTravelChart S C L (C.referenceState, 0)) i) ∧
      (∀ p ∈ Ω, n04TypedPiecePositive i = true → 0 < deriv D.w p.1) ∧
      (∀ p ∈ Ω, n04TypedPiecePositive i = false → deriv D.w p.1 < 0) := by
  have hC : controlGeometryConditions D S C := h03.1.1.2.2.2.1
  obtain ⟨_, hdata⟩ := h03.1.1.1.1
  have hD : RadialProfileGeometry D := hdata.1
  have hf : Continuous (deriv D.w) := hD.2.2.1.1.continuous_deriv (by simp)
  cases i with
  | inl i =>
    have hF := n04b_actualTravelChart_bijOn h03 hS hT hfield hz hs i.1
    have hperiod :
        ∀ p ∈ Ioo (C.left i.1) (C.right i.1) ×ˢ (univ : Set ℝ),
          n04bActualTravelChart S C L z i.1 (p + (0, Real.pi)) =
            n04bActualTravelChart S C L z i.1 p + (0, Real.pi) := by
      rintro ⟨r, θ⟩ hp
      simpa only [Prod.mk_add_mk, add_zero] using
        n04b_actualTravelChart_period_add h03 hS hT hfield hz hs i.1
          ⟨hp.1.1.le, hp.1.2.le⟩ θ
    have hg := n04b_negativeHalfDomain_properties
      (n04b_actualTravel_positive h03 hS hT hfield hz hs i.1)
      hF (n04b_actualTravelChart_smooth h03 hS hT hfield hz hs i.1).continuousOn
      hperiod (fun p _ => n04b_actualTravelChart_reflection i.1 p) i.2
    refine ⟨hg.1, hg.2.1, ?_, hg.2.2.2.1, hg.2.2.2.2, ?_, ?_, ?_⟩
    · intro p hp
      have hr := (hg.2.2.1 hp).1
      exact ⟨⟨(hC.1 i.1).1.trans hr.1, hr.2.trans (hC.1 i.1).2.2⟩, mem_univ _⟩
    · intro hpos
      simp only [n04TypedPiecePositive, Bool.false_eq_true] at hpos
    · intro p hp hpos
      simp only [n04TypedPiecePositive, Bool.false_eq_true] at hpos
    · intro p hp _
      exact n04b_typed_domain_negative hC (.inl i) rfl hp
  | inr i =>
    have hb := n04_typed_piece_bounds hf hC (.inr i)
    let l := n04TypedPieceLeft C (.inr i)
    let r := n04TypedPieceRight C (.inr i)
    refine ⟨isOpen_Ioo.prod isOpen_univ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨((l + r) / 2, 0), ?_, mem_univ _⟩
      change l < (l + r) / 2 ∧ (l + r) / 2 < r
      have hlr : l < r := hb.2.1
      constructor <;> linarith
    · intro p hp
      exact ⟨⟨hb.1.trans hp.1.1, hp.1.2.trans hb.2.2⟩, mem_univ _⟩
    · intro p
      simp only [n04bTypedPhysicalDomain, mem_prod, Prod.fst_add, add_zero, mem_univ,
        and_true]
    · intro p
      rfl
    · intro _
      rfl
    · intro p hp _
      exact n04b_typed_domain_positive hf (.inr i) rfl hp
    · intro p hp hneg
      simp only [n04TypedPiecePositive, Bool.true_eq_false] at hneg

/-- The actual moving cuts, rather than any reference radial substitute,
give the planar null exceptional set of the current typed atlas. -/
theorem n04b_actual_typed_domain_partition
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) :
    ∃ E : Set PolarPoint, volume E = 0 ∧
      ∀ p ∈ annularOpen D \ E, ∃! i : N04PieceIndex D,
        p ∈ n04bTypedPhysicalDomain C (n04bActualTravelChart S C L z) i := by
  have hC : controlGeometryConditions D S C := h03.1.1.2.2.2.1
  obtain ⟨_, hdata⟩ := h03.1.1.1.1
  apply n04b_current_planar_partition hdata.1 hC
    (G := n04bActualTravelInverse S C L z)
  · exact n04b_actualTravel_positive h03 hS hT hfield hz hs
  · exact n04b_actualTravelChart_bijOn h03 hS hT hfield hz hs
  · intro m
    exact (n04b_actualTravelInverse_spec h03 hS hT hfield hz hs m).1
  · intro m q hq
    exact (n04b_actualTravelInverse_spec h03 hS hT hfield hz hs m).2.2.1 hq
  · intro m
    exact (n04b_actualTravelInverse_spec h03 hS hT hfield hz hs m).2.2.2

/-- The same equivalence used for the reference metadata enumerates the
actual state-dependent partition, with uniqueness preserved. -/
theorem n04b_actual_enumerated_domain_partition
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (e : ℕ ≃ N04PieceIndex D) :
    ∃ E : Set PolarPoint, volume E = 0 ∧
      ∀ p ∈ annularOpen D \ E, ∃! m : ℕ,
        p ∈ n04bTypedPhysicalDomain C (n04bActualTravelChart S C L z) (e m) := by
  obtain ⟨E, hE, hcover⟩ := n04b_actual_typed_domain_partition hT hS h03 hfield hz hs
  refine ⟨E, hE, ?_⟩
  intro p hp
  obtain ⟨i, hi, hu⟩ := hcover p hp
  refine ⟨e.symm i, ?_, ?_⟩
  · simpa only [Equiv.apply_symm_apply] using hi
  · intro n hn
    apply e.injective
    simpa only [Equiv.apply_symm_apply] using hu (e n) hn

end ContinuousFlexibility.Analysis
