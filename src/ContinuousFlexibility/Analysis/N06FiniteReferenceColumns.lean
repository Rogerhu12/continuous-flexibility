import ContinuousFlexibility.Analysis.N06FiniteSourceGeometry
import ContinuousFlexibility.Analysis.N06ReferenceRemainderFields
import ContinuousFlexibility.Analysis.N06ReferenceNuColumn
import ContinuousFlexibility.Analysis.MaterialHeightRegularity
import ContinuousFlexibility.Radial.ReferenceColumnSmooth

/-!
# The three actual reference columns have one compact physical support

The left-tail column uses the space model's own cutoff, the nu column is
the actual reference border, and the compatibility column is the decoded
psi. Their common compact radial support is proved from the original
cutoff and physical-space hypotheses. A finite set of intersecting atlas
pieces and finite angular jet bounds then produce all three actual source
elements through the finite local source construction.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open ContinuousFlexibility.Blueprint
open scoped ContDiff Topology BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

/-- The left-tail column is the derivative of the actual radial flux. -/
theorem n06_referenceLeftColumn_formula (D : ReferenceData) (χ : ℝ → ℝ)
    (p : PolarPoint) :
    n06ReferenceTestOperator D (n06ReferenceLeftField χ) p =
      deriv (fun r => D.w r * deriv χ r) p.1 := by
  simp only [n06ReferenceTestOperator, n06ReferenceLeftField, radialPDE,
    deriv_const', deriv_const, mul_zero, add_zero]

theorem n06_referenceLeftColumn_contDiff
    {D : ReferenceData} (hgeom : RadialProfileGeometry D)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (n06ReferenceTestOperator D (n06ReferenceLeftField χ)) := by
  have heq : n06ReferenceTestOperator D (n06ReferenceLeftField χ) =
      fun p => deriv (fun r => D.w r * deriv χ r) p.1 :=
    funext (n06_referenceLeftColumn_formula D χ)
  rw [heq]
  exact ((contDiff_infty_iff_deriv.mp
    (hgeom.2.2.1.1.mul (contDiff_infty_iff_deriv.mp hχ).2)).2).comp contDiff_fst

theorem n06_referenceLeftColumn_radialSupport
    {D : ReferenceData} {χ : ℝ → ℝ} (hχ : CutoffConditions D χ) :
    HasCompactRadialSupport D (n06ReferenceTestOperator D (n06ReferenceLeftField χ)) := by
  obtain ⟨J, hJ, hJD, _, hzero⟩ := hχ.2.2
  refine ⟨J, hJ, hJD, ?_⟩
  intro r hr θ
  have heq : (fun t => D.w t * deriv χ t) =ᶠ[𝓝 r] (fun _ => (0 : ℝ)) := by
    filter_upwards [hJ.isClosed.isOpen_compl.mem_nhds hr] with t ht
    rw [hzero t ht, mul_zero]
  rw [n06_referenceLeftColumn_formula, heq.deriv_eq, deriv_const]

theorem n06_referenceNuField_contDiff
    {D : ReferenceData} (hgeom : RadialProfileGeometry D) (hb : RadialTrueBorder D) :
    ContDiff ℝ ∞ (n06ReferenceNuField D) := by
  have hcos : ContDiff ℝ ∞ (cosineMode 2) := by
    unfold cosineMode
    exact contDiff_const.mul (contDiff_const.mul contDiff_id).cos
  exact ((referenceColumn_contDiff hgeom hb).comp contDiff_fst).mul
    (hcos.comp contDiff_snd)

theorem n06_referenceNuField_radialSupport
    {D : ReferenceData} (hb : RadialTrueBorder D) :
    HasCompactRadialSupport D (n06ReferenceNuField D) := by
  refine ⟨tsupport D.chi, hb.2.1, fun r hr => (hb.2.2.1 hr).1, ?_⟩
  intro r hr θ
  have hz : referenceColumn D r = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hr (referenceColumn_tsupport_subset h))
  simp only [n06ReferenceNuField, hz, zero_mul]

/-- The order agrees with the three scalar coordinates of the actual
N05 unknown: left tail, nu, and compatibility. -/
def n06ReferenceScalarField (D : ReferenceData) (S : PhysicalSpacesData) :
    Fin 3 → PolarPoint → ℝ :=
  ![n06ReferenceTestOperator D (n06ReferenceLeftField S.chiLeft),
    n06ReferenceNuField D, (S.height (3 / 4 : ℝ)).decode S.psi]

theorem n06_referenceScalarField_contDiff
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hb : RadialTrueBorder D) (i : Fin 3) :
    ContDiff ℝ ∞ (n06ReferenceScalarField D S i) := by
  fin_cases i
  · exact n06_referenceLeftColumn_contDiff hD.choose_spec.1 hS.2.2.1.1
  · exact n06_referenceNuField_contDiff hD.choose_spec.1 hb
  · exact (physical_height_contDiff_and_flatJets hT hS
      (by norm_num : (0 : ℝ) < 3 / 4) S.psi).1

theorem n06_referenceScalarField_periodic
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (i : Fin 3) :
    Function.Periodic (n06ReferenceScalarField D S i) (0, Real.pi) := by
  fin_cases i
  · intro p
    change n06ReferenceTestOperator D (n06ReferenceLeftField S.chiLeft) (p + (0, Real.pi)) =
      n06ReferenceTestOperator D (n06ReferenceLeftField S.chiLeft) p
    simp only [n06_referenceLeftColumn_formula, Prod.fst_add, add_zero]
  · exact n06_referenceNuField_periodic D
  · exact ((hS.1 (3 / 4 : ℝ)).2.2.2.1 S.psi).2.2.1

theorem n06_referenceScalarField_even
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (i : Fin 3) (p : PolarPoint) :
    n06ReferenceScalarField D S i (p.1, -p.2) = n06ReferenceScalarField D S i p := by
  fin_cases i
  · change n06ReferenceTestOperator D (n06ReferenceLeftField S.chiLeft) (p.1, -p.2) =
      n06ReferenceTestOperator D (n06ReferenceLeftField S.chiLeft) p
    simp only [n06_referenceLeftColumn_formula]
  · change n06ReferenceNuField D (p.1, -p.2) = n06ReferenceNuField D p
    exact congrArg (fun x : ℝ => referenceColumn D p.1 * x) (cosineMode_even 2 p.2)
  · exact ((hS.1 (3 / 4 : ℝ)).2.2.2.1 S.psi).2.1 p.1 p.2

/-- All three original scalar fields have one compact radial support in
the core. No finiteness property of the canonical atlas is used here. -/
theorem n06_referenceScalarFields_commonSupport
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (hb : RadialTrueBorder D) :
    ∃ J : Set ℝ, IsCompact J ∧ J ⊆ radialCore D ∧
      ∀ i : Fin 3, ∀ r, r ∉ J → ∀ θ, n06ReferenceScalarField D S i (r, θ) = 0 := by
  obtain ⟨Jχ, hJχ, hχD, hχzero⟩ := n06_referenceLeftColumn_radialSupport hS.2.2.1
  obtain ⟨Jν, hJν, hνD, hνzero⟩ := n06_referenceNuField_radialSupport hb
  obtain ⟨Jψ, hJψ, hψD, hψzero⟩ := hS.2.2.2.2.2.2.2.2.1
  refine ⟨(Jχ ∪ Jν) ∪ Jψ, (hJχ.union hJν).union hJψ, ?_, ?_⟩
  · intro r hr
    rcases hr with (hr | hr) | hr
    · exact hχD hr
    · exact hνD hr
    · exact hψD hr
  · intro i r hr θ
    have hrχ : r ∉ Jχ := fun h => hr (Or.inl (Or.inl h))
    have hrν : r ∉ Jν := fun h => hr (Or.inl (Or.inr h))
    have hrψ : r ∉ Jψ := fun h => hr (Or.inr h)
    fin_cases i
    · exact hχzero r hrχ θ
    · exact hνzero r hrν θ
    · exact hψzero r hrψ θ

/-- The middle field is the actual nu derivative on the physical annulus. -/
theorem n06_referenceScalarField_nu_actual
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hD : IsAccumulatingProfile D) (hb : RadialTrueBorder D)
    (href : referenceStateConditions D S C) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    n06ReferenceScalarField D S 1 p = nuColumnField D S C (C.referenceState, 0) p := by
  have hgeom : RadialProfileGeometry D := hD.choose_spec.1
  exact (n06_nuColumn_reference hgeom.2.2.1.1 hb.1 hgeom.2.2.2.1.1 href
    (hgeom.1.trans hp.1.1).ne').symm

/-- Once the common compact support meets finitely many actual pieces,
finite angular bounds construct the three original source columns in the
same selected volume model. The atlas-finiteness input is explicit. -/
theorem n06Volume_referenceScalarColumns
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S} {V : VolumeModelData S K}
    {base : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hb : RadialTrueBorder D)
    (hV : IsVolumeModel T S K V) (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (γ t : ℝ) (b : ℕ) :
    ∃ J : Set ℝ, IsCompact J ∧ J ⊆ radialCore D ∧
      ∀ hfinite : Set.Finite {m : ℕ |
        (physicalPieceOpen S K z m ∩ (J ×ˢ (univ : Set ℝ))).Nonempty},
      ∀ δ : ℝ, 0 ≤ δ →
      (∀ i : Fin 3, ∀ m ∈ hfinite.toFinset, ∀ j, j ≤ b →
        ∀ p ∈ canonicalOpen S K m,
          |mixedDerivative 0 j (canonicalSource S K z m (n06ReferenceScalarField D S i)) p| ≤ δ) →
      ∃ F : Fin 3 → V.level γ t b,
        (∀ i m, (V.forget γ t b (F i) m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
          canonicalSource S K z m (n06ReferenceScalarField D S i)) ∧
        ∀ i, ‖F i‖ ≤ (n06WeakAngularMultiplierCost b *
          n06FiniteSourceCost T S K γ t b hfinite.toFinset) * δ := by
  obtain ⟨J, hJ, hJD, hzero⟩ := n06_referenceScalarFields_commonSupport hS hb
  refine ⟨J, hJ, hJD, ?_⟩
  intro hfinite δ hδ hbound
  choose F hF hnorm using fun i : Fin 3 =>
    n06Volume_exists_finite_canonical_source hD hT hV hK hz hs γ t b hfinite
      (n06_referenceScalarField_contDiff hD hT hS hb i).contDiffOn
      (fun p _ => n06_referenceScalarField_periodic hS i p)
      (fun p _ => n06_referenceScalarField_even hS i p) (hzero i) hδ (hbound i)
  exact ⟨F, hF, hnorm⟩

end ContinuousFlexibility.Statements
