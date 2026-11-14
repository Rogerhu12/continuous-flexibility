module

public import ContinuousFlexibility.Analysis.N01cCoefficientBaseSelection
public import ContinuousFlexibility.Analysis.N01cCoefficientTameBounds
public import ContinuousFlexibility.Analysis.SectorParameterGeometry
public import ContinuousFlexibility.Analysis.CanonicalFieldJetReduction
public import ContinuousFlexibility.Analysis.N07aNeighborhood
public import ContinuousFlexibility.Analysis.MixedDerivativeLocality

/-!
# Actual positive physical coefficients on one fixed sector neighborhood

The existing N01 mixed-power theorem supplies the original coefficient
jets. Its interpolation base is selected once, from the retained physical
spaces and primitive support data. The actual N03 positive-region germs
identify the same corrected coefficients, including every spatial jet.
The affine sector inclusion preserves the grading exactly.

The result retains the distributed spatial exponent and the full
positive-parameter height gain before any canonical composition.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

/-- Restrict the actual spatial domain and pull back through an isometric
grading inclusion. Tower uniqueness keeps every supplied output tower. -/
private theorem n04Realization_mixedPower_affine_domain
    {E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    {base loss : ℕ} {U : Set E} {V : Set F}
    {Ω Ω₀ : Set PolarPoint} {H W : PolarPoint → ℝ}
    {f : F → PolarPoint → ℝ} {g : E → PolarPoint → ℝ}
    (I : E →L[ℝ] F) (center : F)
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hΩ₀ : Ω ⊆ Ω₀)
    (hmap : MapsTo (fun x => center + I x) U V)
    (hgrade : ∀ n x, q n (I x) = p n x)
    (RF : MixedJetRegularity V Ω₀ f)
    (hf : MixedPowerBounds q center base loss V Ω₀ H W f)
    (heq : ∀ x ∈ U, EqOn (g x) (f (center + I x)) Ω) :
    ∃ RG : MixedJetRegularity U Ω g,
      MixedPowerBounds p 0 base loss U Ω H W g := by
  have hspatial (x : E) (hx : x ∈ U) : ContDiffOn ℝ ∞ (g x) Ω :=
    ((RF.spatial (center + I x) (hmap hx)).mono hΩ₀).congr (heq x hx)
  have hjet (a b : ℕ) (y : PolarPoint) (hy : y ∈ Ω) (x : E) (hx : x ∈ U) :
      mixedDerivative a b (g x) y =
        mixedDerivative a b (f (center + I x)) y :=
    mixedDerivative_congr_on_open hΩ (heq x hx) a b hy
  let RG : MixedJetRegularity U Ω g := {
    spatial := hspatial
    parameter := fun a b y hy =>
      ((RF.parameter a b y (hΩ₀ hy)).compAffine I center hU hmap).congr
        (fun x hx => (hjet a b y hy x hx).symm) }
  refine ⟨RG, ?_⟩
  intro K s
  obtain ⟨C, A, hC, hA, hb⟩ := hf K s
  refine ⟨C, A, hC, hA, ?_⟩
  intro k hk a b hab y hy J x hx hlow v hv R hR hhigh hvhigh
  let JF : SmoothDirections V (fun z => mixedDerivative a b (f z) y) :=
    RF.parameter a b y (hΩ₀ hy)
  have he : J.D k x v = JF.D k (center + I x) (fun j => I (v j)) := by
    apply (congrArg (fun A : E [×k]→L[ℝ] ℝ => A v)
      (J.unique (RG.parameter a b y hy) k x hx)).trans
    change (JF.compAffine I center hU hmap).D k x v = _
    exact JF.compAffine_apply I center hU hmap k x v
  have hstate (n : ℕ) :
      q n ((center + I x) - center) = p n (x - 0) := by
    rw [add_sub_cancel_left, hgrade, sub_zero]
  have hb' := hb k hk a b hab y (hΩ₀ hy) JF (center + I x) (hmap hx)
    ((hstate base).trans_le hlow) (fun j => I (v j))
    (fun j => (hgrade base (v j)).trans_le (hv j)) R hR
    ((hstate (s + loss)).trans_le hhigh)
    (fun j => (hgrade (s + loss) (v j)).trans_le (hvhigh j))
  exact (congrArg norm he).trans_le hb'

/-- Assemble a supplied family before specializing the abstract parameter
spaces to the physical state and sector records. -/
private theorem n04Realization_mixedPower_affine_family
    {E F I₀ : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    {base loss : ℕ} {U : Set E} {V : Set F}
    {Ω Ω₀ : Set PolarPoint} {H W : PolarPoint → ℝ}
    {f : I₀ → F → PolarPoint → ℝ} {g : I₀ → E → PolarPoint → ℝ}
    (I : E →L[ℝ] F) (center : F)
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hΩ₀ : Ω ⊆ Ω₀)
    (hmap : MapsTo (fun x => center + I x) U V)
    (hgrade : ∀ n x, q n (I x) = p n x)
    (RF : ∀ i, MixedJetRegularity V Ω₀ (f i))
    (hf : ∀ i, MixedPowerBounds q center base loss V Ω₀ H W (f i))
    (heq : ∀ i x, x ∈ U → EqOn (g i x) (f i (center + I x)) Ω) :
    ∀ i, ∃ RG : MixedJetRegularity U Ω (g i),
      MixedPowerBounds p 0 base loss U Ω H W (g i) := by
  intro i
  exact n04Realization_mixedPower_affine_domain I center hU hΩ hΩ₀
    hmap hgrade (RF i) (hf i) (heq i)

/-- This is a certificate for the literal corrected fields. The domain
contains every positive component, so its constants are uniform in the
component label and physical point. -/
def N04RealizationPositiveCoefficientPowerBounds
    (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S)
    (base loss : ℕ) (ε : ℝ) : Prop :=
  ∀ i : Fin 3, ∃ J : MixedJetRegularity
      (sectorNeighborhood S base ε ε)
      {p : PolarPoint | p ∈ annularOpen D ∧ 0 < deriv D.w p.1}
      (fun z => canonicalCoefficientComponent i (L.coefficients (liftSectorParameter S C z))),
    MixedPowerBounds (pairGrading (sectorGrading S) realGrading) 0 base loss
      (sectorNeighborhood S base ε ε)
      {p : PolarPoint | p ∈ annularOpen D ∧ 0 < deriv D.w p.1}
      (fun p => T.H p.1 ^ (3 / 4 : ℝ)) (fun p => T.E0 p.1)
      (fun z => canonicalCoefficientComponent i (L.coefficients (liftSectorParameter S C z)))

theorem n04Realization_positiveCoefficient_eq_original
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base : ℕ} {ε : ℝ}
    (h03 : N03Properties D T S C R L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {p : PolarPoint}
    (hp : p ∈ annularOpen D) (hpositive : 0 < deriv D.w p.1) (i : Fin 3) :
    canonicalCoefficientComponent i (L.coefficients z) p =
      coefficientOriginalField D S C i z p := by
  have ha := h03.1 z hz hs p
  have hbc := h03.2.1 z hz hs p hp hpositive
  simp only [canonicalCoefficientComponent, coefficientOriginalField, ite_apply]
  split_ifs
  · exact ha
  · exact hbc.1.self_of_nhds
  · exact hbc.2.self_of_nhds

set_option backward.isDefEq.respectTransparency true in
private theorem n04Realization_positiveCoefficient_of_original
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {originalBase base loss : ℕ} {ε η : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base η)
    (h03 : N03Properties D T S C R L originalBase ε)
    (hbase : originalBase ≤ base) (hη : η ≤ ε)
    (hraw : ∀ i : Fin 3,
      MixedPowerBounds (pairGrading (stateGrading S) realGrading) (C.referenceState, 0)
        base loss (stateNeighborhood S C base η) (annularOpen D)
        (fun p => T.H p.1 ^ (3 / 4 : ℝ)) (fun p => T.E0 p.1)
        (coefficientOriginalField D S C i)) :
    N04RealizationPositiveCoefficientPowerBounds D T S C L base loss η := by
  letI : IsTopologicalAddGroup (AnnularState S × ℝ) := inferInstance
  letI : ContinuousSMul ℝ (AnnularState S × ℝ) := inferInstance
  letI : IsTopologicalAddGroup (StateDirections S × ℝ) := inferInstance
  letI : ContinuousSMul ℝ (StateDirections S × ℝ) := inferInstance
  have hw : ContDiff ℝ ∞ D.w := hA.1.1.choose_spec.1.2.2.1.1
  have hΩ : IsOpen {p : PolarPoint | p ∈ annularOpen D ∧ 0 < deriv D.w p.1} :=
    (isOpen_Ioo.prod isOpen_univ).inter
      (isOpen_lt continuous_const ((hw.continuous_deriv (by simp)).comp continuous_fst))
  have hmap : MapsTo (fun z : StateDirections S × ℝ =>
      (C.referenceState, 0) + sectorParameterInclusion S z)
      (sectorNeighborhood S base η η) (stateNeighborhood S C base η) := by
    intro z hz
    change (C.referenceState, 0) + sectorParameterInclusion S z ∈
      stateNeighborhood S C base η
    rw [← liftSectorParameter_eq_affine S C z]
    exact liftSectorParameter_mem_stateNeighborhood hz le_rfl
  exact n04Realization_mixedPower_affine_family
    (E := StateDirections S × ℝ) (F := AnnularState S × ℝ)
    (p := pairGrading (sectorGrading S) realGrading)
    (q := pairGrading (stateGrading S) realGrading) (base := base) (loss := loss)
    (U := sectorNeighborhood S base η η) (V := stateNeighborhood S C base η)
    (Ω := {p : PolarPoint | p ∈ annularOpen D ∧ 0 < deriv D.w p.1})
    (Ω₀ := annularOpen D)
    (H := fun p => T.H p.1 ^ (3 / 4 : ℝ)) (W := fun p => T.E0 p.1)
    (f := coefficientOriginalField D S C)
    (g := fun i z => canonicalCoefficientComponent i
      (L.coefficients (liftSectorParameter S C z)))
    (sectorParameterInclusion S) (C.referenceState, 0)
    (sectorNeighborhood_isOpen S base η η) hΩ (fun _ hp => hp.1)
    hmap (pairGrading_sectorParameterInclusion S)
    (fun i => ⟨fun z hz => contDiffOn_coefficientOriginalField hS hT hA hB i hz,
      n01_originalCoefficientMixedSmoothDirections hS hT hA hB i⟩)
    hraw (fun i z hz p hp => by
      have hz' : liftSectorParameter S C z ∈ stateNeighborhood S C originalBase ε :=
        stateNeighborhood_subset hbase hη
          (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
      have he := n04Realization_positiveCoefficient_eq_original h03 hz'
        (hA.2.1.liftSectorParameter_sector z) hp.1 hp.2 i
      exact he.trans (congrArg (fun x => coefficientOriginalField D S C i x p)
        (liftSectorParameter_eq_affine S C z)))

/-- The retained construction supplies every input. One strengthened low
base and one positive radius precede all parameter and spatial orders;
the reference, material data, controls and corrected field are unchanged. -/
theorem n04Realization_positiveCoefficient_mixedPowerBounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {originalBase originalLoss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L originalBase originalLoss ε)
    (hG : N01PrimitiveGeometry D T S C)
    (hE : ∀ r : ℝ, 1 ≤ T.E0 r) :
    ∃ base loss : ℕ, originalBase ≤ base ∧ 0 < min ε (1 / 2) ∧
      N04RealizationPositiveCoefficientPowerBounds D T S C L base loss (min ε (1 / 2)) := by
  have h01 : N01Properties D T S C originalBase originalLoss ε := hN.1.1
  have hA : N01PartA D T S C :=
    ⟨h01.1, h01.2.2.1, h01.2.2.2.1, h01.2.2.2.2.1, h01.2.2.2.2.2.1⟩
  have hB : N01PartB D S C originalBase ε :=
    ⟨h01.2.2.2.2.2.2.1, h01.2.2.2.2.2.2.2.1,
      h01.2.2.2.2.2.2.2.2.1, h01.2.2.2.2.2.2.2.2.2.1,
      h01.2.2.2.2.2.2.2.2.2.2.1⟩
  have hη : 0 < min ε (1 / 2) := lt_min h01.2.1 (by norm_num)
  exact exists_base_ge_of_spatialPower_continuation
    (pairGrading (stateGrading S) realGrading) (jointStateGrading_monotone S)
    (jointStateGrading_hasInterpolation hS) originalBase 4
    (fun base loss => 0 < min ε (1 / 2) ∧
      N04RealizationPositiveCoefficientPowerBounds D T S C L base loss (min ε (1 / 2)))
    (fun base loss hb hI => by
      have hB' : N01PartB D S C base (min ε (1 / 2)) :=
        n01PartB_mono hB hb (min_le_left _ _)
      refine ⟨hη, n04Realization_positiveCoefficient_of_original hS hT hA hB'
        hN.2 hb (min_le_left _ _) ?_⟩
      intro i
      exact originalCoefficient_mixedPowerBounds hS hT hA hη
        ((min_le_right ε (1 / 2)).trans (by norm_num)) hB'
        (fun r _ => hE r) hG.1 hG.2.1 hI i)

end ContinuousFlexibility.Analysis
