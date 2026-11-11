import ContinuousFlexibility.Analysis.N07aFiniteCoefficientTameVolume
import ContinuousFlexibility.Analysis.N07aScalarColumnSupport
import ContinuousFlexibility.Analysis.N07aCanonicalAtomBounds
import ContinuousFlexibility.Analysis.N07aParameterGrading
import ContinuousFlexibility.Analysis.N07aReferenceReturn
import ContinuousFlexibility.Analysis.N07aCanonicalCoefficientDifference

/-!
# The actual scalar columns in every weighted source level

The primitive jets supply one fixed parameter loss. Their physical
support gives one fixed finite set of pieces. Consequently all three
original columns have genuine weighted graph representatives and a
one-high norm bound, independently of the later nonlinear Source family.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped BigOperators

set_option backward.isDefEq.respectTransparency true

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul n07aNonlinearSectorParameterSub

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S} {L : ReturnCorrectionData S}
  {K : CanonicalData S} {V : VolumeModelData S K} {base loss : ℕ} {ε : ℝ}

local instance n07aScalarColumnVolumesLevelGroup (γ t : ℝ) (s : ℕ) :
    NormedAddCommGroup (V.level γ t s) := Submodule.normedAddCommGroup _
local instance n07aScalarColumnVolumesLevelSpace (γ t : ℝ) (s : ℕ) :
    NormedSpace ℝ (V.level γ t s) := Submodule.normedSpace _

theorem n07aScalarColumn_eq_atomField
    (z : Parameter S) (m : ℕ) (hm : K.left m < K.right m) (i : Fin 3) :
    n07aScalarColumn D S C L K (liftSectorParameter S C z) m i =
      n07aCanonicalAtomField D T S C L K (n07aScalarColumnAtom i) z m := by
  funext y
  change n07aScalarColumn D S C L K (liftSectorParameter S C z) m i y =
    atom D T S C L K (liftSectorParameter S C z) m (n07aScalarColumnAtom i)
      (n07aCanonicalUnitInversePoint K m y)
  rw [← n07aScalarColumn_unit, Function.comp_apply, n07aCanonicalUnitPoint_inverse hm y]

theorem n07a_actualScalarColumns_volume
    (hD : IsAccumulatingProfile D) (hS : IsPhysicalSpaces D T S)
    (hT : IsMaterialData D T) (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hV : IsVolumeModel T S K V) :
    ∃ d : ℕ, ∀ γ t : ℝ, ∀ s : ℕ, ∃ A : ℝ, 0 < A ∧
      ∀ z (hz : z ∈ sectorNeighborhood S base ε ε), ∀ i : Fin 3,
      ∃ W : V.level γ t s,
        V.forget γ t s W = (fun m =>
          (n07aCurrentScalarOpenCoefficient href hcur z hz m (h04.2.2.2.1 m).2.1 i).toLp) ∧
        ‖W‖ ≤ A * (1 + parameterGrading S (s + d) z) := by
  classical
  let hI : ∀ m, K.left m < K.right m := fun m => (h04.2.2.2.1 m).2.1
  obtain ⟨I, hsupport⟩ := n07a_canonicalScalarColumns_finite_support hD hS hT h01 h04 href
  let estimates := n07a_canonicalAtomFields_sampleJetBounds hD hT href hcur hI
  let d : ℕ := estimates.choose
  have hb := estimates.choose_spec
  have hp : Monotone (parameterGrading S) := n07aParameterGrading_monotone S
  let χ (i : Fin 3) (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
      (m : ℕ) := n07aCurrentScalarOpenCoefficient href hcur z hz m (hI m) i
  have hχ (i : Fin 3) (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε) (m : ℕ) :
      (χ i z hz m).value = n07aCanonicalAtomField D T S C L K (n07aScalarColumnAtom i) z m :=
    n07aScalarColumn_eq_atomField z m (hI m) i
  have heven (i : Fin 3) (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
      (m : ℕ) (y : PolarPoint) (hy : y ∈ canonicalOpen S K m) :
      n07aCanonicalAtomField D T S C L K (n07aScalarColumnAtom i) z m (y.1, -y.2) =
        n07aCanonicalAtomField D T S C L K (n07aScalarColumnAtom i) z m y := by
    rw [← n07aScalarColumn_eq_atomField z m (hI m) i]
    exact n07a_canonicalScalarColumn_even hS h03 h04 _
      (liftSectorParameter_mem_stateNeighborhood (S := S) (C := C) hz le_rfl)
      (h01.2.2.1.liftSectorParameter_sector z) m i y hy
  have hzero (i : Fin 3) (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
      (m : ℕ) (hm : m ∉ I) :
      EqOn (n07aCanonicalAtomField D T S C L K (n07aScalarColumnAtom i) z m)
        (fun _ => (0 : ℝ)) (canonicalOpen S K m) := by
    rw [← n07aScalarColumn_eq_atomField z m (hI m) i]
    exact hsupport _ (liftSectorParameter_mem_stateNeighborhood (S := S) (C := C) hz le_rfl)
      (h01.2.2.1.liftSectorParameter_sector z) m hm i
  refine ⟨d, fun γ t s => ?_⟩
  let all (i : Fin 3) := exists_n07aFiniteCoefficientVolume_tame hD hT hV hI hp
    (hb (n07aScalarColumnAtom i)) (χ i) (hχ i) (heven i) I (hzero i) γ t s
  let A : Fin 3 → ℝ := fun i => (all i).choose
  have hA (i : Fin 3) : 0 < A i := (all i).choose_spec.1
  refine ⟨∑ i, A i, Finset.sum_pos (fun i _ => hA i) (by simp), fun z hz i => ?_⟩
  obtain ⟨W, hW, hnorm⟩ := (all i).choose_spec.2 z hz
  refine ⟨W, hW, hnorm.trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun j _ => (hA j).le) (Finset.mem_univ i))
    (add_nonneg zero_le_one (apply_nonneg _ _))

theorem n07a_referenceScalarColumns_volume
    (hD : IsAccumulatingProfile D) (hS : IsPhysicalSpaces D T S)
    (hT : IsMaterialData D T) (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : ReferenceJets D T S C L K) (hV : IsVolumeModel T S K V)
    (γ t : ℝ) (s : ℕ) :
    ∃ W : Fin 3 → V.level γ t s, ∀ i : Fin 3,
      V.forget γ t s (W i) = (fun m =>
        (n07aReferenceScalarOpenCoefficient href m (h04.2.2.2.1 m).2.1 i).toLp) := by
  classical
  let hI : ∀ m, K.left m < K.right m := fun m => (h04.2.2.2.1 m).2.1
  obtain ⟨I, hsupport⟩ := n07a_canonicalScalarColumns_finite_support hD hS hT h01 h04 href
  have hz := n07a_reference_mem_stateNeighborhood h01
  have hs := h01.2.2.1.stateSector
  let χ (i : Fin 3) (m : ℕ) := n07aReferenceScalarOpenCoefficient href m (hI m) i
  have heven (i : Fin 3) (m : ℕ) (p : PolarPoint) (hp : p ∈ canonicalOpen S K m) :
      (χ i m).value (p.1, -p.2) = (χ i m).value p :=
    n07a_canonicalScalarColumn_even hS h03 h04 _ hz hs m i p hp
  have hzero (i : Fin 3) (m : ℕ) (hm : m ∉ I) :
      EqOn (χ i m).value (fun _ => (0 : ℝ)) (canonicalOpen S K m) :=
    hsupport _ hz hs m hm i
  let all (i : Fin 3) := exists_n07aFiniteCoefficientVolume hD hT hV γ t s
    (χ i) (heven i) I (hzero i)
  exact ⟨fun i => (all i).choose, fun i => (all i).choose_spec.1⟩

theorem n07a_relativeScalarColumns_volume
    (hD : IsAccumulatingProfile D) (hS : IsPhysicalSpaces D T S)
    (hT : IsMaterialData D T) (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hV : IsVolumeModel T S K V) :
    ∃ d : ℕ, ∀ γ t : ℝ, ∀ s : ℕ, ∃ A : ℝ, 0 < A ∧
      ∀ z (hz : z ∈ sectorNeighborhood S base ε ε), ∀ i : Fin 3,
      ∃ W : V.level γ t s,
        V.forget γ t s W = (fun m =>
          ((n07aCurrentScalarOpenCoefficient href hcur z hz m (h04.2.2.2.1 m).2.1 i).sub
            (n07aReferenceScalarOpenCoefficient href m (h04.2.2.2.1 m).2.1 i)).toLp) ∧
        ‖W‖ ≤ A * (1 + parameterGrading S (s + d) z) := by
  classical
  obtain ⟨d, hb⟩ := n07a_actualScalarColumns_volume hD hS hT h01 h03 h04 href hcur hV
  refine ⟨d, fun γ t s => ?_⟩
  obtain ⟨A, hA, hcurrent⟩ := hb γ t s
  obtain ⟨Z, hZ⟩ := n07a_referenceScalarColumns_volume hD hS hT h01 h03 h04 href hV γ t s
  let B : ℝ := ∑ i : Fin 3, ‖Z i‖
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  refine ⟨A + B, add_pos_of_pos_of_nonneg hA hB, fun z hz i => ?_⟩
  obtain ⟨W, hW, hnorm⟩ := hcurrent z hz i
  refine ⟨W - Z i, ?_, ?_⟩
  · rw [map_sub, hW, hZ i]
    funext m
    rw [Pi.sub_apply, N07aCanonicalOpenCoefficient.sub_toLp]
  · have hZi : ‖Z i‖ ≤ B :=
      Finset.single_le_sum (fun j _ => norm_nonneg (Z j)) (Finset.mem_univ i)
    have hp : 0 ≤ parameterGrading S (s + d) z := apply_nonneg _ _
    have h := (norm_sub_le W (Z i)).trans (add_le_add hnorm hZi)
    exact h.trans (by nlinarith [mul_nonneg hB hp])

end ContinuousFlexibility.Analysis
