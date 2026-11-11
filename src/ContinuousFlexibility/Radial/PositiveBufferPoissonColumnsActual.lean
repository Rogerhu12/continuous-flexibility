import ContinuousFlexibility.Radial.PositiveBufferPoissonColumns
import ContinuousFlexibility.Radial.PositiveBufferPoissonNorm

/-!
# Actual Poisson fields and their classical representatives

The physical fields are the standard-basis columns of the retained Poisson
map. Their representatives come from the same finite combination in the
actual bordered energy domain. Restriction therefore gives the required
Lebesgue L² field, zero extension, border row, and classical equation.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real Matrix
open ContinuousFlexibility.Statements
open scoped Topology ContDiff InnerProductSpace

def positiveBufferPoissonColumnEnergy (B : BufferData) (A : Fin 2 → ℝ)
    (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (column : Fin 2 → PositiveBufferBorderedEnergy B.potential B.bordered) (j : Fin 2) :
    PositiveBufferBorderedEnergy B.potential B.bordered :=
  ∑ k, (sqrt (A j) * Q k j) • column k

def positiveBufferPoissonColumnState (B : BufferData) (A : Fin 2 → ℝ)
    (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (column : Fin 2 → PositiveBufferBorderedEnergy B.potential B.bordered) (j : Fin 2) :
    RadialL2 × ℝ :=
  positiveBufferPoissonMap B
    (fun k => positiveBufferBorderedState B.potential B.bordered (column k))
    Q A (Pi.single j 1)

def positiveBufferPoissonColumnField (B : BufferData) (A : Fin 2 → ℝ)
    (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (column : Fin 2 → PositiveBufferBorderedEnergy B.potential B.bordered) (j : Fin 2) :
    RadialL2 :=
  (positiveBufferPoissonColumnState B A Q column j).1

def positiveBufferPoissonColumnScalar (B : BufferData) (A : Fin 2 → ℝ)
    (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (column : Fin 2 → PositiveBufferBorderedEnergy B.potential B.bordered) (j : Fin 2) :
    ℝ :=
  (positiveBufferPoissonColumnState B A Q column j).2

theorem positiveBufferPoissonColumns_map_column (B : BufferData) (A : Fin 2 → ℝ)
    (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (column : Fin 2 → PositiveBufferBorderedEnergy B.potential B.bordered) (j : Fin 2) :
    (positiveBufferPoissonColumnField B A Q column j,
      positiveBufferPoissonColumnScalar B A Q column j) =
      positiveBufferPoissonMap B
        (fun k => positiveBufferBorderedState B.potential B.bordered (column k))
        Q A (Pi.single j 1) := rfl

theorem positiveBufferPoisson_matrix_single (A : Fin 2 → ℝ)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (j : Fin 2) :
    Q *ᵥ (fun i => sqrt (A i) * (Pi.single j (1 : ℝ) : Fin 2 → ℝ) i) =
      fun k => sqrt (A j) * Q k j := by
  ext k
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  fin_cases j <;> simp [Pi.single_apply, mul_comm]

theorem positiveBufferPoissonColumnState_retained (B : BufferData) (A : Fin 2 → ℝ)
    (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (column : Fin 2 → PositiveBufferBorderedEnergy B.potential B.bordered) (j : Fin 2) :
    positiveBufferPoissonColumnState B A Q column j =
      positiveBufferRetainedProjection B.l B.h
        (positiveBufferBorderedState B.potential B.bordered
          (positiveBufferPoissonColumnEnergy B A Q column j)) := by
  unfold positiveBufferPoissonColumnState
  rw [positiveBufferPoissonMap_apply, positiveBufferPoisson_matrix_single,
    positiveBufferStateSynthesis_apply]
  congr 1
  unfold positiveBufferPoissonColumnEnergy
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact (map_smul (positiveBufferBorderedState B.potential B.bordered)
    (sqrt (A j) * Q k j) (column k)).symm

theorem positiveBufferPoissonColumnField_eq (B : BufferData) (A : Fin 2 → ℝ)
    (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (column : Fin 2 → PositiveBufferBorderedEnergy B.potential B.bordered) (j : Fin 2) :
    positiveBufferPoissonColumnField B A Q column j =
      bufferL2Indicator (Ioo B.l B.h) measurableSet_Ioo
        (positiveBufferEnergyCoordinate B.potential 0
          (positiveBufferBorderedField B.potential B.bordered
            (positiveBufferPoissonColumnEnergy B A Q column j))) := by
  simp only [positiveBufferPoissonColumnField, positiveBufferPoissonColumnState_retained,
    positiveBufferRetainedProjection_apply, positiveBufferBorderedState_apply,
    positiveBufferBorderedField_apply]

theorem positiveBufferPoissonColumnScalar_eq (B : BufferData) (A : Fin 2 → ℝ)
    (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (column : Fin 2 → PositiveBufferBorderedEnergy B.potential B.bordered) (j : Fin 2) :
    positiveBufferPoissonColumnScalar B A Q column j =
      positiveBufferPoissonScalarCombination A Q
        (fun k => positiveBufferBorderedScalar B.potential B.bordered (column k)) j := by
  unfold positiveBufferPoissonColumnScalar
  rw [positiveBufferPoissonColumnState_retained, positiveBufferRetainedProjection_apply]
  change positiveBufferBorderedScalar B.potential B.bordered
      (positiveBufferPoissonColumnEnergy B A Q column j) = _
  simp only [positiveBufferPoissonColumnEnergy, positiveBufferPoissonScalarCombination,
    map_sum, map_smul, smul_eq_mul]

theorem positiveBufferPoissonColumnEnergy_representative {B : BufferData}
    {A αout : Fin 2 → ℝ} {K η : ℝ}
    (D : PositiveBufferCorrectedData B A αout K η)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (j : Fin 2) :
    EqOn
      (positiveBufferEnergyRepresentative B.potential
        (positiveBufferBorderedField B.potential B.bordered
          (positiveBufferPoissonColumnEnergy B A Q D.column j)))
      (positiveBufferPoissonRepresentative A Q D.representative j) (Icc B.l B.h) := by
  intro x hx
  change positiveBufferTraceAt B.potential x
      (positiveBufferBorderedField B.potential B.bordered
        (∑ k, (sqrt (A j) * Q k j) • D.column k)) =
      ∑ k, (sqrt (A j) * Q k j) * D.representative k x
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [positiveBufferTraceAt_apply, D.representative_eq k hx]

theorem positiveBufferPoissonColumnField_inside {B : BufferData}
    {A αout : Fin 2 → ℝ} {K η : ℝ}
    (D : PositiveBufferCorrectedData B A αout K η)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (j : Fin 2) :
    (positiveBufferPoissonColumnField B A Q D.column j : ℝ → ℝ) =ᵐ[
      volume.restrict (Ioo B.l B.h)]
      positiveBufferPoissonRepresentative A Q D.representative j := by
  let e := positiveBufferBorderedField B.potential B.bordered
    (positiveBufferPoissonColumnEnergy B A Q D.column j)
  have hae := (positiveBufferEnergyRepresentative_spec B.potential e).2.1
  rw [positiveBufferPoissonColumnField_eq]
  filter_upwards [ae_restrict_of_ae
      (bufferL2Indicator_coeFn (Ioo B.l B.h) measurableSet_Ioo
        (positiveBufferEnergyCoordinate B.potential 0 e)),
    ae_restrict_of_ae hae, ae_restrict_mem measurableSet_Ioo] with x hI hx hxin
  rw [hI, Set.indicator_of_mem hxin, hx]
  exact positiveBufferPoissonColumnEnergy_representative D Q j (Ioo_subset_Icc_self hxin)

theorem positiveBufferPoissonColumnField_outside (B : BufferData) (A : Fin 2 → ℝ)
    (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (column : Fin 2 → PositiveBufferBorderedEnergy B.potential B.bordered) (j : Fin 2) :
    (positiveBufferPoissonColumnField B A Q column j : ℝ → ℝ) =ᵐ[
      volume.restrict ((Ioo B.l B.h)ᶜ)] (fun _ => 0) := by
  unfold positiveBufferPoissonColumnField
  rw [positiveBufferPoissonColumnState_retained]
  exact positiveBufferRetainedProjection_supported B.l B.h _

theorem positiveBufferPoisson_projection_border (B : BufferData)
    (hborder : (B.border : ℝ → ℝ) =ᵐ[
      volume.restrict ((Ioo B.l B.h)ᶜ)] (fun _ => 0))
    (F : RadialL2 × ℝ) :
    inner ℝ B.border (positiveBufferRetainedProjection B.l B.h F).1 =
      inner ℝ B.border F.1 := by
  have hagree : ((positiveBufferRetainedProjection B.l B.h F).1 : ℝ → ℝ) =ᵐ[
      volume.restrict (Ioo B.l B.h)] F.1 := by
    rw [positiveBufferRetainedProjection_apply]
    filter_upwards [ae_restrict_of_ae
      (bufferL2Indicator_coeFn (Ioo B.l B.h) measurableSet_Ioo F.1),
      ae_restrict_mem measurableSet_Ioo] with x hx hxin
    rw [hx, Set.indicator_of_mem hxin]
  calc
    _ = inner ℝ (positiveBufferRetainedProjection B.l B.h F).1 B.border :=
      real_inner_comm _ _
    _ = inner ℝ F.1 B.border :=
      buffer_inner_eq_of_agree_on_support measurableSet_Ioo hagree hborder
    _ = _ := real_inner_comm _ _

theorem positiveBufferPoissonColumn_border_row {B : BufferData}
    (hB : BufferHypotheses B) {A αout : Fin 2 → ℝ} {K η : ℝ}
    (D : PositiveBufferCorrectedData B A αout K η)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (j : Fin 2) :
    if B.bordered then inner ℝ B.border (positiveBufferPoissonColumnField B A Q D.column j) = 0
    else positiveBufferPoissonColumnScalar B A Q D.column j = 0 := by
  by_cases hb : B.bordered = true
  · rw [if_pos hb]
    rcases hB with ⟨_, _, _, _, _, _, _, _, _, _, _, hborder, _, _, _⟩
    unfold positiveBufferPoissonColumnField
    rw [positiveBufferPoissonColumnState_retained,
      positiveBufferPoisson_projection_border B hborder]
    have h0 := D.border_row (0 : Fin 2)
    have h1 := D.border_row (1 : Fin 2)
    rw [if_pos hb] at h0 h1
    simp only [positiveBufferPoissonColumnEnergy, Fin.sum_univ_two, map_add, map_smul,
      Prod.fst_add, Prod.smul_fst, inner_add_right, inner_smul_right, h0, h1,
      mul_zero, add_zero]
  · rw [if_neg hb, positiveBufferPoissonColumnScalar_eq]
    unfold positiveBufferPoissonScalarCombination
    apply Finset.sum_eq_zero
    intro k _
    have hk := D.border_row k
    rw [if_neg hb] at hk
    change positiveBufferBorderedScalar B.potential B.bordered (D.column k) = 0 at hk
    change (sqrt (A j) * Q k j) *
      positiveBufferBorderedScalar B.potential B.bordered (D.column k) = 0
    rw [hk, mul_zero]

/-- Exactly the Poisson regularity, representative, support, border-row,
equation and trace clause appearing in the frozen R09 conclusion. -/
theorem positiveBufferPoissonColumns_spec {B : BufferData} (hB : BufferHypotheses B)
    {A αout : Fin 2 → ℝ} {K η : ℝ}
    (D : PositiveBufferCorrectedData B A αout K η) (hA : ∀ i, 0 < A i)
    (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (hQ : positiveBufferPoissonTraceMatrix B A D.representative * Q = 1) :
    ∀ i,
      ContDiffAt ℝ ∞ (positiveBufferPoissonRepresentative A Q D.representative i) B.l ∧
      ContDiffAt ℝ ∞ (positiveBufferPoissonRepresentative A Q D.representative i) B.h ∧
      ContDiffOn ℝ ∞ (positiveBufferPoissonRepresentative A Q D.representative i)
        (Ioo B.l B.h) ∧
      ContinuousOn (positiveBufferPoissonRepresentative A Q D.representative i)
        (Icc B.l B.h) ∧
      ((positiveBufferPoissonColumnField B A Q D.column i : ℝ → ℝ) =ᵐ[
        volume.restrict (Ioo B.l B.h)]
        positiveBufferPoissonRepresentative A Q D.representative i) ∧
      ((positiveBufferPoissonColumnField B A Q D.column i : ℝ → ℝ) =ᵐ[
        volume.restrict ((Ioo B.l B.h)ᶜ)] (fun _ => 0)) ∧
      (if B.bordered then
        inner ℝ B.border (positiveBufferPoissonColumnField B A Q D.column i) = 0
      else positiveBufferPoissonColumnScalar B A Q D.column i = 0) ∧
      (∀ x ∈ Ioo B.l B.h,
        -deriv (deriv (positiveBufferPoissonRepresentative A Q D.representative i)) x +
          B.potential x * positiveBufferPoissonRepresentative A Q D.representative i x +
          positiveBufferPoissonColumnScalar B A Q D.column i * B.borderFunction x = 0) ∧
      ∀ j, positiveBufferPoissonRepresentative A Q D.representative i (bufferCut B j) =
        if i = j then 1 else 0 := by
  intro i
  have hs := positiveBufferPoissonRepresentative_smooth A Q D.representative D.smooth i
  refine ⟨hs.contDiffAt, hs.contDiffAt, hs.contDiffOn, hs.continuous.continuousOn,
    positiveBufferPoissonColumnField_inside D Q i,
    positiveBufferPoissonColumnField_outside B A Q D.column i,
    positiveBufferPoissonColumn_border_row hB D Q i, ?_, ?_⟩
  · intro x hx
    rw [positiveBufferPoissonColumnScalar_eq]
    exact positiveBufferPoissonRepresentative_equation D Q i hx
  · intro j
    simpa only [eq_comm] using
      positiveBufferPoissonRepresentative_boundary B A hA Q D.representative hQ j i

end ContinuousFlexibility.Radial
