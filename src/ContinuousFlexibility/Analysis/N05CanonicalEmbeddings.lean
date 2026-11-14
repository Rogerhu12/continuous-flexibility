module

public import ContinuousFlexibility.Analysis.N05CanonicalMultipliers
public import ContinuousFlexibility.Analysis.N05MaterialWeights

/-!
# Actual embeddings of canonical volume levels

A positive endpoint exponent makes the prescribed forget map a continuous
map to the unweighted Hilbert sequence. A strict endpoint margin absorbs
any change of material order. Every angular jet is scaled by the same
piecewise factor, so the weaker realization represents the same source.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

def n05CanonicalSampleWeight (T : MaterialData) (S : PhysicalSpacesData)
    (K : CanonicalData S) (γ t : ℝ) (m : ℕ) : ℝ :=
  T.M (T.sample (K.cell m)) ^ (-t) * T.H (T.sample (K.cell m)) ^ γ

theorem n05CanonicalSampleWeight_pos {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hPart : RadialPartition D) (S : PhysicalSpacesData)
    (K : CanonicalData S) (γ t : ℝ) (m : ℕ) :
    0 < n05CanonicalSampleWeight T S K γ t m :=
  n05_materialWeight_pos hT (materialSample_mem_radialCore hT hPart (K.cell m)) γ t

def n05CanonicalForgetCLM {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hPart : RadialPartition D) (S : PhysicalSpacesData)
    (K : CanonicalData S) {γ : ℝ} (hγ : 0 < γ) (t : ℝ) (s : ℕ) :
    (n05CanonicalVolumeModel T S K).level γ t s →L[ℝ] CanonicalL2Sequence S K :=
  let hb := n05_materialSampleWeight_bound hT hPart hγ t K.cell
  n05CanonicalWeightedZeroMap S K s (n05CanonicalSampleWeight T S K γ t)
    hb.choose hb.choose_spec.1.le (by
      intro m
      rw [Real.norm_eq_abs, abs_of_pos (n05CanonicalSampleWeight_pos hT hPart S K γ t m)]
      exact hb.choose_spec.2 m)

theorem n05CanonicalForgetCLM_apply {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hPart : RadialPartition D) (S : PhysicalSpacesData)
    (K : CanonicalData S) {γ : ℝ} (hγ : 0 < γ) (t : ℝ) (s : ℕ)
    (v : (n05CanonicalVolumeModel T S K).level γ t s) (m : ℕ) :
    n05CanonicalForgetCLM hT hPart S K hγ t s v m =
      (n05CanonicalVolumeModel T S K).forget γ t s v m := by
  rw [n05CanonicalVolumeModel_forget]
  unfold n05CanonicalForgetCLM
  exact n05CanonicalWeightedZeroMap_apply S K s (n05CanonicalSampleWeight T S K γ t)
    _ _ _ (show n05CanonicalClosedSubmodule S K s from v) m

theorem n05CanonicalForgetCLM_bound {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hPart : RadialPartition D) (S : PhysicalSpacesData)
    (K : CanonicalData S) {γ : ℝ} (hγ : 0 < γ) (t : ℝ) (s : ℕ) :
    ∃ B : ℝ, 0 < B ∧
      ∀ v : (n05CanonicalVolumeModel T S K).level γ t s,
        ‖n05CanonicalForgetCLM hT hPart S K hγ t s v‖ ≤ B * ‖v‖ := by
  let hb := n05_materialSampleWeight_bound hT hPart hγ t K.cell
  refine ⟨hb.choose, hb.choose_spec.1, fun v => ?_⟩
  exact n05CanonicalWeightedZeroMap_bound S K s
    (n05CanonicalSampleWeight T S K γ t) hb.choose hb.choose_spec.1.le (by
      intro m
      rw [Real.norm_eq_abs, abs_of_pos (n05CanonicalSampleWeight_pos hT hPart S K γ t m)]
      exact hb.choose_spec.2 m) v

def n05CanonicalWeightRatio (T : MaterialData) (S : PhysicalSpacesData)
    (K : CanonicalData S) (γlo γhi tlo thi : ℝ) (m : ℕ) : ℝ :=
  n05CanonicalSampleWeight T S K γhi thi m /
    n05CanonicalSampleWeight T S K γlo tlo m

theorem n05CanonicalWeightRatio_bound {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hPart : RadialPartition D) (S : PhysicalSpacesData)
    (K : CanonicalData S) {γlo γhi : ℝ} (hγ : γlo < γhi) (tlo thi : ℝ) :
    ∃ B : ℝ, 0 < B ∧
      ∀ m, ‖n05CanonicalWeightRatio T S K γlo γhi tlo thi m‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ :=
    n05_materialSampleWeight_compare hT hPart hγ tlo thi K.cell
  refine ⟨B, hB, fun m => ?_⟩
  have hlo := n05CanonicalSampleWeight_pos hT hPart S K γlo tlo m
  have hhi := n05CanonicalSampleWeight_pos hT hPart S K γhi thi m
  rw [n05CanonicalWeightRatio, Real.norm_eq_abs, abs_of_pos (div_pos hhi hlo)]
  exact (div_le_iff₀ hlo).mpr (hb m)

def n05CanonicalVolumeEmbed {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hPart : RadialPartition D) (S : PhysicalSpacesData)
    (K : CanonicalData S) {γlo γhi : ℝ} (hγ : γlo < γhi)
    (tlo thi : ℝ) (s : ℕ) :
    (n05CanonicalVolumeModel T S K).level γhi thi s →L[ℝ]
      (n05CanonicalVolumeModel T S K).level γlo tlo s :=
  let hb := n05CanonicalWeightRatio_bound hT hPart S K hγ tlo thi
  n05CanonicalJetMultiplier S K s
    (n05CanonicalWeightRatio T S K γlo γhi tlo thi)
    hb.choose hb.choose_spec.1.le hb.choose_spec.2

theorem n05CanonicalVolumeEmbed_apply {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hPart : RadialPartition D) (S : PhysicalSpacesData)
    (K : CanonicalData S) {γlo γhi : ℝ} (hγ : γlo < γhi)
    (tlo thi : ℝ) (s : ℕ)
    (v : (n05CanonicalVolumeModel T S K).level γhi thi s)
    (m : ℕ) (j : Fin (s + 1)) :
    (n05CanonicalVolumeEmbed hT hPart S K hγ tlo thi s v).val m j =
      n05CanonicalWeightRatio T S K γlo γhi tlo thi m • v.val m j := by
  unfold n05CanonicalVolumeEmbed
  exact n05CanonicalJetMultiplier_apply S K s
    (n05CanonicalWeightRatio T S K γlo γhi tlo thi)
    _ _ _ (show n05CanonicalClosedSubmodule S K s from v) m j

theorem n05CanonicalVolumeEmbed_forget {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hPart : RadialPartition D) (S : PhysicalSpacesData)
    (K : CanonicalData S) {γlo γhi : ℝ} (hγ : γlo < γhi)
    (tlo thi : ℝ) (s : ℕ)
    (v : (n05CanonicalVolumeModel T S K).level γhi thi s) :
    (n05CanonicalVolumeModel T S K).forget γlo tlo s
        (n05CanonicalVolumeEmbed hT hPart S K hγ tlo thi s v) =
      (n05CanonicalVolumeModel T S K).forget γhi thi s v := by
  funext m
  rw [n05CanonicalVolumeModel_forget, n05CanonicalVolumeModel_forget,
    n05CanonicalVolumeEmbed_apply, smul_smul]
  have hlo := (n05CanonicalSampleWeight_pos hT hPart S K γlo tlo m).ne'
  have hw : n05CanonicalSampleWeight T S K γlo tlo m *
      n05CanonicalWeightRatio T S K γlo γhi tlo thi m =
      n05CanonicalSampleWeight T S K γhi thi m := by
    rw [n05CanonicalWeightRatio, div_eq_mul_inv]
    calc
      _ = n05CanonicalSampleWeight T S K γhi thi m *
          (n05CanonicalSampleWeight T S K γlo tlo m *
            (n05CanonicalSampleWeight T S K γlo tlo m)⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hlo, mul_one]
  exact congrArg (fun c : ℝ => c • v.val m 0) hw

theorem n05CanonicalVolumeEmbed_bound {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hPart : RadialPartition D) (S : PhysicalSpacesData)
    (K : CanonicalData S) {γlo γhi : ℝ} (hγ : γlo < γhi)
    (tlo thi : ℝ) (s : ℕ) :
    ∃ B : ℝ, 0 < B ∧
      ∀ v : (n05CanonicalVolumeModel T S K).level γhi thi s,
        ‖n05CanonicalVolumeEmbed hT hPart S K hγ tlo thi s v‖ ≤ B * ‖v‖ := by
  let hb := n05CanonicalWeightRatio_bound hT hPart S K hγ tlo thi
  refine ⟨hb.choose, hb.choose_spec.1, fun v => ?_⟩
  exact n05CanonicalJetMultiplier_bound S K s
    (n05CanonicalWeightRatio T S K γlo γhi tlo thi)
    hb.choose hb.choose_spec.1.le hb.choose_spec.2 v

end ContinuousFlexibility.Statements
