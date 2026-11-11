import ContinuousFlexibility.Radial.PositiveBufferEnergyGlobalData
import ContinuousFlexibility.Radial.PositiveBufferGreenDataRegularity
import ContinuousFlexibility.Radial.PositiveBufferFullInverse
import ContinuousFlexibility.Radial.PositiveBufferGlobalRegularity
import ContinuousFlexibility.Radial.PositiveBufferComparisonExteriorUniqueness
import ContinuousFlexibility.Radial.PositiveBufferComparisonEnergyTrace

/-!
# The actual full-inverse correction of each Green column

The full inverse is applied to the constructed smooth commutator source.
Its canonical energy representative is globally smooth, is homogeneous
through both buffers, and satisfies the exterior conormal relation.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open ContinuousFlexibility.Statements
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

theorem positiveBufferFullGraph_field_weak {V : ℝ → ℝ} {border : RadialL2}
    {bordered : Bool} {U F : RadialL2 × ℝ}
    (h : BorderedFullGraph V border bordered U F) :
    WeakSchrodingerGraph V U.1 (F.1 - U.2 • border) := by
  cases bordered with
  | false =>
    simp only [BorderedFullGraph, Bool.false_eq_true, ite_false] at h
    simpa only [h.2.1, zero_smul, sub_zero] using h.1
  | true =>
    simp only [BorderedFullGraph, ite_true] at h
    exact h.1

namespace PositiveBufferGreenData

variable {B : BufferData} {Ccut : ℝ}
variable (D : PositiveBufferGreenData B Ccut) (hB : BufferHypotheses B)
variable (H : (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ))
variable (hH : ∀ F, (B.bordered = false → F.2 = 0) →
  BorderedFullGraph B.potential B.border B.bordered (H F) F)

def zeroScalar (j : Fin 2) : PositiveBufferBorderedEnergy B.potential B.bordered :=
  ⟨(D.energy j, 0), fun _ => rfl⟩

def correction (j : Fin 2) : PositiveBufferBorderedEnergy B.potential B.bordered :=
  positiveBufferLiftedInverse hB.2.2.2.2.2.1 B.border B.bordered H hH (D.source j, 0)

def correctionRepresentative (j : Fin 2) : ℝ → ℝ :=
  positiveBufferEnergyRepresentative B.potential
    (positiveBufferBorderedField B.potential B.bordered (D.correction hB H hH j))

def correctedColumn (j : Fin 2) : PositiveBufferBorderedEnergy B.potential B.bordered :=
  sqrt (D.profiles.A j) • (D.zeroScalar j - D.correction hB H hH j)

def correctedRepresentative (j : Fin 2) : ℝ → ℝ :=
  fun x => sqrt (D.profiles.A j) *
    (D.profiles.interiorKernel j x - D.correctionRepresentative hB H hH j x)

@[simp] theorem zeroScalar_field (j : Fin 2) :
    positiveBufferBorderedField B.potential B.bordered (D.zeroScalar j) = D.energy j := rfl

@[simp] theorem zeroScalar_scalar (j : Fin 2) :
    positiveBufferBorderedScalar B.potential B.bordered (D.zeroScalar j) = 0 := rfl

@[simp] theorem zeroScalar_state (j : Fin 2) :
    positiveBufferBorderedState B.potential B.bordered (D.zeroScalar j) =
      (positiveBufferEnergyCoordinate B.potential 0 (D.energy j), 0) := rfl

theorem correction_state (j : Fin 2) :
    positiveBufferBorderedState B.potential B.bordered (D.correction hB H hH j) =
      H (D.source j, 0) := by
  unfold correction
  rw [positiveBufferLiftedInverse_state,
    positiveBufferSourceProjection_eq B.bordered (D.source j, 0) (fun _ => rfl)]

theorem correction_graph (j : Fin 2) :
    BorderedFullGraph B.potential B.border B.bordered
      (positiveBufferBorderedState B.potential B.bordered (D.correction hB H hH j))
      (D.source j, 0) := by
  rw [D.correction_state hB H hH]
  exact hH _ (fun _ => rfl)

theorem correction_smooth_equation (j : Fin 2) :
    ContDiff ℝ ∞ (D.correctionRepresentative hB H hH j) ∧
      ∀ x : ℝ,
        -deriv (deriv (D.correctionRepresentative hB H hH j)) x +
          B.potential x * D.correctionRepresentative hB H hH j x =
        D.profiles.sourceFunction j x -
          positiveBufferBorderedScalar B.potential B.bordered
            (D.correction hB H hH j) * B.borderFunction x := by
  let W := D.correction hB H hH j
  let s := positiveBufferBorderedScalar B.potential B.bordered W
  have hweak : WeakSchrodingerGraph B.potential
      (positiveBufferEnergyCoordinate B.potential 0
        (positiveBufferBorderedField B.potential B.bordered W))
      (D.source j - s • B.border) :=
    positiveBufferFullGraph_field_weak (D.correction_graph hB H hH j)
  have hsource : ((D.source j - s • B.border : RadialL2) : ℝ → ℝ) =ᵐ[volume]
      (fun x => D.profiles.sourceFunction j x - s * B.borderFunction x) := by
    filter_upwards [Lp.coeFn_sub (D.source j) (s • B.border),
      Lp.coeFn_smul s B.border, D.source_ae j, hB.2.2.2.2.2.2.2.2.1]
      with x hsub hsmul hsource hborder
    rw [hsub]
    simp only [Pi.sub_apply, hsource, hsmul, Pi.smul_apply, smul_eq_mul, hborder]
  exact positiveBufferEnergyRepresentative_global_smooth hB.2.2.2.2.1
    ((D.source_smooth j).sub (hB.2.2.2.2.2.2.1.const_mul s))
    (positiveBufferBorderedField B.potential B.bordered W) hweak hsource

theorem correction_homogeneous (i j : Fin 2) {t : ℝ} (ht : t < B.action i + 2) :
    -deriv (deriv (D.correctionRepresentative hB H hH j)) (positiveBufferPoint B i t) +
      B.potential (positiveBufferPoint B i t) *
        D.correctionRepresentative hB H hH j (positiveBufferPoint B i t) = 0 := by
  exact positiveBufferGreenCorrection_homogeneous hB j (D.profiles.A j)
    (positiveBufferBorderedScalar B.potential B.bordered (D.correction hB H hH j))
    (D.profiles.normalizedIn j) (deriv (D.profiles.normalizedIn j))
    (D.correctionRepresentative hB H hH j)
    (D.correction_smooth_equation hB H hH j).2 i ht

theorem correction_exterior_equation (i j : Fin 2) {x : ℝ} (hx : x ∈ bufferExterior B i) :
    -deriv (deriv (D.correctionRepresentative hB H hH j)) x +
      B.potential x * D.correctionRepresentative hB H hH j x = 0 := by
  have ht : positiveBufferCoordinate B i x < 0 := by
    change positiveBufferCoordinate B i x ∈ Iio (0 : ℝ)
    rw [← positiveBufferPoint_preimage_exterior hB i]
    change positiveBufferPoint B i (positiveBufferCoordinate B i x) ∈ bufferExterior B i
    rwa [positiveBufferPoint_coordinate hB i x]
  have hσ := buffer_action_pos hB i
  have he := D.correction_homogeneous hB H hH i j (t := positiveBufferCoordinate B i x)
    (by linarith)
  simpa only [positiveBufferPoint_coordinate] using he

theorem correction_state_bound (hHnorm : ‖H‖ ≤ B.B₀) (j : Fin 2) :
    ‖positiveBufferBorderedState B.potential B.bordered (D.correction hB H hH j)‖ ≤
      B.B₀ * ‖D.source j‖ := by
  have hn := positiveBufferLiftedInverse_state_bound hB.2.2.2.2.2.1
    B.border B.bordered H hH hHnorm (D.source j, 0)
  simpa only [correction, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)] using hn

theorem correction_field_bound (hHnorm : ‖H‖ ≤ B.B₀) (j : Fin 2) :
    ‖positiveBufferEnergyCoordinate B.potential 0
      (positiveBufferBorderedField B.potential B.bordered (D.correction hB H hH j))‖ ≤
      B.B₀ * ‖D.source j‖ := by
  apply le_trans ?_ (D.correction_state_bound hB H hH hHnorm j)
  change ‖positiveBufferEnergyCoordinate B.potential 0 (D.correction hB H hH j).val.1‖ ≤
    ‖(positiveBufferEnergyCoordinate B.potential 0 (D.correction hB H hH j).val.1,
      (D.correction hB H hH j).val.2)‖
  rw [Prod.norm_def]
  exact le_max_left _ _

theorem correction_cut_bound (hHnorm : ‖H‖ ≤ B.B₀) (i j : Fin 2) :
    |D.correctionRepresentative hB H hH j (bufferCut B i)| ≤
      sqrt (B.mass i) * exp (-B.action i) * (B.B₀ * ‖D.source j‖) := by
  exact positiveBufferEnergyGreenCorrection_cut_trace_bound hB i j (D.profiles.A j)
    (positiveBufferBorderedScalar B.potential B.bordered (D.correction hB H hH j))
    (D.profiles.normalizedIn j) (deriv (D.profiles.normalizedIn j))
    (positiveBufferBorderedField B.potential B.bordered (D.correction hB H hH j))
    (D.correction_smooth_equation hB H hH j).1
    (D.correction_smooth_equation hB H hH j).2
    (D.correction_field_bound hB H hH hHnorm j)

theorem correction_exterior_conormal (i j : Fin 2) :
    bufferSign i * deriv (D.correctionRepresentative hB H hH j) (bufferCut B i) =
      -D.profiles.alphaOut i * D.correctionRepresentative hB H hH j (bufferCut B i) := by
  obtain ⟨M, hM, hpbound⟩ := D.pout_bounded hB i
  have hprop := positiveBuffer_exterior_proportional hB i
    (D.correction_smooth_equation hB H hH j).1 (D.profiles.pout_smooth i)
    (fun x hx => D.correction_exterior_equation hB H hH i j hx)
    (D.profiles.pout_equation i) (D.profiles.pout_cut i)
    (show 0 ≤ 2 * ‖positiveBufferBorderedField B.potential B.bordered
      (D.correction hB H hH j)‖ by positivity) hM
    (fun x _ => positiveBufferEnergyRepresentative_bound B.potential
      (positiveBufferBorderedField B.potential B.bordered (D.correction hB H hH j)) x)
    hpbound
  rw [hprop.2, D.profiles.alphaOut_conormal i]
  ring

end PositiveBufferGreenData

end ContinuousFlexibility.Radial
