import ContinuousFlexibility.Analysis.SeeleyCoefficients
import ContinuousFlexibility.Analysis.SeeleyLpSeries
import ContinuousFlexibility.Analysis.SobolevJetBonding

/-!
# The same Seeley operator at every Sobolev order

The coefficients in `seeleyData` are constructed independently of the input
function and of the order. This file combines their moment identities with
the smooth-jet and actual `L²` estimates. The resulting linear map on the
smooth core extends to a bounded operator at every Sobolev level, and these
extensions agree under the natural inclusions between levels.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff ENNReal

variable {ι F : Type*} [Countable ι]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A valid bound for one derivative of the fixed reflection operator. -/
def seeleyDerivativeBound (S : SeeleyData ι) (n : ℕ) : ℝ :=
  1 + ∑' i, |S.a i| * S.b i ^ n

theorem seeleyDerivativeBound_nonneg (S : SeeleyData ι) (n : ℕ) :
    0 ≤ seeleyDerivativeBound S n :=
  add_nonneg zero_le_one (tsum_nonneg fun i =>
    mul_nonneg (abs_nonneg _) (pow_nonneg (S.b_nonneg i) n))

/-- The linear extension maps the true half-line smooth Sobolev core into
the true whole-line smooth Sobolev core. -/
def seeleySobolevCoreExtension (S : SeeleyData ι) :
    HalfLineSobolevCore F →ₗ[ℝ] LineSobolevCore F where
  toFun f := ⟨seeleyExtend S f, by
    refine ⟨(contDiff_seeleyExtend_of_contDiffOn S f.property.1 f.property.2).contDiffOn,
      fun n => ?_⟩
    rw [iteratedDerivWithin_univ, Measure.restrict_univ,
      iteratedDeriv_seeleyExtend_of_contDiffOn S f.property.1 f.property.2 n]
    exact memLp_seeleyExtensionJet S (fun k => iteratedDerivWithin k f (Ici 0)) n
      (f.property.2 n)⟩
  map_add' f g := Subtype.ext <| seeleyExtend_add S
    (HalfLineSobolevCore.bounded f) (HalfLineSobolevCore.bounded g)
  map_smul' c f := Subtype.ext <| seeleyExtend_smul S c f

@[simp] theorem seeleySobolevCoreExtension_coe (S : SeeleyData ι)
    (f : HalfLineSobolevCore F) :
    (seeleySobolevCoreExtension S f : ℝ → F) = seeleyExtend S f := rfl

theorem seeleySobolevCoreExtension_rightInverse (S : SeeleyData ι)
    (f : HalfLineSobolevCore F) {x : ℝ} (hx : 0 ≤ x) :
    seeleySobolevCoreExtension S f x = f x := seeleyExtend_of_nonneg S f hx

/-- Each output derivative is bounded by the same input derivative.
In particular, the extension has no loss of Sobolev order. -/
theorem seeleySobolevCoreExtension_derivative_bound (S : SeeleyData ι)
    (n : ℕ) (f : HalfLineSobolevCore F) :
    ‖sobolevCoreDerivative F univ MeasurableSet.univ uniqueDiffOn_univ n
        (seeleySobolevCoreExtension S f)‖ ≤
      seeleyDerivativeBound S n *
        ‖sobolevCoreDerivative F (Ici 0) measurableSet_Ici (uniqueDiffOn_Ici 0) n f‖ := by
  rw [norm_sobolevCoreDerivative, norm_sobolevCoreDerivative,
    seeleySobolevCoreExtension_coe, iteratedDerivWithin_univ, Measure.restrict_univ,
    iteratedDeriv_seeleyExtend_of_contDiffOn S f.property.1 f.property.2 n]
  exact norm_seeleyExtensionJet_le S (fun k => iteratedDerivWithin k f (Ici 0)) n
    (f.property.2 n)

/-- One finite constant for the complete derivative norm of order `k`. -/
def seeleySobolevBound (S : SeeleyData ι) (k : ℕ) : ℝ :=
  ∑ j : Fin (k + 1), seeleyDerivativeBound S j.val

theorem seeleySobolevBound_nonneg (S : SeeleyData ι) (k : ℕ) :
    0 ≤ seeleySobolevBound S k :=
  Finset.sum_nonneg fun j _ => seeleyDerivativeBound_nonneg S j.val

theorem seeleySobolevCoreExtension_bound (S : SeeleyData ι)
    (k : ℕ) (f : HalfLineSobolevCore F) :
    ‖sobolevCoreJet F univ MeasurableSet.univ uniqueDiffOn_univ k
        (seeleySobolevCoreExtension S f)‖ ≤
      seeleySobolevBound S k *
        ‖sobolevCoreJet F (Ici 0) measurableSet_Ici (uniqueDiffOn_Ici 0) k f‖ := by
  apply sobolevCoreJet_norm_le_of_coordinate_bounds F (seeleySobolevCoreExtension S) k
    (fun j => seeleyDerivativeBound S j.val) (fun j => seeleyDerivativeBound_nonneg S j.val)
  intro j g
  refine (seeleySobolevCoreExtension_derivative_bound S j.val g).trans ?_
  apply mul_le_mul_of_nonneg_left _ (seeleyDerivativeBound_nonneg S j.val)
  simpa only [sobolevCoreJet_apply] using
    PiLp.norm_apply_le (sobolevCoreJet F (Ici 0) measurableSet_Ici (uniqueDiffOn_Ici 0) k g) j

/-- The actual bounded operator on `H^k`, obtained from the single common
smooth extension. -/
def seeleySobolevExtension (S : SeeleyData ι) (k : ℕ) :
    SobolevJetCompletion F (Ici 0) measurableSet_Ici (uniqueDiffOn_Ici 0) k →L[ℝ]
      SobolevJetCompletion F univ MeasurableSet.univ uniqueDiffOn_univ k :=
  sobolevJetExtension F (seeleySobolevCoreExtension S) k

theorem norm_seeleySobolevExtension_le (S : SeeleyData ι) (k : ℕ) :
    ‖seeleySobolevExtension (F := F) S k‖ ≤ seeleySobolevBound S k :=
  norm_sobolevJetExtension_le F (seeleySobolevCoreExtension S) k
    (seeleySobolevBound_nonneg S k) (seeleySobolevCoreExtension_bound S k)

theorem seeleySobolevExtension_apply_core (S : SeeleyData ι) (k : ℕ)
    (f : HalfLineSobolevCore F) :
    seeleySobolevExtension S k
        (coreToSobolevJet F (Ici 0) measurableSet_Ici (uniqueDiffOn_Ici 0) k f) =
      coreToSobolevJet F univ MeasurableSet.univ uniqueDiffOn_univ k
        (seeleySobolevCoreExtension S f) :=
  sobolevJetExtension_apply F (seeleySobolevCoreExtension S) k
    (seeleySobolevCoreExtension_bound S k) f

/-- The operators at different orders are restrictions of the same
extension, not unrelated choices made for each order. -/
theorem seeleySobolevExtension_compatible (S : SeeleyData ι) {k m : ℕ} (hkm : k ≤ m) :
    (sobolevJetBonding F univ MeasurableSet.univ uniqueDiffOn_univ hkm).comp
        (seeleySobolevExtension S m) =
      (seeleySobolevExtension S k).comp
        (sobolevJetBonding F (Ici 0) measurableSet_Ici (uniqueDiffOn_Ici 0) hkm) :=
  sobolevJetExtension_compatible F (seeleySobolevCoreExtension S) hkm
    (seeleySobolevCoreExtension_bound S k) (seeleySobolevCoreExtension_bound S m)

end ContinuousFlexibility.Analysis
