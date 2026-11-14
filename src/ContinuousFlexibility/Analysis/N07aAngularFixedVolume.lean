module

public import ContinuousFlexibility.Analysis.N07aAngularFixedJetEnvelope
public import ContinuousFlexibility.Analysis.N07aLinearJetVolumeBounds
public import ContinuousFlexibility.Analysis.N07aCompositionBudget

/-!
# Actual volume membership from fixed-parameter spatial envelopes

Apply the genuine source-linear producer to scalar multiples of the one
displayed field. This uses its actual angular jets and all material orders;
no uniform estimate in a varying nonlinear parameter is assumed here.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

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

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {base loss : ℕ} {ε γ : ℝ}

theorem n07a_fixedJetEnvelope_volume
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hV : IsVolumeModel T S K V) {f : ℕ → PolarPoint → ℝ}
    (hfs : ∀ m, ContDiffOn ℝ ∞ (f m) (canonicalOpen S K m))
    (hfp : ∀ m p, p ∈ canonicalOpen S K m → f m (p + (0, Real.pi)) = f m p)
    (hfe : ∀ m p, p ∈ canonicalOpen S K m → f m (p.1, -p.2) = f m p)
    (hf : ∀ c : ℕ, N07aAngularFixedJetEnvelope T K (canonicalOpen S K)
      (fun m => T.H (T.sample (K.cell m)) ^ γ * (T.M (T.sample (K.cell m)) ^ c)⁻¹) f)
    (t s : ℕ) :
    ∃ Fts : V.level γ (t : ℝ) s,
      ∀ m, (V.forget γ (t : ℝ) s Fts m : PolarPoint → ℝ)
        =ᵐ[canonicalMeasure S K m] f m := by
  let p : ℕ → Seminorm ℝ ℝ := fun _ => 0
  let q : ℕ → Seminorm ℝ ℝ := realGrading
  let w := fun c m => T.H (T.sample (K.cell m)) ^ γ *
    (T.M (T.sample (K.cell m)) ^ c)⁻¹
  have hw (c m : ℕ) : 0 ≤ w c m := by
    have hp := hT.2.1 _ (materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m))
    exact mul_nonneg (Real.rpow_nonneg hp.2.1.le γ)
      (inv_nonneg.mpr (pow_nonneg (zero_le_one.trans hp.2.2.2) c))
  have hlinear : N07aSampleLinearJetBounds T K p q univ (canonicalOpen S K) w 0 0
      (fun (_ : ℝ) (a : ℝ) m y => a * f m y) := by
    intro i j c
    let e : ℕ → ℝ := (hf c (i + j)).choose
    have he := (hf c (i + j)).choose_spec.1
    have he0 := (hf c (i + j)).choose_spec.2.1
    have heb := (hf c (i + j)).choose_spec.2.2
    refine ⟨e, he, he0, fun _ _ a m y hy => ?_⟩
    have hb : |mixedDerivative i j (f m) y| ≤ e m * w c m :=
      (n07a_mixedDerivative_norm_le_iteratedFDeriv (isOpen_Ioo.prod isOpen_univ)
        (hfs m) i j hy).trans (heb m y hy)
    rw [spaces_mixedDerivative_const_mul, abs_mul]
    apply (mul_le_mul_of_nonneg_left hb (abs_nonneg a)).trans
    simp only [p, q, realGrading, coe_normSeminorm, zero_apply, Real.norm_eq_abs]
    nlinarith only [mul_nonneg (mul_nonneg (he0 m) (hw c m)) (abs_nonneg a)]
  have hp : Monotone p := fun _ _ _ _ => le_rfl
  have hq : Monotone q := weighted_realGrading_monotone
  let producer := n07a_sampleLinearJet_volume_bound (γ := γ) hD hT h04 href hV hp hq hlinear
    (fun _ _ a m => contDiffOn_const.mul (hfs m))
    (fun _ _ a m y hy => congrArg (a * ·) (hfp m y hy))
    (fun _ _ a m y hy => congrArg (a * ·) (hfe m y hy)) t s
  have hAb := producer.choose_spec.2
  let result := hAb 0 (mem_univ _) 1
  let Fts : V.level γ (t : ℝ) s := result.choose
  have hFts := result.choose_spec.1
  refine ⟨Fts, fun m => ?_⟩
  have hsame : (V.forget γ (t : ℝ) s Fts m : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m] (fun y => (1 : ℝ) * f m y) := hFts m
  exact hsame.trans (Filter.Eventually.of_forall (fun y => one_mul (f m y)))

end ContinuousFlexibility.Analysis
