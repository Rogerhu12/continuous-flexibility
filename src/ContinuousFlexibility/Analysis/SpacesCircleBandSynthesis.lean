module

public import ContinuousFlexibility.Analysis.SpacesCircleBandEstimates

/-!
# Synthesis into the actual closed circle-jet levels

Every band is sent to its genuine weighted angular derivatives in the
prescribed inner finite `PiLp` norm and outer square-summable norm. These
jets satisfy the weak graph equations and commute with the actual bonds.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ENNReal NNReal BigOperators ContDiff

/-- A uniform synthesis constant for an order-`s` jet row. -/
def circleBandSynthesisConstant (s : ℕ) : ℝ≥0 :=
  ⟨((Fintype.card (CircleJetIndex s) : ℝ) + 1) * Real.exp (s : ℝ), by positivity⟩

/-- The actual weighted finite jet row of one angular band. -/
def circleBandJetRow (M : ℝ) (hM : 1 ≤ M) (k s : ℕ) :
    AngleL2 →L[ℝ] PiLp 2 (fun _ : CircleJetIndex s => AngleL2) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : CircleJetIndex s => AngleL2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j : CircleJetIndex s =>
      M ^ (j.val 1).val • circleBandJet M hM k (j.val 0).val)

theorem circleBandJetRow_apply (M : ℝ) (hM : 1 ≤ M) (k s : ℕ)
    (f : AngleL2) (j : CircleJetIndex s) :
    circleBandJetRow M hM k s f j =
      M ^ (j.val 1).val • circleBandJet M hM k (j.val 0).val f := rfl

theorem circleBandJetRow_norm_le (M : ℝ) (hM : 1 ≤ M) (k s : ℕ) (f : AngleL2) :
    ‖circleBandJetRow M hM k s f‖ ≤
      (circleBandSynthesisConstant s : ℝ) * Real.exp ((s : ℝ) * (k : ℝ)) * ‖f‖ := by
  let B : ℝ := (Real.exp (s : ℝ) * Real.exp ((s : ℝ) * (k : ℝ))) * ‖f‖
  have hB : 0 ≤ B := by positivity
  have hpoint (j : CircleJetIndex s) : ‖circleBandJetRow M hM k s f j‖ ≤ B :=
    circleBandJet_synthesis_bound M hM k (j.val 0).val (j.val 1).val s j.property f
  have hcard : 0 ≤ (Fintype.card (CircleJetIndex s) : ℝ) := Nat.cast_nonneg _
  have hcard' : (Fintype.card (CircleJetIndex s) : ℝ) ≤
      ((Fintype.card (CircleJetIndex s) : ℝ) + 1) ^ 2 := by nlinarith
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [PiLp.norm_sq_eq_of_L2]
  calc
    (∑ j : CircleJetIndex s, ‖circleBandJetRow M hM k s f j‖ ^ 2) ≤
        ∑ _j : CircleJetIndex s, B ^ 2 :=
      Finset.sum_le_sum (fun j _ => (sq_le_sq₀ (norm_nonneg _) hB).mpr (hpoint j))
    _ = (Fintype.card (CircleJetIndex s) : ℝ) * B ^ 2 := by simp
    _ ≤ ((Fintype.card (CircleJetIndex s) : ℝ) + 1) ^ 2 * B ^ 2 :=
      mul_le_mul_of_nonneg_right hcard' (sq_nonneg B)
    _ = _ := by
      change ((Fintype.card (CircleJetIndex s) : ℝ) + 1) ^ 2 *
        ((Real.exp (s : ℝ) * Real.exp ((s : ℝ) * (k : ℝ))) * ‖f‖) ^ 2 =
        ((((Fintype.card (CircleJetIndex s) : ℝ) + 1) * Real.exp (s : ℝ)) *
          Real.exp ((s : ℝ) * (k : ℝ)) * ‖f‖) ^ 2
      ring

/-- The Fourier derivatives satisfy the actual weak graph relation. -/
theorem circleBandJet_weak (M : ℝ) (hM : 1 ≤ M) (k b : ℕ) (f : AngleL2) :
    HasWeakAngularDerivative (circleBandJet M hM k 0 f) (circleBandJet M hM k b f) b := by
  let g := circleFourierCutFunction (circleFrequencyBand M k) f
  have hg : ContDiff ℝ ∞ g := circleFourierCutFunction_contDiff _ f
  have hp : Function.Periodic g Real.pi := circleFourierCutFunction_periodic _ f
  have h₀ : MemLp g 2 angleMeasure := memLp_angleMeasure_of_continuous hg.continuous
  have hb : MemLp (iteratedDeriv b g) 2 angleMeasure :=
    memLp_angleMeasure_iteratedDeriv_of_contDiff hg b
  have he₀ : circleBandJet M hM k 0 f = h₀.toLp g := by
    apply Lp.ext
    have hae := circleBandJet_ae M hM k 0 f
    simp only [iteratedDeriv_zero] at hae
    exact hae.trans (MemLp.coeFn_toLp h₀).symm
  have heb : circleBandJet M hM k b f = hb.toLp (iteratedDeriv b g) :=
    Lp.ext ((circleBandJet_ae M hM k b f).trans (MemLp.coeFn_toLp hb).symm)
  rw [he₀, heb]
  exact hasWeakAngularDerivative_toLp_iteratedDeriv hg hp b h₀ hb

variable (T : MaterialData) (hM : ∀ m, 1 ≤ T.M (T.sample m))

/-- Synthesis into the exact outer and inner Hilbert jet norm. -/
def circleBandHilbert (s k : ℕ) : CircleModelBanach →L[ℝ] CircleJetHilbert s :=
  Analysis.lpSpectralDiagonal (fun m => circleBandJetRow (T.M (T.sample m)) (hM m) k s)
    (show 0 ≤ (circleBandSynthesisConstant s : ℝ) * Real.exp ((s : ℝ) * (k : ℝ)) by positivity)
    (fun m f => circleBandJetRow_norm_le (T.M (T.sample m)) (hM m) k s f)

theorem circleBandHilbert_apply (s k m : ℕ) (f : CircleModelBanach) (j : CircleJetIndex s) :
    circleBandHilbert T hM s k f m j =
      circleJetWeight T m j • circleBandJet (T.M (T.sample m)) (hM m) k (j.val 0).val (f m) := rfl

theorem circleBandHilbert_norm_le (s k : ℕ) (f : CircleModelBanach) :
    ‖circleBandHilbert T hM s k f‖ ≤
      (circleBandSynthesisConstant s : ℝ) * Real.exp ((s : ℝ) * (k : ℝ)) * ‖f‖ :=
  Analysis.lpSpectralDiagonal_norm_le _ _ _ f

theorem circleBandHilbert_mem_graph (s k : ℕ) (f : CircleModelBanach) :
    circleBandHilbert T hM s k f ∈ circleJetGraph T s := by
  intro m j
  refine ⟨circleBandJet (T.M (T.sample m)) (hM m) k (j.val 0).val (f m), ?_, ?_⟩
  · simpa only [circleBandHilbert_apply, circleJetWeight, zeroCircleJetIndex,
      Pi.zero_apply, Fin.val_zero, pow_zero, one_smul] using
      circleBandJet_weak (T.M (T.sample m)) (hM m) k (j.val 0).val (f m)
  · filter_upwards [Lp.coeFn_smul (circleJetWeight T m j)
      (circleBandJet (T.M (T.sample m)) (hM m) k (j.val 0).val (f m))] with θ hθ
    exact hθ

variable (hM0 : ∀ m, 0 < T.M (T.sample m))

/-- Band synthesis lands in the closed weak graph, without an additional
model or closure assumption from the caller. -/
def circleBandSynthesisLevel (s k : ℕ) : CircleModelBanach →L[ℝ] circleJetClosedSubmodule T s :=
  (circleBandHilbert T hM s k).codRestrict (circleJetClosedSubmodule T s) (by
    intro f
    rw [← SetLike.mem_coe, circleJetClosedSubmodule_carrier hM0]
    exact circleBandHilbert_mem_graph T hM s k f)

theorem circleBandSynthesisLevel_apply (s k m : ℕ) (f : CircleModelBanach)
    (j : CircleJetIndex s) :
    (circleBandSynthesisLevel T hM hM0 s k f).val m j =
      circleJetWeight T m j • circleBandJet (T.M (T.sample m)) (hM m) k (j.val 0).val (f m) := rfl

theorem circleBandSynthesisLevel_norm_le (s k : ℕ) (f : CircleModelBanach) :
    ‖circleBandSynthesisLevel T hM hM0 s k f‖ ≤
      (circleBandSynthesisConstant s : ℝ) * Real.exp ((s : ℝ) * (k : ℝ)) * ‖f‖ :=
  circleBandHilbert_norm_le T hM s k f

theorem circleBandSynthesisLevel_compatible (s k : ℕ) (f : CircleModelBanach) :
    circleJetBond T hM0 s (circleBandSynthesisLevel T hM hM0 (s + 1) k f) =
      circleBandSynthesisLevel T hM hM0 s k f := by
  apply Subtype.ext
  apply lp.ext
  funext m
  apply (WithLp.ext_iff 2).mpr
  funext j
  rfl

end ContinuousFlexibility.Statements
