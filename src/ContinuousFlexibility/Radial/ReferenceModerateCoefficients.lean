import ContinuousFlexibility.Radial.ReferenceRadialWeighted
import ContinuousFlexibility.Radial.MorseChainScales
import ContinuousFlexibility.Radial.CentralStatementBridges
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Coefficient powers and rapidly attenuated scalar fields

Smooth coefficients whose actual values have a fixed cell coefficient-power
bound form an algebra. Multiplication by such a coefficient preserves the
union of all positively attenuated scalar L² spaces. The profile, reciprocal
profile, and reciprocal radius provide all ordinary derivative generators
needed when the radial equation is differentiated.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

def ReferenceModerate (D : ReferenceData) (k : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ k (radialCore D) ∧ ∃ C B : ℝ, 0 ≤ C ∧
    ∀ m r, r ∈ D.cells m → |k r| ≤ C * exp (B * radialQ (D.cellIndex m))

def ReferenceRapid (D : ReferenceData) (u : ℝ → ℝ) : Prop :=
  ∃ γ A : ℝ, 0 < γ ∧ ReferenceRadialWeighted D γ A u

theorem ReferenceModerate.const (D : ReferenceData) (c : ℝ) :
    ReferenceModerate D (fun _ => c) := by
  refine ⟨contDiffOn_const, |c|, 0, abs_nonneg c, fun m r _ => ?_⟩
  simp only [zero_mul, exp_zero, mul_one, le_refl]

theorem ReferenceModerate.add {D : ReferenceData} {k l : ℝ → ℝ}
    (hk : ReferenceModerate D k) (hl : ReferenceModerate D l) :
    ReferenceModerate D (fun r => k r + l r) := by
  obtain ⟨hkc, C, B, hC, hk⟩ := hk
  obtain ⟨hlc, C', B', hC', hl⟩ := hl
  refine ⟨hkc.add hlc, C + C', max B B', add_nonneg hC hC', fun m r hr => ?_⟩
  have he (x : ℝ) (hx : x ≤ max B B') :
      exp (x * radialQ (D.cellIndex m)) ≤ exp (max B B' * radialQ (D.cellIndex m)) :=
    exp_le_exp.mpr (mul_le_mul_of_nonneg_right hx (radialQ_nonneg _))
  calc
    |k r + l r| ≤ |k r| + |l r| := abs_add_le _ _
    _ ≤ C * exp (B * radialQ (D.cellIndex m)) +
        C' * exp (B' * radialQ (D.cellIndex m)) := add_le_add (hk m r hr) (hl m r hr)
    _ ≤ C * exp (max B B' * radialQ (D.cellIndex m)) +
        C' * exp (max B B' * radialQ (D.cellIndex m)) :=
      add_le_add (mul_le_mul_of_nonneg_left (he B (le_max_left _ _)) hC)
        (mul_le_mul_of_nonneg_left (he B' (le_max_right _ _)) hC')
    _ = _ := by ring

theorem ReferenceModerate.mul {D : ReferenceData} {k l : ℝ → ℝ}
    (hk : ReferenceModerate D k) (hl : ReferenceModerate D l) :
    ReferenceModerate D (fun r => k r * l r) := by
  obtain ⟨hkc, C, B, hC, hk⟩ := hk
  obtain ⟨hlc, C', B', hC', hl⟩ := hl
  refine ⟨hkc.mul hlc, C * C', B + B', mul_nonneg hC hC', fun m r hr => ?_⟩
  calc
    |k r * l r| = |k r| * |l r| := abs_mul _ _
    _ ≤ (C * exp (B * radialQ (D.cellIndex m))) *
        (C' * exp (B' * radialQ (D.cellIndex m))) :=
      mul_le_mul (hk m r hr) (hl m r hr) (abs_nonneg _) (mul_nonneg hC (exp_pos _).le)
    _ = _ := by
      rw [add_mul, exp_add]
      ring

theorem ReferenceRapid.congr_ae {D : ReferenceData} {u v : ℝ → ℝ}
    (hu : ReferenceRapid D u) (he : u =ᵐ[volume.restrict (radialCore D)] v) :
    ReferenceRapid D v := by
  obtain ⟨γ, A, hγ, hu⟩ := hu
  exact ⟨γ, A, hγ, hu.congr_ae he⟩

theorem ReferenceRapid.of_eqOn {D : ReferenceData} {u v : ℝ → ℝ}
    (hu : ReferenceRapid D u) (he : EqOn u v (radialCore D)) : ReferenceRapid D v := by
  apply hu.congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  exact he hr

theorem ReferenceRapid.mul_moderate {D : ReferenceData}
    (hp : RadialPartition D) {u k : ℝ → ℝ}
    (hu : ReferenceRapid D u) (hk : ReferenceModerate D k) :
    ReferenceRapid D (fun r => k r * u r) := by
  obtain ⟨γ, A, hγ, hu⟩ := hu
  obtain ⟨hkc, C, B, hC, hb⟩ := hk
  refine ⟨γ / 2, 0, by positivity, ?_⟩
  exact hu.mul_coefficient hp 0 (by linarith)
    (hkc.continuousOn.aemeasurable measurableSet_Ioo).aestronglyMeasurable hC hb

theorem ReferenceRapid.add {D : ReferenceData}
    (hp : RadialPartition D) {u v : ℝ → ℝ}
    (hu : ReferenceRapid D u) (hv : ReferenceRapid D v) :
    ReferenceRapid D (fun r => u r + v r) := by
  obtain ⟨γ, A, hγ, hu⟩ := hu
  obtain ⟨δ, B, hδ, hv⟩ := hv
  let ε : ℝ := min γ δ / 2
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hεγ : ε < γ := by
    have hm := min_le_left γ δ
    dsimp only [ε]
    linarith [lt_min hγ hδ]
  have hεδ : ε < δ := by
    have hm := min_le_right γ δ
    dsimp only [ε]
    linarith [lt_min hγ hδ]
  have hbound : ∀ m r, r ∈ D.cells m → |(1 : ℝ)| ≤ 1 * exp (0 * radialQ (D.cellIndex m)) :=
    fun _ _ _ => by simp
  have hu' : ReferenceRadialWeighted D ε 0 u := by
    simpa only [one_mul] using
      hu.mul_coefficient hp 0 hεγ aestronglyMeasurable_const zero_le_one hbound
  have hv' : ReferenceRadialWeighted D ε 0 v := by
    simpa only [one_mul] using
      hv.mul_coefficient hp 0 hεδ aestronglyMeasurable_const zero_le_one hbound
  exact ⟨ε, 0, hε, hu'.add hv'⟩

theorem reference_contDiffOn_iteratedDeriv {s : Set ℝ} (hs : IsOpen s)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f s) (n : ℕ) :
    ContDiffOn ℝ ∞ (iteratedDeriv n f) s := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact (contDiffOn_infty_iff_deriv_of_isOpen hs).mp ih |>.2

theorem referenceModerate_profile_jet {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (s : ℕ) :
    ReferenceModerate D (iteratedDeriv s D.w) := by
  obtain ⟨C, hgeom, _, hC, _, _, _, _, _, hjet, _⟩ := hD
  refine ⟨reference_contDiffOn_iteratedDeriv isOpen_Ioo hgeom.2.2.1.1.contDiffOn s,
    C s, C s, (hC s).le, fun m r hr => ?_⟩
  have hj := hjet m r hr s
  rw [radialJet_eq_iteratedDeriv] at hj
  apply hj.trans
  apply mul_le_mul_of_nonneg_left _ (hC s).le
  apply exp_le_exp.mpr
  have hn := mul_le_mul_of_nonneg_left (radial_nat_sq_le_Q (D.cellIndex m)) (hC s).le
  linarith [Real.rpow_nonneg (Nat.cast_nonneg (D.cellIndex m)) (5 / 2 : ℝ)]

theorem referenceModerate_reciprocal_profile_jet {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (s : ℕ) :
    ReferenceModerate D (iteratedDeriv s (fun r => (D.w r)⁻¹)) := by
  obtain ⟨C, hgeom, _, hC, _, _, _, _, _, _, hjet, _⟩ := hD
  have hinv : ContDiffOn ℝ ∞ (fun r => (D.w r)⁻¹) (radialCore D) := by
    simpa only [one_div] using contDiffOn_const.div hgeom.2.2.1.1.contDiffOn
      (fun r hr => (hgeom.2.2.2.2.1 r hr).ne')
  refine ⟨reference_contDiffOn_iteratedDeriv isOpen_Ioo hinv s,
    C s, C s, (hC s).le, fun m r hr => ?_⟩
  have hj := hjet m r hr s
  simpa only [radialJet_eq_iteratedDeriv, radialE, ← Real.exp_mul, mul_comm] using hj

theorem referenceModerate_reciprocal_radius_jet {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (s : ℕ) :
    ReferenceModerate D (iteratedDeriv s (fun r : ℝ => r⁻¹)) := by
  have hgeom : RadialProfileGeometry D := hD.choose_spec.1
  have hinv : ContDiffOn ℝ ∞ (fun r : ℝ => r⁻¹) (Ioi (0 : ℝ)) := by
    simpa only [one_div] using contDiffOn_const.div contDiffOn_id
      (fun r hr => (show 0 < r from hr).ne')
  have hj := reference_contDiffOn_iteratedDeriv isOpen_Ioi hinv s
  have hsub : Icc D.a D.b ⊆ Ioi (0 : ℝ) := fun r hr => hgeom.1.trans_le hr.1
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image (hj.continuousOn.norm.mono hsub)
  refine ⟨hj.mono (fun r hr => hgeom.1.trans hr.1), |C|, 0, abs_nonneg C, fun m r hr => ?_⟩
  have hrI : r ∈ Icc D.a D.b := Ioo_subset_Icc_self (hD.choose_spec.2.1.2.2.2.1 m hr)
  have hb := hC ⟨r, hrI, rfl⟩
  simpa only [zero_mul, exp_zero, mul_one, Real.norm_eq_abs] using
    hb.trans (le_abs_self C)

end ContinuousFlexibility.Radial
