module

public import ContinuousFlexibility.Radial.TerminalConeCutoff
public import ContinuousFlexibility.Radial.TerminalCapSourceEnergy

/-!
# Energy of the actual first-cone cutoff

The error is supported on the same fixed-ratio layer as the actual
Hilbert source. Its integral on the whole cap is therefore the layer
integral. Boundary normalization cancels radius and profile height.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real MeasureTheory Filter
open scoped Topology ContDiff

theorem terminalCone_cutoffEnergy_support (right : Bool) {a : ℝ} (ha : 0 < a)
    {w u : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u) :
    Function.support (terminalCapCutoffEnergy w (terminalPhysicalCutoff right a (2 * a)) u) ⊆
      Ioo a (2 * a) := by
  have hab : a < 2 * a := by linarith
  have hs : Function.support (terminalCapCutoffEnergy w (terminalPhysicalCutoff right a (2 * a)) u) ⊆
      Icc a (2 * a) := by
    intro r hr
    have hd : deriv (terminalPhysicalCutoff right a (2 * a)) r ≠ 0 := by
      intro hz
      exact hr (by simp only [terminalCapCutoffEnergy, hz, zero_pow (by decide : 2 ≠ 0),
        mul_zero, zero_mul])
    exact terminalPhysicalCutoff_tsupport_deriv right hab (subset_tsupport _ hd)
  have hopen := (terminalCapCutoffEnergy_continuous hw
    (terminalPhysicalCutoff_smooth right a (2 * a)) hu).isOpen_support
  simpa only [interior_Icc] using hopen.subset_interior_iff.mpr hs

theorem terminalCone_cutoffEnergy_integral_layer (right : Bool) {a lo hi : ℝ}
    (ha : 0 < a) (hlo : lo ≤ a) (hhi : 2 * a ≤ hi)
    {w u : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u) :
    (∫ r in lo..hi, terminalCapCutoffEnergy w (terminalPhysicalCutoff right a (2 * a)) u r) =
      ∫ r in a..2 * a, terminalCapCutoffEnergy w (terminalPhysicalCutoff right a (2 * a)) u r := by
  have hs := terminalCone_cutoffEnergy_support right ha hw hu
  have hsmall : Function.support (terminalCapCutoffEnergy w (terminalPhysicalCutoff right a (2 * a)) u) ⊆
      Ioc a (2 * a) := fun r hr => ⟨(hs hr).1, (hs hr).2.le⟩
  have hlarge : Function.support (terminalCapCutoffEnergy w (terminalPhysicalCutoff right a (2 * a)) u) ⊆
      Ioc lo hi := fun r hr => ⟨hlo.trans_lt (hs hr).1, (hs hr).2.le.trans hhi⟩
  rw [intervalIntegral.integral_eq_integral_of_support_subset hlarge,
    intervalIntegral.integral_eq_integral_of_support_subset hsmall]

/-- The actual positive energy error, on any enclosing physical cap. -/
theorem terminalCone_cutoffEnergy_budget (right : Bool) {a lo hi scale j σ : ℝ}
    {w u : ℝ → ℝ} (ha : 0 < a) (hs : 0 < scale) (hj : 0 < j)
    (hlo : lo ≤ a) (hhi : 2 * a ≤ hi)
    (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u)
    (hcone : ∀ r ∈ Icc a (2 * a), w r = scale * r)
    (huval : ∀ r ∈ Icc a (2 * a), |u r| ≤ exp (-σ)) :
    let χ := terminalPhysicalCutoff right a (2 * a)
    let error := (∫ r in lo..hi, terminalCapCutoffEnergy w χ u r) / (j ^ 2 * scale)
    0 ≤ error ∧ error ≤
      (2 * terminalPhysicalCutoffJetConstant 1 ^ 2 / j ^ 2) * exp (-2 * σ) := by
  let χ := terminalPhysicalCutoff right a (2 * a)
  have hab : a < 2 * a := by linarith
  have hlam : 0 < j ^ 2 * scale := mul_pos (sq_pos_of_pos hj) hs
  have hwidth : 2 * a - a = a := by ring
  have hb (r : ℝ) (hr : r ∈ Icc a (2 * a)) :
      0 ≤ w r ∧ w r ≤ 2 * scale * a := by
    rw [hcone r hr]
    refine ⟨mul_nonneg hs.le (ha.le.trans hr.1), ?_⟩
    calc
      _ ≤ scale * (2 * a) := mul_le_mul_of_nonneg_left hr.2 hs.le
      _ = _ := by ring
  obtain ⟨hpos, hbound⟩ := terminalCapCutoffEnergy_integral_bound
    (W := 2 * scale * a) (C := terminalPhysicalCutoffJetConstant 1 / a)
    (A := 1) (σ := σ) hab.le (by positivity) hw
    (terminalPhysicalCutoff_smooth right a (2 * a)) hu hb
    (fun r _ => by simpa only [hwidth] using terminalPhysicalCutoff_deriv_bound right hab r)
    (fun r hr _ => by simpa only [one_mul] using huval r hr)
  dsimp only
  rw [terminalCone_cutoffEnergy_integral_layer right ha hlo hhi hw hu]
  refine ⟨div_nonneg hpos hlam.le, ?_⟩
  calc
    _ ≤ ((2 * a - a) * (2 * scale * a) *
        (terminalPhysicalCutoffJetConstant 1 / a) ^ 2 * (1 : ℝ) ^ 2 * exp (-2 * σ)) /
          (j ^ 2 * scale) := div_le_div_of_nonneg_right hbound hlam.le
    _ = _ := by field_simp [ha.ne', hs.ne', hj.ne'] <;> ring

/-- The stand-in has d=1/j; the fixed error constant is independent of
the retained cone length and of the height and radius scales. -/
theorem terminalCone_cutoffEnergy_relative (right : Bool) {a lo hi scale j σ : ℝ}
    {w u : ℝ → ℝ} (ha : 0 < a) (hs : 0 < scale) (hj : 1 ≤ j)
    (hlo : lo ≤ a) (hhi : 2 * a ≤ hi)
    (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u)
    (hcone : ∀ r ∈ Icc a (2 * a), w r = scale * r)
    (huval : ∀ r ∈ Icc a (2 * a), |u r| ≤ exp (-σ)) :
    (∫ r in lo..hi, terminalCapCutoffEnergy w (terminalPhysicalCutoff right a (2 * a)) u r) /
        (j ^ 2 * scale) ≤
      (1 / j) * (2 * terminalPhysicalCutoffJetConstant 1 ^ 2) * exp (-2 * σ) := by
  have hjpos : 0 < j := lt_of_lt_of_le (by norm_num) hj
  apply (terminalCone_cutoffEnergy_budget right ha hs hjpos hlo hhi hw hu hcone huval).2.trans
  apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
  have hjj : j ≤ j ^ 2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr hj) hjpos.le]
  calc
    _ ≤ (2 * terminalPhysicalCutoffJetConstant 1 ^ 2) / j :=
      div_le_div_of_nonneg_left (by positivity) hjpos hjj
    _ = _ := by ring

end ContinuousFlexibility.Radial
