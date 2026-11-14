module

public import ContinuousFlexibility.Radial.PositiveBufferComparisonGreenRegularity

/-!
# Cut values, conormals, and the corrected Green identity

The retained expression of each Green kernel has its exact own-cut
derivative and is identically zero near the opposite cut. Subtracting
a smooth exterior-homogeneous correction yields the delta-minus-exterior
conormal identity used by the finite-dimensional DN calculation.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem positiveBufferGreenInterior_own_cut {B : BufferData}
    (hB : BufferHypotheses B) (j : Fin 2) (A : ℝ) {pin : ℝ → ℝ}
    (hpin0 : pin 0 = 1) :
    positiveBufferGreenInterior B j A pin (bufferCut B j) = A⁻¹ := by
  have hσ := buffer_action_pos hB j
  unfold positiveBufferGreenInterior
  rw [positiveBufferCoordinate_cut, positiveBufferCutoff_one (by linarith),
    hpin0, mul_one, mul_one]

theorem positiveBufferGreenInterior_deriv_own_cut {B : BufferData}
    (hB : BufferHypotheses B) (j : Fin 2) (A : ℝ) {pin : ℝ → ℝ}
    (hpin : ContDiff ℝ ∞ pin) :
    deriv (positiveBufferGreenInterior B j A pin) (bufferCut B j) =
      A⁻¹ * (-bufferSign j * B.mass j) * deriv pin 0 := by
  have hσ := buffer_action_pos hB j
  have hχ0 : positiveBufferCutoff (B.action j) 0 = 1 :=
    positiveBufferCutoff_one (by linarith)
  have hχ'0 : deriv (positiveBufferCutoff (B.action j)) 0 = 0 :=
    (positiveBufferCutoff_derivatives_zero
      (σ := B.action j) (x := 0) (by intro h; linarith [h.1])).1
  have hχd : HasDerivAt (positiveBufferCutoff (B.action j)) 0 0 := by
    have hd : HasDerivAt (positiveBufferCutoff (B.action j))
        (deriv (positiveBufferCutoff (B.action j)) 0) 0 :=
      ((positiveBufferCutoff_contDiff (B.action j)).differentiable (by simp) 0).hasDerivAt
    simpa only [hχ'0] using hd
  have hprod : HasDerivAt (fun t => positiveBufferCutoff (B.action j) t * pin t)
      (deriv pin 0) 0 := by
    convert hχd.fun_mul ((hpin.differentiable (by simp) 0).hasDerivAt) using 1
    rw [hχ0]
    ring
  have hcoord : HasDerivAt (positiveBufferCoordinate B j) (-bufferSign j * B.mass j)
      (bufferCut B j) := by
    change HasDerivAt (fun x => -bufferSign j * B.mass j * (x - bufferCut B j))
      (-bufferSign j * B.mass j) (bufferCut B j)
    simpa only [id_eq, mul_one] using
      (((hasDerivAt_id (bufferCut B j)).sub_const (bufferCut B j)).const_mul
        (-bufferSign j * B.mass j))
  have hprod' : HasDerivAt (fun t => positiveBufferCutoff (B.action j) t * pin t)
      (deriv pin 0) (positiveBufferCoordinate B j (bufferCut B j)) := by
    rwa [positiveBufferCoordinate_cut]
  have h := (hprod'.comp (bufferCut B j) hcoord).const_mul A⁻¹
  have hd : deriv (positiveBufferGreenInterior B j A pin) (bufferCut B j) =
      A⁻¹ * (deriv pin 0 * (-bufferSign j * B.mass j)) := by
    change deriv (fun x => A⁻¹ *
      (positiveBufferCutoff (B.action j) (positiveBufferCoordinate B j x) *
        pin (positiveBufferCoordinate B j x))) (bufferCut B j) = _
    simpa only [Function.comp_def] using h.deriv
  rw [hd]
  ring

theorem positiveBufferGreenInterior_opposite_cut {B : BufferData}
    (hB : BufferHypotheses B) {i j : Fin 2} (hij : i ≠ j) (A : ℝ) (pin : ℝ → ℝ) :
    positiveBufferGreenInterior B j A pin (bufferCut B i) = 0 ∧
      deriv (positiveBufferGreenInterior B j A pin) (bufferCut B i) = 0 := by
  have hsep : B.action j + 6 < positiveBufferCoordinate B j (bufferCut B i) := by
    by_contra hn
    have hσ := buffer_action_pos hB i
    have hne := positiveBufferPoint_end_regions_disjoint hB (Ne.symm hij)
      (s := positiveBufferCoordinate B j (bufferCut B i)) (t := 0)
      (le_of_not_gt hn) (by linarith)
    apply hne
    rw [positiveBufferPoint_coordinate hB j (bufferCut B i), positiveBufferPoint_zero]
  have hnear : ∀ᶠ x in 𝓝 (bufferCut B i),
      B.action j + 4 < positiveBufferCoordinate B j x := by
    have hopen : IsOpen {x : ℝ | B.action j + 4 < positiveBufferCoordinate B j x} :=
      isOpen_lt continuous_const (positiveBufferCoordinate_contDiff B j).continuous
    apply hopen.mem_nhds
    change B.action j + 4 < positiveBufferCoordinate B j (bufferCut B i)
    linarith
  have he : positiveBufferGreenInterior B j A pin =ᶠ[𝓝 (bufferCut B i)] fun _ => (0 : ℝ) := by
    filter_upwards [hnear] with x hx
    unfold positiveBufferGreenInterior
    rw [positiveBufferCutoff_zero hx.le, zero_mul, mul_zero]
  exact ⟨he.eq_of_nhds, by simpa only [deriv_const] using he.deriv_eq⟩

theorem positiveBufferGreenInterior_cut_values {B : BufferData}
    (hB : BufferHypotheses B) (A : Fin 2 → ℝ) (pin : Fin 2 → ℝ → ℝ)
    (hpin0 : ∀ j, pin j 0 = 1) :
    ∀ i j, positiveBufferGreenInterior B j (A j) (pin j) (bufferCut B i) =
      if i = j then (A j)⁻¹ else 0 := by
  intro i j
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    exact positiveBufferGreenInterior_own_cut hB i (A i) (hpin0 i)
  · rw [if_neg hij]
    exact (positiveBufferGreenInterior_opposite_cut hB hij (A j) (pin j)).1

theorem positiveBufferGreenInterior_conormals {B : BufferData}
    (hB : BufferHypotheses B) (A αin : Fin 2 → ℝ) (pin : Fin 2 → ℝ → ℝ)
    (hpin : ∀ j, ContDiff ℝ ∞ (pin j))
    (hαin : ∀ j, αin j = -B.mass j * deriv (pin j) 0) :
    ∀ i j, bufferSign i *
      deriv (positiveBufferGreenInterior B j (A j) (pin j)) (bufferCut B i) =
        if i = j then αin i / A j else 0 := by
  intro i j
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, positiveBufferGreenInterior_deriv_own_cut hB i (A i) (hpin i), hαin i]
    calc
      _ = -(bufferSign i ^ 2) * (B.mass i * deriv (pin i) 0 / A i) := by ring
      _ = -B.mass i * deriv (pin i) 0 / A i := by rw [bufferSign_sq]; ring
  · rw [if_neg hij, (positiveBufferGreenInterior_opposite_cut hB hij (A j) (pin j)).2, mul_zero]

/-- The exact conormal identity before normalizing the two Green columns.
All traces and derivatives here belong to actual smooth representatives. -/
theorem positiveBuffer_corrected_conormal_identity (B : BufferData)
    (A αin αout : Fin 2 → ℝ) (K U : Fin 2 → ℝ → ℝ)
    (hK : ∀ j, ContDiff ℝ ∞ (K j)) (hU : ∀ j, ContDiff ℝ ∞ (U j))
    (hKcut : ∀ i j, K j (bufferCut B i) = if i = j then (A j)⁻¹ else 0)
    (hKcon : ∀ i j, bufferSign i * deriv (K j) (bufferCut B i) =
      if i = j then αin i / A j else 0)
    (hUcon : ∀ i j, bufferSign i * deriv (U j) (bufferCut B i) =
      -αout i * U j (bufferCut B i))
    (hA : ∀ i, A i ≠ 0) (hAsum : ∀ i, A i = αin i + αout i) :
    ∀ i j, bufferSign i * deriv (fun x => K j x - U j x) (bufferCut B i) =
      (if i = j then 1 else 0) -
        αout i * (K j (bufferCut B i) - U j (bufferCut B i)) := by
  intro i j
  have hd : deriv (fun x => K j x - U j x) (bufferCut B i) =
      deriv (K j) (bufferCut B i) - deriv (U j) (bufferCut B i) :=
    (((hK j).differentiable (by simp) (bufferCut B i)).hasDerivAt.fun_sub
      (((hU j).differentiable (by simp) (bufferCut B i)).hasDerivAt)).deriv
  rw [hd, mul_sub, hKcon, hUcon, hKcut]
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    calc
      _ = (αin i + αout i) / A i -
          αout i * ((A i)⁻¹ - U i (bufferCut B i)) := by ring
      _ = _ := by rw [← hAsum i, div_self (hA i)]
  · simp only [if_neg hij]
    ring

end ContinuousFlexibility.Radial
