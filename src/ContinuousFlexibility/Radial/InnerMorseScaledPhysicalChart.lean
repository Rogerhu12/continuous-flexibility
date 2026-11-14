module

public import ContinuousFlexibility.Radial.InnerMorseBufferLeading

/-!
# Independent physical dilations of the same retained Morse model

The original realization remains on its original reference profile.
A positive radius dilation and an independent positive height dilation
identify its retained buffer with a piece of the final physical chain.
The localized R09 model is unchanged. Its actual physical Dirichlet
operator, conormal diagonal and full error matrix all use this same
model and the final reference measure.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set ContinuousFlexibility.Statements
open scoped ContDiff

/-- Constant radius dilation preserves the logarithmic derivative,
including points where the radius vanishes. -/
theorem innerScaledRadius_log_deriv (R : ℝ → ℝ) {rs : ℝ} (hrs : rs ≠ 0) (x : ℝ) :
    deriv (fun y => rs * R y) x / (rs * R x) = deriv R x / R x := by
  rw [deriv_const_mul_field]
  by_cases hR : R x = 0
  · simp only [hR, mul_zero, div_zero]
  · field_simp [hrs, hR] <;> ring

/-- The second derivative ratio is invariant under the same dilation. -/
theorem innerScaledRadius_second_ratio (R : ℝ → ℝ) {rs : ℝ}
    (hrs : rs ≠ 0) (x : ℝ) :
    deriv (deriv (fun y => rs * R y)) x / (rs * R x) =
      deriv (deriv R) x / R x := by
  have hd : deriv (fun y => rs * R y) = fun y => rs * deriv R y :=
    deriv_const_mul_field' rs
  rw [hd, deriv_const_mul_field]
  by_cases hR : R x = 0
  · simp only [hR, mul_zero, div_zero]
  · field_simp [hrs, hR] <;> ring

theorem innerScaledRadius_rho_one (R : ℝ → ℝ) {rs : ℝ} (hrs : rs ≠ 0) (x : ℝ) :
    liouvilleRho (fun y => rs * R y) (fun _ => 1) x =
      liouvilleRho R (fun _ => 1) x := by
  simp only [liouvilleRho, deriv_const, mul_zero, zero_div, zero_mul, add_zero]
  simpa only [neg_div] using
    congrArg (fun z : ℝ => -z) (innerScaledRadius_second_ratio R hrs x)

section RealizedCell

variable {T : MorseChainData} {σ : ℕ → ℝ} {D₀ : ReferenceData} {cost : ℕ → ℝ}
  (hreal : MorseChainRealization T σ D₀ cost) (side : Bool) {m : ℕ}
  (hm : T.index ≤ m) {rs : ℝ} (hrs : 0 < rs)

include hreal hm hrs

theorem innerMorseScaledChain_buffer_chart_positive (x : ℝ)
    (hx : x ∈ Icc innerMorseBufferLeftCut
      (innerMorseBufferRightCut (morseChainA T m) (morseChainB T m))) :
    0 < rs * T.radius side m x ∧
      0 < deriv (fun y => rs * T.radius side m y) x ∧ 0 < (1 : ℝ) := by
  have hp := innerMorseChain_buffer_chart_positive hreal side hm x hx
  refine ⟨mul_pos hrs hp.1, ?_, zero_lt_one⟩
  rw [deriv_const_mul_field]
  exact mul_pos hrs hp.2.1

theorem innerMorseScaledChain_buffer_velocity (hindex : 10 ≤ T.index) {x : ℝ}
    (hx : x ∈ Icc innerMorseBufferLeftCut
      (innerMorseBufferRightCut (morseChainA T m) (morseChainB T m))) :
    |deriv (fun y => rs * T.radius side m y) x / (rs * T.radius side m x)| ≤ 14 := by
  rw [innerScaledRadius_log_deriv _ hrs.ne']
  exact innerMorseChain_buffer_velocity hreal side hindex hm hx

theorem innerMorseScaledChain_buffer_potential (j x : ℝ)
    (hx : x ∈ Ioo innerMorseBufferLeftCut
      (innerMorseBufferRightCut (morseChainA T m) (morseChainB T m))) :
    morsePotential j (morseChainA T m) (morseChainB T m) x =
      liouvilleV0 (fun _ => 1) x -
        j ^ 2 * liouvilleRho (fun y => rs * T.radius side m y) (fun _ => 1) x := by
  rw [innerScaledRadius_rho_one _ hrs.ne']
  exact innerMorseChain_buffer_potential hreal side hm j x hx

theorem innerMorseScaledChain_buffer_cap_ratio (hindex : 10 ≤ T.index)
    {j : ℝ} (hj : 0 < j) (B₀ : ℝ) (i : Fin 2) {x : ℝ}
    (hx : x ∈ uIcc
      (bufferCut (innerMorseBufferData (morseChainA T m) (morseChainB T m) j B₀) i)
      (bufferInnerWall (innerMorseBufferData (morseChainA T m) (morseChainB T m) j B₀) i)) :
    |deriv (fun y => rs * T.radius side m y) x / (rs * T.radius side m x)| /
      innerMorseBufferMass (morseChainA T m) (morseChainB T m) j i ≤ 30000 / j := by
  rw [innerScaledRadius_log_deriv _ hrs.ne']
  exact innerMorseChain_buffer_cap_ratio hreal side hindex hm hj B₀ i hx

end RealizedCell

section CommonChain

variable {T : MorseChainData} {σ : ℕ → ℝ} {D₀ : ReferenceData} {cost : ℕ → ℝ}
  (hreal : MorseChainRealization T σ D₀ cost) (hindex : 10 ≤ T.index)
  (D : ReferenceData) {n : ℕ} (G : InnerRadialChainGeometry D n)
  (bordered : Bool) (j : ℝ) (central piece : Fin (n + 1)) (column : RadialModeL2 D)
  (side : Bool) (m : ℕ) (hm : T.index ≤ m) (rs hs : ℝ)
  (hrs : 0 < rs) (hhs : 0 < hs)
  (hprofile : ∀ x ∈ Icc innerMorseBufferLeftCut
      (innerMorseBufferRightCut (morseChainA T m) (morseChainB T m)),
    D.w (rs * T.radius side m x) = hs * rs * D₀.w (T.radius side m x))
  (haway : piece ≠ central)
  (hleft : G.left piece = rs * innerMorseChainCut T side m 0)
  (hright : G.right piece = rs * innerMorseChainCut T side m 1)
  {C K : ℝ}
  (hB : BufferHypotheses (innerMorseBufferData (morseChainA T m) (morseChainB T m)
    j (8 * (T.d m : ℝ) ^ 9)))
  (M : InnerBufferLocalizedData
    (innerMorseBufferData (morseChainA T m) (morseChainB T m)
      j (8 * (T.d m : ℝ) ^ 9)) C K)

include hreal hm hprofile in
/-- The final profile identity has height `hs * amplitude`: the radius
dilation is already present in the derivative of the new radius. -/
theorem innerMorseScaledChain_buffer_profile (x : ℝ)
    (hx : x ∈ Icc innerMorseBufferLeftCut
      (innerMorseBufferRightCut (morseChainA T m) (morseChainB T m))) :
    D.w (rs * T.radius side m x) =
      (hs * morseChainAmplitude T σ m) * (1 : ℝ) ^ 2 *
        deriv (fun y => rs * T.radius side m y) x := by
  rw [hprofile x hx, innerMorseChain_buffer_profile hreal side hm x hx,
    deriv_const_mul_field]
  ring

/-- A scaled actual chart for the same supplied model. Neither the
physical reference nor its measure is replaced by an auxiliary one. -/
def innerMorseScaledPhysicalModelChart :
    InnerRadialModelChart D G bordered j central column piece where
  buffer := innerMorseBufferData (morseChainA T m) (morseChainB T m) j (8 * (T.d m : ℝ) ^ 9)
  buffer_hypotheses := hB
  C := C
  K := K
  localized := M
  radius := fun x => rs * T.radius side m x
  scale := fun _ => 1
  height := hs * morseChainAmplitude T σ m
  height_pos := mul_pos hhs (innerMorseChain_height_pos hreal side hm)
  radius_smooth := contDiff_const.mul (hreal.radius_smooth side m hm)
  scale_smooth := contDiff_const
  chart_pos := innerMorseScaledChain_buffer_chart_positive hreal side hm hrs
  in_core := by
    have hcore : Ioo (G.left piece) (G.right piece) ⊆ radialCore D := G.in_core piece
    simpa only [hleft, hright, innerMorseChainCut_zero, innerMorseChainCut_one,
      innerMorseBufferData] using hcore
  weight_identity := innerMorseScaledChain_buffer_profile hreal D side m hm rs hs hprofile
  U := 14
  U_nonneg := by norm_num
  log_deriv_bound := fun _ hx =>
    innerMorseScaledChain_buffer_velocity hreal side hm hrs hindex hx
  potential_identity := innerMorseScaledChain_buffer_potential hreal side hm hrs j
  left_eq := by simpa only [innerMorseChainCut_zero, innerMorseBufferData] using hleft
  right_eq := by simpa only [innerMorseChainCut_one, innerMorseBufferData] using hright
  bordered_eq := by simp only [innerMorseBufferData, if_neg haway]
  column_eq := fun hp => (haway hp).elim

@[simp] theorem innerMorseScaledPhysicalModelChart_localized :
    (innerMorseScaledPhysicalModelChart hreal hindex D G bordered j central piece column
      side m hm rs hs hrs hhs hprofile haway hleft hright hB M).localized = M := rfl

/-- The diagonal is the physical normalization of this same model's
inward energies; the constant scale has zero drift. -/
theorem innerMorseScaledPhysicalModelChart_kappa (i : Fin 2) :
    (innerMorseScaledPhysicalModelChart hreal hindex D G bordered j central piece column
      side m hm rs hs hrs hhs hprofile haway hleft hright hB M).kappa i =
        innerPhysicalCutKappa (hs * morseChainAmplitude T σ m) (fun _ => 1)
          (fun k => (M.column k).inwardEnergy) i := by
  simp only [innerMorseScaledPhysicalModelChart, InnerRadialModelChart.kappa,
    innerPhysicalCutKappa, innerLiouvilleBoundaryKappa, innerLiouvilleBoundaryDrift,
    deriv_const, mul_zero, zero_div, add_zero]

/-- All entries, including the off-diagonal conormal error, use the
same model and the same physical height. -/
theorem innerMorseScaledPhysicalModelChart_errorMatrix :
    (innerMorseScaledPhysicalModelChart hreal hindex D G bordered j central piece column
      side m hm rs hs hrs hhs hprofile haway hleft hright hB M).errorMatrix =
        M.physicalFluxError (hs * morseChainAmplitude T σ m) (fun _ => 1) := rfl

theorem innerMorseScaledPhysicalModelChart_dirichlet_cost (hj : 1 ≤ j) (hC : 0 ≤ C) :
    ‖(innerMorseScaledPhysicalModelChart hreal hindex D G bordered j central piece column
      side m hm rs hs hrs hhs hprofile haway hleft hright hB M).dirichlet‖ ≤
        innerMorseDirichletConstant C * radialE m ^ (36 : ℝ) := by
  dsimp only [innerMorseScaledPhysicalModelChart, InnerRadialModelChart.dirichlet]
  exact innerMorseHilbertDirichlet_cost D T m (hreal.d_eq m hm) hj hC hB M
    hB.1.le (mul_pos hhs (innerMorseChain_height_pos hreal side hm))
    (contDiff_const.mul (hreal.radius_smooth side m hm)) contDiff_const
    (innerMorseScaledChain_buffer_chart_positive hreal side hm hrs)
    (by
      have hcore : Ioo (G.left piece) (G.right piece) ⊆ radialCore D := G.in_core piece
      simpa only [hleft, hright, innerMorseChainCut_zero, innerMorseChainCut_one,
        innerMorseBufferData] using hcore)
    (innerMorseScaledChain_buffer_profile hreal D side m hm rs hs hprofile)
    (fun _ hx => innerMorseScaledChain_buffer_velocity hreal side hm hrs hindex hx)

end CommonChain

end ContinuousFlexibility.Radial
