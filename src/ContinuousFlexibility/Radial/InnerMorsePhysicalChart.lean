module

public import ContinuousFlexibility.Radial.InnerRadialActualPieces
public import ContinuousFlexibility.Radial.InnerMorseTailGeometry

/-!
# The actual retained Morse models in the common physical chain

The original realization supplies the radius, its positive speed, the
height identity, the differential coefficient, and the retained velocity
bound. The only endpoint data below identify the chosen physical cuts
with their positions in the finite chain. No physical local inverse,
Poisson equation, or norm estimate is an additional input.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set ContinuousFlexibility.Statements
open scoped ContDiff

section RealizedCell

variable {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {cost : ℕ → ℝ}
  (hreal : MorseChainRealization T σ D cost) (side : Bool) {m : ℕ} (hm : T.index ≤ m)

include hreal side hm

theorem innerMorseChain_buffer_subset :
    Icc innerMorseBufferLeftCut (innerMorseBufferRightCut (morseChainA T m) (morseChainB T m)) ⊆
      Icc (T.leftX side m) (T.rightX side m) := by
  obtain ⟨hl, hr⟩ := innerMorseChain_retained_endpoints hreal side hm
  rw [hl, hr]
  exact innerMorseBufferInterval_subset (hreal.retained_data side m hm).1
    (hreal.retained_data side m hm).2.1

theorem innerMorseChain_height_pos : 0 < morseChainAmplitude T σ m := by
  obtain ⟨hB, hAB, _, hlt, hgt, _, _⟩ := hreal.retained_data side m hm
  have hx : morseChainRightTurn T m ∈ Icc (T.leftX side m) (T.rightX side m) :=
    ⟨hlt.le, hgt.le⟩
  apply (mul_pos_iff_of_pos_right
    (hreal.derivative_positive side m hm _ hx)).mp
  rw [← hreal.profile_eq side m hm _ hx]
  exact hreal.geometry.2.2.2.2.1 _ (hreal.radius_mem_core side m hm _ hx)

theorem innerMorseChain_buffer_chart_positive (x : ℝ)
    (hx : x ∈ Icc innerMorseBufferLeftCut
      (innerMorseBufferRightCut (morseChainA T m) (morseChainB T m))) :
    0 < T.radius side m x ∧ 0 < deriv (T.radius side m) x ∧ 0 < (1 : ℝ) := by
  have hwhole := innerMorseChain_buffer_subset hreal side hm hx
  exact ⟨hreal.radius_positive side m hm x hwhole,
    hreal.derivative_positive side m hm x hwhole, zero_lt_one⟩

theorem innerMorseChain_buffer_profile (x : ℝ)
    (hx : x ∈ Icc innerMorseBufferLeftCut
      (innerMorseBufferRightCut (morseChainA T m) (morseChainB T m))) :
    D.w (T.radius side m x) = morseChainAmplitude T σ m * (1 : ℝ) ^ 2 *
      deriv (T.radius side m) x := by
  simpa only [one_pow, mul_one] using
    hreal.profile_eq side m hm x (innerMorseChain_buffer_subset hreal side hm hx)

/-- The actual Liouville coefficient is exactly the Morse potential;
the original increasing chart is used on either tail. -/
theorem innerMorseChain_buffer_potential (j : ℝ) (x : ℝ)
    (hx : x ∈ Ioo innerMorseBufferLeftCut
      (innerMorseBufferRightCut (morseChainA T m) (morseChainB T m))) :
    morsePotential j (morseChainA T m) (morseChainB T m) x =
      liouvilleV0 (fun _ => 1) x - j ^ 2 * liouvilleRho (T.radius side m) (fun _ => 1) x := by
  have hwhole := innerMorseChain_buffer_subset hreal side hm (Ioo_subset_Icc_self hx)
  have hRpos := hreal.radius_positive side m hm x hwhole
  have hρ : liouvilleRho (T.radius side m) (fun _ => 1) x =
      morseRho (morseChainA T m) (morseChainB T m) x := by
    simp only [liouvilleRho, deriv_const, mul_zero, zero_div, zero_mul, add_zero,
      hreal.equation side m hm x hwhole, neg_mul, neg_neg]
    exact mul_div_cancel_right₀ _ hRpos.ne'
  have hderiv : deriv (fun _ : ℝ => (1 : ℝ)) = fun _ => 0 :=
    funext (fun _ => deriv_const _ _)
  simp only [liouvilleV0, hderiv, deriv_const, zero_div, hρ, zero_sub, morsePotential,
    neg_mul]

end RealizedCell

section CommonChain

variable {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {cost : ℕ → ℝ}
  (hreal : MorseChainRealization T σ D cost) (hindex : 10 ≤ T.index)
  {n : ℕ} (G : InnerRadialChainGeometry D n) (bordered : Bool) (j : ℝ)
  (central piece : Fin (n + 1)) (column : RadialModeL2 D)
  (side : Bool) (m : ℕ) (hm : T.index ≤ m) (haway : piece ≠ central)
  (hleft : G.left piece = innerMorseChainCut T side m 0)
  (hright : G.right piece = innerMorseChainCut T side m 1)
  {C K : ℝ}
  (hB : BufferHypotheses (innerMorseBufferData (morseChainA T m) (morseChainB T m)
    j (8 * (T.d m : ℝ) ^ 9)))
  (M : InnerBufferLocalizedData
    (innerMorseBufferData (morseChainA T m) (morseChainB T m)
      j (8 * (T.d m : ℝ) ^ 9)) C K)

/-- The same compressed Morse model as an actual physical piece. All
chart and coefficient fields are proved from the original realization. -/
def innerMorsePhysicalModelChart :
    InnerRadialModelChart D G bordered j central column piece where
  buffer := innerMorseBufferData (morseChainA T m) (morseChainB T m) j (8 * (T.d m : ℝ) ^ 9)
  buffer_hypotheses := hB
  C := C
  K := K
  localized := M
  radius := T.radius side m
  scale := fun _ => 1
  height := morseChainAmplitude T σ m
  height_pos := innerMorseChain_height_pos hreal side hm
  radius_smooth := hreal.radius_smooth side m hm
  scale_smooth := contDiff_const
  chart_pos := innerMorseChain_buffer_chart_positive hreal side hm
  in_core := by
    have hcore : Ioo (G.left piece) (G.right piece) ⊆ radialCore D := G.in_core piece
    simpa only [hleft, hright, innerMorseChainCut_zero, innerMorseChainCut_one,
      innerMorseBufferData] using hcore
  weight_identity := innerMorseChain_buffer_profile hreal side hm
  U := 14
  U_nonneg := by norm_num
  log_deriv_bound := fun _ hx => innerMorseChain_buffer_velocity hreal side hindex hm hx
  potential_identity := innerMorseChain_buffer_potential hreal side hm j
  left_eq := by simpa only [innerMorseChainCut_zero, innerMorseBufferData] using hleft
  right_eq := by simpa only [innerMorseChainCut_one, innerMorseBufferData] using hright
  bordered_eq := by simp only [innerMorseBufferData, if_neg haway]
  column_eq := fun hp => (haway hp).elim

/-- The norm bound is for precisely the operator stored in the actual
piece dictionary, with the fixed exponent thirty-six. -/
theorem innerMorsePhysicalModelChart_dirichlet_cost (hj : 1 ≤ j) (hC : 0 ≤ C) :
    ‖(innerMorsePhysicalModelChart hreal hindex G bordered j central piece column
      side m hm haway hleft hright hB M).dirichlet‖ ≤
        innerMorseDirichletConstant C * radialE m ^ (36 : ℝ) := by
  dsimp only [innerMorsePhysicalModelChart, InnerRadialModelChart.dirichlet]
  exact innerMorseHilbertDirichlet_cost D T m (hreal.d_eq m hm) hj hC hB M
    hB.1.le (innerMorseChain_height_pos hreal side hm) (hreal.radius_smooth side m hm)
    contDiff_const (innerMorseChain_buffer_chart_positive hreal side hm)
    (by
      have hcore : Ioo (G.left piece) (G.right piece) ⊆ radialCore D := G.in_core piece
      simpa only [hleft, hright, innerMorseChainCut_zero, innerMorseChainCut_one,
        innerMorseBufferData] using hcore)
    (innerMorseChain_buffer_profile hreal side hm)
    (fun _ hx => innerMorseChain_buffer_velocity hreal side hindex hm hx)

end CommonChain

end ContinuousFlexibility.Radial
