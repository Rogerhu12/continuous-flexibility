import ContinuousFlexibility.Radial.SelectedRetainedMorseProfile
import ContinuousFlexibility.Radial.InnerMorsePhysicalChart

/-!
# Actual Morse charts on the retained reference

The radius is dilated by the factor of its own side and the Liouville
height is multiplied by that side's height factor. The original model,
its localized inverse, and its columns are unchanged. The coefficient
identity is proved on the new physical profile, without assuming that
the whole new reference realizes the original Morse chain.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set ContinuousFlexibility.Statements
open scoped ContDiff

namespace SeedRetainedPair

variable {S : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ}
  (P : SeedRetainedPair S K q length) {D : ReferenceData}
  (hw : D.w = P.pair.profile) (hS : IsSelectedTail S)
  (G₀ : MorseChainGeometryWitness S.chain)
  (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
  {n : ℕ} (H : InnerRadialChainGeometry D n) (bordered : Bool) (j : ℝ)
  (central piece : Fin (n + 1)) (column : RadialModeL2 D)
  (side : Bool) (m : ℕ) (hm : S.chain.index ≤ m) (haway : piece ≠ central)
  (hleft : H.left piece = P.sideRadius side * innerMorseChainCut S.chain side m 0)
  (hright : H.right piece = P.sideRadius side * innerMorseChainCut S.chain side m 1)
  {Cmodel Kmodel : ℝ}
  (hB : BufferHypotheses
    (innerMorseBufferData (morseChainA S.chain m) (morseChainB S.chain m)
      j (8 * (S.chain.d m : ℝ) ^ 9)))
  (M : InnerBufferLocalizedData
    (innerMorseBufferData (morseChainA S.chain m) (morseChainB S.chain m)
      j (8 * (S.chain.d m : ℝ) ^ 9)) Cmodel Kmodel)

private theorem retainedMorse_radius_potential
    (x : ℝ) (hx : x ∈ Ioo innerMorseBufferLeftCut
      (innerMorseBufferRightCut (morseChainA S.chain m) (morseChainB S.chain m))) :
    morsePotential j (morseChainA S.chain m) (morseChainB S.chain m) x =
      liouvilleV0 (fun _ => 1) x -
        j ^ 2 * liouvilleRho (fun y => P.sideRadius side * S.chain.radius side m y)
          (fun _ => 1) x := by
  have hreal := (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hpos := hreal.radius_positive side m hm x
    (innerMorseChain_buffer_subset hreal side hm (Ioo_subset_Icc_self hx))
  have hderiv : deriv (fun y => P.sideRadius side * S.chain.radius side m y) =
      fun y => P.sideRadius side * deriv (S.chain.radius side m) y :=
    funext (fun y => deriv_const_mul_field _ _)
  have hρ : liouvilleRho (fun y => P.sideRadius side * S.chain.radius side m y)
      (fun _ => 1) x = liouvilleRho (S.chain.radius side m) (fun _ => 1) x := by
    unfold liouvilleRho
    rw [hderiv, deriv_const_mul_field]
    simp only [deriv_const, mul_zero, zero_div, zero_mul, add_zero]
    field_simp [(P.sideRadius_pos side).ne', hpos.ne']
    <;> ring
  rw [hρ]
  exact innerMorseChain_buffer_potential hreal side hm j x hx

/-- The original localized Morse witness, transported to this same
retained reference and to its actual physical cuts. -/
def retainedMorseModelChart :
    InnerRadialModelChart D H bordered j central column piece where
  buffer := innerMorseBufferData (morseChainA S.chain m) (morseChainB S.chain m)
    j (8 * (S.chain.d m : ℝ) ^ 9)
  buffer_hypotheses := hB
  C := Cmodel
  K := Kmodel
  localized := M
  radius := fun x => P.sideRadius side * S.chain.radius side m x
  scale := fun _ => 1
  height := P.sideHeight side * morseChainAmplitude S.chain S.sigma m
  height_pos := mul_pos (P.sideHeight_pos side)
    (innerMorseChain_height_pos (hS.2.2.2.1 S.sigma hS.2.2.1).1 side hm)
  radius_smooth := contDiff_const.mul
    ((hS.2.2.2.1 S.sigma hS.2.2.1).1.radius_smooth side m hm)
  scale_smooth := contDiff_const
  chart_pos := by
    intro x hx
    have hp := innerMorseChain_buffer_chart_positive
      (hS.2.2.2.1 S.sigma hS.2.2.1).1 side hm x hx
    refine ⟨mul_pos (P.sideRadius_pos side) hp.1, ?_, hp.2.2⟩
    rw [deriv_const_mul_field]
    exact mul_pos (P.sideRadius_pos side) hp.2.1
  in_core := by
    have hcore := H.in_core piece
    simpa only [hleft, hright, innerMorseChainCut_zero, innerMorseChainCut_one,
      innerMorseBufferData] using hcore
  weight_identity := by
    intro x hx
    simp only [one_pow, mul_one, deriv_const_mul_field]
    exact P.reference_morse_cell_profile hw hS G₀ hband side hm
      (innerMorseChain_buffer_subset (hS.2.2.2.1 S.sigma hS.2.2.1).1 side hm hx)
  U := 14
  U_nonneg := by norm_num
  log_deriv_bound := by
    intro x hx
    have hreal := (hS.2.2.2.1 S.sigma hS.2.2.1).1
    have hpos := hreal.radius_positive side m hm x
      (innerMorseChain_buffer_subset hreal side hm hx)
    have he : (P.sideRadius side * deriv (S.chain.radius side m) x) /
        (P.sideRadius side * S.chain.radius side m x) =
        deriv (S.chain.radius side m) x / S.chain.radius side m x := by
      field_simp [(P.sideRadius_pos side).ne', hpos.ne']
    rw [deriv_const_mul_field, he]
    exact innerMorseChain_buffer_velocity hreal side
      ((by norm_num : 10 ≤ 100).trans G₀.start_large) hm hx
  potential_identity := P.retainedMorse_radius_potential hS j side m hm
  left_eq := by simpa only [innerMorseChainCut_zero, innerMorseBufferData] using hleft
  right_eq := by simpa only [innerMorseChainCut_one, innerMorseBufferData] using hright
  bordered_eq := by simp only [innerMorseBufferData, if_neg haway]
  column_eq := fun hp => (haway hp).elim

theorem retainedMorseModelChart_kappa (i : Fin 2) :
    (P.retainedMorseModelChart hw hS G₀ hband H bordered j central piece column
      side m hm haway hleft hright hB M).kappa i =
      (P.sideHeight side * morseChainAmplitude S.chain S.sigma m) *
        (M.column i).inwardEnergy := by
  simp only [retainedMorseModelChart, InnerRadialModelChart.kappa,
    innerLiouvilleBoundaryKappa, one_pow, mul_one]

theorem retainedMorseModelChart_errorMatrix :
    (P.retainedMorseModelChart hw hS G₀ hband H bordered j central piece column
      side m hm haway hleft hright hB M).errorMatrix =
      M.physicalFluxError (P.sideHeight side * morseChainAmplitude S.chain S.sigma m)
        (fun _ => 1) := rfl

theorem retainedMorseModelChart_dirichlet_cost (hj : 1 ≤ j) (hC : 0 ≤ Cmodel) :
    ‖(P.retainedMorseModelChart hw hS G₀ hband H bordered j central piece column
      side m hm haway hleft hright hB M).dirichlet‖ ≤
        innerMorseDirichletConstant Cmodel * radialE m ^ (36 : ℝ) := by
  let A := P.retainedMorseModelChart hw hS G₀ hband H bordered j central piece column
    side m hm haway hleft hright hB M
  exact innerMorseHilbertDirichlet_cost D S.chain m
    ((hS.2.2.2.1 S.sigma hS.2.2.1).1.d_eq m hm) hj hC hB M
    hB.1.le A.height_pos A.radius_smooth A.scale_smooth A.chart_pos A.in_core
    A.weight_identity A.log_deriv_bound

end SeedRetainedPair

end ContinuousFlexibility.Radial
