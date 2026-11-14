module

public import ContinuousFlexibility.Geometry.CapDisk
public import ContinuousFlexibility.Geometry.SurfaceGeometry
public import Mathlib.Analysis.Matrix.Normed

/-!
# The actual smooth unit normal of the meridian cap

The integrated meridian tangent determines a normal which is upward on the
attaching collar and downward on the bottom disk. Its Cartesian expression
extends smoothly across the axis because it is exactly constant there.
Orthogonality is proved for the actual derivative of `capDiskMap`, using the
surjective polar Jacobian away from the axis. Identification as the outward
normal of a closed surface requires the separate inside-region construction.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false

def capRevolutionNormal (L : ℝ) (x : PolarPoint) : E3 :=
  graphMap (fun q => (capDownwardVelocity (q.1 / L) * Real.cos q.2,
    capDownwardVelocity (q.1 / L) * Real.sin q.2))
    (fun q => capRadialVelocity (q.1 / L)) x

def capDiskNormal (R L : ℝ) : PolarPoint → E3 :=
  graphMap (fun y => (capDownwardVelocity (capDiskParameter R L y / L) /
    cartesianRadius y) • y)
    (fun y => capRadialVelocity (capDiskParameter R L y / L))

@[simp] theorem capRevolutionNormal_zero (L : ℝ) (x : PolarPoint) :
    capRevolutionNormal L x 0 = capDownwardVelocity (x.1 / L) * Real.cos x.2 := by
  simp [capRevolutionNormal]

@[simp] theorem capRevolutionNormal_one (L : ℝ) (x : PolarPoint) :
    capRevolutionNormal L x 1 = capDownwardVelocity (x.1 / L) * Real.sin x.2 := by
  simp [capRevolutionNormal]

@[simp] theorem capRevolutionNormal_two (L : ℝ) (x : PolarPoint) :
    capRevolutionNormal L x 2 = capRadialVelocity (x.1 / L) := by
  simp [capRevolutionNormal]

@[simp] theorem capDiskNormal_zero (R L : ℝ) (y : PolarPoint) :
    capDiskNormal R L y 0 =
      capDownwardVelocity (capDiskParameter R L y / L) / cartesianRadius y * y.1 := by
  simp [capDiskNormal]

@[simp] theorem capDiskNormal_one (R L : ℝ) (y : PolarPoint) :
    capDiskNormal R L y 1 =
      capDownwardVelocity (capDiskParameter R L y / L) / cartesianRadius y * y.2 := by
  simp [capDiskNormal]

@[simp] theorem capDiskNormal_two (R L : ℝ) (y : PolarPoint) :
    capDiskNormal R L y 2 = capRadialVelocity (capDiskParameter R L y / L) := by
  simp [capDiskNormal]

theorem contDiff_capRevolutionNormal (L : ℝ) : ContDiff ℝ ∞ (capRevolutionNormal L) := by
  have hd : ContDiff ℝ ∞ (fun q : PolarPoint => capDownwardVelocity (q.1 / L)) :=
    contDiff_capDownwardVelocity.comp (contDiff_fst.div_const L)
  exact contDiff_graphMap ((hd.mul contDiff_snd.cos).prodMk (hd.mul contDiff_snd.sin))
    (contDiff_capRadialVelocity.comp (contDiff_fst.div_const L))

theorem capRevolutionNormal_inner_self (L : ℝ) (x : PolarPoint) :
    inner ℝ (capRevolutionNormal L x) (capRevolutionNormal L x) = 1 := by
  rw [e3_inner_coordinates]
  simp only [capRevolutionNormal_zero, capRevolutionNormal_one, capRevolutionNormal_two]
  have ht := Real.cos_sq_add_sin_sq x.2
  have hv : capRadialVelocity (x.1 / L) ^ 2 + capDownwardVelocity (x.1 / L) ^ 2 = 1 := by
    dsimp [capRadialVelocity, capDownwardVelocity]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * capTurn (x.1 / L))]
  linear_combination capDownwardVelocity (x.1 / L) ^ 2 * ht + hv

theorem capRevolutionNormal_norm (L : ℝ) (x : PolarPoint) :
    ‖capRevolutionNormal L x‖ = 1 := by
  have hh := capRevolutionNormal_inner_self L x
  rw [real_inner_self_eq_norm_sq] at hh
  nlinarith [norm_nonneg (capRevolutionNormal L x)]

theorem capRevolutionNormal_orthogonal (R h : ℝ) {L : ℝ} (hL : 0 < L)
    (x v : PolarPoint) :
    inner ℝ (fderiv ℝ (capRevolution R h L) x v) (capRevolutionNormal L x) = 0 := by
  rw [capRevolution_fderiv R h hL, e3_inner_coordinates]
  simp [e3Basis]
  linear_combination capRadialVelocity (x.1 / L) * capDownwardVelocity (x.1 / L) *
    v.1 * Real.cos_sq_add_sin_sq x.2

theorem isUnitSurfaceNormal_capRevolution (R h : ℝ) {L : ℝ} (hL : 0 < L)
    (x : PolarPoint) :
    IsUnitSurfaceNormal (capRevolution R h L) x (capRevolutionNormal L x) :=
  ⟨capRevolutionNormal_norm L x, capRevolutionNormal_orthogonal R h hL x⟩

theorem capDiskNormal_top_collar (R : ℝ) {L : ℝ} (hL : 0 < L)
    {y : PolarPoint} (hy : capDiskParameter R L y ≤ L / 4) :
    capDiskNormal R L y = e3Basis 2 := by
  have ht : capDiskParameter R L y / L ≤ 1 / 4 := (div_le_iff₀ hL).2 (by linarith)
  simp [capDiskNormal, graphMap, capDownwardVelocity_eq_zero_left ht,
    capRadialVelocity_eq_one ht]

theorem capDiskNormal_bottom_collar (R : ℝ) {L : ℝ} (hL : 0 < L)
    {y : PolarPoint} (hy : 3 * L / 4 ≤ capDiskParameter R L y) :
    capDiskNormal R L y = -e3Basis 2 := by
  have ht : 3 / 4 ≤ capDiskParameter R L y / L := (le_div_iff₀ hL).2 (by linarith)
  simp [capDiskNormal, graphMap, capDownwardVelocity_eq_zero_right ht,
    capRadialVelocity_eq_neg_one ht]

theorem capDiskNormal_axis_neighborhood {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    {y : PolarPoint} (hy : cartesianRadius y < 1 / 4) :
    capDiskNormal R L y = -e3Basis 2 :=
  capDiskNormal_bottom_collar R hL (capDisk_axis_parameter hR hL hy)

theorem capDiskNormal_axis {R L : ℝ} (hR : 0 < R) (hL : 0 < L) :
    capDiskNormal R L 0 = -e3Basis 2 :=
  capDiskNormal_axis_neighborhood hR hL (by norm_num [cartesianRadius])

theorem capDiskNormal_axis_germ {R L : ℝ} (hR : 0 < R) (hL : 0 < L) :
    capDiskNormal R L =ᶠ[𝓝 0] fun _ => -e3Basis 2 := by
  have hn : {y : PolarPoint | cartesianRadius y < (1 / 4 : ℝ)} ∈ 𝓝 0 :=
    (isOpen_lt continuous_cartesianRadius continuous_const).mem_nhds
      (by norm_num [cartesianRadius])
  filter_upwards [hn] with y hy
  exact capDiskNormal_axis_neighborhood hR hL hy

theorem contDiff_capDiskNormal {R L : ℝ} (hR : 0 < R) (hL : 0 < L) :
    ContDiff ℝ ∞ (capDiskNormal R L) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : y = 0
  · subst y
    exact contDiffAt_const.congr_of_eventuallyEq (capDiskNormal_axis_germ hR hL)
  · have hρ := contDiffAt_cartesianRadius hy
    have hs : ContDiffAt ℝ ∞ (fun y => capDiskParameter R L y / L) y :=
      (contDiffAt_const.mul (contDiffAt_const.sub hρ)).div_const L
    apply contDiffAt_graphMap
    · exact ((contDiff_capDownwardVelocity.contDiffAt.comp y hs).div hρ
        (cartesianRadius_pos hy).ne').smul contDiffAt_id
    · exact contDiff_capRadialVelocity.contDiffAt.comp y hs

theorem capDiskNormal_polarMap (R L : ℝ) {p : PolarPoint} (hp : 0 < p.1) :
    capDiskNormal R L (polarMap p) =
      capRevolutionNormal L ((L + R) * (1 - p.1), p.2) := by
  have hρ : cartesianRadius (polarMap p) = p.1 := cartesianRadius_polarPosition hp p.2
  ext i
  fin_cases i
  · change capDiskNormal R L (polarMap p) 0 =
      capRevolutionNormal L ((L + R) * (1 - p.1), p.2) 0
    rw [capDiskNormal_zero, capRevolutionNormal_zero]
    unfold capDiskParameter
    rw [hρ]
    simp only [polarMap, polarPosition]
    field_simp [hp.ne']
  · change capDiskNormal R L (polarMap p) 1 =
      capRevolutionNormal L ((L + R) * (1 - p.1), p.2) 1
    rw [capDiskNormal_one, capRevolutionNormal_one]
    unfold capDiskParameter
    rw [hρ]
    simp only [polarMap, polarPosition]
    field_simp [hp.ne']
  · change capDiskNormal R L (polarMap p) 2 =
      capRevolutionNormal L ((L + R) * (1 - p.1), p.2) 2
    rw [capDiskNormal_two, capRevolutionNormal_two]
    unfold capDiskParameter
    rw [hρ]

theorem capDiskNormal_norm {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    (y : PolarPoint) : ‖capDiskNormal R L y‖ = 1 := by
  by_cases hy : y = 0
  · subst y
    rw [capDiskNormal_axis hR hL]
    simp [e3Basis]
  · let p : PolarPoint := (cartesianRadius y, (Complex.equivRealProdCLM.symm y).arg)
    have hp : polarMap p = y := polarMap_cartesianCoordinates y
    rw [← hp, capDiskNormal_polarMap R L (cartesianRadius_pos hy)]
    exact capRevolutionNormal_norm L _

theorem capDiskNormal_orthogonal {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    (h : ℝ) (y v : PolarPoint) :
    inner ℝ (fderiv ℝ (capDiskMap R h L) y v) (capDiskNormal R L y) = 0 := by
  by_cases hy : y = 0
  · subst y
    rw [(hasFDerivAt_capDiskMap_axis hR hL h).fderiv, capDiskNormal_axis hR hL,
      e3_inner_coordinates]
    simp [e3Basis]
  · let S : ℝ := L + R
    let p : PolarPoint := (cartesianRadius y, (Complex.equivRealProdCLM.symm y).arg)
    have hpρ : 0 < p.1 := cartesianRadius_pos hy
    have hp : polarMap p = y := polarMap_cartesianCoordinates y
    let T : PolarPoint → PolarPoint := fun q => (S * (1 - q.1), q.2)
    let J : PolarPoint →L[ℝ] PolarPoint :=
      ((-S) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)
    have hfst : HasFDerivAt (fun q : PolarPoint => q.1)
        (ContinuousLinearMap.fst ℝ ℝ ℝ) p := hasFDerivAt_fst
    have hsnd : HasFDerivAt (fun q : PolarPoint => q.2)
        (ContinuousLinearMap.snd ℝ ℝ ℝ) p := hasFDerivAt_snd
    have hT : HasFDerivAt T J p := by
      have h1 : HasFDerivAt (fun q : PolarPoint => S * (1 - q.1))
          ((-S) • ContinuousLinearMap.fst ℝ ℝ ℝ) p := by
        convert! (((hasFDerivAt_const (1 : ℝ) p).sub hfst).const_mul S) using 1
        apply ContinuousLinearMap.ext
        intro w
        simp
      exact h1.prodMk hsnd
    have heq : (capDiskMap R h L ∘ polarMap) =ᶠ[𝓝 p] (capRevolution R h L ∘ T) :=
      capDiskMap_polar_germ R h L hpρ
    have hD : DifferentiableAt ℝ (capDiskMap R h L) (polarMap p) :=
      (contDiff_capDiskMap hR hL h).differentiable (by simp) _
    have hdleft := hD.hasFDerivAt.comp p (hasFDerivAt_polarMap p)
    have hdright := ((contDiff_capRevolution R h L).differentiable
      (by simp) (T p)).hasFDerivAt.comp p hT
    have hder := heq.fderiv_eq (𝕜 := ℝ)
    rw [hdleft.fderiv, hdright.fderiv, hp] at hder
    have hN : capDiskNormal R L y = capRevolutionNormal L (T p) := by
      rw [← hp]
      exact capDiskNormal_polarMap R L hpρ
    obtain ⟨w, hw⟩ := (polarJacobian_bijective hpρ.ne').surjective v
    have hv := congrArg (fun A : PolarPoint →L[ℝ] E3 => A w) hder
    simp only [ContinuousLinearMap.comp_apply, hw] at hv
    rw [hv, hN]
    exact capRevolutionNormal_orthogonal R h hL (T p) (J w)

theorem isUnitSurfaceNormal_capDisk {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    (h : ℝ) (y : PolarPoint) :
    IsUnitSurfaceNormal (capDiskMap R h L) y (capDiskNormal R L y) :=
  ⟨capDiskNormal_norm hR hL y, capDiskNormal_orthogonal hR hL h y⟩

private theorem cap_contDiff_gram_entry {F : PolarPoint → E3}
    (hF : ContDiff ℝ ∞ F) (i j : Fin 2) :
    ContDiff ℝ ∞ (fun y => surfaceGram F y i j) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by simp)
  exact (hd.clm_apply contDiff_const).inner ℝ (hd.clm_apply contDiff_const)

private theorem cap_contDiff_second_entry {F N : PolarPoint → E3}
    (hF : ContDiff ℝ ∞ F) (hN : ContDiff ℝ ∞ N) (i j : Fin 2) :
    ContDiff ℝ ∞ (fun y => surfaceSecondMatrix F (N y) y i j) := by
  have hd₁ : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by simp)
  have hd : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ F)) := hd₁.fderiv_right (by simp)
  exact ((hd.clm_apply contDiff_const).clm_apply contDiff_const).inner ℝ hN

private theorem cap_contDiffAt_shape_entry {F N : PolarPoint → E3}
    (hF : ContDiff ℝ ∞ F) (hN : ContDiff ℝ ∞ N) {x : PolarPoint}
    (hi : Function.Injective (fderiv ℝ F x)) (i j : Fin 2) :
    ContDiffAt ℝ ∞ (fun y => surfaceShapeMatrix F (N y) y i j) x := by
  have hg := cap_contDiff_gram_entry hF
  have hb := cap_contDiff_second_entry hF hN
  have hdet : ContDiff ℝ ∞ (fun y => (surfaceGram F y).det) := by
    simp only [Matrix.det_fin_two]
    exact ((hg 0 0).mul (hg 1 1)).sub ((hg 0 1).mul (hg 1 0))
  have hadj (a b : Fin 2) :
      ContDiff ℝ ∞ (fun y => (surfaceGram F y).adjugate a b) := by
    simp only [Matrix.adjugate_fin_two]
    fin_cases a <;> fin_cases b
    · simpa using hg 1 1
    · simpa using (hg 0 1).neg
    · simpa using (hg 1 0).neg
    · simpa using hg 0 0
  have hinv (a b : Fin 2) :
      ContDiffAt ℝ ∞ (fun y => (surfaceGram F y)⁻¹ a b) x := by
    simp only [Matrix.inv_def, Ring.inverse_eq_inv]
    exact (hdet.contDiffAt.inv (surfaceGram_det_pos hi).ne').mul (hadj a b).contDiffAt
  simp only [surfaceShapeMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  exact ((hinv i 0).mul (hb 0 j).contDiffAt).add ((hinv i 1).mul (hb 1 j).contDiffAt)

/-- Smoothness of the actual shape matrix holds in a neighborhood of each
point of the closed cap disk, by the already proved immersion. -/
theorem contDiffAt_capDiskShapeMatrix {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    (h : ℝ) {x : PolarPoint} (hx : cartesianRadius x ≤ 1) :
    ContDiffAt ℝ ∞ (fun y => surfaceShapeMatrix
      (capDiskMap R h L) (capDiskNormal R L y) y) x := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  exact cap_contDiffAt_shape_entry (contDiff_capDiskMap hR hL h)
    (contDiff_capDiskNormal hR hL) (capDiskMap_fderiv_injective hR hL h hx) i j

theorem contDiffAt_capDiskGaussianCurvature {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    (h : ℝ) {x : PolarPoint} (hx : cartesianRadius x ≤ 1) :
    ContDiffAt ℝ ∞ (fun y => surfaceGaussianCurvature
      (capDiskMap R h L) (capDiskNormal R L y) y) x := by
  have hs (i j : Fin 2) := contDiffAt_pi.mp
    (contDiffAt_pi.mp (contDiffAt_capDiskShapeMatrix hR hL h hx) i) j
  simp only [surfaceGaussianCurvature, Matrix.det_fin_two]
  exact ((hs 0 0).mul (hs 1 1)).sub ((hs 0 1).mul (hs 1 0))

theorem contDiffAt_capDiskMeanCurvature {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    (h : ℝ) {x : PolarPoint} (hx : cartesianRadius x ≤ 1) :
    ContDiffAt ℝ ∞ (fun y => surfaceMeanCurvature
      (capDiskMap R h L) (capDiskNormal R L y) y) x := by
  have hs (i j : Fin 2) := contDiffAt_pi.mp
    (contDiffAt_pi.mp (contDiffAt_capDiskShapeMatrix hR hL h hx) i) j
  simp only [surfaceMeanCurvature, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two]
  exact ((hs 0 0).add (hs 1 1)).div_const 2

theorem contDiffOn_capDiskGaussianCurvature {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    (h : ℝ) : ContDiffOn ℝ ∞ (fun y => surfaceGaussianCurvature
      (capDiskMap R h L) (capDiskNormal R L y) y) {y | cartesianRadius y ≤ 1} :=
  fun _ hy => (contDiffAt_capDiskGaussianCurvature hR hL h hy).contDiffWithinAt

theorem contDiffOn_capDiskMeanCurvature {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    (h : ℝ) : ContDiffOn ℝ ∞ (fun y => surfaceMeanCurvature
      (capDiskMap R h L) (capDiskNormal R L y) y) {y | cartesianRadius y ≤ 1} :=
  fun _ hy => (contDiffAt_capDiskMeanCurvature hR hL h hy).contDiffWithinAt

/-- A genuine compactness bound for both actual curvatures of this fixed cap.
The bound is an output, not an input to the cap construction. -/
theorem capDisk_curvature_uniform_bound {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    (h : ℝ) : ∃ C : ℝ, 0 < C ∧ ∀ y : PolarPoint, cartesianRadius y ≤ 1 →
      |surfaceGaussianCurvature (capDiskMap R h L) (capDiskNormal R L y) y| ≤ C ∧
      |surfaceMeanCurvature (capDiskMap R h L) (capDiskNormal R L y) y| ≤ C := by
  have hc : ContinuousOn (fun y =>
      |surfaceGaussianCurvature (capDiskMap R h L) (capDiskNormal R L y) y| +
      |surfaceMeanCurvature (capDiskMap R h L) (capDiskNormal R L y) y|)
      {y : PolarPoint | cartesianRadius y ≤ 1} :=
    ((contDiffOn_capDiskGaussianCurvature hR hL h).continuousOn.abs).add
      (contDiffOn_capDiskMeanCurvature hR hL h).continuousOn.abs
  obtain ⟨B, hB⟩ := isCompact_capDiskDomain_set.bddAbove_image hc
  refine ⟨|B| + 1, by positivity, ?_⟩
  intro y hy
  have hb := hB (Set.mem_image_of_mem _ hy)
  have hba : B ≤ |B| := le_abs_self B
  have hk := abs_nonneg (surfaceGaussianCurvature (capDiskMap R h L) (capDiskNormal R L y) y)
  have hm := abs_nonneg (surfaceMeanCurvature (capDiskMap R h L) (capDiskNormal R L y) y)
  constructor <;> linarith

end ContinuousFlexibility
