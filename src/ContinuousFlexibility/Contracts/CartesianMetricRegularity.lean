module

public import ContinuousFlexibility.Contracts.CartesianMetric
public import ContinuousFlexibility.Geometry.CartesianMetricCoframe

/-!
# Global regularity and positivity of the actual Cartesian remainder

The analytic annular core supplies all the hypotheses here. Smoothness at
the center is proved from its actual constant/zero exterior extensions;
positivity away from the center is transported by the actual polar
derivative, not imposed as a new assumption on a Cartesian matrix.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open Set Filter
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem continuous_cartesianRadius : Continuous cartesianRadius :=
  continuous_norm.comp Complex.equivRealProdCLM.symm.continuous

theorem cartesianRadius_pos {x : PolarPoint} (hx : x ≠ 0) : 0 < cartesianRadius x := by
  apply norm_pos_iff.mpr
  intro hz
  apply hx
  have heq := congrArg Complex.equivRealProdCLM hz
  simpa only [ContinuousLinearEquiv.apply_symm_apply, map_zero] using heq

theorem contDiffAt_cartesianRadius {x : PolarPoint} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ cartesianRadius x := by
  apply Complex.equivRealProdCLM.symm.contDiff.contDiffAt.norm ℂ
  exact (norm_pos_iff.mp (cartesianRadius_pos hx))

theorem polarMap_cartesianCoordinates (x : PolarPoint) :
    polarMap (cartesianRadius x, (Complex.equivRealProdCLM.symm x).arg) = x := by
  apply Prod.ext
  · simpa only [polarMap, polarPosition, cartesianRadius,
      Complex.equivRealProdCLM_symm_apply_re] using
      Complex.norm_mul_cos_arg (Complex.equivRealProdCLM.symm x)
  · simpa only [polarMap, polarPosition, cartesianRadius,
      Complex.equivRealProdCLM_symm_apply_im] using
      Complex.norm_mul_sin_arg (Complex.equivRealProdCLM.symm x)

theorem FlatAnnularCore.cartesianHeight_germ_left (A : FlatAnnularCore) {x : PolarPoint}
    (hx : cartesianRadius x < A.a) : A.cartesianHeight =ᶠ[𝓝 x] fun _ => A.cLeft := by
  have hn : {y : PolarPoint | cartesianRadius y < A.a} ∈ 𝓝 x :=
    (isOpen_lt continuous_cartesianRadius continuous_const).mem_nhds hx
  filter_upwards [hn] with y hy
  exact A.cartesianHeight_left hy.le

theorem FlatAnnularCore.cartesianHeight_germ_right (A : FlatAnnularCore) {x : PolarPoint}
    (hx : A.b < cartesianRadius x) : A.cartesianHeight =ᶠ[𝓝 x] fun _ => A.cRight := by
  have hn : {y : PolarPoint | A.b < cartesianRadius y} ∈ 𝓝 x :=
    (isOpen_lt continuous_const continuous_cartesianRadius).mem_nhds hx
  filter_upwards [hn] with y hy
  exact A.cartesianHeight_right hy.le

theorem cartesianRemainder_eq_euclidean_of_zero_jets
    {w : ℝ → ℝ} {Z : PolarPoint → ℝ} {x : PolarPoint}
    (hw : w (cartesianRadius x) = 0) (hZ : fderiv ℝ Z x = 0) (u v : PolarPoint) :
    cartesianRemainder w Z x u v = coordinateEuclideanPair u v := by
  simp [cartesianRemainder, cartesianMetric, cartesianProfileFactor, hw, hZ]

theorem FlatAnnularCore.cartesianRemainder_left (A : FlatAnnularCore) {x : PolarPoint}
    (hx : cartesianRadius x < A.a) (u v : PolarPoint) :
    cartesianRemainder A.w A.cartesianHeight x u v = coordinateEuclideanPair u v := by
  apply cartesianRemainder_eq_euclidean_of_zero_jets
    (A.w_zero _ (Or.inl hx.le))
  simpa using (A.cartesianHeight_germ_left hx).fderiv_eq (𝕜 := ℝ)

theorem FlatAnnularCore.cartesianRemainder_right (A : FlatAnnularCore) {x : PolarPoint}
    (hx : A.b < cartesianRadius x) (u v : PolarPoint) :
    cartesianRemainder A.w A.cartesianHeight x u v = coordinateEuclideanPair u v := by
  apply cartesianRemainder_eq_euclidean_of_zero_jets
    (A.w_zero _ (Or.inr hx.le))
  simpa using (A.cartesianHeight_germ_right hx).fderiv_eq (𝕜 := ℝ)

theorem coordinateEuclideanPair_self_pos {v : PolarPoint} (hv : v ≠ 0) :
    0 < coordinateEuclideanPair v v := by
  unfold coordinateEuclideanPair
  by_cases h1 : v.1 = 0
  · have h2 : v.2 ≠ 0 := fun h2 => hv (Prod.ext h1 h2)
    nlinarith [sq_pos_of_ne_zero h2]
  · nlinarith [sq_pos_of_ne_zero h1, sq_nonneg v.2]

theorem remainderBilinear_self (r E k p : ℝ) (v : PolarPoint) :
    remainderBilinear r E k p v v = remainderQuadratic r E k p v.1 v.2 := by
  unfold remainderBilinear remainderQuadratic
  ring

theorem FlatAnnularCore.cartesianRemainder_pos (A : FlatAnnularCore)
    (x : PolarPoint) {v : PolarPoint} (hv : v ≠ 0) :
    0 < cartesianRemainder A.w A.cartesianHeight x v v := by
  by_cases hx : x = 0
  · subst x
    have hz : cartesianRadius (0 : PolarPoint) < A.a := by
      simpa only [cartesianRadius, map_zero, norm_zero] using A.a_pos
    rw [A.cartesianRemainder_left hz]
    exact coordinateEuclideanPair_self_pos hv
  let p : PolarPoint := (cartesianRadius x, (Complex.equivRealProdCLM.symm x).arg)
  have hr : 0 < p.1 := cartesianRadius_pos hx
  obtain ⟨u, hu⟩ := (polarJacobian_bijective hr.ne').surjective v
  have hune : u ≠ 0 := by
    intro hzero
    apply hv
    rw [← hu, hzero, map_zero]
  have hxy : u.1 ≠ 0 ∨ u.2 ≠ 0 := by
    by_cases h1 : u.1 = 0
    · exact Or.inr (fun h2 => hune (Prod.ext h1 h2))
    · exact Or.inl h1
  have hq := remainderPositive_of_discriminant_pos hr (radialEnergy_pos (A.w p.1))
    (A.discriminant_pos_global p.1 p.2) u.1 u.2 hxy
  have hmetric := A.cartesianRemainder_polar_pullback hr u u
  rw [show polarMap p = x from polarMap_cartesianCoordinates x, hu,
    remainderBilinear_self] at hmetric
  rw [hmetric]
  exact hq

theorem FlatAnnularCore.contDiff_cartesianProfileFactor (A : FlatAnnularCore) :
    ContDiff ℝ ∞ (cartesianProfileFactor A.w) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    have hn : {y : PolarPoint | cartesianRadius y < A.a} ∈ 𝓝 0 :=
      (isOpen_lt continuous_cartesianRadius continuous_const).mem_nhds
        (by simpa [cartesianRadius] using A.a_pos)
    have heq : cartesianProfileFactor A.w =ᶠ[𝓝 0] fun _ => 0 := by
      filter_upwards [hn] with y hy
      simp only [cartesianProfileFactor, A.w_zero _ (Or.inl hy.le), zero_div]
    exact contDiffAt_const.congr_of_eventuallyEq heq
  · have hR := contDiffAt_cartesianRadius hx
    exact (A.smooth_w.contDiffAt.comp x hR).div hR (cartesianRadius_pos hx).ne'

theorem cartesianRemainderA_eq (w : ℝ → ℝ) (Z : PolarPoint → ℝ) (x : PolarPoint) :
    cartesianRemainderA w Z x =
      1 + cartesianProfileFactor w x ^ 2 * x.1 ^ 2 - radialPartial Z x ^ 2 := by
  simp [cartesianRemainderA, cartesianRemainder, cartesianMetric,
    coordinateEuclideanPair, radialPartial]
  ring

theorem cartesianRemainderB_eq (w : ℝ → ℝ) (Z : PolarPoint → ℝ) (x : PolarPoint) :
    cartesianRemainderB w Z x = cartesianProfileFactor w x ^ 2 * x.1 * x.2 -
      radialPartial Z x * angularPartial Z x := by
  simp [cartesianRemainderB, cartesianRemainder, cartesianMetric,
    coordinateEuclideanPair, radialPartial, angularPartial]

theorem cartesianRemainderC_eq (w : ℝ → ℝ) (Z : PolarPoint → ℝ) (x : PolarPoint) :
    cartesianRemainderC w Z x =
      1 + cartesianProfileFactor w x ^ 2 * x.2 ^ 2 - angularPartial Z x ^ 2 := by
  simp [cartesianRemainderC, cartesianRemainder, cartesianMetric,
    coordinateEuclideanPair, angularPartial]
  ring

theorem cartesianRemainder_matrix (w : ℝ → ℝ) (Z : PolarPoint → ℝ)
    (x u v : PolarPoint) :
    cartesianRemainder w Z x u v =
      cartesianRemainderA w Z x * u.1 * v.1 +
        cartesianRemainderB w Z x * (u.1 * v.2 + u.2 * v.1) +
          cartesianRemainderC w Z x * u.2 * v.2 := by
  rw [cartesianRemainderA_eq, cartesianRemainderB_eq, cartesianRemainderC_eq]
  unfold cartesianRemainder cartesianMetric coordinateEuclideanPair
  rw [polarCLM_apply_decompose (fderiv ℝ Z x) u,
    polarCLM_apply_decompose (fderiv ℝ Z x) v]
  unfold radialPartial angularPartial
  ring

theorem FlatAnnularCore.cartesianRemainderA_pos (A : FlatAnnularCore) (x : PolarPoint) :
    0 < cartesianRemainderA A.w A.cartesianHeight x :=
  A.cartesianRemainder_pos x (by intro h; have := congrArg Prod.fst h; norm_num at this)

theorem FlatAnnularCore.cartesianRemainder_det_pos (A : FlatAnnularCore) (x : PolarPoint) :
    0 < matrixDiscriminant (cartesianRemainderA A.w A.cartesianHeight)
      (cartesianRemainderB A.w A.cartesianHeight) (cartesianRemainderC A.w A.cartesianHeight) x := by
  let a := cartesianRemainderA A.w A.cartesianHeight x
  let b := cartesianRemainderB A.w A.cartesianHeight x
  let c := cartesianRemainderC A.w A.cartesianHeight x
  have ha : 0 < a := A.cartesianRemainderA_pos x
  have hp := A.cartesianRemainder_pos x (v := (-b / a, 1))
    (by intro h; have := congrArg Prod.snd h; norm_num at this)
  rw [cartesianRemainder_matrix] at hp
  change 0 < a * (-b / a) * (-b / a) + b * ((-b / a) * 1 + 1 * (-b / a)) + c * 1 * 1 at hp
  have heq : a * (-b / a) * (-b / a) +
      b * ((-b / a) * 1 + 1 * (-b / a)) + c * 1 * 1 = (a * c - b ^ 2) / a := by
    field_simp [ha.ne']
    ring
  rw [heq] at hp
  exact (div_pos_iff_of_pos_right ha).mp hp

theorem FlatAnnularCore.contDiff_cartesianRemainder_entries (A : FlatAnnularCore) :
    ContDiff ℝ ∞ (cartesianRemainderA A.w A.cartesianHeight) ∧
      ContDiff ℝ ∞ (cartesianRemainderB A.w A.cartesianHeight) ∧
      ContDiff ℝ ∞ (cartesianRemainderC A.w A.cartesianHeight) := by
  have hf := A.contDiff_cartesianProfileFactor
  have hr : ContDiff ℝ ∞ (radialPartial A.cartesianHeight) :=
    contDiff_iff_contDiffAt.mpr (fun _ =>
      contDiffAt_radialPartial A.contDiff_cartesianHeight.contDiffAt (by simp))
  have ht : ContDiff ℝ ∞ (angularPartial A.cartesianHeight) :=
    contDiff_iff_contDiffAt.mpr (fun _ =>
      contDiffAt_angularPartial A.contDiff_cartesianHeight.contDiffAt (by simp))
  have ha : cartesianRemainderA A.w A.cartesianHeight =
      (fun x => 1 + cartesianProfileFactor A.w x ^ 2 * x.1 ^ 2 -
        radialPartial A.cartesianHeight x ^ 2) :=
    funext (cartesianRemainderA_eq A.w A.cartesianHeight)
  have hb : cartesianRemainderB A.w A.cartesianHeight =
      (fun x => cartesianProfileFactor A.w x ^ 2 * x.1 * x.2 -
        radialPartial A.cartesianHeight x * angularPartial A.cartesianHeight x) :=
    funext (cartesianRemainderB_eq A.w A.cartesianHeight)
  have hc : cartesianRemainderC A.w A.cartesianHeight =
      (fun x => 1 + cartesianProfileFactor A.w x ^ 2 * x.2 ^ 2 -
        angularPartial A.cartesianHeight x ^ 2) :=
    funext (cartesianRemainderC_eq A.w A.cartesianHeight)
  rw [ha, hb, hc]
  exact ⟨(contDiff_const.add ((hf.pow 2).mul (contDiff_fst.pow 2))).sub (hr.pow 2),
    (((hf.pow 2).mul contDiff_fst).mul contDiff_snd).sub (hr.mul ht),
    (contDiff_const.add ((hf.pow 2).mul (contDiff_snd.pow 2))).sub (ht.pow 2)⟩

theorem FlatAnnularCore.cartesianRemainder_standard_right (A : FlatAnnularCore)
    {x : PolarPoint} (hx : A.b < cartesianRadius x) :
    cartesianRemainderA A.w A.cartesianHeight x = 1 ∧
      cartesianRemainderB A.w A.cartesianHeight x = 0 ∧
      cartesianRemainderC A.w A.cartesianHeight x = 1 := by
  simp [cartesianRemainderA, cartesianRemainderB, cartesianRemainderC,
    A.cartesianRemainder_right hx, coordinateEuclideanPair]

theorem FlatAnnularCore.cartesianRemainder_standard_left (A : FlatAnnularCore)
    {x : PolarPoint} (hx : cartesianRadius x < A.a) :
    cartesianRemainderA A.w A.cartesianHeight x = 1 ∧
      cartesianRemainderB A.w A.cartesianHeight x = 0 ∧
      cartesianRemainderC A.w A.cartesianHeight x = 1 := by
  simp [cartesianRemainderA, cartesianRemainderB, cartesianRemainderC,
    A.cartesianRemainder_left hx, coordinateEuclideanPair]

end ContinuousFlexibility
