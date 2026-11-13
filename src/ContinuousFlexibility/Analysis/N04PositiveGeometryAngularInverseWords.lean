import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseBoundsMixedWords
import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseBoundsAngularGraph
import ContinuousFlexibility.Analysis.N01cFiniteAffineJets

/-!
# Saved words of the actual angular inverse

The first inverse differential uses the actual forward angular slope.
Its operator norm is a polynomial in the forward first-jet bound and
the reciprocal slope. Higher inverse words then follow from the genuine
inverse equation on the original parameter seminorm boxes.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {E : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

theorem n04PositiveGeometry_joint_spatial_first
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {U : Set (E × PolarPoint)} {f : E × PolarPoint → F}
    (J : SmoothDirections U f) (x : E) (q : PolarPoint) (hx : (x, q) ∈ U)
    (v : PolarPoint) :
    fderiv ℝ (fun y => f (x, y)) q v = J.D 1 (x, q) (fun _ => (0, v)) := by
  let L : PolarPoint →L[ℝ] E × PolarPoint :=
    (0 : PolarPoint →L[ℝ] E).prod (ContinuousLinearMap.id ℝ PolarPoint)
  have hp (y : PolarPoint) : (x, (0 : PolarPoint)) + L y = (x, y) := by
    simp only [L, ContinuousLinearMap.prod_apply, zero_apply,
      ContinuousLinearMap.id_apply, Prod.mk_add_mk, add_zero, zero_add]
  have hf : (fun y => f ((x, (0 : PolarPoint)) + L y)) = (fun y => f (x, y)) :=
    funext (fun y => congrArg f (hp y))
  have h := smoothDirections_iteratedFDeriv_finiteAffine J (x, (0 : PolarPoint)) L 1
    (y := q) (by rw [hp]; exact hx) (fun _ => v)
  simpa only [hf, hp, iteratedFDeriv_one_apply, L, ContinuousLinearMap.prod_apply,
    zero_apply, ContinuousLinearMap.id_apply] using h

/-- Only positive forward words and the pointwise reciprocal slope are
quantitative premises. The unwrapped angular value is never bounded. -/
theorem n04PositiveGeometry_angularInverse_unit_word_bound (n : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∃ degree : ℕ,
    ∀ (U : Set E) (φ : E → PolarPoint → ℝ)
      (JF : SmoothDirections (U ×ˢ univ)
        (fun z : E × PolarPoint => n04PositiveGeometry_angularGraph (φ z.1) z.2))
      (JG : SmoothDirections (U ×ˢ univ)
        (fun z : E × PolarPoint => n04PositiveGeometry_angularGraphInverse (φ z.1) z.2)),
      (∀ y ∈ U, ContDiff ℝ ∞ (φ y)) →
      (∀ y ∈ U, ∀ p : PolarPoint, 0 < deriv (fun θ => φ y (p.1, θ)) p.2) →
      (∀ y ∈ U, ∀ r θ, φ y (r, θ + Real.pi) = φ y (r, θ) + Real.pi) →
    ∀ (x : E × PolarPoint), x.1 ∈ U →
    ∀ (p q : Seminorm ℝ E) (R : ℝ), 0 ≤ R →
    ∀ (M H t : ℝ), 1 ≤ M → 0 ≤ H → H ≤ M → 1 ≤ t →
      |(deriv (fun θ => φ x.1 (x.2.1, θ))
        (parameterizedCircleInverse (φ x.1) x.2))⁻¹| ≤ M →
    ∀ (K C : ℕ), 1 ≤ C →
      (∀ j, 0 < j → j ≤ n → ∀ w : StateAngleWord j, w.stateArity ≤ K →
        ∀ v : Fin j → E × PolarPoint,
        (∀ i, if w.isState i then (v i).2 = 0 else (v i).1 = 0) →
        (∀ i, p (v i).1 ≤ 1 ∧ q (v i).1 ≤ R ∧ ‖(v i).2‖ ≤ 1) →
        ‖JF.D j (x.1, n04PositiveGeometry_angularGraphInverse (φ x.1) x.2) v‖ ≤
          M * parameterHeightWeight H w.stateArity *
            t ^ (w.angleArity + C * w.stateArity - 1)) →
      0 < n → ∀ w : StateAngleWord n, w.stateArity ≤ K →
      ∀ v : Fin n → E × PolarPoint,
      (∀ i, if w.isState i then (v i).2 = 0 else (v i).1 = 0) →
      (∀ i, p (v i).1 ≤ 1 ∧ q (v i).1 ≤ R ∧ ‖(v i).2‖ ≤ 1) →
        ‖JG.D n x v‖ ≤ A * M ^ degree * parameterHeightWeight H w.stateArity *
          t ^ (w.angleArity + C * w.stateArity - 1) := by
  obtain ⟨A, hA, degree, hbound⟩ :=
    n04PositiveGeometry_mixedInverse_unit_word_bound (E := E) (V := PolarPoint) n
  refine ⟨A * 3 ^ degree,
    one_le_mul_of_one_le_of_one_le hA (one_le_pow₀ (by norm_num)), 2 * degree, ?_⟩
  intro U φ JF JG hsmooth hpositive hperiod x hx p q R hR M H t hM hH hHM ht
    hslope K C hC hforward hn w hw v hpure hv
  let f : E × PolarPoint → PolarPoint :=
    fun z => n04PositiveGeometry_angularGraph (φ z.1) z.2
  let g : E × PolarPoint → PolarPoint :=
    fun z => n04PositiveGeometry_angularGraphInverse (φ z.1) z.2
  let y : PolarPoint := g x
  have hy : (x.1, y) ∈ U ×ˢ (univ : Set PolarPoint) := ⟨hx, mem_univ _⟩
  have hφ : ContDiff ℝ ∞ (φ x.1) := hsmooth x.1 hx
  have hp := hpositive x.1 hx
  have hper := hperiod x.1 hx
  have hdf (u : PolarPoint) (hu : ‖u‖ ≤ 1) :
      ‖fderiv ℝ (n04PositiveGeometry_angularGraph (φ x.1)) y u‖ ≤ M := by
    let word : StateAngleWord 1 := .angle .nil
    have hk : word.stateArity = 0 := rfl
    have hb : word.angleArity = 1 := by have := word.arity_sum; omega
    have hh := hforward 1 zero_lt_one hn word (by rw [hk]; exact Nat.zero_le K)
      (fun _ => (0, u)) (fun _ => rfl)
      (fun _ => ⟨by simp, by simpa only [map_zero] using hR, hu⟩)
    rw [← n04PositiveGeometry_joint_spatial_first JF x.1 y hy u] at hh
    simpa only [hk, hb, parameterHeightWeight, ite_true, mul_one,
      Nat.mul_zero, Nat.add_zero, Nat.sub_self, pow_zero] using hh
  let κ : ℝ := deriv (fun θ => φ x.1 (x.2.1, θ))
    (parameterizedCircleInverse (φ x.1) x.2)
  have hκ : 0 < κ := hp y
  have hκinv : κ⁻¹ ≤ M := (le_abs_self _).trans hslope
  have hκangle : κ ≤ angularPartial (φ x.1) y := by
    rw [← deriv_cylinder_angular_slice (hφ.differentiable (by simp))]
  have hrad : |radialPartial (φ x.1) y| ≤ M := by
    have he : fderiv ℝ (n04PositiveGeometry_angularGraph (φ x.1)) y =
        (ContinuousLinearMap.fst ℝ ℝ ℝ).prod (fderiv ℝ (φ x.1) y) :=
      (hasFDerivAt_fst.prodMk (hφ.differentiable (by simp) y).hasFDerivAt).fderiv
    have hu := hdf (1, 0) (by simp)
    rw [he, ContinuousLinearMap.prod_apply] at hu
    exact (norm_snd_le _).trans hu
  have hα := contDiff_parameterizedCircleInverse Real.pi_ne_zero hφ hp hper
  have hαbound := norm_fderiv_parameterizedCircleInverse_le
    Real.pi_ne_zero hφ hp hper hκ (zero_le_one.trans hM) x.2 hκangle hrad
  have hαcost : ‖fderiv ℝ (parameterizedCircleInverse (φ x.1)) x.2‖ ≤ (1 + M) * M :=
    hαbound.trans (by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hκinv (by linarith only [hM]))
  let B : PolarPoint →L[ℝ] PolarPoint :=
    fderiv ℝ (n04PositiveGeometry_angularGraphInverse (φ x.1)) x.2
  have hMM : M ≤ 3 * M ^ 2 := by nlinarith only [hM, sq_nonneg (M - 1)]
  have hM' : 1 ≤ 3 * M ^ 2 := hM.trans hMM
  have hBnorm : ‖B‖ ≤ 3 * M ^ 2 := by
    have hh := flowJet_augmented_jet_norm_le hα (n := 1) le_rfl x.2
    simp only [norm_iteratedFDeriv_one] at hh
    exact (hh.trans (add_le_add_left hαcost 1)).trans (by nlinarith only [hM])
  have hBleft (u : PolarPoint) : B (JF.D 1 (x.1, g x) (fun _ => (0, u))) = u := by
    rw [← n04PositiveGeometry_joint_spatial_first JF x.1 (g x) hy u]
    exact congrArg (fun L : PolarPoint →L[ℝ] PolarPoint => L u)
      (n04PositiveGeometry_angularGraphInverse_fderiv_left Real.pi_ne_zero hφ hp hper x.2)
  have hout := hbound (U ×ˢ univ) (U ×ˢ univ) f g JF JG x ⟨hx, mem_univ _⟩ hy
    (fun z hz => n04PositiveGeometry_angularGraph_right_inverse Real.pi_ne_zero
      (hsmooth z.1 hz.1) (hperiod z.1 hz.1) z.2)
    p q R hR (3 * M ^ 2) H t hM' hH (hHM.trans hMM) ht K C hC B hBleft hBnorm
    (fun j hj hjn u hu a ha hbox => (hforward j hj hjn u hu a ha hbox).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hMM (parameterHeightWeight_nonneg hH _))
        (pow_nonneg (zero_le_one.trans ht) _))) hn w hw v hpure hv
  apply hout.trans_eq
  rw [mul_pow, ← pow_mul]
  ring

end ContinuousFlexibility.Analysis
