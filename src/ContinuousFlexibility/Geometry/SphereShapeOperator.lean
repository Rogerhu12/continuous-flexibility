import ContinuousFlexibility.Geometry.SphereMetric
import ContinuousFlexibility.Geometry.SurfaceReparametrization
import Mathlib.LinearAlgebra.Trace

/-!
# The actual shape operator on the standard sphere's tangent bundle

The operator is constructed by inverting the immersion differential together
with its unit normal. Its Weingarten equation uses the genuine manifold
differential. Smoothness is proved in the actual endomorphism bundle; no norm
or artificial trivialization is installed on the tangent fibers.
-/

noncomputable section

namespace ContinuousFlexibility

open Filter Set Bundle
open scoped ContDiff Manifold Topology

local notation "SpherePoint" => {v : E3 // v ∈ Metric.sphere (0 : E3) 1}
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "TSphere" => (fun x : SpherePoint => TangentSpace (𝓡 2) x)

local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩

set_option backward.isDefEq.respectTransparency false

private def normalAugment (J : E2 →L[ℝ] E3) (n : E3) : (E2 × ℝ) →L[ℝ] E3 :=
  J.comp (ContinuousLinearMap.fst ℝ E2 ℝ) +
    (ContinuousLinearMap.snd ℝ E2 ℝ).smulRight n

private theorem normalAugment_apply (J : E2 →L[ℝ] E3) (n : E3) (p : E2 × ℝ) :
    normalAugment J n p = J p.1 + p.2 • n := rfl

private theorem normalAugment_injective {J : E2 →L[ℝ] E3} {n : E3}
    (hi : Function.Injective J) (hu : ‖n‖ = 1)
    (ho : ∀ v, inner ℝ (J v) n = 0) : Function.Injective (normalAugment J n) := by
  have hnn : inner ℝ n n = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  intro p q hpq
  have ht : p.2 = q.2 := by
    have hh := congrArg (fun z : E3 => inner ℝ z n) hpq
    change inner ℝ (J p.1 + p.2 • n) n = inner ℝ (J q.1 + q.2 • n) n at hh
    simpa only [inner_add_left, real_inner_smul_left, ho, hnn, zero_add, mul_one] using hh
  apply Prod.ext
  · apply hi
    change J p.1 + p.2 • n = J q.1 + q.2 • n at hpq
    rw [ht] at hpq
    exact add_right_cancel hpq
  · exact ht

private theorem normalAugment_isInvertible {J : E2 →L[ℝ] E3} {n : E3}
    (hi : Function.Injective J) (hu : ‖n‖ = 1)
    (ho : ∀ v, inner ℝ (J v) n = 0) : (normalAugment J n).IsInvertible := by
  let e := ((normalAugment J n).toLinearMap.linearEquivOfInjective
    (normalAugment_injective hi hu ho) (by simp [E3])).toContinuousLinearEquiv
  refine ⟨e, ?_⟩
  apply ContinuousLinearMap.ext
  intro p
  rfl

private theorem normalAugment_inverse_snd {J : E2 →L[ℝ] E3} {n z : E3}
    (hi : Function.Injective J) (hu : ‖n‖ = 1)
    (ho : ∀ v, inner ℝ (J v) n = 0) (hz : inner ℝ z n = 0) :
    ((normalAugment J n).inverse z).2 = 0 := by
  have hnn : inner ℝ n n = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have he := (normalAugment_isInvertible hi hu ho).self_apply_inverse z
  have hh := congrArg (fun w : E3 => inner ℝ w n) he
  rw [normalAugment_apply] at hh
  simpa only [inner_add_left, real_inner_smul_left, ho, hnn, zero_add, mul_one, hz] using hh

private theorem normalAugment_inverse_fst {J : E2 →L[ℝ] E3} {n z : E3}
    (hi : Function.Injective J) (hu : ‖n‖ = 1)
    (ho : ∀ v, inner ℝ (J v) n = 0) (hz : inner ℝ z n = 0) :
    J ((normalAugment J n).inverse z).1 = z := by
  have he := (normalAugment_isInvertible hi hu ho).self_apply_inverse z
  rw [normalAugment_apply, normalAugment_inverse_snd hi hu ho hz, zero_smul, add_zero] at he
  exact he

private def sphereShapeFrame (x : SpherePoint) : TSphere x ≃L[ℝ] E2 :=
  VectorBundle.continuousLinearEquivAt ℝ E2 TSphere x

/-- The actual endomorphism of the sphere tangent space. Invertibility of the
augmented differential is proved from immersion and unit-normal hypotheses. -/
def sphereShapeOperator (F N : SpherePoint → E3) (x : SpherePoint) :
    TSphere x →L[ℝ] TSphere x :=
  -((sphereShapeFrame x).symm : E2 →L[ℝ] TSphere x).comp
    ((ContinuousLinearMap.fst ℝ E2 ℝ).comp
      ((normalAugment ((mvfderiv (𝓡 2) F x).comp
        ((sphereShapeFrame x).symm : E2 →L[ℝ] TSphere x)) (N x)).inverse.comp
          (mvfderiv (𝓡 2) N x)))

/-- A differentiable unit field has derivative perpendicular to its value. -/
theorem sphere_mvfderiv_normal_inner_zero {N : SpherePoint → E3}
    (hN : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ N) (hu : ∀ x, ‖N x‖ = 1)
    (x : SpherePoint) (v : TSphere x) :
    inner ℝ (mvfderiv (𝓡 2) N x v) (N x) = 0 := by
  let Q : E3 → ℝ := fun z => inner ℝ z z
  have hQ : DifferentiableAt ℝ Q (N x) := differentiableAt_id.inner ℝ differentiableAt_id
  have he : Q ∘ N = fun _ : SpherePoint => (1 : ℝ) := by
    funext y
    simp only [Function.comp_apply, Q, real_inner_self_eq_norm_sq, hu, one_pow]
  have hz : mvfderiv (𝓡 2) (Q ∘ N) x v = 0 := by
    rw [he, mvfderiv_const]
    rfl
  rw [mvfderiv_comp x hQ.mdifferentiableAt ((hN x).mdifferentiableAt (by simp)),
    mvfderiv_eq_fderiv] at hz
  change fderiv ℝ Q (N x) (mvfderiv (𝓡 2) N x v) = 0 at hz
  change fderiv ℝ (fun z : E3 => inner ℝ (id z) (id z)) (N x)
    (mvfderiv (𝓡 2) N x v) = 0 at hz
  rw [fderiv_inner_apply ℝ differentiableAt_id differentiableAt_id] at hz
  simp only [fderiv_id, ContinuousLinearMap.id_apply, id_eq] at hz
  have hc := real_inner_comm (N x) (mvfderiv (𝓡 2) N x v)
  linarith

/-- The actual image of the immersion differential is the normal's orthogonal plane. -/
theorem sphereDifferential_range_eq_normal {F N : SpherePoint → E3} (x : SpherePoint)
    (hi : Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) F x))
    (hu : ‖N x‖ = 1) (ho : ∀ v, inner ℝ (mvfderiv (𝓡 2) F x v) (N x) = 0) :
    Set.range (mvfderiv (𝓡 2) F x) = {z : E3 | inner ℝ z (N x) = 0} := by
  let e := sphereShapeFrame x
  let J := (mvfderiv (𝓡 2) F x).comp (e.symm : E2 →L[ℝ] TSphere x)
  have hJ : Function.Injective J :=
    ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (F x)).injective.comp hi).comp e.symm.injective
  have hJo : ∀ v, inner ℝ (J v) (N x) = 0 := fun v => ho (e.symm v)
  ext z
  constructor
  · rintro ⟨v, rfl⟩
    exact ho v
  · intro hz
    refine ⟨e.symm ((normalAugment J (N x)).inverse z).1, ?_⟩
    exact normalAugment_inverse_fst hJ hu hJo hz

/-- The Weingarten equation for genuine sphere differentials, with convention S = -dN. -/
theorem sphereShapeOperator_weingarten {F N : SpherePoint → E3}
    (hN : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ N)
    (hi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) F x))
    (hu : ∀ x, ‖N x‖ = 1)
    (ho : ∀ x v, inner ℝ (mvfderiv (𝓡 2) F x v) (N x) = 0)
    (x : SpherePoint) (v : TSphere x) :
    mvfderiv (𝓡 2) F x (sphereShapeOperator F N x v) = -mvfderiv (𝓡 2) N x v := by
  let e := sphereShapeFrame x
  let J := (mvfderiv (𝓡 2) F x).comp (e.symm : E2 →L[ℝ] TSphere x)
  have hJ : Function.Injective J :=
    ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (F x)).injective.comp (hi x)).comp e.symm.injective
  have hJo : ∀ u, inner ℝ (J u) (N x) = 0 := fun u => ho x (e.symm u)
  have hz := sphere_mvfderiv_normal_inner_zero hN hu x v
  change mvfderiv (𝓡 2) F x
    (-(e.symm (((normalAugment J (N x)).inverse (mvfderiv (𝓡 2) N x v)).1))) = _
  rw [map_neg]
  exact congrArg Neg.neg (normalAugment_inverse_fst hJ (hu x) hJo hz)

private theorem sphereDifferential_in_frame_contMDiff {F : SpherePoint → E3}
    (hF : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ F) (x0 : SpherePoint) :
    ContMDiffAt (𝓡 2) 𝓘(ℝ, E2 →L[ℝ] E3) ∞
      (fun x => (mvfderiv (𝓡 2) F x).comp
        ((trivializationAt E2 TSphere x0).symmL ℝ x)) x0 := by
  have he : inTangentCoordinates (𝓡 2) 𝓘(ℝ, E3) id F
      (mfderiv (𝓡 2) 𝓘(ℝ, E3) F) x0 =
      fun x => (mvfderiv (𝓡 2) F x).comp
        ((trivializationAt E2 TSphere x0).symmL ℝ x) := by
    funext x
    dsimp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates, id_eq]
    rw [TangentBundle.continuousLinearMapAt_model_space]
    ext v
    rfl
  have hd := (hF x0).mfderiv_const (m := ∞) (by simp)
  rw [he] at hd
  exact hd

/-- The shape field is smooth as a section of the genuine tangent endomorphism bundle. -/
theorem sphereShapeOperator_contMDiff {F N : SpherePoint → E3}
    (hF : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ F)
    (hN : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ N)
    (hi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) F x))
    (hu : ∀ x, ‖N x‖ = 1)
    (ho : ∀ x v, inner ℝ (mvfderiv (𝓡 2) F x v) (N x) = 0) :
    ContMDiff (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, E2 →L[ℝ] E2)) ∞
      (fun x => TotalSpace.mk' (E2 →L[ℝ] E2) x (sphereShapeOperator F N x)) := by
  intro x0
  rw [contMDiffAt_section]
  let e := trivializationAt E2 TSphere x0
  let J : SpherePoint → E2 →L[ℝ] E3 :=
    fun x => (mvfderiv (𝓡 2) F x).comp (e.symmL ℝ x)
  let B : SpherePoint → E2 →L[ℝ] E3 :=
    fun x => (mvfderiv (𝓡 2) N x).comp (e.symmL ℝ x)
  let A : SpherePoint → (E2 × ℝ) →L[ℝ] E3 := fun x => normalAugment (J x) (N x)
  let T : SpherePoint → E2 →L[ℝ] E2 := fun x =>
    -(ContinuousLinearMap.fst ℝ E2 ℝ).comp ((A x).inverse.comp (B x))
  have hJ : ContMDiffAt (𝓡 2) 𝓘(ℝ, E2 →L[ℝ] E3) ∞ J x0 :=
    sphereDifferential_in_frame_contMDiff hF x0
  have hB : ContMDiffAt (𝓡 2) 𝓘(ℝ, E2 →L[ℝ] E3) ∞ B x0 :=
    sphereDifferential_in_frame_contMDiff hN x0
  have hA : ContMDiffAt (𝓡 2) 𝓘(ℝ, (E2 × ℝ) →L[ℝ] E3) ∞ A x0 := by
    have hr : ContMDiffAt (𝓡 2) 𝓘(ℝ, (E2 × ℝ) →L[ℝ] E3) ∞
        (fun x => (ContinuousLinearMap.snd ℝ E2 ℝ).smulRight (N x)) x0 :=
      (ContinuousLinearMap.smulRightL ℝ (E2 × ℝ) E3
        (ContinuousLinearMap.snd ℝ E2 ℝ)).contDiff.contDiffAt.contMDiffAt.comp x0 (hN x0)
    exact (hJ.clm_comp contMDiffAt_const).add hr
  have hx0 : x0 ∈ e.baseSet := mem_baseSet_trivializationAt E2 TSphere x0
  have hJ0 : Function.Injective (J x0) := by
    have he0 := e.symm_continuousLinearEquivAt_eq' (R := ℝ) hx0
    change Function.Injective ((mvfderiv (𝓡 2) F x0).comp (e.symmL ℝ x0))
    rw [← he0]
    exact ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (F x0)).injective.comp (hi x0)).comp
      (e.continuousLinearEquivAt ℝ x0 hx0).symm.injective
  have hA0 : (A x0).IsInvertible :=
    normalAugment_isInvertible hJ0 (hu x0) (fun v => ho x0 (e.symmL ℝ x0 v))
  have hAi : ContMDiffAt (𝓡 2) 𝓘(ℝ, E3 →L[ℝ] (E2 × ℝ)) ∞
      (fun x => (A x).inverse) x0 :=
    (hA0.contDiffAt_map_inverse (n := ∞)).contMDiffAt.comp x0 hA
  have hT : ContMDiffAt (𝓡 2) 𝓘(ℝ, E2 →L[ℝ] E2) ∞ T x0 :=
    (contMDiffAt_const.clm_comp (hAi.clm_comp hB)).neg
  apply hT.congr_of_eventuallyEq
  have hn : e.baseSet ∈ 𝓝 x0 := e.open_baseSet.mem_nhds hx0
  filter_upwards [hn] with x hx
  rw [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates_eq hx hx]
  let E : TSphere x ≃L[ℝ] E2 := e.continuousLinearEquivAt ℝ x hx
  have he : (E.symm : E2 →L[ℝ] TSphere x) = e.symmL ℝ x :=
    e.symm_continuousLinearEquivAt_eq' hx
  have hJx : Function.Injective (J x) := by
    change Function.Injective ((mvfderiv (𝓡 2) F x).comp (e.symmL ℝ x))
    rw [← he]
    exact ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (F x)).injective.comp (hi x)).comp E.symm.injective
  apply ContinuousLinearMap.ext
  intro u
  change E (sphereShapeOperator F N x (E.symm u)) = T x u
  apply hJx
  have hl : J x (T x u) = -(B x u) := by
    change J x (-((A x).inverse (B x u)).1) = _
    rw [map_neg]
    exact congrArg Neg.neg (normalAugment_inverse_fst hJx (hu x)
      (fun v => ho x (e.symmL ℝ x v))
      (sphere_mvfderiv_normal_inner_zero hN hu x (e.symmL ℝ x u)))
  have hr : J x (E (sphereShapeOperator F N x (E.symm u))) = -(B x u) := by
    change mvfderiv (𝓡 2) F x
      (e.symmL ℝ x (E (sphereShapeOperator F N x (E.symm u)))) = _
    rw [← he]
    change mvfderiv (𝓡 2) F x
      (E.symm (E (sphereShapeOperator F N x (E.symm u)))) = _
    rw [E.symm_apply_apply, sphereShapeOperator_weingarten hN hi hu ho]
    change -(mvfderiv (𝓡 2) N x (E.symm u)) = -(mvfderiv (𝓡 2) N x (e.symmL ℝ x u))
    rw [← he]
    simp only [ContinuousLinearEquiv.coe_coe]
  exact hr.trans hl.symm

private theorem sphere_normal_derivative_symm_in_chart {F N : SpherePoint → E3}
    (hF : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ F)
    (hN : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ N)
    (ho : ∀ x v, inner ℝ (mvfderiv (𝓡 2) F x v) (N x) = 0)
    (P : PolarPoint → SpherePoint) (hP : ContMDiff 𝓘(ℝ, PolarPoint) (𝓡 2) ∞ P)
    (u : PolarPoint) (hPi : Function.Surjective (mfderiv 𝓘(ℝ, PolarPoint) (𝓡 2) P u)) :
    ∀ v w : TSphere (P u),
      inner ℝ (mvfderiv (𝓡 2) F (P u) v) (mvfderiv (𝓡 2) N (P u) w) =
        inner ℝ (mvfderiv (𝓡 2) F (P u) w) (mvfderiv (𝓡 2) N (P u) v) := by
  let dP (y : PolarPoint) : PolarPoint →L[ℝ] TSphere (P y) :=
    (mfderiv 𝓘(ℝ, PolarPoint) (𝓡 2) P y).comp
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm :
        PolarPoint →L[ℝ] TangentSpace 𝓘(ℝ, PolarPoint) y)
  have hcomp (G : SpherePoint → E3) (hG : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ G)
      (y : PolarPoint) :
      fderiv ℝ (G ∘ P) y = (mvfderiv (𝓡 2) G (P y)).comp (dP y) := by
    have hh := mvfderiv_comp y ((hG (P y)).mdifferentiableAt (by simp))
      ((hP y).mdifferentiableAt (by simp))
    rw [mvfderiv_eq_fderiv] at hh
    apply ContinuousLinearMap.ext
    intro z
    have hz := congrArg (fun L => L ((NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm z)) hh
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, dP]
      using hz
  have hFp : ContDiff ℝ ∞ (F ∘ P) := (hF.comp hP).contDiff
  have hNp : ContDiff ℝ ∞ (N ∘ P) := (hN.comp hP).contDiff
  have hnormal : ∀ y z, inner ℝ (fderiv ℝ (F ∘ P) y z) ((N ∘ P) y) = 0 := by
    intro y z
    rw [hcomp F hF y]
    exact ho (P y) (dP y z)
  have hs (a b : PolarPoint) :
      inner ℝ (fderiv ℝ (F ∘ P) u a) (fderiv ℝ (N ∘ P) u b) =
        inner ℝ (fderiv ℝ (F ∘ P) u b) (fderiv ℝ (N ∘ P) u a) := by
    have hh := surfaceSecondForm_symm hFp ((N ∘ P) u) u a b
    rw [surfaceSecondForm_eq_neg_normal_derivative hFp
        (hNp.differentiable (by simp) u) hnormal a b,
      surfaceSecondForm_eq_neg_normal_derivative hFp
        (hNp.differentiable (by simp) u) hnormal b a] at hh
    exact neg_injective hh.symm
  have hsurj : Function.Surjective (dP u) :=
    hPi.comp (NormedSpace.fromTangentSpace (𝕜 := ℝ) u).symm.surjective
  intro v w
  obtain ⟨a, ha⟩ := hsurj v
  obtain ⟨b, hb⟩ := hsurj w
  have hh := hs a b
  rw [hcomp F hF u, hcomp N hN u] at hh
  simpa only [ContinuousLinearMap.comp_apply, ha, hb] using hh

private theorem sphere_normal_derivative_symm {F N : SpherePoint → E3}
    (hF : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ F)
    (hN : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ N)
    (ho : ∀ x v, inner ℝ (mvfderiv (𝓡 2) F x v) (N x) = 0) (x : SpherePoint) :
    ∀ v w : TSphere x,
      inner ℝ (mvfderiv (𝓡 2) F x v) (mvfderiv (𝓡 2) N x w) =
        inner ℝ (mvfderiv (𝓡 2) F x w) (mvfderiv (𝓡 2) N x v) := by
  let B (y : SpherePoint) : Prop := ∀ v w : TSphere y,
    inner ℝ (mvfderiv (𝓡 2) F y v) (mvfderiv (𝓡 2) N y w) =
      inner ℝ (mvfderiv (𝓡 2) F y w) (mvfderiv (𝓡 2) N y v)
  change B x
  by_cases hn : x ∈ sphereNorthSource
  · have hi : Function.Surjective (mfderiv 𝓘(ℝ, PolarPoint) (𝓡 2)
        sphereNorthInverse (sphereNorthChart x)) :=
      (mdifferentiable_sphereNorthCoordinates.symm.mfderiv_bijective (Set.mem_univ _)).surjective
    have hh := sphere_normal_derivative_symm_in_chart hF hN ho sphereNorthInverse
      contMDiff_sphereNorthInverse (sphereNorthChart x) hi
    exact Eq.mp (congrArg B (sphereNorthInverse_chart x hn)) hh
  · have hs : x ∈ sphereSouthSource := by
      change (x : E3) 2 ≠ 1
      change ¬ (x : E3) 2 ≠ -1 at hn
      have he := not_ne_iff.mp hn
      linarith
    have hi : Function.Surjective (mfderiv 𝓘(ℝ, PolarPoint) (𝓡 2)
        sphereSouthInverse (sphereSouthChart x)) :=
      (mdifferentiable_sphereSouthCoordinates.symm.mfderiv_bijective (Set.mem_univ _)).surjective
    have hh := sphere_normal_derivative_symm_in_chart hF hN ho sphereSouthInverse
      contMDiff_sphereSouthInverse (sphereSouthChart x) hi
    exact Eq.mp (congrArg B (sphereSouthInverse_chart x hs)) hh

/-- Self-adjointness is measured in the actual metric induced by the immersion. -/
theorem sphereShapeOperator_self_adjoint {F N : SpherePoint → E3}
    (hF : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ F)
    (hN : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ N)
    (hi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) F x))
    (hu : ∀ x, ‖N x‖ = 1)
    (ho : ∀ x v, inner ℝ (mvfderiv (𝓡 2) F x v) (N x) = 0)
    (x : SpherePoint) (v w : TSphere x) :
    inner ℝ (mvfderiv (𝓡 2) F x (sphereShapeOperator F N x v)) (mvfderiv (𝓡 2) F x w) =
      inner ℝ (mvfderiv (𝓡 2) F x v) (mvfderiv (𝓡 2) F x (sphereShapeOperator F N x w)) := by
  rw [sphereShapeOperator_weingarten hN hi hu ho,
    sphereShapeOperator_weingarten hN hi hu ho, inner_neg_left, inner_neg_right]
  rw [real_inner_comm (mvfderiv (𝓡 2) F x w) (mvfderiv (𝓡 2) N x v)]
  exact congrArg Neg.neg (sphere_normal_derivative_symm hF hN ho x w v)

/-- Half the actual fiberwise trace of a smooth sphere endomorphism field is smooth. -/
theorem sphereEnd_trace_half_contMDiff
    (S : (x : SpherePoint) → TSphere x →L[ℝ] TSphere x)
    (hS : ContMDiff (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, E2 →L[ℝ] E2)) ∞
      (fun x => TotalSpace.mk' (E2 →L[ℝ] E2) x (S x))) :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
      (fun x => LinearMap.trace ℝ (TSphere x) (S x).toLinearMap / 2) := by
  let tr : (E2 →L[ℝ] E2) →L[ℝ] ℝ :=
    ((LinearMap.trace ℝ E2).comp (ContinuousLinearMap.coeLM ℝ)).toContinuousLinearMap
  have hm : ContDiff ℝ ∞
      (fun A : E2 →L[ℝ] E2 => LinearMap.trace ℝ E2 A.toLinearMap / 2) := by
    change ContDiff ℝ ∞ (fun A => tr A / 2)
    exact tr.contDiff.div_const 2
  intro x0
  let e := trivializationAt E2 TSphere x0
  let T : SpherePoint → E2 →L[ℝ] E2 := fun x =>
    ContinuousLinearMap.inCoordinates E2 TSphere E2 TSphere x0 x x0 x (S x)
  have hT : ContMDiffAt (𝓡 2) 𝓘(ℝ, E2 →L[ℝ] E2) ∞ T x0 := by
    have hs0 := hS x0
    rw [contMDiffAt_section] at hs0
    simpa only [T, hom_trivializationAt_apply] using hs0
  have hlocal : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞
      (fun x => LinearMap.trace ℝ E2 (T x).toLinearMap / 2) x0 :=
    hm.contDiffAt.comp_contMDiffAt hT
  apply hlocal.congr_of_eventuallyEq
  have hn : e.baseSet ∈ 𝓝 x0 :=
    e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E2 TSphere x0)
  filter_upwards [hn] with x hx
  let E : TSphere x ≃L[ℝ] E2 := e.continuousLinearEquivAt ℝ x hx
  have hc : (T x).toLinearMap = E.toLinearEquiv.conj (S x).toLinearMap := by
    dsimp only [T]
    rw [ContinuousLinearMap.inCoordinates_eq hx hx]
    ext v
    rfl
  rw [hc, LinearMap.trace_conj']

/-- The actual fiberwise determinant of a smooth sphere endomorphism field is smooth. -/
theorem sphereEnd_det_contMDiff
    (S : (x : SpherePoint) → TSphere x →L[ℝ] TSphere x)
    (hS : ContMDiff (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, E2 →L[ℝ] E2)) ∞
      (fun x => TotalSpace.mk' (E2 →L[ℝ] E2) x (S x))) :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun x => LinearMap.det (S x).toLinearMap) := by
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  let a (i j : Fin 2) : (E2 →L[ℝ] E2) → ℝ := fun A => (A (b j)) i
  have ha (i j : Fin 2) : ContDiff ℝ ∞ (a i j) := by
    have hev : ContDiff ℝ ∞ (fun A : E2 →L[ℝ] E2 => A (b j)) :=
      (contDiff_id : ContDiff ℝ ∞ (fun A : E2 →L[ℝ] E2 => A)).clm_apply contDiff_const
    exact (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hev
  have hformula (A : E2 →L[ℝ] E2) :
      LinearMap.det A.toLinearMap = a 0 0 A * a 1 1 A - a 0 1 A * a 1 0 A := by
    rw [← LinearMap.det_toMatrix b.toBasis, Matrix.det_fin_two]
    simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply]
    rfl
  have hm : ContDiff ℝ ∞ (fun A : E2 →L[ℝ] E2 => LinearMap.det A.toLinearMap) := by
    simp_rw [hformula]
    exact ((ha 0 0).mul (ha 1 1)).sub ((ha 0 1).mul (ha 1 0))
  intro x0
  let e := trivializationAt E2 TSphere x0
  let T : SpherePoint → E2 →L[ℝ] E2 := fun x =>
    ContinuousLinearMap.inCoordinates E2 TSphere E2 TSphere x0 x x0 x (S x)
  have hT : ContMDiffAt (𝓡 2) 𝓘(ℝ, E2 →L[ℝ] E2) ∞ T x0 := by
    have hs0 := hS x0
    rw [contMDiffAt_section] at hs0
    simpa only [T, hom_trivializationAt_apply] using hs0
  have hlocal : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞
      (fun x => LinearMap.det (T x).toLinearMap) x0 := hm.contDiffAt.comp_contMDiffAt hT
  apply hlocal.congr_of_eventuallyEq
  have hn : e.baseSet ∈ 𝓝 x0 :=
    e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E2 TSphere x0)
  filter_upwards [hn] with x hx
  let E : TSphere x ≃L[ℝ] E2 := e.continuousLinearEquivAt ℝ x hx
  have hc : (T x).toLinearMap = E.toLinearEquiv.conj (S x).toLinearMap := by
    dsimp only [T]
    rw [ContinuousLinearMap.inCoordinates_eq hx hx]
    ext v
    rfl
  rw [hc, LinearEquiv.conj_apply]
  simpa only [LinearMap.comp_assoc] using
    (LinearMap.det_conj (S x).toLinearMap E.toLinearEquiv).symm

/-- Smooth signed mean curvature, defined by half the trace of the actual shape operator. -/
theorem sphereShapeOperator_trace_contMDiff {F N : SpherePoint → E3}
    (hF : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ F)
    (hN : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ N)
    (hi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) F x))
    (hu : ∀ x, ‖N x‖ = 1)
    (ho : ∀ x v, inner ℝ (mvfderiv (𝓡 2) F x v) (N x) = 0) :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
      (fun x => LinearMap.trace ℝ (TSphere x) (sphereShapeOperator F N x).toLinearMap / 2) :=
  sphereEnd_trace_half_contMDiff _ (sphereShapeOperator_contMDiff hF hN hi hu ho)

/-- Smooth Gaussian curvature, defined by the determinant of the actual shape operator. -/
theorem sphereShapeOperator_det_contMDiff {F N : SpherePoint → E3}
    (hF : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ F)
    (hN : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ N)
    (hi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) F x))
    (hu : ∀ x, ‖N x‖ = 1)
    (ho : ∀ x v, inner ℝ (mvfderiv (𝓡 2) F x v) (N x) = 0) :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
      (fun x => LinearMap.det (sphereShapeOperator F N x).toLinearMap) :=
  sphereEnd_det_contMDiff _ (sphereShapeOperator_contMDiff hF hN hi hu ho)

end ContinuousFlexibility
