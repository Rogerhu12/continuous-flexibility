import ContinuousFlexibility.Analysis.TravelStripAngularInverse
import ContinuousFlexibility.Geometry.PlanarOrientation
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

/-!
# A global inverse for a full travel-coordinate strip

The angular coordinate is first inverted on each radial slice. In these
coordinates the radial derivative of travel time is the actual planar
Jacobian divided by the positive angular derivative. Strict monotonicity
and the two endpoint values therefore give a genuine global bijection.
The inverse is the actual `Function.invFunOn` and is smooth by the local
inverse function theorem.

This is a statement about the full negative component. It does not identify
a fixed radial half-cut with a moving travel-time half-cut.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Travel time at a fixed value of the actual angular coordinate. -/
def angleNormalizedTravel (Γ : PolarPoint → PolarPoint) (p : PolarPoint) : ℝ :=
  (Γ (p.1, parameterizedCircleInverse (fun q => (Γ q).2) p)).1

theorem continuousOn_angleNormalizedTravel
    {Γ : PolarPoint → PolarPoint} {I : Set ℝ}
    (hΓ : ContinuousOn Γ (I ×ˢ univ))
    (hMono : ∀ r ∈ I, StrictMono (fun θ : ℝ => (Γ (r, θ)).2))
    (hSurj : ∀ r ∈ I, Function.Surjective (fun θ : ℝ => (Γ (r, θ)).2)) :
    ContinuousOn (angleNormalizedTravel Γ) (I ×ˢ univ) := by
  have hA := continuousOn_parameterizedCircleInverse_of_strictMono hΓ.snd hMono hSurj
  exact (hΓ.comp (continuous_fst.continuousOn.prodMk hA)
    (fun p hp => ⟨hp.1, mem_univ _⟩)).fst

theorem contDiffOn_angleNormalizedTravel
    {Γ : PolarPoint → PolarPoint} {I : Set ℝ}
    (hI : IsOpen I) (hΓ : ContDiffOn ℝ ∞ Γ (I ×ˢ univ))
    (hPositive : ∀ p ∈ I ×ˢ univ, 0 < angularPartial (fun q => (Γ q).2) p)
    (hMono : ∀ r ∈ I, StrictMono (fun θ : ℝ => (Γ (r, θ)).2))
    (hSurj : ∀ r ∈ I, Function.Surjective (fun θ : ℝ => (Γ (r, θ)).2)) :
    ContDiffOn ℝ ∞ (angleNormalizedTravel Γ) (I ×ˢ univ) := by
  have hA := contDiffOn_parameterizedCircleInverse_of_strictMono
    hI hΓ.snd hPositive hMono hSurj
  exact (hΓ.comp (contDiff_fst.contDiffOn.prodMk hA)
    (fun p hp => ⟨hp.1, mem_univ _⟩)).fst

/-- Keeping the second coordinate fixed leaves exactly the actual radial
derivative as the planar Jacobian. -/
theorem planeJacobian_preserve_second
    {F : PolarPoint → ℝ} {p : PolarPoint}
    (hF : DifferentiableAt ℝ F p) :
    planeJacobian (fun q : PolarPoint => (F q, q.2)) p =
      radialPartial F p := by
  have hy : HasFDerivAt (fun q : PolarPoint => q.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) p := hasFDerivAt_snd
  have hh := hF.hasFDerivAt.prodMk hy
  unfold planeJacobian radialPartial
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_snd',
    mul_one, zero_mul, sub_zero]

/-- The radial derivative at fixed angular coordinate is the actual
Jacobian quotient J/φθ, without an assumed inverse derivative formula. -/
theorem radialPartial_angleNormalizedTravel
    {Γ : PolarPoint → PolarPoint} {I : Set ℝ}
    (hI : IsOpen I) (hΓ : ContDiffOn ℝ ∞ Γ (I ×ˢ univ))
    (hPositive : ∀ p ∈ I ×ˢ univ, 0 < angularPartial (fun q => (Γ q).2) p)
    (hMono : ∀ r ∈ I, StrictMono (fun θ : ℝ => (Γ (r, θ)).2))
    (hSurj : ∀ r ∈ I, Function.Surjective (fun θ : ℝ => (Γ (r, θ)).2))
    {p : PolarPoint} (hp : p ∈ I ×ˢ univ) :
    radialPartial (angleNormalizedTravel Γ) p =
      planeJacobian Γ (p.1, parameterizedCircleInverse (fun q => (Γ q).2) p) /
        angularPartial (fun q => (Γ q).2)
          (p.1, parameterizedCircleInverse (fun q => (Γ q).2) p) := by
  let φ : PolarPoint → ℝ := fun q => (Γ q).2
  let A : PolarPoint → PolarPoint := fun q => (q.1, parameterizedCircleInverse φ q)
  let H : PolarPoint → PolarPoint := fun q => (q.1, φ q)
  have hOpen : IsOpen (I ×ˢ (univ : Set ℝ)) := hI.prod isOpen_univ
  have hMaps : MapsTo A (I ×ˢ univ) (I ×ˢ univ) :=
    fun q hq => ⟨hq.1, mem_univ _⟩
  have hAngle := contDiffOn_parameterizedCircleInverse_of_strictMono
    hI hΓ.snd hPositive hMono hSurj
  have hA : ContDiffOn ℝ ∞ A (I ×ˢ univ) := contDiff_fst.contDiffOn.prodMk hAngle
  have hH : ContDiffOn ℝ ∞ H (I ×ˢ univ) :=
    contDiff_fst.contDiffOn.prodMk hΓ.snd
  have hAd := (hA.contDiffAt (hOpen.mem_nhds hp)).differentiableAt (by simp)
  have hHd := (hH.contDiffAt (hOpen.mem_nhds (hMaps hp))).differentiableAt (by simp)
  have hΓd := (hΓ.contDiffAt (hOpen.mem_nhds (hMaps hp))).differentiableAt (by simp)
  have hRight (q : PolarPoint) (hq : q ∈ I ×ˢ univ) : φ (A q) = q.2 :=
    Function.rightInverse_invFun (hSurj q.1 hq.1) q.2
  have hHA : H ∘ A =ᶠ[𝓝 p] id := by
    filter_upwards [hOpen.mem_nhds hp] with q hq
    simp only [Function.comp_apply, id_eq]
    exact Prod.ext rfl (hRight q hq)
  have hJHA : planeJacobian (H ∘ A) p = 1 := by
    unfold planeJacobian
    rw [hHA.fderiv_eq]
    simp only [fderiv_id, ContinuousLinearMap.id_apply, one_mul, zero_mul, sub_zero]
  have hJH : planeJacobian H (A p) = angularPartial φ (A p) :=
    planeJacobian_preserve_first hΓd.snd
  have hproduct : angularPartial φ (A p) * planeJacobian A p = 1 := by
    rw [← hJH]
    exact (planeJacobian_comp hAd hHd).symm.trans hJHA
  have hne : angularPartial φ (A p) ≠ 0 := (hPositive (A p) (hMaps hp)).ne'
  have hJA : planeJacobian A p = (angularPartial φ (A p))⁻¹ := by
    apply mul_left_cancel₀ hne
    rw [hproduct, mul_inv_cancel₀ hne]
  have hB : Γ ∘ A =ᶠ[𝓝 p]
      (fun q : PolarPoint => (angleNormalizedTravel Γ q, q.2)) := by
    filter_upwards [hOpen.mem_nhds hp] with q hq
    simp only [Function.comp_apply]
    exact Prod.ext rfl (hRight q hq)
  have hU := contDiffOn_angleNormalizedTravel hI hΓ hPositive hMono hSurj
  have hJB : planeJacobian (Γ ∘ A) p = radialPartial (angleNormalizedTravel Γ) p := by
    calc
      planeJacobian (Γ ∘ A) p =
          planeJacobian (fun q : PolarPoint => (angleNormalizedTravel Γ q, q.2)) p := by
        unfold planeJacobian
        rw [hB.fderiv_eq]
      _ = radialPartial (angleNormalizedTravel Γ) p :=
        planeJacobian_preserve_second
          ((hU.contDiffAt (hOpen.mem_nhds hp)).differentiableAt (by simp))
  calc
    radialPartial (angleNormalizedTravel Γ) p = planeJacobian (Γ ∘ A) p := hJB.symm
    _ = planeJacobian Γ (A p) * planeJacobian A p := planeJacobian_comp hAd hΓd
    _ = planeJacobian Γ (A p) / angularPartial φ (A p) := by rw [hJA, div_eq_mul_inv]

/-- Positive actual angular derivatives on the open strip, together with
strict boundary lifts, give strict angular monotonicity on every closed slice. -/
theorem strictMono_travelStrip_angle
    {Γ : PolarPoint → PolarPoint} {a b : ℝ}
    (hΓ : ContDiffOn ℝ ∞ Γ (Ioo a b ×ˢ univ))
    (hAngle : ∀ p ∈ Ioo a b ×ˢ univ, 0 < angularPartial (fun q => (Γ q).2) p)
    (hLeft : StrictMono (fun θ : ℝ => (Γ (a, θ)).2))
    (hRight : StrictMono (fun θ : ℝ => (Γ (b, θ)).2))
    {r : ℝ} (hr : r ∈ Icc a b) :
    StrictMono (fun θ : ℝ => (Γ (r, θ)).2) := by
  by_cases hra : r = a
  · subst r
    exact hLeft
  by_cases hrb : r = b
  · subst r
    exact hRight
  have hri : r ∈ Ioo a b := by
    constructor <;> apply lt_of_le_of_ne
    · exact hr.1
    · exact Ne.symm hra
    · exact hr.2
    · exact hrb
  apply strictMono_of_deriv_pos
  intro θ
  have hp : (r, θ) ∈ Ioo a b ×ˢ (univ : Set ℝ) := ⟨hri, mem_univ _⟩
  have hDiff : DifferentiableAt ℝ Γ (r, θ) :=
    (hΓ.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).differentiableAt (by simp)
  have hd := hDiff.hasFDerivAt.snd
  have hc := hd.comp_hasDerivAt θ
    ((hasDerivAt_const θ r).prodMk (hasDerivAt_id θ))
  have he : (fun q : PolarPoint => (Γ q).2) ∘ (fun η : ℝ => (r, η)) =
      (fun η : ℝ => (Γ (r, η)).2) := by
    funext η
    exact Function.comp_apply
  rw [he] at hc
  have hvalue : deriv (fun η : ℝ => (Γ (r, η)).2) θ =
      angularPartial (fun q => (Γ q).2) (r, θ) := by
    rw [hc.deriv]
    unfold angularPartial
    rw [hd.fderiv]
  rw [hvalue]
  exact hAngle (r, θ) hp

/-- Every fixed-angle travel function is strictly increasing all the way
from the left endpoint to the right endpoint. -/
theorem strictMonoOn_angleNormalizedTravel
    {Γ : PolarPoint → PolarPoint} {a b : ℝ}
    (hClosed : ContinuousOn Γ (Icc a b ×ˢ univ))
    (hSmooth : ContDiffOn ℝ ∞ Γ (Ioo a b ×ˢ univ))
    (hAngle : ∀ p ∈ Ioo a b ×ˢ univ, 0 < angularPartial (fun q => (Γ q).2) p)
    (hJ : ∀ p ∈ Ioo a b ×ˢ univ, 0 < planeJacobian Γ p)
    (hMono : ∀ r ∈ Icc a b, StrictMono (fun θ : ℝ => (Γ (r, θ)).2))
    (hSurj : ∀ r ∈ Icc a b, Function.Surjective (fun θ : ℝ => (Γ (r, θ)).2))
    (η : ℝ) :
    StrictMonoOn (fun r : ℝ => angleNormalizedTravel Γ (r, η)) (Icc a b) := by
  have hMonoI := fun r (hr : r ∈ Ioo a b) => hMono r (Ioo_subset_Icc_self hr)
  have hSurjI := fun r (hr : r ∈ Ioo a b) => hSurj r (Ioo_subset_Icc_self hr)
  have hc := continuousOn_angleNormalizedTravel hClosed hMono hSurj
  have hs := contDiffOn_angleNormalizedTravel isOpen_Ioo hSmooth hAngle hMonoI hSurjI
  have hline : MapsTo (fun r : ℝ => (r, η)) (Icc a b) (Icc a b ×ˢ univ) :=
    fun r hr => ⟨hr, mem_univ _⟩
  apply strictMonoOn_of_deriv_pos (convex_Icc a b)
    (hc.comp (continuous_id.prodMk continuous_const).continuousOn hline)
  intro r hr
  have hri : r ∈ Ioo a b := by simpa only [interior_Icc] using hr
  have hp : (r, η) ∈ Ioo a b ×ˢ (univ : Set ℝ) := ⟨hri, mem_univ _⟩
  have hDiff : DifferentiableAt ℝ (angleNormalizedTravel Γ) (r, η) :=
    (hs.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).differentiableAt (by simp)
  have hd := hDiff.hasFDerivAt
  have hc := hd.comp_hasDerivAt r
    ((hasDerivAt_id r).prodMk (hasDerivAt_const r η))
  have he : (angleNormalizedTravel Γ) ∘ (fun s : ℝ => (id s, η)) =
      (fun s : ℝ => angleNormalizedTravel Γ (s, η)) := by
    funext s
    simp only [Function.comp_apply, id_eq]
  rw [he] at hc ⊢
  have hderiv : deriv (fun s : ℝ => angleNormalizedTravel Γ (s, η)) r =
      radialPartial (angleNormalizedTravel Γ) (r, η) := hc.deriv
  rw [hderiv, radialPartial_angleNormalizedTravel isOpen_Ioo hSmooth hAngle hMonoI hSurjI hp]
  exact div_pos (hJ _ ⟨hri, mem_univ _⟩) (hAngle _ ⟨hri, mem_univ _⟩)

/-- A full travel chart satisfying the actual differential signs and the
constant endpoint travel values is a bijection onto the full target strip. -/
theorem travelStrip_bijOn
    {Γ : PolarPoint → PolarPoint} {a b W P : ℝ}
    (hab : a < b) (hP : P ≠ 0)
    (hClosed : ContinuousOn Γ (Icc a b ×ˢ univ))
    (hSmooth : ContDiffOn ℝ ∞ Γ (Ioo a b ×ˢ univ))
    (hAngle : ∀ p ∈ Ioo a b ×ˢ univ, 0 < angularPartial (fun q => (Γ q).2) p)
    (hJ : ∀ p ∈ Ioo a b ×ˢ univ, 0 < planeJacobian Γ p)
    (hPeriod : ∀ r ∈ Icc a b, ∀ θ : ℝ,
      (Γ (r, θ + P)).2 = (Γ (r, θ)).2 + P)
    (hLeftMono : StrictMono (fun θ : ℝ => (Γ (a, θ)).2))
    (hRightMono : StrictMono (fun θ : ℝ => (Γ (b, θ)).2))
    (hLeft : ∀ θ : ℝ, (Γ (a, θ)).1 = 0)
    (hRight : ∀ θ : ℝ, (Γ (b, θ)).1 = W) :
    BijOn Γ (Ioo a b ×ˢ univ) (Ioo 0 W ×ˢ univ) := by
  have hMono (r : ℝ) (hr : r ∈ Icc a b) :
      StrictMono (fun θ : ℝ => (Γ (r, θ)).2) :=
    strictMono_travelStrip_angle hSmooth hAngle hLeftMono hRightMono hr
  have hSurj (r : ℝ) (hr : r ∈ Icc a b) :
      Function.Surjective (fun θ : ℝ => (Γ (r, θ)).2) :=
    surjective_of_continuous_periodic_lift hP
      (hClosed.snd.comp_continuous (continuous_const.prodMk continuous_id)
        (fun θ => ⟨hr, mem_univ θ⟩))
      (hPeriod r hr)
  have hTravelMono (η : ℝ) :
      StrictMonoOn (fun r : ℝ => angleNormalizedTravel Γ (r, η)) (Icc a b) :=
    strictMonoOn_angleNormalizedTravel hClosed hSmooth hAngle hJ hMono hSurj η
  have hTravelContinuous := continuousOn_angleNormalizedTravel hClosed hMono hSurj
  have hImage (η : ℝ) :
      (fun r : ℝ => angleNormalizedTravel Γ (r, η)) '' Ioo a b = Ioo 0 W := by
    have hc : ContinuousOn (fun r : ℝ => angleNormalizedTravel Γ (r, η)) (Icc a b) :=
      hTravelContinuous.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun r hr => ⟨hr, mem_univ _⟩)
    simpa only [angleNormalizedTravel, hLeft, hRight] using
      ContinuousOn.image_Ioo_of_strictMonoOn hab.le hc (hTravelMono η)
  have hRecover (p : PolarPoint) (hp : p ∈ Icc a b ×ˢ univ) :
      angleNormalizedTravel Γ (p.1, (Γ p).2) = (Γ p).1 := by
    have hi : parameterizedCircleInverse (fun q => (Γ q).2) (p.1, (Γ p).2) = p.2 :=
      Function.leftInverse_invFun (hMono p.1 hp.1).injective p.2
    simp only [angleNormalizedTravel, hi, Prod.eta]
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    have hm : angleNormalizedTravel Γ (p.1, (Γ p).2) ∈ Ioo 0 W := by
      rw [← hImage (Γ p).2]
      exact ⟨p.1, hp.1, rfl⟩
    rw [hRecover p ⟨Ioo_subset_Icc_self hp.1, hp.2⟩] at hm
    exact ⟨hm, mem_univ _⟩
  · rintro ⟨r, θ⟩ hp ⟨s, η⟩ hq he
    have hφ : (Γ (r, θ)).2 = (Γ (s, η)).2 := congrArg Prod.snd he
    have hσ : (Γ (r, θ)).1 = (Γ (s, η)).1 := congrArg Prod.fst he
    have heTravel :
        angleNormalizedTravel Γ (r, (Γ (r, θ)).2) =
          angleNormalizedTravel Γ (s, (Γ (r, θ)).2) := by
      calc
        angleNormalizedTravel Γ (r, (Γ (r, θ)).2) = (Γ (r, θ)).1 :=
          hRecover (r, θ) ⟨Ioo_subset_Icc_self hp.1, mem_univ _⟩
        _ = (Γ (s, η)).1 := hσ
        _ = angleNormalizedTravel Γ (s, (Γ (s, η)).2) :=
          (hRecover (s, η) ⟨Ioo_subset_Icc_self hq.1, mem_univ _⟩).symm
        _ = angleNormalizedTravel Γ (s, (Γ (r, θ)).2) :=
          congrArg (fun v => angleNormalizedTravel Γ (s, v)) hφ.symm
    have hrs : r = s := (hTravelMono (Γ (r, θ)).2).injOn
      (Ioo_subset_Icc_self hp.1) (Ioo_subset_Icc_self hq.1) heTravel
    subst s
    exact Prod.ext rfl ((hMono r (Ioo_subset_Icc_self hp.1)).injective hφ)
  · intro y hy
    have hm : y.1 ∈ (fun r : ℝ => angleNormalizedTravel Γ (r, y.2)) '' Ioo a b := by
      rw [hImage y.2]
      exact hy.1
    obtain ⟨r, hr, he⟩ := hm
    refine ⟨(r, parameterizedCircleInverse (fun q => (Γ q).2) (r, y.2)),
      ⟨hr, mem_univ _⟩, ?_⟩
    apply Prod.ext he
    exact Function.rightInverse_invFun (hSurj r (Ioo_subset_Icc_self hr)) y.2

/-- The actual chosen inverse of the full travel chart takes values in the
physical open component, satisfies both inverse identities, and is smooth. -/
theorem travelStrip_inverse_spec
    {Γ : PolarPoint → PolarPoint} {a b W P : ℝ}
    (hab : a < b) (hP : P ≠ 0)
    (hClosed : ContinuousOn Γ (Icc a b ×ˢ univ))
    (hSmooth : ContDiffOn ℝ ∞ Γ (Ioo a b ×ˢ univ))
    (hAngle : ∀ p ∈ Ioo a b ×ˢ univ, 0 < angularPartial (fun q => (Γ q).2) p)
    (hJ : ∀ p ∈ Ioo a b ×ˢ univ, 0 < planeJacobian Γ p)
    (hPeriod : ∀ r ∈ Icc a b, ∀ θ : ℝ,
      (Γ (r, θ + P)).2 = (Γ (r, θ)).2 + P)
    (hLeftMono : StrictMono (fun θ : ℝ => (Γ (a, θ)).2))
    (hRightMono : StrictMono (fun θ : ℝ => (Γ (b, θ)).2))
    (hLeft : ∀ θ : ℝ, (Γ (a, θ)).1 = 0)
    (hRight : ∀ θ : ℝ, (Γ (b, θ)).1 = W) :
    MapsTo (Function.invFunOn Γ (Ioo a b ×ˢ univ))
        (Ioo 0 W ×ˢ univ) (Ioo a b ×ˢ univ) ∧
      LeftInvOn (Function.invFunOn Γ (Ioo a b ×ˢ univ)) Γ (Ioo a b ×ˢ univ) ∧
      RightInvOn (Function.invFunOn Γ (Ioo a b ×ˢ univ)) Γ (Ioo 0 W ×ˢ univ) ∧
      ContDiffOn ℝ ∞ (Function.invFunOn Γ (Ioo a b ×ˢ univ)) (Ioo 0 W ×ˢ univ) := by
  have hBij := travelStrip_bijOn hab hP hClosed hSmooth hAngle hJ hPeriod
    hLeftMono hRightMono hLeft hRight
  exact ⟨hBij.surjOn.mapsTo_invFunOn, hBij.injOn.leftInvOn_invFunOn,
    hBij.surjOn.rightInvOn_invFunOn,
    contDiffOn_planar_invFunOn_of_bijOn (isOpen_Ioo.prod isOpen_univ)
      (isOpen_Ioo.prod isOpen_univ) hSmooth (fun p hp => (hJ p hp).ne') hBij⟩

end ContinuousFlexibility.Analysis
