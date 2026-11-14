module

public import ContinuousFlexibility.Analysis.N05CanonicalInverseDefinition

/-!
# Linearity of the fixed source selection on actual volume levels

The forget map is linear in the genuine L² classes. Its actual canonical
representatives therefore identify the corresponding physical sources
almost everywhere. Positive weaker source membership justifies integrating
that identity, so the actual auxiliary correction is linear as well.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Radial

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
  {base loss : ℕ} {ε γ t : ℝ} {s : ℕ}

/-- Equality of the actual source classes supplies physical linearity;
no pointwise linearity of an L² representative is asserted. -/
theorem n05CanonicalSourceLift_linear_combination_ae
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (hV : IsVolumeModel T S K V)
    (v w : V.level γ t s) (c d : ℝ) :
    n05CanonicalSourceLift S C K (V.forget γ t s (c • v + d • w))
      =ᵐ[radialPhysicalMeasure D]
        (fun p => c * n05CanonicalSourceLift S C K (V.forget γ t s v) p +
          d * n05CanonicalSourceLift S C K (V.forget γ t s w) p) := by
  let F := V.forget γ t s
  have hrep (x : V.level γ t s) (m : ℕ) :
      (F x m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        canonicalSource S K (C.referenceState, 0) m
          (n05CanonicalSourceLift S C K (F x)) :=
    n05CanonicalSourceLift_source_ae h hcoordinates (F x)
      (n05_volumeMember_reflection hV (show VolumeMember S K V γ t s (F x) from ⟨x, rfl⟩)) m
  refine n05_referenceCanonicalSource_ae_physical h hcoordinates
    (n05CanonicalSourceLift_periodic S C K _) ?_ ?_
  · intro p
    change c * n05CanonicalSourceLift S C K (V.forget γ t s v) (p + (0, Real.pi)) +
      d * n05CanonicalSourceLift S C K (V.forget γ t s w) (p + (0, Real.pi)) =
        c * n05CanonicalSourceLift S C K (V.forget γ t s v) p +
          d * n05CanonicalSourceLift S C K (V.forget γ t s w) p
    rw [n05CanonicalSourceLift_periodic S C K (V.forget γ t s v) p,
      n05CanonicalSourceLift_periodic S C K (V.forget γ t s w) p]
  · intro m
    have hmap : F (c • v + d • w) m = c • F v m + d • F w m := by
      simp only [F, map_add, map_smul, Pi.add_apply, Pi.smul_apply]
    have hsum : (F (c • v + d • w) m : PolarPoint → ℝ)
        =ᵐ[canonicalMeasure S K m] (fun p => c * F v m p + d * F w m p) := by
      rw [hmap]
      filter_upwards [Lp.coeFn_add (c • F v m) (d • F w m),
        Lp.coeFn_smul c (F v m), Lp.coeFn_smul d (F w m)] with p hp hc hd
      rw [hp]
      simp only [Pi.add_apply, hc, hd, Pi.smul_apply, smul_eq_mul]
    filter_upwards [hrep (c • v + d • w) m, hrep v m, hrep w m, hsum]
      with p hp hv hw he
    rw [← hp, he]
    rw [hv, hw]
    simp only [canonicalSource]
    ring

/-- The actual normalized integral is linear because all three lifted
sources are integrable in the genuine physical measure. -/
theorem n05CanonicalAuxiliaryScalar_linear_combination
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (hV : IsVolumeModel T S K V) {γw : ℝ} (hγw : 0 < γw) (hgap : γw < γ)
    (M : ℝ) (v w : V.level γ t s) (c d : ℝ) :
    n05CanonicalAuxiliaryScalar D S C K (V.forget γ t s (c • v + d • w)) =
      c * n05CanonicalAuxiliaryScalar D S C K (V.forget γ t s v) +
        d * n05CanonicalAuxiliaryScalar D S C K (V.forget γ t s w) := by
  let F := V.forget γ t s
  let f : V.level γ t s → PolarPoint → ℝ := fun x => n05CanonicalSourceLift S C K (F x)
  obtain ⟨_, _, hsource⟩ :=
    n05_canonicalSourceLift_reference_bound hD hT h hcoordinates hV hγw hgap t M s
  letI : IsFiniteMeasure (radialPhysicalMeasure D) := ⟨r11b_radialPhysicalMeasure_finite D⟩
  have hi (x : V.level γ t s) : Integrable (f x) (radialPhysicalMeasure D) :=
    (r11b_sourceDerivative_memLp hD hγw (hsource x).1).integrable (by norm_num)
  have hmean (x : V.level γ t s) :
      n05CanonicalAuxiliaryScalar D S C K (F x) =
        (2 * Real.pi)⁻¹ * ∫ p, f x p ∂radialPhysicalMeasure D :=
    r11b_integral_angularMean_eq hD.choose_spec.1.2.1.le (hi x)
  have hlin := n05CanonicalSourceLift_linear_combination_ae h hcoordinates hV v w c d
  calc
    _ = (2 * Real.pi)⁻¹ * ∫ p, f (c • v + d • w) p ∂radialPhysicalMeasure D :=
      hmean (c • v + d • w)
    _ = (2 * Real.pi)⁻¹ * ∫ p, c * f v p + d * f w p ∂radialPhysicalMeasure D := by
      rw [integral_congr_ae hlin]
    _ = _ := by
      rw [integral_add ((hi v).const_mul c) ((hi w).const_mul d),
        integral_const_mul, integral_const_mul, hmean v, hmean w]
      ring

@[simp] theorem n05CanonicalNormalizedSource_snd (D : ReferenceData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (K : CanonicalData S)
    (F : CanonicalSequence S K) :
    (n05CanonicalNormalizedSource D S C K F).2 = 0 := rfl

/-- The same corrected source is linear in its physical equivalence class,
including its literal zero row scalar. -/
theorem n05CanonicalNormalizedSource_linear_combination_ae
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (hV : IsVolumeModel T S K V) {γw : ℝ} (hγw : 0 < γw) (hgap : γw < γ)
    (M : ℝ) (v w : V.level γ t s) (c d : ℝ) :
    (n05CanonicalNormalizedSource D S C K (V.forget γ t s (c • v + d • w))).2 =
      (c • n05CanonicalNormalizedSource D S C K (V.forget γ t s v) +
        d • n05CanonicalNormalizedSource D S C K (V.forget γ t s w)).2 ∧
    (n05CanonicalNormalizedSource D S C K (V.forget γ t s (c • v + d • w))).1
      =ᵐ[radialPhysicalMeasure D]
        (c • n05CanonicalNormalizedSource D S C K (V.forget γ t s v) +
          d • n05CanonicalNormalizedSource D S C K (V.forget γ t s w)).1 := by
  refine ⟨?_, ?_⟩
  · change (0 : ℝ) = c * 0 + d * 0
    ring
  have hLambda := n05CanonicalAuxiliaryScalar_linear_combination hD hT h hcoordinates hV
    hγw hgap M v w c d
  filter_upwards [n05CanonicalSourceLift_linear_combination_ae h hcoordinates hV v w c d]
    with p hp
  change n05CanonicalSourceLift S C K (V.forget γ t s (c • v + d • w)) p -
      n05CanonicalAuxiliaryScalar D S C K (V.forget γ t s (c • v + d • w)) *
        (S.height (3 / 4 : ℝ)).decode S.psi p =
    c * (n05CanonicalSourceLift S C K (V.forget γ t s v) p -
      n05CanonicalAuxiliaryScalar D S C K (V.forget γ t s v) *
        (S.height (3 / 4 : ℝ)).decode S.psi p) +
    d * (n05CanonicalSourceLift S C K (V.forget γ t s w) p -
      n05CanonicalAuxiliaryScalar D S C K (V.forget γ t s w) *
        (S.height (3 / 4 : ℝ)).decode S.psi p)
  rw [hp, hLambda]
  ring

end ContinuousFlexibility.Statements
