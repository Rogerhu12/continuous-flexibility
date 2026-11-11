import ContinuousFlexibility.Analysis.ReturnCorrectionPatching
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Reflection parity of the actual return-corrected coefficients

The reflection identities below use the actual total Fréchet derivative.
Composition with a continuous linear equivalence is valid also at points
where the derivative is totalized to zero. Consequently the coefficient
parity is global, as required by N03, and does not require extending an
interior smoothness hypothesis to the turning points or annulus endpoints.
-/

noncomputable section

namespace ContinuousFlexibility

set_option backward.isDefEq.respectTransparency false

/-- The total Fréchet derivative transforms under angular reflection. -/
theorem fderiv_angular_reflection_apply (f : PolarPoint → ℝ) (p v : PolarPoint) :
    fderiv ℝ (fun q : PolarPoint => f (q.1, -q.2)) p v =
      fderiv ℝ f (p.1, -p.2) (v.1, -v.2) := by
  let R : PolarPoint ≃L[ℝ] PolarPoint :=
    (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (ContinuousLinearEquiv.neg ℝ)
  have hR (q : PolarPoint) : R q = (q.1, -q.2) := by
    simp only [R, ContinuousLinearEquiv.prodCongr_apply,
      ContinuousLinearEquiv.refl_apply, ContinuousLinearEquiv.neg_apply]
  have hfun : f ∘ R = fun q : PolarPoint => f (q.1, -q.2) := by
    funext q
    exact congrArg f (hR q)
  have hf := R.comp_right_fderiv (f := f) (x := p)
  rw [hfun] at hf
  have hv := congrArg (fun A : PolarPoint →L[ℝ] ℝ => A v) hf
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, hR] using hv

theorem radialPartial_angular_reflection (f : PolarPoint → ℝ) (p : PolarPoint) :
    radialPartial (fun q : PolarPoint => f (q.1, -q.2)) p =
      radialPartial f (p.1, -p.2) := by
  simpa only [radialPartial, neg_zero] using fderiv_angular_reflection_apply f p (1, 0)

theorem angularPartial_angular_reflection (f : PolarPoint → ℝ) (p : PolarPoint) :
    angularPartial (fun q : PolarPoint => f (q.1, -q.2)) p =
      -angularPartial f (p.1, -p.2) := by
  have h := fderiv_angular_reflection_apply f p (0, 1)
  have hv : ((0 : ℝ), -(1 : ℝ)) = -((0, 1) : PolarPoint) := by
    simp only [Prod.neg_mk, neg_zero]
  rw [hv, map_neg] at h
  exact h

theorem radialPartial_neg_total (f : PolarPoint → ℝ) (p : PolarPoint) :
    radialPartial (fun q => -f q) p = -radialPartial f p := by
  simp only [radialPartial, fderiv_fun_neg, ContinuousLinearMap.neg_apply]

theorem angularPartial_neg_total (f : PolarPoint → ℝ) (p : PolarPoint) :
    angularPartial (fun q => -f q) p = -angularPartial f p := by
  simp only [angularPartial, fderiv_fun_neg, ContinuousLinearMap.neg_apply]

theorem radialPartial_of_even (f : PolarPoint → ℝ)
    (hf : ∀ r θ, f (r, -θ) = f (r, θ)) (r θ : ℝ) :
    radialPartial f (r, -θ) = radialPartial f (r, θ) := by
  have heq : (fun q : PolarPoint => f (q.1, -q.2)) = f :=
    funext fun q => hf q.1 q.2
  have h := radialPartial_angular_reflection f (r, θ)
  rw [heq] at h
  exact h.symm

theorem angularPartial_of_even (f : PolarPoint → ℝ)
    (hf : ∀ r θ, f (r, -θ) = f (r, θ)) (r θ : ℝ) :
    angularPartial f (r, -θ) = -angularPartial f (r, θ) := by
  have heq : (fun q : PolarPoint => f (q.1, -q.2)) = f :=
    funext fun q => hf q.1 q.2
  have h := angularPartial_angular_reflection f (r, θ)
  rw [heq] at h
  linarith

theorem radialPartial_of_odd (f : PolarPoint → ℝ)
    (hf : ∀ r θ, f (r, -θ) = -f (r, θ)) (r θ : ℝ) :
    radialPartial f (r, -θ) = -radialPartial f (r, θ) := by
  have heq : (fun q : PolarPoint => f (q.1, -q.2)) = fun q => -f q :=
    funext fun q => hf q.1 q.2
  have h := radialPartial_angular_reflection f (r, θ)
  rw [heq, radialPartial_neg_total] at h
  exact h.symm

theorem angularPartial_of_odd (f : PolarPoint → ℝ)
    (hf : ∀ r θ, f (r, -θ) = -f (r, θ)) (r θ : ℝ) :
    angularPartial f (r, -θ) = angularPartial f (r, θ) := by
  have heq : (fun q : PolarPoint => f (q.1, -q.2)) = fun q => -f q :=
    funext fun q => hf q.1 q.2
  have h := angularPartial_angular_reflection f (r, θ)
  rw [heq, angularPartial_neg_total] at h
  linarith

/-- An even actual height has the even/odd/even parity of the three
actual type-corrected symmetric coefficients. -/
theorem polarLinearCoefficients_parity (w : ℝ → ℝ) (z : PolarPoint → ℝ)
    (hz : ∀ r θ, z (r, -θ) = z (r, θ)) (r θ : ℝ) :
    polarLinearA w z (r, -θ) = polarLinearA w z (r, θ) ∧
    polarLinearB w z (r, -θ) = -polarLinearB w z (r, θ) ∧
    polarCorrectedC w z (r, -θ) = polarCorrectedC w z (r, θ) := by
  have hk : ∀ s t, heightRadial z (s, -t) = heightRadial z (s, t) :=
    radialPartial_of_even z hz
  have hp : ∀ s t, heightAngular z (s, -t) = -heightAngular z (s, t) := by
    intro s t
    simp only [heightAngular, angularPartial_of_even z hz, neg_div]
  have hkr := radialPartial_of_even (heightRadial z) hk
  have hpr := radialPartial_of_odd (heightAngular z) hp
  have hpt := angularPartial_of_odd (heightAngular z) hp
  have hE : ∀ s t, profileEnergy w (s, -t) = profileEnergy w (s, t) := fun _ _ => rfl
  have hEr := radialPartial_of_even (profileEnergy w) hE
  have hdisc : polarDiscriminant w z (r, -θ) = polarDiscriminant w z (r, θ) := by
    simp only [polarDiscriminant, heightDiscriminant, hE, hk, hp, neg_sq]
  have hs : polarScale w z (r, -θ) = polarScale w z (r, θ) := by
    simp only [polarScale, hdisc]
  refine ⟨?_, ?_, ?_⟩
  · simp only [polarLinearA, hE, hk, hpt, hs]
  · simp only [polarLinearB, hE, hpr, hs, linearMixed]
    ring
  · simp only [polarCorrectedC, hE, hEr, hk, hp, hkr, hpr, hpt, hs,
      correctedAngular, scaledCoordinateResidual, darbouxNumerator, neg_sq]

end ContinuousFlexibility

namespace ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

theorem stateHeight_even_of_physical
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (C : NonlinearGeometryData S)
    (z : AnnularState S × ℝ) (r θ : ℝ) :
    stateHeight D S C z (r, -θ) = stateHeight D S C z (r, θ) := by
  obtain ⟨_, _, _, hmember, _⟩ := hS.1 (3 / 4 : ℝ)
  have hu := (hmember z.1.1.1).2.1 r θ
  simp only [stateHeight, stateU, heightPairField, hu]

theorem originalCoefficients_parity_of_physical
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (C : NonlinearGeometryData S)
    (z : AnnularState S × ℝ) (r θ : ℝ) :
    (originalCoefficients D S C z).a (r, -θ) = (originalCoefficients D S C z).a (r, θ) ∧
    (originalCoefficients D S C z).b (r, -θ) = -(originalCoefficients D S C z).b (r, θ) ∧
    (originalCoefficients D S C z).c (r, -θ) = (originalCoefficients D S C z).c (r, θ) :=
  polarLinearCoefficients_parity (stateProfile D S C z.1) (stateHeight D S C z)
    (stateHeight_even_of_physical hS C z) r θ

/-- The global actual patch has precisely the parity required by N03,
using the existing physical height realization. -/
theorem returnCorrectedCoefficients_parity_of_physical
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (C : NonlinearGeometryData S)
    (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ) (r θ : ℝ) :
    (returnCorrectedCoefficients D S C χ z).a (r, -θ) =
        (returnCorrectedCoefficients D S C χ z).a (r, θ) ∧
    (returnCorrectedCoefficients D S C χ z).b (r, -θ) =
        -(returnCorrectedCoefficients D S C χ z).b (r, θ) ∧
    (returnCorrectedCoefficients D S C χ z).c (r, -θ) =
        (returnCorrectedCoefficients D S C χ z).c (r, θ) :=
  returnCorrectedCoefficients_parity D S C χ z
    (fun s t => (originalCoefficients_parity_of_physical hS C z s t).1)
    (fun s t => (originalCoefficients_parity_of_physical hS C z s t).2.1)
    (fun s t => (originalCoefficients_parity_of_physical hS C z s t).2.2) r θ

end ContinuousFlexibility.Statements
