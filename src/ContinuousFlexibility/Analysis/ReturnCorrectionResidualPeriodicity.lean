module

public import ContinuousFlexibility.Analysis.ReturnCorrectionResidualCompatibility
public import ContinuousFlexibility.Scalar.GreenIdentity
public import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Periodicity of the independent return error

The actual inverse maps, interpolation inverse, and removable divided
difference all preserve the circle period. Hence the frozen coefficient
error, its two fluxes, and its scalar divergence are periodic for every
independent residual. The source compatibility theorem consequently
requires only regularity of those actual fluxes, with periodicity and
radial boundary matching proved from the original data.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

theorem returnLift_surjective {f : ℝ → ℝ} {P : ℝ} (hP : 0 < P)
    (hf : Continuous f) (hlift : ∀ x, f (x + P) = f x + P) :
    Function.Surjective f := by
  have hn (x : ℝ) (n : ℕ) : f (x + (n : ℝ) * P) = f x + (n : ℝ) * P := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show x + ((n + 1 : ℕ) : ℝ) * P = (x + (n : ℝ) * P) + P by
        push_cast; ring, hlift, ih]
      push_cast
      ring
  intro y
  apply mem_range_of_exists_le_of_exists_ge hf
  · obtain ⟨n, hny⟩ := exists_nat_gt ((f 0 - y) / P)
    have hbound := (div_lt_iff₀ hP).mp hny
    have heq := hn (-(n : ℝ) * P) n
    rw [show -(n : ℝ) * P + (n : ℝ) * P = 0 by ring] at heq
    exact ⟨-(n : ℝ) * P, by linarith⟩
  · obtain ⟨n, hny⟩ := exists_nat_gt ((y - f 0) / P)
    have hbound := (div_lt_iff₀ hP).mp hny
    refine ⟨(n : ℝ) * P, ?_⟩
    have heq := hn 0 n
    simp only [zero_add] at heq
    rw [heq]
    linarith

theorem returnLift_deriv_periodic {f : ℝ → ℝ} {P : ℝ}
    (hlift : ∀ x, f (x + P) = f x + P) :
    Function.Periodic (deriv f) P := by
  intro x
  rw [← deriv_comp_add_const f P x,
    show (fun t => f (t + P)) = (fun t => f t + P) from funext hlift,
    deriv_add_const]

theorem returnLift_dslope_add_period {f : ℝ → ℝ} {P : ℝ}
    (hlift : ∀ x, f (x + P) = f x + P) (x y : ℝ) :
    dslope f (x + P) (y + P) = dslope f x y := by
  by_cases hxy : y = x
  · subst y
    simpa only [dslope_same] using returnLift_deriv_periodic hlift x
  · apply mul_left_cancel₀ (sub_ne_zero.mpr hxy)
    calc
      (y - x) * dslope f (x + P) (y + P) =
          ((y + P) - (x + P)) * dslope f (x + P) (y + P) := by ring
      _ = f (y + P) - f (x + P) := by
        simpa only [smul_eq_mul] using sub_smul_dslope f (x + P) (y + P)
      _ = f y - f x := by rw [hlift, hlift]; ring
      _ = (y - x) * dslope f x y := by
        simpa only [smul_eq_mul] using (sub_smul_dslope f x y).symm

theorem returnLift_invFun_add_period {f : ℝ → ℝ} {P : ℝ}
    (hinj : Function.Injective f) (hsurj : Function.Surjective f)
    (hlift : ∀ x, f (x + P) = f x + P) (x : ℝ) :
    Function.invFun f (x + P) = Function.invFun f x + P :=
  returnChart_inverse_add_period f (Function.invFun f) P hlift
    (Function.leftInverse_invFun hinj) (Function.rightInverse_invFun hsurj) x

theorem returnDisplacementFactor_periodic
    (f h G e u : ℝ → ℝ) (P : ℝ)
    (hf : ∀ x, f (x + P) = f x + P)
    (hh : ∀ x, h (x + P) = h x + P)
    (hG : ∀ x, G (x + P) = G x + P)
    (he : Function.Periodic e P) (hu : Function.Periodic u P) :
    Function.Periodic (fun θ =>
      dslope G (h (f θ)) (h (f θ) + e (h (f θ))) * u (h (f θ))) P := by
  intro θ
  dsimp only
  rw [hf, hh, he, hu,
    show h (f θ) + P + e (h (f θ)) = (h (f θ) + e (h (f θ))) + P by ring,
    returnLift_dslope_add_period hG]

/-- The velocity factor is a scalar periodic expression. Keeping this
calculation outside the physical-model types avoids unfolding their
linear maps during the periodicity proof. -/
theorem returnVelocityFactor_periodic
    (f J d : ℝ → ℝ) (c P : ℝ)
    (hfi : Function.Injective f) (hfs : Function.Surjective f)
    (hJi : Function.Injective J) (hJs : Function.Surjective J)
    (hf : ∀ x, f (x + P) = f x + P)
    (hJ : ∀ x, J (x + P) = J x + P) (hd : Function.Periodic d P) :
    Function.Periodic (fun x => deriv f (Function.invFun f x) * c *
      d (Function.invFun J (Function.invFun f x))) P := by
  intro x
  dsimp only
  rw [returnLift_invFun_add_period hfi hfs hf,
    returnLift_invFun_add_period hJi hJs hJ,
    returnLift_deriv_periodic hf, hd]

theorem periodic_reflected_drift_speed
    (v : ℝ → ℝ) {P : ℝ} (hv : Function.Periodic v P) (θ : ℝ) :
    (v (θ + P) - v (-(θ + P))) / 2 = (v θ - v (-θ)) / 2 ∧
      (-v (-(θ + P)) - v (θ + P)) / 2 = (-v (-θ) - v θ) / 2 := by
  have hn := hv (-θ - P)
  rw [show -θ - P + P = -θ by ring] at hn
  have hneg : v (-(θ + P)) = v (-θ) := by
    rw [show -(θ + P) = -θ - P by ring]
    exact hn.symm
  rw [hv θ, hneg]
  exact ⟨rfl, rfl⟩

section ActualCharts

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN01 : N01Properties D T S C base loss ε)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hsector : stateSector S z.1)

include hN01 hz

theorem N01Properties.minusFlow_add_period (m : ℕ) {r : ℝ}
    (hr : r ∈ Icc (C.left m) (C.right m)) (θ : ℝ) :
    C.minusFlow z m r (θ + Real.pi) = C.minusFlow z m r θ + Real.pi := by
  have hflow : ordinaryFlowConditions D S C (stateNeighborhood S C base ε) :=
    hN01.2.2.2.2.2.2.1
  exact ((hflow z hz m θ).2.2.2 r hr).2

include hsector

theorem N01Properties.minusReturnInverse_add_period (m : ℕ) (θ : ℝ) :
    C.minusReturnInverse z m (θ + Real.pi) =
      C.minusReturnInverse z m θ + Real.pi := by
  have hC : controlGeometryConditions D S C := hN01.2.2.2.1
  have hI := N01Properties.return_inverse_and_positive S C z m hN01 hz hsector
  exact returnChart_inverse_add_period _ _ Real.pi
    (hN01.minusFlow_add_period hz m ⟨(hC.1 m).2.1.le, le_rfl⟩)
    (fun t => (hI t).2.1) (fun t => (hI t).1) θ

theorem N01Properties.rightChartCandidate_add_period (m : ℕ) (θ : ℝ) :
    rightChartCandidate S C z m (θ + Real.pi) =
      rightChartCandidate S C z m θ + Real.pi := by
  have hleft := hN01.2.2.2.2.2.2.2.1 z hz hsector m
  exact ContinuousFlexibility.Statements.rightChartCandidate_add_period S C z m Real.pi
    (fun t => (hleft t).2.2.1)
    (hN01.minusReturnInverse_add_period hz hsector m) θ

theorem N01Properties.rightChartInverse_add_period (m : ℕ) (θ : ℝ) :
    C.rightChartInverse z m (θ + Real.pi) =
      C.rightChartInverse z m θ + Real.pi := by
  have hI := N01Properties.return_inverse_and_positive S C z m hN01 hz hsector
  exact returnChart_inverse_add_period _ _ Real.pi
    (hN01.rightChartCandidate_add_period hz hsector m)
    (fun t => (hI t).2.2.2.1) (fun t => (hI t).2.2.1) θ

theorem N01Properties.returnCorrectionInitialMap_add_period (m : ℕ) (θ : ℝ) :
    returnCorrectionInitialMap S C z m (θ + Real.pi) =
      returnCorrectionInitialMap S C z m θ + Real.pi := by
  have hleft := hN01.2.2.2.2.2.2.2.1 z hz hsector m
  rw [returnCorrectionInitialMap_apply, (hleft θ).2.2.1,
    show stateLeftChart S z.1 m θ + Real.pi - C.travel m =
      (stateLeftChart S z.1 m θ - C.travel m) + Real.pi by ring,
    hN01.rightChartInverse_add_period hz hsector m,
    hN01.minusReturnInverse_add_period hz hsector m, returnCorrectionInitialMap_apply]

theorem N01Properties.returnResidualField_periodic (m : ℕ) :
    Function.Periodic (returnResidualField S C z m) Real.pi := by
  have hleft := hN01.2.2.2.2.2.2.2.1 z hz hsector m
  have hI := N01Properties.return_inverse_and_positive S C z m hN01 hz hsector
  exact returnResidualField_add_period S C z m Real.pi
    (fun t => (hleft t).2.2.1)
    (hN01.minusReturnInverse_add_period hz hsector m)
    (fun t => (hI t).2.2.2.1) (fun t => (hI t).2.2.1)

theorem N01Properties.returnCorrectionInitialMap_continuous
    (hS : IsPhysicalSpaces D T S) (m : ℕ) :
    Continuous (returnCorrectionInitialMap S C z m) := by
  have hfi := N01Properties.minusReturnInverse_differentiable S C z m hN01 hz hsector
  have hhi := N01Properties.rightChartInverse_differentiable S C z m hN01 hz hsector
  have hL := stateLeftChart_contDiff S z m (hS.2.1 (3 / 4 : ℝ))
  exact hfi.continuous.comp (hhi.continuous.comp (hL.continuous.sub continuous_const))

theorem N01Properties.returnCorrectionDisplacementLinear_periodic
    (hS : IsPhysicalSpaces D T S) (m : ℕ) (ρ : CircleSpace S) :
    Function.Periodic (fun θ => returnCorrectionDisplacementLinear S C z m θ ρ) Real.pi := by
  have hC : controlGeometryConditions D S C := hN01.2.2.2.1
  have hf := hN01.minusFlow_add_period hz m ⟨(hC.1 m).2.1.le, le_rfl⟩
  have hh := hN01.rightChartCandidate_add_period hz hsector m
  have he := hN01.returnResidualField_periodic hz hsector m
  have hρ := (((hS.2.1 (3 / 4 : ℝ)).2.2.2.1 ρ).1 m).2
  let G : ℝ → ℝ := fun t => C.minusReturnInverse z m (C.rightChartInverse z m t)
  have hG : ∀ t, G (t + Real.pi) = G t + Real.pi := by
    intro t
    dsimp only [G]
    rw [hN01.rightChartInverse_add_period hz hsector m,
      hN01.minusReturnInverse_add_period hz hsector m]
  have hscalar := returnDisplacementFactor_periodic
    (C.minusFlow z m (C.right m)) (rightChartCandidate S C z m) G
    (returnResidualField S C z m) ((S.circle (3 / 4 : ℝ)).decode ρ m) Real.pi
    hf hh hG he hρ
  intro θ
  exact (returnCorrectionDisplacementLinear_apply S C z m (θ + Real.pi) ρ).trans
    ((hscalar θ).trans (returnCorrectionDisplacementLinear_apply S C z m θ ρ).symm)

theorem N01Properties.returnCorrectionVelocityLinear_periodic
    (hS : IsPhysicalSpaces D T S) (χ : ℕ → ℝ → ℝ) (m : ℕ) {r : ℝ}
    (hr : r ∈ Icc (C.left m) (C.right m)) (hχ : χ m r ∈ Icc (0 : ℝ) 1)
    (ρ : CircleSpace S) :
    Function.Periodic (fun θ => returnCorrectionVelocityLinear D S C χ z m (r, θ) ρ)
      Real.pi := by
  have hf := hN01.minusFlow_add_period hz m hr
  have hflow : ordinaryFlowConditions D S C (stateNeighborhood S C base ε) :=
    hN01.2.2.2.2.2.2.1
  have hfinj : Function.Injective (C.minusFlow z m r) :=
    (strictMono_of_deriv_pos (fun θ => ((hflow z hz m θ).2.2.2 r hr).1)).injective
  have hfsurj := returnLift_surjective Real.pi_pos
    (N01Properties.minusFlow_differentiable S C z m hN01 hz hr).continuous hf
  have hK := hN01.returnCorrectionInitialMap_add_period hz hsector m
  have hJ := returnInterpolation_periodic_lift hK (χ m r)
  have hJinj : Function.Injective
      (returnInterpolation (χ m r) (returnCorrectionInitialMap S C z m)) :=
    (returnInterpolation_strictMono hχ.1 hχ.2
      (hN01.returnCorrectionInitialMap_strictMono hz hsector m)).injective
  have hJcont : Continuous
      (returnInterpolation (χ m r) (returnCorrectionInitialMap S C z m)) :=
    continuous_id.add (continuous_const.mul
      ((hN01.returnCorrectionInitialMap_continuous hz hsector hS m).sub continuous_id))
  have hJsurj := returnLift_surjective Real.pi_pos hJcont hJ
  have hdisp := hN01.returnCorrectionDisplacementLinear_periodic hz hsector hS m ρ
  have hscalar := returnVelocityFactor_periodic (C.minusFlow z m r)
    (returnInterpolation (χ m r) (returnCorrectionInitialMap S C z m))
    (fun θ => returnCorrectionDisplacementLinear S C z m θ ρ)
    (deriv (χ m) r) Real.pi hfinj hfsurj hJinj hJsurj hf hJ hdisp
  intro θ
  exact (returnCorrectionVelocityLinear_apply D S C χ z m (r, θ + Real.pi) ρ).trans
    ((hscalar θ).trans (returnCorrectionVelocityLinear_apply D S C χ z m (r, θ) ρ).symm)

theorem N01Properties.returnCorrectionDriftSpeedLinear_periodic
    (hS : IsPhysicalSpaces D T S) (χ : ℕ → ℝ → ℝ) (m : ℕ) {r : ℝ}
    (hr : r ∈ Icc (C.left m) (C.right m)) (hχ : χ m r ∈ Icc (0 : ℝ) 1)
    (ρ : CircleSpace S) (θ : ℝ) :
    returnCorrectionDriftLinear D S C χ z m (r, θ + Real.pi) ρ =
        returnCorrectionDriftLinear D S C χ z m (r, θ) ρ ∧
    returnCorrectionSpeedLinear D S C χ z m (r, θ + Real.pi) ρ =
        returnCorrectionSpeedLinear D S C χ z m (r, θ) ρ := by
  have hv := hN01.returnCorrectionVelocityLinear_periodic hz hsector hS χ m hr hχ ρ
  have h := periodic_reflected_drift_speed
    (fun t => returnCorrectionVelocityLinear D S C χ z m (r, t) ρ) hv θ
  exact ⟨(returnCorrectionDriftLinear_apply D S C χ z m (r, θ + Real.pi) ρ).trans
      (h.1.trans (returnCorrectionDriftLinear_apply D S C χ z m (r, θ) ρ).symm),
    (returnCorrectionSpeedLinear_apply D S C χ z m (r, θ + Real.pi) ρ).trans
      (h.2.trans (returnCorrectionSpeedLinear_apply D S C χ z m (r, θ) ρ).symm)⟩

end ActualCharts

theorem heightPairField_periodic_of_physical
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (η : HeightPair S) :
    Function.Periodic (heightPairField S η) (0, Real.pi) := by
  have hu := ((hS.1 (3 / 4 : ℝ)).2.2.2.1 η.1).2.2.1
  intro p
  simp only [heightPairField, Prod.fst_add, add_zero]
  rw [hu p]

theorem originalCoefficients_periodic_of_physical
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (C : NonlinearGeometryData S) (z : AnnularState S × ℝ) :
    Function.Periodic (originalCoefficients D S C z).a (0, Real.pi) ∧
      Function.Periodic (originalCoefficients D S C z).b (0, Real.pi) ∧
      Function.Periodic (originalCoefficients D S C z).c (0, Real.pi) := by
  have hu := heightPairField_periodic_of_physical hS z.1.1
  have hz : Function.Periodic (stateHeight D S C z) (0, Real.pi) := by
    intro p
    simp only [stateHeight, stateU, Prod.fst_add, add_zero]
    rw [hu p]
  exact periodic_heightCorrectedCoefficients (stateProfile D S C z.1) hz

section ActualError

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN01 : N01Properties D T S C base loss ε) (hS : IsPhysicalSpaces D T S)
  (R : ReturnEquationData S) (χ : ℕ → ℝ → ℝ)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hsector : stateSector S z.1)

include hN01 hS hz hsector

theorem N01Properties.returnCorrectionLocalCoefficientError_periodic
    (m : ℕ) {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m))
    (hχ : χ m r ∈ Icc (0 : ℝ) 1) (ρ : CircleSpace S) (θ : ℝ) :
    returnCorrectionLocalCoefficientError D S C R χ z m (r, θ + Real.pi) ρ =
      returnCorrectionLocalCoefficientError D S C R χ z m (r, θ) ρ := by
  have hp := originalCoefficients_periodic_of_physical hS C z
  have ha : (originalCoefficients D S C z).a (r, θ + Real.pi) =
      (originalCoefficients D S C z).a (r, θ) := by
    simpa only [Prod.mk_add_mk, add_zero] using hp.1 (r, θ)
  have hb : (originalCoefficients D S C z).b (r, θ + Real.pi) =
      (originalCoefficients D S C z).b (r, θ) := by
    simpa only [Prod.mk_add_mk, add_zero] using hp.2.1 (r, θ)
  have hc : (originalCoefficients D S C z).c (r, θ + Real.pi) =
      (originalCoefficients D S C z).c (r, θ) := by
    simpa only [Prod.mk_add_mk, add_zero] using hp.2.2 (r, θ)
  have hs := hN01.returnCorrectionDriftSpeedLinear_periodic hz hsector hS χ m hr hχ ρ θ
  have he := hN01.returnCorrectionDriftSpeedLinear_periodic hz hsector hS χ m hr hχ
    (R.residual z) θ
  simp only [returnCorrectionLocalCoefficientError, returnCoefficientError_apply,
    ha, hb, hc, hs.1, hs.2, he.1, he.2]

theorem N01Properties.returnCorrectionCoefficientError_periodic
    (hχ : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (ρ : CircleSpace S) (r θ : ℝ) :
    returnCorrectionCoefficientError D S C R χ z (r, θ + Real.pi) ρ =
      returnCorrectionCoefficientError D S C R χ z (r, θ) ρ := by
  classical
  by_cases h : ∃ m, r ∈ Ioo (C.left m) (C.right m) ∧ deriv (χ m) r ≠ 0
  · have hm := Classical.choose_spec h
    have hr : r ∈ Icc (C.left (Classical.choose h)) (C.right (Classical.choose h)) :=
      ⟨hm.1.1.le, hm.1.2.le⟩
    simpa only [returnCorrectionCoefficientError, dif_pos h] using
      hN01.returnCorrectionLocalCoefficientError_periodic hS R χ hz hsector
        (Classical.choose h) hr (hχ _ _ hr) ρ θ
  · simp only [returnCorrectionCoefficientError, dif_neg h, LinearMap.zero_apply]

theorem N01Properties.returnCorrectionErrorFluxes_periodic
    (hχ : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (ρ : CircleSpace S) (η : HeightPair S) :
    Function.Periodic (returnCorrectionRadialErrorFlux D S C R χ z ρ η) (0, Real.pi) ∧
      Function.Periodic (returnCorrectionAngularErrorFlux D S C R χ z ρ η) (0, Real.pi) := by
  have hu := heightPairField_periodic_of_physical hS η
  have hur := periodic_radialPartial hu
  have huθ := periodic_angularPartial hu
  have hcoeff := hN01.returnCorrectionCoefficientError_periodic hS R χ hz hsector hχ ρ
  constructor <;> rintro ⟨r, θ⟩
  · have hr := hur (r, θ)
    have ht := huθ (r, θ)
    simp only [Prod.mk_add_mk, add_zero] at hr ht
    simp only [returnCorrectionRadialErrorFlux, Prod.mk_add_mk, add_zero, hcoeff, ht]
  · have hr := hur (r, θ)
    have ht := huθ (r, θ)
    simp only [Prod.mk_add_mk, add_zero] at hr ht
    simp only [returnCorrectionAngularErrorFlux, Prod.mk_add_mk, add_zero, hcoeff, hr, ht]

theorem N01Properties.returnCorrectionResidualErrorField_periodic
    (hχ : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (ρ : CircleSpace S) (η : HeightPair S) :
    Function.Periodic (returnCorrectionResidualErrorField D S C R χ z ρ η)
      (0, Real.pi) := by
  classical
  have hf := hN01.returnCorrectionErrorFluxes_periodic hS R χ hz hsector hχ ρ η
  have hF := periodic_radialPartial hf.1
  have hG := periodic_angularPartial hf.2
  intro p
  by_cases hp : p ∈ annularOpen D
  · have hp' : p + (0, Real.pi) ∈ annularOpen D :=
      ⟨by simpa only [Prod.fst_add, add_zero] using hp.1, mem_univ _⟩
    simp only [returnCorrectionResidualErrorField, if_pos hp, if_pos hp']
    exact congrArg₂ (· + ·) (hF p) (hG p)
  · have hp' : p + (0, Real.pi) ∉ annularOpen D := by
      intro h
      apply hp
      exact ⟨by simpa only [Prod.fst_add, add_zero] using h.1, mem_univ _⟩
    simp only [returnCorrectionResidualErrorField, if_neg hp, if_neg hp']

/-- The actual periodicity and radial boundary terms are now fully
discharged. The only input is C¹ regularity of the actual frozen fluxes. -/
theorem N01Properties.returnCorrectionResidualErrorField_sourceIntegral_eq_zero_of_regular
    (hχ : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (ρ : CircleSpace S) (η : HeightPair S)
    (hF : ∀ p ∈ uIcc D.a D.b ×ˢ uIcc (0 : ℝ) Real.pi,
      ContDiffAt ℝ 1 (returnCorrectionRadialErrorFlux D S C R χ z ρ η) p)
    (hG : ∀ p ∈ uIcc D.a D.b ×ˢ uIcc (0 : ℝ) Real.pi,
      ContDiffAt ℝ 1 (returnCorrectionAngularErrorFlux D S C R χ z ρ η) p) :
    physicalSourceIntegral D (returnCorrectionResidualErrorField D S C R χ z ρ η) = 0 := by
  apply returnCorrectionResidualErrorField_sourceIntegral_eq_zero
    hN01.2.2.2.1 R χ z ρ η hF hG
  intro r _
  simpa only [Prod.mk_add_mk, add_zero, zero_add] using
    (hN01.returnCorrectionErrorFluxes_periodic hS R χ hz hsector hχ ρ η).2 (r, 0)

end ActualError

end ContinuousFlexibility.Statements
