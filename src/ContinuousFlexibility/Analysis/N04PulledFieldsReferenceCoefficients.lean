module

public import ContinuousFlexibility.Analysis.N04PulledFieldsCoefficientRegularity
public import ContinuousFlexibility.Analysis.N01OriginalCoefficientTameBounds
public import ContinuousFlexibility.Analysis.N05ReferenceResidual

/-!
# The retained coefficient jets at the actual reference

The actual N02 residual vanishes at the reference state. Linearity of
the retained coefficient error then identifies each corrected physical
coefficient with its original reference coefficient on the open annulus.
Consequently the existing uniform reference spatial bounds apply before
any inverse-chart substitution or material-envelope transfer.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry

local instance n04PulledFieldsReferenceCoefficientsStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

set_option backward.isDefEq.respectTransparency false

/-- At the actual reference the linear correction error is zero, so the
retained physical coefficients equal the original physical coefficients. -/
theorem n04PulledFields_correctedCoefficient_reference_eq
    (W : N04RealizationStart) (i : Fin 3) :
    EqOn (canonicalCoefficientComponent i (W.L.coefficients (W.C.referenceState, 0)))
      (originalCoefficientEntry W.D W.S W.C i (W.C.referenceState, 0))
      (annularOpen W.D) := by
  intro p hp
  have hz := n05_referenceState_mem (S := W.S) (C := W.C)
    (base := W.base) W.through03.1.1.2.1
  have hs := n05_referenceState_sector W.through03.1.1.2.2.1
  have he := returnCorrectionCoefficientError_at_actual W.through03.1.1
    W.through03.1.2 W.hS W.cutoff.cutoff hz hs p hp
    (fun m hm hd => (W.cutoff.active_discriminant _ hz hs m p hm hd).le)
  have hzero : returnCorrectionCoefficientError W.D W.S W.C W.R W.cutoff.cutoff
      (W.C.referenceState, 0) p (W.R.residual (W.C.referenceState, 0)) = 0 := by
    rw [n05_returnResidual_reference_zero W.through03.1.1 W.through03.1.2, map_zero]
  have hpair :
      ((originalCoefficients W.D W.S W.C (W.C.referenceState, 0)).b p -
          (W.L.coefficients (W.C.referenceState, 0)).b p,
        (originalCoefficients W.D W.S W.C (W.C.referenceState, 0)).c p -
          (W.L.coefficients (W.C.referenceState, 0)).c p) = 0 :=
    he.symm.trans hzero
  have hrec := n04PulledFields_coefficient_reconstruction i
    (originalCoefficients W.D W.S W.C (W.C.referenceState, 0))
    (W.L.coefficients (W.C.referenceState, 0))
    (returnCorrectedCoefficients_a W.D W.S W.C W.cutoff.cutoff _) p
  rw [hpair, map_zero, sub_zero] at hrec
  simpa only [originalCoefficientEntry, canonicalCoefficientComponent, ite_apply]
    using hrec.symm

/-- Every corrected reference spatial jet has one uniform bound over
all three coefficients and the entire physical annulus. -/
theorem n04PulledFields_correctedCoefficient_reference_uniform
    (W : N04RealizationStart) (s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (i : Fin 3) (a b : ℕ), a + b ≤ s →
      ∀ p ∈ annularOpen W.D,
        |mixedDerivative a b
          (canonicalCoefficientComponent i (W.L.coefficients (W.C.referenceState, 0))) p| ≤ K := by
  obtain ⟨K, hK, hb⟩ := W.through03.1.1.reference_coefficient_mixed_uniform_bound s
  refine ⟨K, hK, fun i a b hab p hp => ?_⟩
  exact (congrArg abs (mixedDerivative_congr_on_open (isOpen_Ioo.prod isOpen_univ)
    (n04PulledFields_correctedCoefficient_reference_eq W i) a b hp)).trans_le
      (hb i a b hab p hp)

/-- Replacing the auxiliary column and using the zero sector parameter
preserves the same actual physical reference bounds. -/
theorem n04PulledFields_gaugeCoefficient_reference_uniform
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space) (s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (i : Fin 3) (a b : ℕ), a + b ≤ s →
      ∀ p ∈ annularOpen G.W.D,
        |mixedDerivative a b (G.coefficientField η i (G.lift η 0)) p| ≤ K := by
  have href : G.lift η (0 : Parameter (G.S η)) = G.ref η := by
    apply Prod.ext
    · change G.W.C.referenceState + (0 : AnnularState G.W.S) = G.W.C.referenceState
      exact add_zero _
    · rfl
  rw [href]
  exact n04PulledFields_correctedCoefficient_reference_uniform G.W s

end ContinuousFlexibility.Analysis
