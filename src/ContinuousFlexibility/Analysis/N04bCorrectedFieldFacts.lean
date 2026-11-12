import ContinuousFlexibility.Analysis.ReturnCorrectionOperatorComparison

/-!
# Spatial regularity of the explicit optical return correction

These results concern the already defined cutoff correction. They do
not infer regularity of an arbitrary frozen N03 coefficient witness.
The full discriminant statement isolates the remaining original-field
positivity premise away from the active cutoff collars.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

section SpatialRegularity

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}
  (hN01 : N01Properties D T S C base loss ε)
  (hN02 : N02Properties D T S C R base ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hsector : stateSector S z.1)
  (χ : ℕ → ℝ → ℝ) (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
  (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
  (hsupp : ∀ m, Function.support (deriv (χ m)) ⊆ Ioo (C.left m) (C.right m))
  (hend : ∀ m, χ m =ᶠ[𝓝 (C.left m)] (fun _ => 0) ∧
    χ m =ᶠ[𝓝 (C.right m)] (fun _ => 1))
  (hdisc : ∀ m p, p.1 ∈ tsupport (deriv (χ m)) →
    0 < (originalCoefficients D S C z).b p ^ 2 -
      (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p)

include hN01 hN02 hS hT hz hsector hχ hχrange hsupp hend hdisc

theorem N01Properties.n04b_opticalCorrectedCoefficients_contDiffAt
    (p : PolarPoint) (hp : p ∈ annularOpen D) :
    ContDiffAt ℝ ∞ (returnCorrectedCoefficients D S C χ z).a p ∧
    ContDiffAt ℝ ∞ (returnCorrectedCoefficients D S C χ z).b p ∧
    ContDiffAt ℝ ∞ (returnCorrectedCoefficients D S C χ z).c p := by
  have hreg := hN01.originalCoefficients_contDiffAt hS hT hz hsector hp
  have herr : ContDiffAt ℝ ∞
      (fun q => returnCorrectionCoefficientError D S C R χ z q (R.residual z)) p :=
    hN01.returnCorrectionCoefficientError_contDiffAt_of_cutoffs hS hT R hz hsector
      χ hχ hχrange hsupp hend hdisc (R.residual z) p hp
  have hb : (returnCorrectedCoefficients D S C χ z).b =ᶠ[𝓝 p]
      fun q => (originalCoefficients D S C z).b q -
        (returnCorrectionCoefficientError D S C R χ z q (R.residual z)).1 := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with q hq
    have h := congrArg Prod.fst
      (hN01.returnCorrectionCoefficientError_at_actual_of_cutoffs
        hN02 hS hz hsector χ hdisc q hq)
    dsimp only [Prod.fst] at h
    linarith
  have hc : (returnCorrectedCoefficients D S C χ z).c =ᶠ[𝓝 p]
      fun q => (originalCoefficients D S C z).c q -
        (returnCorrectionCoefficientError D S C R χ z q (R.residual z)).2 := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with q hq
    have h := congrArg Prod.snd
      (hN01.returnCorrectionCoefficientError_at_actual_of_cutoffs
        hN02 hS hz hsector χ hdisc q hq)
    dsimp only [Prod.snd] at h
    linarith
  refine ⟨?_, (hreg.2.1.sub herr.fst).congr_of_eventuallyEq hb,
    (hreg.2.2.sub herr.snd).congr_of_eventuallyEq hc⟩
  rw [returnCorrectedCoefficients_a]
  exact hreg.1

theorem N01Properties.n04b_opticalCorrectedCoefficients_contDiffOn :
    ContDiffOn ℝ ∞ (returnCorrectedCoefficients D S C χ z).a (annularOpen D) ∧
    ContDiffOn ℝ ∞ (returnCorrectedCoefficients D S C χ z).b (annularOpen D) ∧
    ContDiffOn ℝ ∞ (returnCorrectedCoefficients D S C χ z).c (annularOpen D) := by
  have h := hN01.n04b_opticalCorrectedCoefficients_contDiffAt hN02 hS hT hz hsector
    χ hχ hχrange hsupp hend hdisc
  exact ⟨fun p hp => (h p hp).1.contDiffWithinAt,
    fun p hp => (h p hp).2.1.contDiffWithinAt,
    fun p hp => (h p hp).2.2.contDiffWithinAt⟩

end SpatialRegularity

section Periodicity

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}
  (hN01 : N01Properties D T S C base loss ε)
  (hN02 : N02Properties D T S C R base ε)
  (hS : IsPhysicalSpaces D T S)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hsector : stateSector S z.1) (χ : ℕ → ℝ → ℝ)
  (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
  (hdisc : ∀ m p, p.1 ∈ tsupport (deriv (χ m)) →
    0 < (originalCoefficients D S C z).b p ^ 2 -
      (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p)

include hN01 hN02 hS hz hsector hχrange hdisc

theorem N01Properties.n04b_opticalCorrectedCoefficients_periodic
    (r : ℝ) (hr : r ∈ Ioo D.a D.b) :
    Function.Periodic (fun θ => (returnCorrectedCoefficients D S C χ z).a (r, θ))
        Real.pi ∧
    Function.Periodic (fun θ => (returnCorrectedCoefficients D S C χ z).b (r, θ))
        Real.pi ∧
    Function.Periodic (fun θ => (returnCorrectedCoefficients D S C χ z).c (r, θ))
        Real.pi := by
  have horig := originalCoefficients_periodic_of_physical hS C z
  have heq (θ : ℝ) :=
    hN01.returnCorrectionCoefficientError_at_actual_of_cutoffs
      hN02 hS hz hsector χ hdisc (r, θ) ⟨hr, mem_univ _⟩
  have hperiod (θ : ℝ) :=
    hN01.returnCorrectionCoefficientError_periodic
      hS R χ hz hsector hχrange (R.residual z) r θ
  refine ⟨?_, ?_, ?_⟩
  · intro θ
    rw [returnCorrectedCoefficients_a]
    simpa only [Prod.mk_add_mk, add_zero] using horig.1 (r, θ)
  · intro θ
    have h₀ := congrArg Prod.fst (heq θ)
    have h₁ := congrArg Prod.fst (heq (θ + Real.pi))
    have h₂ := congrArg Prod.fst (hperiod θ)
    have hb : (originalCoefficients D S C z).b (r, θ + Real.pi) =
        (originalCoefficients D S C z).b (r, θ) := by
      simpa only [Prod.mk_add_mk, add_zero] using horig.2.1 (r, θ)
    dsimp only [Prod.fst] at h₀ h₁ h₂
    linarith
  · intro θ
    have h₀ := congrArg Prod.snd (heq θ)
    have h₁ := congrArg Prod.snd (heq (θ + Real.pi))
    have h₂ := congrArg Prod.snd (hperiod θ)
    have hc : (originalCoefficients D S C z).c (r, θ + Real.pi) =
        (originalCoefficients D S C z).c (r, θ) := by
      simpa only [Prod.mk_add_mk, add_zero] using horig.2.2 (r, θ)
    dsimp only [Prod.snd] at h₀ h₁ h₂
    linarith

end Periodicity

/-- The inactive region retains the original strict discriminant; on
the active region the reconstructed discriminant is a square of the
positive radial coefficient times a square of the positive half-gap. -/
theorem n04b_opticalCorrected_discriminant_pos
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hdisj : ∀ m n, m ≠ n → Disjoint (Ioo (C.left m) (C.right m))
      (Ioo (C.left n) (C.right n)))
    (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ)
    (m : ℕ) (p : PolarPoint) (hp : p.1 ∈ Ioo (C.left m) (C.right m))
    (ha : 0 < (originalCoefficients D S C z).a p)
    (hdisc : 0 < (originalCoefficients D S C z).b p ^ 2 -
      (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p)
    (hgap : deriv (χ m) p.1 ≠ 0 →
      0 < (-returnCorrectedMinusSpeed D S C χ z m (p.1, -p.2) -
        returnCorrectedMinusSpeed D S C χ z m p) / 2) :
    0 < (returnCorrectedCoefficients D S C χ z).b p ^ 2 -
      (returnCorrectedCoefficients D S C χ z).a p *
        (returnCorrectedCoefficients D S C χ z).c p := by
  by_cases hzero : deriv (χ m) p.1 = 0
  · obtain ⟨hb, hc⟩ :=
      returnCorrectedCoefficients_eq_original_at_of_deriv_zero (D := D) hdisj χ z m p hp hzero
    rw [hb, hc, returnCorrectedCoefficients_a]
    exact hdisc
  · obtain ⟨hb, hc⟩ :=
      returnCorrectedCoefficients_eq_component_at (D := D) hdisj χ z m p hp hzero
    rw [hb, hc, returnCorrectedCoefficients_a]
    simp only [returnCorrectedComponentCoefficients,
      returnCorrectionCoefficients_b_apply, returnCorrectionCoefficients_c_apply]
    rw [returnCorrection_discriminant]
    exact sq_pos_of_pos (mul_pos ha (hgap hzero))

end ContinuousFlexibility.Statements
