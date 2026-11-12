import ContinuousFlexibility.Analysis.N04bOriginalType
import ContinuousFlexibility.Analysis.N04bCorrectedFieldFacts
import ContinuousFlexibility.Analysis.N04bFieldRegularity

/-!
# Global strict type and raw regularity of the optical correction

The established correction estimate gives a strict gap wherever the
cutoff derivative is active. Off that support the actual original field
has the strict type proved from N01. These two facts supply strict type
on the whole negative component, together with the actual coefficient
regularity and periodicity.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}

theorem N01Properties.n04b_opticalCorrected_halfGap_pos
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (χ : ℕ → ℝ → ℝ)
    (m : ℕ) {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) (θ : ℝ)
    (hactive : deriv (χ m) r ≠ 0 →
      0 < (-returnCorrectedMinusSpeed D S C χ z m (r, -θ) -
        returnCorrectedMinusSpeed D S C χ z m (r, θ)) / 2) :
    0 < (-returnCorrectedMinusSpeed D S C χ z m (r, -θ) -
      returnCorrectedMinusSpeed D S C χ z m (r, θ)) / 2 := by
  by_cases hzero : deriv (χ m) r = 0
  · obtain ⟨ha, hdisc⟩ := hN.n04b_original_negative_type hS hT hz hsector m
      (p := (r, θ)) hr
    obtain ⟨hap, hbp, hcp⟩ := originalCoefficients_parity_of_physical hS C z r θ
    have hreflection := minusCharacteristicSpeed_reflection
      (originalCoefficients D S C z) r θ hap hbp hcp
    have hspeed : 0 < Real.sqrt ((originalCoefficients D S C z).b (r, θ) ^ 2 -
        (originalCoefficients D S C z).a (r, θ) *
          (originalCoefficients D S C z).c (r, θ)) /
        (originalCoefficients D S C z).a (r, θ) :=
      div_pos (Real.sqrt_pos.mpr hdisc) ha
    simp only [returnCorrectedMinusSpeed, hzero, mul_zero, zero_mul, add_zero]
    rw [hreflection, neg_neg]
    unfold minusCharacteristicSpeed plusCharacteristicSpeed
    linarith only [hspeed]
  · exact hactive hzero

theorem N01Properties.n04b_opticalFieldRegularity
    (hN : N01Properties D T S C base loss ε)
    (hR : N02Properties D T S C R base ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (χ : ℕ → ℝ → ℝ)
    (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (hsupp : ∀ m, tsupport (deriv (χ m)) ⊆ Ioo (C.left m) (C.right m))
    (hend : ∀ m, χ m =ᶠ[𝓝 (C.left m)] (fun _ => 0) ∧
      χ m =ᶠ[𝓝 (C.right m)] (fun _ => 1))
    (hgap : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ m r, r ∈ Ioo (C.left m) (C.right m) → ∀ θ,
        deriv (χ m) r ≠ 0 →
          0 < (-returnCorrectedMinusSpeed D S C χ z m (r, -θ) -
            returnCorrectedMinusSpeed D S C χ z m (r, θ)) / 2)
    (L : ReturnCorrectionData S)
    (hL : L.coefficients = returnCorrectedCoefficients D S C χ)
    (hreference : ∀ m r, r ∈ Icc (C.left m) (C.right m) → ∀ θ,
      L.minusFlow (C.referenceState, 0) m r θ =
        θ - opticalTravel D.w (C.left m) r) :
    N04bFieldRegularity D S C L base ε := by
  have hsupp' (m : ℕ) : Function.support (deriv (χ m)) ⊆
      Ioo (C.left m) (C.right m) :=
    subset_trans (subset_tsupport _) (hsupp m)
  have hdisc (z) (hz : z ∈ stateNeighborhood S C base ε)
      (hsector : stateSector S z.1) (m) (p : PolarPoint)
      (hp : p.1 ∈ tsupport (deriv (χ m))) :
      0 < (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p :=
    (hN.n04b_original_negative_type hS hT hz hsector m (hsupp m hp)).2
  refine
    { smooth_coefficients := ?_
      periodic_coefficients := ?_
      positive_a := ?_
      negative_discriminant := ?_
      reference_flow := fun m r hr θ => hreference m r hr θ }
  · intro z hz hsector
    simpa only [hL] using
      hN.n04b_opticalCorrectedCoefficients_contDiffOn hR hS hT hz hsector
        χ hχ hχrange hsupp' hend (hdisc z hz hsector)
  · intro z hz hsector r hr
    simpa only [hL] using
      hN.n04b_opticalCorrectedCoefficients_periodic hR hS hz hsector
        χ hχrange (hdisc z hz hsector) r hr
  · intro z hz hsector p hp
    rw [hL, returnCorrectedCoefficients_a]
    exact hN.originalRadialCoefficient_pos hz hsector hp
  · intro z hz hsector m p hp
    obtain ⟨ha, hd⟩ := hN.n04b_original_negative_type hS hT hz hsector m hp.1
    rw [hL]
    exact n04b_opticalCorrected_discriminant_pos hN.2.2.2.1.2.2.1
      χ z m p hp.1 ha hd (hgap z hz hsector m p.1 hp.1 p.2)

end ContinuousFlexibility.Statements
