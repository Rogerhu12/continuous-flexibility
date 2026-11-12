import ContinuousFlexibility.Analysis.N01RootFactorAxisGlobalJets
import ContinuousFlexibility.Analysis.N01RootFactorAxisMaterialInverse
import ContinuousFlexibility.Analysis.PositivePowerPolynomialMaterialJets
import ContinuousFlexibility.Analysis.MaterialGlobalEndpointModels
import ContinuousFlexibility.Analysis.CanonicalStateInterpolation

/-!
# All root jets of actual factor powers under the raw optical lower

The actual numerator division supplies uniform upper jets at the root,
and the same-witness optical inequality supplies the reciprocal value.
The common low state order and loss precede every real power and all
root, host, state and strip choices. The strip radius never enters a cost.
The raw optical lower remains an explicit upstream construction input.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

theorem n01_rootFactor_axis_rpow_material_jets_of_component_optical
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε K : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) (hK : 0 < K) :
    ∃ C0 : ℝ, ∃ low outLoss : ℕ, 1 ≤ C0 ∧
      (∀ j, 1 ≤ C0 * T.E0 (T.sample j)) ∧
      ∀ γ : ℝ, ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1 →
      ∀ m j : ℕ, Ioo (C.left m) (C.right m) ⊆ D.cells j →
      (∀ x ∈ Ioo (C.left m) (C.right m),
        K⁻¹ * T.E0 (T.sample j) ^ (-K) * min (x - C.left m) (C.right m - x) ≤
          -deriv D.w x / (x * D.w x)) →
      ∀ (side : Bool) (g : ℝ → ℝ), ContDiff ℝ ∞ g →
      (∀ t, -deriv D.w (n01ComponentRoot C m side +
        n01ComponentRootOrientation side * t) = t * g t) →
      ∀ R : ℝ, 0 < R →
      RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
        (stateHeight D S C z) (n01ComponentRoot C m side)
        (n01ComponentRootOrientation side) R → ∀ θ : ℝ, ∀ n : ℕ,
        ‖iteratedFDeriv ℝ n
          (fun p => rootCoefficientRadialFactor D.w g (stateProfile D S C z.1)
            (stateHeight D S C z) (n01ComponentRoot C m side)
            (n01ComponentRootOrientation side) p ^ γ) (0, θ)‖ ≤
          B n * (C0 * T.E0 (T.sample j)) ^ (B n) *
            (1 + pairGrading (stateGrading S) realGrading (n + outLoss)
              (z - (C.referenceState, 0))) := by
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  have hI : HasInterpolation (pairGrading (stateGrading S) realGrading) :=
    coordinate_hasInterpolation_pair (stateGrading_monotone S)
      (fun _ _ _ => le_rfl) (coordinate_hasInterpolation_stateGrading hS)
      coordinate_hasInterpolation_realGrading
  obtain ⟨factorLow, factorLoss, A, hA, hraw⟩ :=
    n01_rootFactor_axis_global_fixed_loss hS hT hN
  obtain ⟨Ki, Pi, hKi, hPi, hinverse⟩ :=
    n01_rootFactor_axis_inverse_of_component_optical hT hN hK
  obtain ⟨powerLow, outLoss, hpower⟩ :=
    positivePower_polynomial_material_bound (X := PolarPoint) hp hI factorLoss
  obtain ⟨C0, hC0, hfloor⟩ := material_E0_uniform_scaled_lower hT hN.1.1
  let K0 : ℝ := max 1 (max (2 * A 0) (max Ki Pi))
  have hK0 : 1 ≤ K0 := le_max_left _ _
  have hAK : 2 * A 0 ≤ K0 := (le_max_left _ _).trans (le_max_right _ _)
  have hKiK : Ki ≤ K0 := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hPiK : Pi ≤ K0 := (le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  let A' : ℕ → ℝ := fun n => max 1 (A n)
  have hA' (n : ℕ) : 1 ≤ A' n := le_max_left _ _
  have hAA' (n : ℕ) : A n ≤ A' n := le_max_right _ _
  have hsample (j : ℕ) : 1 ≤ C0 * T.E0 (T.sample j) :=
    hfloor _ (materialSample_mem_interval hN.1.1 hT j)
  refine ⟨C0, max factorLow (max powerLow factorLoss), outLoss, hC0, hsample, ?_⟩
  intro γ
  obtain ⟨B, hB, hbound⟩ := hpower γ K0 hK0 A' hA'
  refine ⟨B, hB, ?_⟩
  intro z hz hs hzlow m j hhost hoptical side g hg hfactor R hR hstrip θ n
  have hlowF := (hp (le_max_left factorLow (max powerLow factorLoss)) _).trans hzlow
  have hlowP := (hp ((le_max_left powerLow factorLoss).trans
    (le_max_right factorLow (max powerLow factorLoss))) _).trans hzlow
  have hsmall := (hp ((le_max_right powerLow factorLoss).trans
    (le_max_right factorLow (max powerLow factorLoss))) _).trans hzlow
  let W := C0 * T.E0 (T.sample j)
  have hW : 1 ≤ W := hsample j
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hE : 0 < T.E0 (T.sample j) :=
    (hT.2.1 _ (materialSample_mem_interval hN.1.1 hT j)).2.2.1
  have hEW : T.E0 (T.sample j) ≤ W := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hC0 hE.le
  have hK0pos : 0 ≤ K0 := zero_le_one.trans hK0
  let r := n01ComponentRoot C m side
  let σ := n01ComponentRootOrientation side
  let G := rootCoefficientRadialFactor D.w g (stateProfile D S C z.1)
    (stateHeight D S C z) r σ
  have hroot := n01_component_root_data hN m side
  have hjets (k : ℕ) : ‖iteratedFDeriv ℝ k G (0, θ)‖ ≤
      A k * (1 + pairGrading (stateGrading S) realGrading (k + factorLoss)
        (z - (C.referenceState, 0))) :=
    hraw z hz hs hlowF r hroot.1 σ (n01ComponentRootOrientation_eq side)
      g hg R hR hstrip k θ
  have hpositive_inverse :=
    hinverse m j hhost hoptical side g hg hfactor R hR z hz hs hstrip θ
  have hpositive : 0 < G (0, θ) := hpositive_inverse.1
  have hvalue0 : G (0, θ) ≤ 2 * A 0 := by
    have hb : |G (0, θ)| ≤ A 0 *
        (1 + pairGrading (stateGrading S) realGrading factorLoss
          (z - (C.referenceState, 0))) := by
      simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, zero_add] using hjets 0
    calc
      _ ≤ A 0 * (1 + pairGrading (stateGrading S) realGrading factorLoss
          (z - (C.referenceState, 0))) := (le_abs_self _).trans hb
      _ ≤ A 0 * (1 + 1) :=
        mul_le_mul_of_nonneg_left (add_le_add_left hsmall 1) (hA 0).le
      _ = 2 * A 0 := by ring
  have hvalue : G (0, θ) ≤ K0 * W ^ K0 :=
    (hvalue0.trans hAK).trans (le_mul_of_one_le_right hK0pos
      (Real.one_le_rpow hW hK0pos))
  have hinv : (G (0, θ))⁻¹ ≤ K0 * W ^ K0 := by
    calc
      _ ≤ Ki * T.E0 (T.sample j) ^ Pi := hpositive_inverse.2
      _ ≤ Ki * W ^ Pi := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hE.le hEW hPi) hKi.le
      _ ≤ K0 * W ^ K0 := mul_le_mul hKiK
        (Real.rpow_le_rpow_of_exponent_le hW hPiK)
        (Real.rpow_nonneg hW0 _) hK0pos
  have hzero : ((0, θ) : PolarPoint) ∈ Ioo (-R - R) (R + R) ×ˢ (univ : Set ℝ) := by
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩ <;> linarith only [hR]
  have hdata := hstrip (0, θ) hzero
  have hG : ContDiffAt ℝ ∞ G (0, θ) :=
    contDiffAt_rootCoefficientRadialFactor hN.1.1.choose_spec.1.2.2.1.1 hg
      (contDiff_stateProfile_of_n01 hS hT hN z.1)
      (contDiff_stateHeight_of_n01 hS hT hN z)
      hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2.1 hdata.2.2.2.2.1
  refine hbound (z - (C.referenceState, 0)) hlowP W hW G (0, θ) hG
    hpositive hvalue hinv ?_ n
  intro k _hk
  have hscale : A k ≤ A' k * W ^ (A' k) :=
    (hAA' k).trans (le_mul_of_one_le_right (zero_le_one.trans (hA' k))
      (Real.one_le_rpow hW (zero_le_one.trans (hA' k))))
  exact (hjets k).trans (mul_le_mul_of_nonneg_right hscale
    (add_nonneg zero_le_one (apply_nonneg _ _)))

end ContinuousFlexibility.Analysis
