import ContinuousFlexibility.Analysis.N01OriginalCoefficientOrdinaryGlobalJets
import ContinuousFlexibility.Analysis.N01RadialCoefficientMaterialInverse
import ContinuousFlexibility.Analysis.PositivePowerPolynomialMaterialJets
import ContinuousFlexibility.Analysis.MaterialGlobalEndpointModels
import ContinuousFlexibility.Analysis.CanonicalStateInterpolation

/-!
# Material jets of every real power of the actual radial coefficient

The original N01 ratios and inverse profile estimate supply the positive
value and its reciprocal on each genuinely hosted closed component.
The global ordinary coefficient tower supplies all positive jets. The
same material data are retained; only a fixed scalar multiplies E0 so
that its envelope is at least one. No optical root lower is used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

theorem n01_radialCoefficient_rpow_component_material_jets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) :
    ∃ C0 : ℝ, ∃ low outLoss : ℕ, 1 ≤ C0 ∧
      (∀ j, 1 ≤ C0 * T.E0 (T.sample j)) ∧
      ∀ γ : ℝ, ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1 →
      ∀ m j : ℕ, Ioo (C.left m) (C.right m) ⊆ D.cells j →
      ∀ q : PolarPoint, q.1 ∈ Icc (C.left m) (C.right m) → ∀ n : ℕ,
        ‖iteratedFDeriv ℝ n (fun x => (originalCoefficients D S C z).a x ^ γ) q‖ ≤
          B n * (C0 * T.E0 (T.sample j)) ^ (B n) *
            (1 + pairGrading (stateGrading S) realGrading (n + outLoss)
              (z - (C.referenceState, 0))) := by
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  have hI : HasInterpolation (pairGrading (stateGrading S) realGrading) :=
    coordinate_hasInterpolation_pair (stateGrading_monotone S)
      (fun _ _ _ => le_rfl) (coordinate_hasInterpolation_stateGrading hS)
      coordinate_hasInterpolation_realGrading
  obtain ⟨powerLow, outLoss, hpower⟩ :=
    positivePower_polynomial_material_bound (X := PolarPoint) hp hI loss
  obtain ⟨A, hA, hraw⟩ := originalCoefficient_ordinary_global_bound_of_n01 hS hT hN
  obtain ⟨K0, P, hK0, hP, hinverse⟩ :=
    hN.originalRadialCoefficient_inverse_component_material_bound hT
  obtain ⟨C0, hC0, hfloor⟩ := material_E0_uniform_scaled_lower hT hN.1.1
  let K : ℝ := max 1 (max (2 * A 0) (max K0 P))
  have hK : 1 ≤ K := le_max_left _ _
  have hAK : 2 * A 0 ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hK0K : K0 ≤ K := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hPK : P ≤ K := (le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hsample (j : ℕ) : 1 ≤ C0 * T.E0 (T.sample j) :=
    hfloor _ (materialSample_mem_interval hN.1.1 hT j)
  refine ⟨C0, max powerLow loss, outLoss, hC0, hsample, ?_⟩
  intro γ
  obtain ⟨B, hB, hbound⟩ := hpower γ K hK A hA
  refine ⟨B, hB, ?_⟩
  intro z hz hs hzlow m j hhost q hq n
  have hcomp := n01Properties_negativeRadialComponent hN m
  have hqD : q ∈ annularOpen D :=
    ⟨⟨hcomp.1.trans_le hq.1, hq.2.trans_lt hcomp.2.2.1⟩, mem_univ _⟩
  let W : ℝ := C0 * T.E0 (T.sample j)
  have hW : 1 ≤ W := hsample j
  have hE : 0 < T.E0 (T.sample j) :=
    (hT.2.1 _ (materialSample_mem_interval hN.1.1 hT j)).2.2.1
  have hEW : T.E0 (T.sample j) ≤ W := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hC0 hE.le
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hKnonneg : 0 ≤ K := zero_le_one.trans hK
  have hlow : pairGrading (stateGrading S) realGrading powerLow
      (z - (C.referenceState, 0)) ≤ 1 := (hp (le_max_left _ _) _).trans hzlow
  have hsmall : pairGrading (stateGrading S) realGrading loss
      (z - (C.referenceState, 0)) ≤ 1 := (hp (le_max_right _ _) _).trans hzlow
  have hw : 0 < D.w q.1 := hN.1.1.choose_spec.1.2.2.2.2.1 q.1 hqD.1
  have hpositive : 0 < (originalCoefficients D S C z).a q :=
    (div_pos hw (by norm_num : (0 : ℝ) < 16)).trans_le
      (hN.originalRadialCoefficient_ge_sixteenth_profile hz hs hqD)
  have hvalue0 : (originalCoefficients D S C z).a q ≤ 2 * A 0 := by
    have hb : |(originalCoefficients D S C z).a q| ≤
        A 0 * (1 + pairGrading (stateGrading S) realGrading loss
          (z - (C.referenceState, 0))) := by
      simpa only [canonicalCoefficientComponent, ↓reduceIte,
        norm_iteratedFDeriv_zero, Real.norm_eq_abs, zero_add] using
        hraw z hz hs (0 : Fin 3) 0 q hqD
    calc
      _ ≤ A 0 * (1 + pairGrading (stateGrading S) realGrading loss
          (z - (C.referenceState, 0))) := (le_abs_self _).trans hb
      _ ≤ A 0 * (1 + 1) := mul_le_mul_of_nonneg_left
        (add_le_add_left hsmall 1) (zero_le_one.trans (hA 0))
      _ = 2 * A 0 := by ring
  have hvalue : (originalCoefficients D S C z).a q ≤ K * W ^ K :=
    (hvalue0.trans hAK).trans (le_mul_of_one_le_right hKnonneg
      (Real.one_le_rpow hW hKnonneg))
  have hinv : ((originalCoefficients D S C z).a q)⁻¹ ≤ K * W ^ K := by
    calc
      _ ≤ K0 * T.E0 (T.sample j) ^ P := hinverse z hz hs m j hhost q hq
      _ ≤ K0 * W ^ P := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hE.le hEW hP) hK0.le
      _ ≤ K * W ^ K := mul_le_mul hK0K
        (Real.rpow_le_rpow_of_exponent_le hW hPK)
        (Real.rpow_nonneg hW0 _) hKnonneg
  have hf : ContDiffOn ℝ ∞ (originalCoefficients D S C z).a (annularOpen D) := by
    simpa only [canonicalCoefficientComponent, ↓reduceIte] using
      contDiffOn_originalCoefficientComponent_of_n01 hS hT hN hz hs (0 : Fin 3)
  refine hbound (z - (C.referenceState, 0)) hlow W hW
    (originalCoefficients D S C z).a q
    (hf.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hqD))
    hpositive hvalue hinv ?_ n
  intro k _hk
  have hb : ‖iteratedFDeriv ℝ k (originalCoefficients D S C z).a q‖ ≤
      A k * (1 + pairGrading (stateGrading S) realGrading (k + loss)
        (z - (C.referenceState, 0))) := by
    simpa only [canonicalCoefficientComponent, ↓reduceIte] using
      hraw z hz hs (0 : Fin 3) k q hqD
  have ha : A k ≤ A k * W ^ (A k) := le_mul_of_one_le_right
    (zero_le_one.trans (hA k)) (Real.one_le_rpow hW (zero_le_one.trans (hA k)))
  exact hb.trans (mul_le_mul_of_nonneg_right ha
    (add_nonneg zero_le_one (apply_nonneg _ _)))

end ContinuousFlexibility.Analysis
