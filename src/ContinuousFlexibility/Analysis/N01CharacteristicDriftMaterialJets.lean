import ContinuousFlexibility.Analysis.N01RadialCoefficientPowerMaterialJets
import ContinuousFlexibility.Analysis.PointwiseProductPolynomialMaterialJets
import ContinuousFlexibility.Analysis.N04bOpticalCoefficientVariation
import ContinuousFlexibility.Analysis.OneSidedOrdinaryJets

/-!
# Uniform material jets of the actual characteristic drift

The same physical coefficient fields satisfy the true identity d=b/a.
The already proved inverse-radial material tower and global b tower are
multiplied at the actual point, preserving one high state seminorm.
The same original neighborhood and genuine component host are retained.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

theorem n01_characteristicDrift_eq_original_ratio
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {q : PolarPoint} (hq : q ∈ annularOpen D) :
    characteristicDrift (stateProfile D S C z.1) (stateHeight D S C z) q =
      (originalCoefficients D S C z).b q / (originalCoefficients D S C z).a q := by
  have hgeom : RadialProfileGeometry D := hN.1.1.choose_spec.1
  have hw : 0 < D.w q.1 := hgeom.2.2.2.2.1 q.1 hq.1
  have hlow := hN.2.2.2.2.2.2.2.2.2.1 z hz hs q hq
  have hwp : 0 < stateProfile D S C z.1 q.1 :=
    (mul_pos (by norm_num : (0 : ℝ) < 1 / 2) hw).trans_le
      ((le_div_iff₀ hw).mp hlow.1)
  have hQ : 0 < heightQ (profileEnergy (stateProfile D S C z.1) q)
      (heightRadial (stateHeight D S C z) q)
      (angularPartial (heightAngular (stateHeight D S C z)) q) :=
    (mul_pos (by norm_num : (0 : ℝ) < 7 / 8) hwp).trans_le
      ((le_div_iff₀ hwp).mp hlow.2.2.1)
  have hdisc : 0 < polarDiscriminant (stateProfile D S C z.1)
      (stateHeight D S C z) q :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le hlow.2.2.2.2.1
  exact n04b_characteristicDrift_eq_corrected_ratio
    ((contDiff_stateHeight_of_n01 hS hT hN z).contDiffAt.of_le (by simp))
    (hgeom.1.trans hq.1.1).ne' hdisc hQ

private theorem drift_material_envelope_mono
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    {a b W : ℝ} {k l m : ℕ} (hab : a ≤ b) (hb : 0 ≤ b)
    (hW : 1 ≤ W) (hlm : l ≤ m) (z : E) :
    a * W ^ a * (1 + p (k + l) z) ≤ b * W ^ b * (1 + p (k + m) z) := by
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  exact mul_le_mul
    (mul_le_mul hab (Real.rpow_le_rpow_of_exponent_le hW hab)
      (Real.rpow_nonneg hW0 _) hb)
    (add_le_add_left (hp (Nat.add_le_add_left hlm k) z) 1)
    (add_nonneg zero_le_one (apply_nonneg _ _))
    (mul_nonneg hb (Real.rpow_nonneg hW0 _))

theorem n01_characteristicDrift_component_material_jets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) :
    ∃ C0 : ℝ, ∃ low outLoss : ℕ, 1 ≤ C0 ∧
      (∀ j, 1 ≤ C0 * T.E0 (T.sample j)) ∧
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1 →
      ∀ m j : ℕ, Ioo (C.left m) (C.right m) ⊆ D.cells j →
      ∀ q : PolarPoint, q.1 ∈ Icc (C.left m) (C.right m) → ∀ n : ℕ,
        ‖iteratedFDeriv ℝ n
          (characteristicDrift (stateProfile D S C z.1) (stateHeight D S C z)) q‖ ≤
          B n * (C0 * T.E0 (T.sample j)) ^ (B n) *
            (1 + pairGrading (stateGrading S) realGrading (n + outLoss)
              (z - (C.referenceState, 0))) := by
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  have hI : HasInterpolation (pairGrading (stateGrading S) realGrading) :=
    coordinate_hasInterpolation_pair (stateGrading_monotone S)
      (fun _ _ _ => le_rfl) (coordinate_hasInterpolation_stateGrading hS)
      coordinate_hasInterpolation_realGrading
  obtain ⟨C0, inverseLow, inverseLoss, hC0, hfloor, hpowers⟩ :=
    n01_radialCoefficient_rpow_component_material_jets hS hT hN
  obtain ⟨AI, hAI, hinverse⟩ := hpowers (-1)
  obtain ⟨A, hA, hraw⟩ := originalCoefficient_ordinary_global_bound_of_n01 hS hT hN
  let commonLoss := max loss inverseLoss
  obtain ⟨productLow, outLoss, hproduct⟩ :=
    pointwiseProduct_polynomial_material_bound (X := PolarPoint) hp hI commonLoss
  let M : ℕ → ℝ := fun k => max 1 (max (A k) (AI k))
  have hM (k : ℕ) : 1 ≤ M k := le_max_left _ _
  have hAM (k : ℕ) : A k ≤ M k := (le_max_left _ _).trans (le_max_right _ _)
  have hAIM (k : ℕ) : AI k ≤ M k := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨B, hB, hbound⟩ := hproduct M hM
  refine ⟨C0, max inverseLow productLow, outLoss, hC0, hfloor, B, hB, ?_⟩
  intro z hz hs hzlow m j hhost q hq n
  have hcomp := n01Properties_negativeRadialComponent hN m
  have hqD : q ∈ annularOpen D :=
    ⟨⟨hcomp.1.trans_le hq.1, hq.2.trans_lt hcomp.2.2.1⟩, mem_univ _⟩
  have hU : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  let W : ℝ := C0 * T.E0 (T.sample j)
  have hW : 1 ≤ W := hfloor j
  have hzI := (hp (le_max_left inverseLow productLow) _).trans hzlow
  have hzP := (hp (le_max_right inverseLow productLow) _).trans hzlow
  have ha : ContDiffAt ℝ ∞ (originalCoefficients D S C z).a q := by
    simpa only [canonicalCoefficientComponent, if_pos rfl] using
      (contDiffOn_originalCoefficientComponent_of_n01 hS hT hN hz hs (0 : Fin 3)).contDiffAt
        (hU.mem_nhds hqD)
  have hb : ContDiffAt ℝ ∞ (originalCoefficients D S C z).b q := by
    simpa only [canonicalCoefficientComponent, if_neg (show (1 : Fin 3) ≠ 0 by decide),
      if_pos rfl] using
      (contDiffOn_originalCoefficientComponent_of_n01 hS hT hN hz hs (1 : Fin 3)).contDiffAt
        (hU.mem_nhds hqD)
  have hapos : 0 < (originalCoefficients D S C z).a q :=
    (div_pos (hN.1.1.choose_spec.1.2.2.2.2.1 q.1 hqD.1)
      (by norm_num : (0 : ℝ) < 16)).trans_le
        (hN.originalRadialCoefficient_ge_sixteenth_profile hz hs hqD)
  have he : EqOn
      (characteristicDrift (stateProfile D S C z.1) (stateHeight D S C z))
      (fun x => (originalCoefficients D S C z).b x *
        ((originalCoefficients D S C z).a x)⁻¹) (annularOpen D) := by
    intro x hx
    simpa only [div_eq_mul_inv] using n01_characteristicDrift_eq_original_ratio hS hT hN hz hs hx
  rw [iteratedFDeriv_eqOn_of_isOpen hU he n hqD]
  refine hbound (z - (C.referenceState, 0)) hzP W hW
    (originalCoefficients D S C z).b (fun x => ((originalCoefficients D S C z).a x)⁻¹)
    q hb (ha.inv hapos.ne') ?_ ?_ n
  · intro k
    have hjet : ‖iteratedFDeriv ℝ k (originalCoefficients D S C z).b q‖ ≤
        A k * (1 + pairGrading (stateGrading S) realGrading (k + loss)
          (z - (C.referenceState, 0))) := by
      simpa only [canonicalCoefficientComponent, if_neg (show (1 : Fin 3) ≠ 0 by decide),
        if_pos rfl] using hraw z hz hs (1 : Fin 3) k q hqD
    have hscale : A k ≤ A k * W ^ (A k) := le_mul_of_one_le_right
      (zero_le_one.trans (hA k)) (Real.one_le_rpow hW (zero_le_one.trans (hA k)))
    exact hjet.trans ((mul_le_mul_of_nonneg_right hscale
      (add_nonneg zero_le_one (apply_nonneg _ _))).trans
        (drift_material_envelope_mono hp (hAM k) (zero_le_one.trans (hM k))
          hW (le_max_left loss inverseLoss) _))
  · intro k
    have hjet : ‖iteratedFDeriv ℝ k
        (fun x => ((originalCoefficients D S C z).a x)⁻¹) q‖ ≤
        AI k * W ^ (AI k) * (1 + pairGrading (stateGrading S) realGrading (k + inverseLoss)
          (z - (C.referenceState, 0))) := by
      simpa only [Real.rpow_neg_one] using hinverse z hz hs hzI m j hhost q hq k
    exact hjet.trans (drift_material_envelope_mono hp (hAIM k)
      (zero_le_one.trans (hM k)) hW (le_max_right loss inverseLoss) _)

end ContinuousFlexibility.Analysis
