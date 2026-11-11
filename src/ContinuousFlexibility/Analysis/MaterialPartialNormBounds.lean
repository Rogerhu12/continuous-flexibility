import ContinuousFlexibility.Analysis.MaterialMultiplierNormBounds
import ContinuousFlexibility.Analysis.MaterialPartialEnergy

/-!
# Fixed losses for the actual physical partial derivatives

Angular differentiation costs one order. Radial differentiation costs
two orders: one actual material derivative and one fixed power of the
material weight from the inverse length scale. The estimates require
only smoothness and weighted L² jets, so they also apply to intermediate
fields without a parity assumption.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff BigOperators ENNReal

theorem physicalNorm_angularPartial_le
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {u : PolarPoint → ℝ}
    (hT : IsMaterialData D T) (hu : ContDiffOn ℝ ∞ u (annularOpen D))
    (huLp : ∀ a b c, MemLp (weightedPhysicalJet T γ a b c u) 2 materialCylinderMeasure)
    (s : ℕ) :
    physicalNorm T γ s (angularPartial u) ≤
      Real.sqrt (Fintype.card (JetIndex s) : ℝ) * physicalNorm T γ (s + 1) u := by
  have hpull : materialPullback T γ (angularPartial u) =
      angularPartial (materialPullback T γ u) :=
    funext (materialPullback_angularPartial hT hu)
  have hG := contDiff_materialPullback (γ := γ) hT hu
  apply physicalNorm_le_of_common_jet_bound (Real.sqrt_nonneg _)
  intro J
  have heq : weightedPhysicalJet T γ (J.val 0).val (J.val 1).val (J.val 2).val
      (angularPartial u) =
      weightedPhysicalJet T γ (J.val 0).val ((J.val 1).val + 1) (J.val 2).val u := by
    funext p
    change T.M (T.radius p.1) ^ (J.val 2).val *
      mixedDerivative (J.val 0).val (J.val 1).val
        (materialPullback T γ (angularPartial u)) p = _
    rw [hpull, mixedDerivative_angularPartial isOpen_univ hG.contDiffOn
      (J.val 0).val (J.val 1).val (mem_univ p)]
    rfl
  rw [heq]
  exact weightedPhysicalJet_eLpNorm_le_physicalNorm_of_memLp huLp
    (by have h := J.property; omega)

private theorem finite_mixed_coefficient_bound
    {W F : PolarPoint → ℝ} (hW : ∀ p, 0 ≤ W p) (s d : ℕ)
    (h : ∀ a b, ∃ K : ℝ, 0 ≤ K ∧
      ∀ p, |mixedDerivative a b F p| ≤ K * W p ^ d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a b, a + b ≤ s → ∀ p,
      |mixedDerivative a b F p| ≤ K * W p ^ d := by
  classical
  choose K hK hb using h
  let C : ℝ := ∑ i : Fin (s + 1), ∑ j : Fin (s + 1), K i.val j.val
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hK _ _))
  refine ⟨C, hC, fun a b hab p => ?_⟩
  let i : Fin (s + 1) := ⟨a, by omega⟩
  let j : Fin (s + 1) := ⟨b, by omega⟩
  have hfirst : K a b ≤ ∑ j : Fin (s + 1), K a j.val :=
    Finset.single_le_sum (f := fun j : Fin (s + 1) => K a j.val)
      (fun _ _ => hK _ _) (Finset.mem_univ j)
  have hsecond : (∑ j : Fin (s + 1), K a j.val) ≤ C :=
    Finset.single_le_sum (f := fun i : Fin (s + 1) => ∑ j : Fin (s + 1), K i.val j.val)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => hK _ _)) (Finset.mem_univ i)
  exact (hb a b p).trans
    (mul_le_mul_of_nonneg_right (hfirst.trans hsecond) (pow_nonneg (hW p) d))

/-- The constant is chosen before the input field and the derivative
loss is the same two orders for every output order. -/
theorem exists_physicalNorm_radialPartial_bound
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T) (γ : ℝ) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : PolarPoint → ℝ,
      ContDiffOn ℝ ∞ u (annularOpen D) →
      (∀ a b c, MemLp (weightedPhysicalJet T γ a b c u) 2 materialCylinderMeasure) →
      physicalNorm T γ s (radialPartial u) ≤ C * physicalNorm T γ (s + 2) u := by
  let W (p : PolarPoint) : ℝ := T.M (T.radius p.1)
  let A (p : PolarPoint) : ℝ := (T.ell (T.radius p.1))⁻¹
  let L (p : PolarPoint) : ℝ :=
    γ * deriv (fun t => Real.log (T.H (T.radius t))) p.1
  have hrange (t : ℝ) : T.radius t ∈ Ioo D.a D.b := (hT.2.2.2.2.2.2.2.1 t).1
  have hW : Continuous W :=
    ((materialRadius_comp_contDiff hT (hT.1 T.M (by simp))).comp contDiff_fst).continuous
  have hWpos (p : PolarPoint) : 0 ≤ W p :=
    zero_le_one.trans (hT.2.1 _ (hrange p.1)).2.2.2
  have hA : ContDiff ℝ ∞ A := (materialInvEll_radius_contDiff hT).comp contDiff_fst
  have hlog : ContDiff ℝ ∞ (fun t => Real.log (T.H (T.radius t))) :=
    materialRadius_comp_contDiff hT
      ((hT.1 T.H (by simp)).log (fun r hr => (hT.2.1 r hr).2.1.ne'))
  have hL : ContDiff ℝ ∞ L :=
    contDiff_const.mul ((contDiff_infty_iff_deriv.mp hlog).2.comp contDiff_fst)
  have hAb (a b : ℕ) : ∃ K : ℝ, 0 ≤ K ∧
      ∀ p, |mixedDerivative a b A p| ≤ K * W p ^ 1 := by
    obtain ⟨K, hK, hb⟩ := materialInvEll_mixedDerivative_bound hT a b
    exact ⟨K, hK, fun p => by simpa only [pow_one] using hb p⟩
  have hLb (a b : ℕ) : ∃ K : ℝ, 0 ≤ K ∧
      ∀ p, |mixedDerivative a b L p| ≤ K * W p ^ 0 := by
    obtain ⟨K, hK, hb⟩ := materialLogH_radius_deriv_mixed_bounded hT γ a b
    exact ⟨K, hK, fun p => by simpa only [pow_zero, mul_one] using hb p⟩
  obtain ⟨KA, hKA, hbA⟩ := finite_mixed_coefficient_bound hWpos s 1 hAb
  obtain ⟨KL, hKL, hbL⟩ := finite_mixed_coefficient_bound hWpos (s + 1) 0 hLb
  let B : ℝ := 1 + materialMultiplierJetConstant (s + 1) * KL
  have hB : 0 ≤ B := add_nonneg zero_le_one
    (mul_nonneg (materialMultiplierJetConstant_nonneg _) hKL)
  let C : ℝ := Real.sqrt (Fintype.card (JetIndex s) : ℝ) *
    materialMultiplierJetConstant s * KA * B
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (materialMultiplierJetConstant_nonneg _)) hKA) hB
  refine ⟨C, hC, fun u hu huLp => ?_⟩
  let G : PolarPoint → ℝ := materialPullback T γ u
  let V (p : PolarPoint) : ℝ := radialPartial G p + L p * G p
  let N : ℝ := physicalNorm T γ (s + 2) u
  have hN : 0 ≤ N := Real.sqrt_nonneg _
  have hG : ContDiff ℝ ∞ G := contDiff_materialPullback hT hu
  have hR : ContDiff ℝ ∞ (radialPartial G) := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    exact contDiffAt_radialPartial hG.contDiffAt (m := ∞) (by simp)
  have hV : ContDiff ℝ ∞ V := hR.add (hL.mul hG)
  have hGb (a b c : ℕ) (habc : a + b + c ≤ s + 2) :
      eLpNorm (fun p => W p ^ c * mixedDerivative a b G p)
        2 materialCylinderMeasure ≤ ENNReal.ofReal N :=
    weightedPhysicalJet_eLpNorm_le_physicalNorm_of_memLp huLp habc
  have hLG := weightedMixedJets_eLpNorm_mul_bound hW hWpos hL hG
    (s + 1) 0 hKL hN hbL (fun a b c h => hGb a b c (by omega))
  have hVb (a b c : ℕ) (habc : a + b + c ≤ s + 1) :
      eLpNorm (fun p => W p ^ c * mixedDerivative a b V p)
        2 materialCylinderMeasure ≤ ENNReal.ofReal (B * N) := by
    have hRjet : (fun p => W p ^ c * mixedDerivative a b (radialPartial G) p) =
        (fun p => W p ^ c * mixedDerivative (a + 1) b G p) := by
      funext p
      rw [mixedDerivative_radialPartial isOpen_univ hG.contDiffOn a b (mem_univ p)]
    have hRb : eLpNorm (fun p => W p ^ c * mixedDerivative a b (radialPartial G) p)
        2 materialCylinderMeasure ≤ ENNReal.ofReal N := by
      rw [hRjet]
      exact hGb (a + 1) b c (by omega)
    have heq : (fun p => W p ^ c * mixedDerivative a b V p) =
        (fun p => W p ^ c * mixedDerivative a b (radialPartial G) p) +
          (fun p => W p ^ c * mixedDerivative a b (fun q => L q * G q) p) := by
      funext p
      change W p ^ c * mixedDerivative a b (fun q => radialPartial G q + L q * G q) p = _
      rw [mixedDerivative_add_of_contDiff hR (hL.mul hG), mul_add]
      rfl
    rw [heq]
    have hb := (eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans
      (add_le_add hRb (hLG a b c habc))
    have hpos : 0 ≤ materialMultiplierJetConstant (s + 1) * KL * N :=
      mul_nonneg (mul_nonneg (materialMultiplierJetConstant_nonneg _) hKL) hN
    have he : ENNReal.ofReal N +
        ENNReal.ofReal (materialMultiplierJetConstant (s + 1) * KL * N) =
          ENNReal.ofReal (B * N) := by
      rw [← ENNReal.ofReal_add hN hpos]
      congr 1
      dsimp only [B]
      ring
    exact hb.trans_eq he
  have hAV := weightedMixedJets_eLpNorm_mul_bound hW hWpos hA hV s 1 hKA
    (mul_nonneg hB hN) hbA hVb
  have hpull : materialPullback T γ (radialPartial u) = (fun p => A p * V p) :=
    funext (materialPullback_radialPartial hT hu)
  have hjet (J : JetIndex s) :
      eLpNorm (weightedPhysicalJet T γ (J.val 0).val (J.val 1).val (J.val 2).val
        (radialPartial u)) 2 materialCylinderMeasure ≤
        ENNReal.ofReal (materialMultiplierJetConstant s * KA * (B * N)) := by
    have heq : weightedPhysicalJet T γ (J.val 0).val (J.val 1).val (J.val 2).val
        (radialPartial u) = (fun p => W p ^ (J.val 2).val *
          mixedDerivative (J.val 0).val (J.val 1).val (fun q => A q * V q) p) := by
      funext p
      change W p ^ (J.val 2).val * mixedDerivative (J.val 0).val (J.val 1).val
        (materialPullback T γ (radialPartial u)) p = _
      rw [hpull]
    rw [heq]
    exact hAV _ _ _ J.property
  have hb := physicalNorm_le_of_common_jet_bound
    (mul_nonneg (mul_nonneg (materialMultiplierJetConstant_nonneg _) hKA) (mul_nonneg hB hN)) hjet
  exact hb.trans_eq (by dsimp only [C, N]; ring)

end ContinuousFlexibility.Statements
