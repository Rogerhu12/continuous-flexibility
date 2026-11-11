import ContinuousFlexibility.Analysis.N08RadialFamilyMaterialJets
import ContinuousFlexibility.Analysis.N08MaterialWeightIntegrability
import ContinuousFlexibility.Scalar.WeightedAngularPrimitiveBounds
import ContinuousFlexibility.Scalar.WeightedJetNorm

/-!
# Uniform height norms from a positive radial decay margin

The family index carries no topology or norm. Ordinary jets bounded by
`H^(2γ)` give uniformly bounded physical `γ` norms at every fixed order.
The positive margin supplies an actual square-integrable majorant on the
whole material cylinder.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped BigOperators ENNReal ContDiff

variable {D : ReferenceData} {T : MaterialData} {I : Type*} {F : I → ℝ → ℝ}
  {γ : ℝ}

theorem n08_radialPositive_pullback_bound
    (hT : IsMaterialData D T)
    (hF : ∀ i, ContDiffOn ℝ ∞ (F i) (Ioo D.a D.b))
    (hB : ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ i r, r ∈ Ioo D.a D.b →
      |iteratedDeriv s (F i) r| ≤ K * T.H r ^ (2 * γ)) (a : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i x,
      |iteratedDeriv a (fun t => T.H (T.radius t) ^ (-γ) * F i (T.radius t)) x| ≤
        K * T.H (T.radius x) ^ γ := by
  have hinside := hT.2.2.2.2.2.2.2.1
  have hradius := hT.2.2.2.2.2.2.1
  have hbF (j : ℕ) (_ : j ≤ a) : ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ (univ : Set ℝ),
      |iteratedDeriv j (fun t => T.H (T.radius t) ^ (-γ)) x| ≤
        K * T.H (T.radius x) ^ (-γ) := by
    obtain ⟨K, hK, hKb⟩ := iteratedDeriv_materialH_rpow_bound hT (-γ) j
    exact ⟨K, hK, fun x _ => hKb x⟩
  have hbG (j : ℕ) (_ : j ≤ a) : ∃ K : ℝ, 0 ≤ K ∧ ∀ i x, x ∈ (univ : Set ℝ) →
      |iteratedDeriv j (fun t => F i (T.radius t)) x| ≤
        K * T.H (T.radius x) ^ (2 * γ) * (1 : ℝ) := by
    have hb (n : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ i r, r ∈ Ioo D.a D.b →
        |iteratedDeriv n (F i) r| ≤ K * (1 : ℝ) * T.H r ^ (2 * γ) := by
      obtain ⟨K, hK, hKb⟩ := hB n
      exact ⟨K, hK, fun i r hr => by simpa only [mul_one] using hKb i r hr⟩
    obtain ⟨K, hK, hKb⟩ := n08_comp_materialRadius_majorant hT hF
      (N := fun _ : I => (1 : ℝ)) (W := fun r => T.H r ^ (2 * γ))
      (fun _ => zero_le_one) (fun r hr => Real.rpow_nonneg (hT.2.1 r hr).2.1.le _) hb j
    exact ⟨K, hK, fun i x _ => by simpa only [mul_one] using hKb i x⟩
  obtain ⟨K, hK, hKb⟩ := n08_product_jet_majorant
    (f := fun x => T.H (T.radius x) ^ (-γ)) (g := fun i x => F i (T.radius x))
    (W := fun x => T.H (T.radius x) ^ (-γ))
    (V := fun x => T.H (T.radius x) ^ (2 * γ)) (P := fun _ : I => (1 : ℝ))
    isOpen_univ (contDiff_materialH_rpow hT (-γ)).contDiffOn
    (fun i => ((hF i).comp_contDiff hradius (fun x => (hinside x).1)).contDiffOn)
    (fun x _ => Real.rpow_nonneg (hT.2.1 _ (hinside x).1).2.1.le _)
    (fun x _ => Real.rpow_nonneg (hT.2.1 _ (hinside x).1).2.1.le _)
    (fun _ => zero_le_one) a hbF hbG
  refine ⟨K, hK, fun i x => (hKb i x (mem_univ x)).trans_eq ?_⟩
  rw [mul_one, mul_assoc, ← Real.rpow_add (hT.2.1 _ (hinside x).1).2.1]
  congr 2
  ring

theorem n08_radialPositive_weightedJet_bound
    (hT : IsMaterialData D T) (hγ : 0 < γ)
    (hF : ∀ i, ContDiffOn ℝ ∞ (F i) (Ioo D.a D.b))
    (hB : ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ i r, r ∈ Ioo D.a D.b →
      |iteratedDeriv s (F i) r| ≤ K * T.H r ^ (2 * γ)) (a b c : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i p,
      |weightedPhysicalJet T γ a b c (n08RadialFamilyField F i) p| ≤
        K * T.H (T.radius p.1) ^ (γ / 2) := by
  obtain ⟨K, hK, hKb⟩ := n08_radialPositive_pullback_bound hT hF hB a
  have hdata := hT
  obtain ⟨_, hpos, _, _, _, _, _, hinside, _, _, _, _, henv, _⟩ := hdata
  obtain ⟨A, hA, hAb, _, _⟩ := henv (c : ℝ) (γ / 2) (half_pos hγ)
  refine ⟨K * A, mul_nonneg hK hA.le, fun i p => ?_⟩
  have hp := hpos _ (hinside p.1).1
  have hM : 0 ≤ T.M (T.radius p.1) := zero_le_one.trans hp.2.2.2
  have hH : 0 < T.H (T.radius p.1) := hp.2.1
  change |T.M (T.radius p.1) ^ c * mixedDerivative a b
    (fun q => T.H (T.radius q.1) ^ (-γ) * F i (T.radius q.1)) p| ≤ _
  rw [n08_mixedDerivative_radial
    (fun t => T.H (T.radius t) ^ (-γ) * F i (T.radius t)) a b p]
  by_cases hb : b = 0
  · rw [if_pos hb, abs_mul, abs_of_nonneg (pow_nonneg hM _)]
    have hpay : T.H (T.radius p.1) ^ (γ / 2) * T.M (T.radius p.1) ^ c ≤ A := by
      simpa only [Real.rpow_natCast] using hAb _ (hinside p.1).1
    have hpow : T.H (T.radius p.1) ^ γ =
        T.H (T.radius p.1) ^ (γ / 2) * T.H (T.radius p.1) ^ (γ / 2) := by
      rw [← Real.rpow_add hH]
      congr 1
      ring
    calc
      _ ≤ T.M (T.radius p.1) ^ c * (K * T.H (T.radius p.1) ^ γ) :=
        mul_le_mul_of_nonneg_left (hKb i p.1) (pow_nonneg hM _)
      _ = K * (T.H (T.radius p.1) ^ (γ / 2) * T.M (T.radius p.1) ^ c) *
          T.H (T.radius p.1) ^ (γ / 2) := by rw [hpow]; ring
      _ ≤ K * A * T.H (T.radius p.1) ^ (γ / 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpay hK)
          (Real.rpow_nonneg hH.le _)
  · rw [if_neg hb, mul_zero, abs_zero]
    exact mul_nonneg (mul_nonneg hK hA.le) (Real.rpow_nonneg hH.le _)

theorem n08_radialPositive_weightedJet_L2_bound
    (hT : IsMaterialData D T) (hγ : 0 < γ)
    (hF : ∀ i, ContDiffOn ℝ ∞ (F i) (Ioo D.a D.b))
    (hB : ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ i r, r ∈ Ioo D.a D.b →
      |iteratedDeriv s (F i) r| ≤ K * T.H r ^ (2 * γ)) (a b c : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i,
      MemLp (weightedPhysicalJet T γ a b c (n08RadialFamilyField F i)) 2 materialCylinderMeasure ∧
      (eLpNorm (weightedPhysicalJet T γ a b c (n08RadialFamilyField F i))
        2 materialCylinderMeasure).toReal ≤ K := by
  obtain ⟨K, hK, hKb⟩ := n08_radialPositive_weightedJet_bound hT hγ hF hB a b c
  let W : PolarPoint → ℝ := fun p => T.H (T.radius p.1) ^ (γ / 2)
  have hW : MemLp W 2 materialCylinderMeasure :=
    n08_memLp_cylinder_materialH_rpow hT (half_pos hγ)
  refine ⟨K * (eLpNorm W 2 materialCylinderMeasure).toReal,
    mul_nonneg hK ENNReal.toReal_nonneg, fun i => ?_⟩
  have hfield : ContDiffOn ℝ ∞ (n08RadialFamilyField F i) (annularOpen D) :=
    (hF i).comp contDiff_fst.contDiffOn (fun _ hp => hp.1)
  have hm : AEStronglyMeasurable (weightedPhysicalJet T γ a b c (n08RadialFamilyField F i))
      materialCylinderMeasure :=
    (contDiff_weightedPhysicalJet hT hfield a b c).continuous.aestronglyMeasurable
  have hae : ∀ᵐ p ∂materialCylinderMeasure,
      ‖weightedPhysicalJet T γ a b c (n08RadialFamilyField F i) p‖ ≤ K * ‖W p‖ := by
    apply Eventually.of_forall
    intro p
    have hp := (hT.2.1 _ (hT.2.2.2.2.2.2.2.1 p.1).1).2.1
    simpa only [Real.norm_eq_abs, W, abs_of_pos (Real.rpow_pos_of_pos hp _)] using hKb i p
  refine ⟨hW.of_le_mul hm hae, ?_⟩
  have he := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hm hae 2
  have hfinite : ENNReal.ofReal K * eLpNorm W 2 materialCylinderMeasure ≠ ⊤ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hW.eLpNorm_lt_top).ne
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK] using ENNReal.toReal_mono hfinite he

theorem n08_radialPositive_physicalNorm_bound
    (hT : IsMaterialData D T) (hγ : 0 < γ)
    (hF : ∀ i, ContDiffOn ℝ ∞ (F i) (Ioo D.a D.b))
    (hB : ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ i r, r ∈ Ioo D.a D.b →
      |iteratedDeriv s (F i) r| ≤ K * T.H r ^ (2 * γ)) (s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i,
      physicalNorm T γ s (n08RadialFamilyField F i) ≤ K := by
  classical
  choose B hBpos hBx using fun j : JetIndex s =>
    n08_radialPositive_weightedJet_L2_bound hT hγ hF hB
      (j.val 0).val (j.val 1).val (j.val 2).val
  let K : ℝ := ∑ j, B j
  have hK : 0 ≤ K := Finset.sum_nonneg (fun j _ => hBpos j)
  have hBK (j : JetIndex s) : B j ≤ K :=
    Finset.single_le_sum (fun i _ => hBpos i) (Finset.mem_univ j)
  refine ⟨Real.sqrt (Fintype.card (JetIndex s) : ℝ) * K,
    mul_nonneg (Real.sqrt_nonneg _) hK, fun i => ?_⟩
  have hmem (a b c : ℕ) (_ : a + b + c ≤ s) :
      MemLp (weightedPhysicalJet T γ a b c (n08RadialFamilyField F i)) 2 materialCylinderMeasure := by
    obtain ⟨_, _, h⟩ := n08_radialPositive_weightedJet_L2_bound hT hγ hF hB a b c
    exact (h i).1
  have hbound (a b c : ℕ) (horder : a + b + c ≤ s) :
      (eLpNorm (weightedPhysicalJet T γ a b c (n08RadialFamilyField F i))
        2 materialCylinderMeasure).toReal ≤ K := by
    let j : JetIndex s :=
      ⟨![⟨a, by omega⟩, ⟨b, by omega⟩, ⟨c, by omega⟩], by simpa using horder⟩
    have hj : (eLpNorm (weightedPhysicalJet T γ a b c (n08RadialFamilyField F i))
        2 materialCylinderMeasure).toReal ≤ B j := by
      simpa [j] using (hBx j i).2
    exact hj.trans (hBK j)
  exact physicalNorm_le_of_weightedJet_bounds hK hmem hbound

end ContinuousFlexibility.Statements
