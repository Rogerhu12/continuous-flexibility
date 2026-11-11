import ContinuousFlexibility.Analysis.SpacesNemytskiiJetBounds

/-!
# The actual normalized Nemytskii kernels

These functions are the composition map and its proposed directional
derivatives. Their spatial jets belong to every weighted Hilbert level,
so they determine elements of the original compatible-jet space.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)

def spacesNemytskiiMaterial (γ : ℝ) (F : ℝ → ℝ) (k : ℕ)
    (u : PhysicalJetProjectiveLimit hT) (v : Fin k → PhysicalJetProjectiveLimit hT) : PolarPoint → ℝ :=
  (SpacesNemytskiiTerm.initial hT γ k).evaluate F (spacesPhysicalRepresentative hT u)
    (fun i => spacesPhysicalRepresentative hT (v i))

theorem spacesNemytskiiMaterial_apply (γ : ℝ) (F : ℝ → ℝ) (k : ℕ)
    (u : PhysicalJetProjectiveLimit hT) (v : Fin k → PhysicalJetProjectiveLimit hT) (p : PolarPoint) :
    spacesNemytskiiMaterial hT γ F k u v p =
      T.H (T.radius p.1) ^ (((k : ℝ) - 1) * γ) *
        iteratedDeriv k F (T.H (T.radius p.1) ^ γ * spacesPhysicalRepresentative hT u p) *
          ∏ i, spacesPhysicalRepresentative hT (v i) p :=
  SpacesNemytskiiTerm.initial_evaluate hT γ k F _ _ p

theorem spacesNemytskiiMaterial_contDiff (γ : ℝ) {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (k : ℕ)
    (u : PhysicalJetProjectiveLimit hT) (v : Fin k → PhysicalJetProjectiveLimit hT) :
    ContDiff ℝ ∞ (spacesNemytskiiMaterial hT γ F k u v) :=
  (SpacesNemytskiiTerm.initial hT γ k).evaluate_contDiff hT hF
    (spacesPhysicalRepresentative_contDiff hT u)
    (fun i => spacesPhysicalRepresentative_contDiff hT (v i))

theorem spacesNemytskiiMaterial_even (γ : ℝ) (F : ℝ → ℝ) (k : ℕ)
    (u : PhysicalJetProjectiveLimit hT) (v : Fin k → PhysicalJetProjectiveLimit hT) (r θ : ℝ) :
    spacesNemytskiiMaterial hT γ F k u v (r, -θ) =
      spacesNemytskiiMaterial hT γ F k u v (r, θ) := by
  simp only [spacesNemytskiiMaterial_apply, spacesPhysicalRepresentative_even]

theorem spacesNemytskiiMaterial_periodic (γ : ℝ) (F : ℝ → ℝ) (k : ℕ)
    (u : PhysicalJetProjectiveLimit hT) (v : Fin k → PhysicalJetProjectiveLimit hT) :
    Function.Periodic (spacesNemytskiiMaterial hT γ F k u v) (0, Real.pi) := by
  intro p
  have hp (z : PhysicalJetProjectiveLimit hT) := spacesPhysicalRepresentative_periodic hT z p
  simp only [spacesNemytskiiMaterial_apply, Prod.fst_add, add_zero,
    hp]

theorem spacesNemytskiiMaterial_weightedJet (γ : ℝ) {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (k a b c : ℕ) (u : PhysicalJetProjectiveLimit hT) (v : Fin k → PhysicalJetProjectiveLimit hT) :
    (fun p => T.M (T.radius p.1) ^ c * mixedDerivative a b
      (spacesNemytskiiMaterial hT γ F k u v) p) =
      SpacesNemytskiiTerm.weightedEvaluateTerms hT
        (SpacesNemytskiiTerm.jetExpansion hT γ k a b) F c u v := by
  funext p
  change _ = T.M (T.radius p.1) ^ c *
    SpacesNemytskiiTerm.evaluateTerms _ F _ _ p
  rw [SpacesNemytskiiTerm.evaluate_jetExpansion hT γ k a b hF
    (spacesPhysicalRepresentative_contDiff hT u)
    (fun i => spacesPhysicalRepresentative_contDiff hT (v i))]
  rfl

theorem spaces_nemytskii_material_jet_tame (hI : HasInterpolation (spacesPhysicalGrading hT)) :
    ∃ base loss : ℕ, ∀ (γ : ℝ), 0 < γ → ∀ (F : ℝ → ℝ), ContDiff ℝ ∞ F → F 0 = 0 →
      (∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv n F x| ≤ C) →
      ∀ k a b c s : ℕ, a + b + c ≤ s →
      ∀ R : ℝ, 1 ≤ R → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : PhysicalJetProjectiveLimit hT), spacesPhysicalGrading hT base u ≤ R →
      ∀ v : Fin k → PhysicalJetProjectiveLimit hT,
        MemLp (fun p => T.M (T.radius p.1) ^ c * mixedDerivative a b
          (spacesNemytskiiMaterial hT γ F k u v) p) 2 materialCylinderMeasure ∧
        lpNorm (fun p => T.M (T.radius p.1) ^ c * mixedDerivative a b
          (spacesNemytskiiMaterial hT γ F k u v) p) 2 materialCylinderMeasure ≤
          C * spacesNemytskiiMajorant hT base (s + loss) u v := by
  obtain ⟨base, loss, hb⟩ := spaces_nemytskii_expansion_tame hT hI
  refine ⟨base, loss, fun γ hγ F hF hF0 hFb k a b c s hs R hR => ?_⟩
  obtain ⟨C, hC, hbound⟩ := hb γ hγ F hF hF0 hFb k
    (SpacesNemytskiiTerm.jetExpansion hT γ k a b) c s
    (fun t ht => (Nat.add_le_add_right (SpacesNemytskiiTerm.jetExpansion_order hT γ k a b t ht) c).trans hs)
    R hR
  exact ⟨C, hC, fun u hu v => by
    rw [spacesNemytskiiMaterial_weightedJet hT γ hF]
    exact hbound u hu v⟩

theorem spacesNemytskiiMaterial_memLp (hI : HasInterpolation (spacesPhysicalGrading hT))
    {γ : ℝ} (hγ : 0 < γ) {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hF0 : F 0 = 0)
    (hFb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv n F x| ≤ C)
    (k a b c : ℕ) (u : PhysicalJetProjectiveLimit hT) (v : Fin k → PhysicalJetProjectiveLimit hT) :
    MemLp (fun p => T.M (T.radius p.1) ^ c * mixedDerivative a b
      (spacesNemytskiiMaterial hT γ F k u v) p) 2 materialCylinderMeasure := by
  obtain ⟨base, loss, hb⟩ := spaces_nemytskii_material_jet_tame hT hI
  obtain ⟨C, hC, hbound⟩ := hb γ hγ F hF hF0 hFb k a b c (a + b + c) le_rfl
    (max 1 (spacesPhysicalGrading hT base u)) (le_max_left _ _)
  exact (hbound u (le_max_right _ _) v).1

def spacesNemytskiiPhysical (γ : ℝ) (F : ℝ → ℝ) (k : ℕ)
    (u : PhysicalJetProjectiveLimit hT) (v : Fin k → PhysicalJetProjectiveLimit hT) : PolarPoint → ℝ :=
  spacesPhysicalPushforward (D := D) (T := T) γ (spacesNemytskiiMaterial hT γ F k u v)

theorem spacesNemytskiiPhysical_pullback (γ : ℝ) (F : ℝ → ℝ) (k : ℕ)
    (u : PhysicalJetProjectiveLimit hT) (v : Fin k → PhysicalJetProjectiveLimit hT) :
    materialPullback T γ (spacesNemytskiiPhysical hT γ F k u v) = spacesNemytskiiMaterial hT γ F k u v :=
  spacesPhysicalPushforward_pullback hT γ _

theorem spacesNemytskiiPhysical_heightMember (hI : HasInterpolation (spacesPhysicalGrading hT))
    {γ : ℝ} (hγ : 0 < γ) {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hF0 : F 0 = 0)
    (hFb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv n F x| ≤ C)
    (k : ℕ) (u : PhysicalJetProjectiveLimit hT) (v : Fin k → PhysicalJetProjectiveLimit hT) :
    HeightMember D T γ (spacesNemytskiiPhysical hT γ F k u v) := by
  classical
  refine ⟨spacesPhysicalPushforward_contDiffOn hT γ (spacesNemytskiiMaterial_contDiff hT γ hF k u v),
    ?_, ?_, ?_, ?_⟩
  · intro r θ
    have he : ((r, -θ) : PolarPoint) ∈ annularOpen D ↔ ((r, θ) : PolarPoint) ∈ annularOpen D := by
      simp only [annularOpen, mem_prod, mem_univ, and_true]
    simp only [spacesNemytskiiPhysical, spacesPhysicalPushforward, he, spacesNemytskiiMaterial_even]
  · intro p
    have he : p + (0, Real.pi) ∈ annularOpen D ↔ p ∈ annularOpen D := by
      simp only [annularOpen, mem_prod, Prod.fst_add, Prod.snd_add, add_zero, mem_univ, and_true]
    have hp := spacesNemytskiiMaterial_periodic hT γ F k u v (T.rho p.1, p.2)
    simp only [Prod.mk_add_mk, add_zero] at hp
    simp only [spacesNemytskiiPhysical, spacesPhysicalPushforward, he, Prod.fst_add,
      Prod.snd_add, add_zero, hp]
  · intro p hp
    exact ite_eq_right hp
  · intro a b c
    change MemLp (fun p => T.M (T.radius p.1) ^ c *
      mixedDerivative a b (materialPullback T γ (spacesNemytskiiPhysical hT γ F k u v)) p)
      2 materialCylinderMeasure
    rw [spacesNemytskiiPhysical_pullback]
    exact spacesNemytskiiMaterial_memLp hT hI hγ hF hF0 hFb k a b c u v

def spacesNemytskiiKernel (hI : HasInterpolation (spacesPhysicalGrading hT))
    {γ : ℝ} (hγ : 0 < γ) {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hF0 : F 0 = 0)
    (hFb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv n F x| ≤ C)
    (k : ℕ) (u : PhysicalJetProjectiveLimit hT) (v : Fin k → PhysicalJetProjectiveLimit hT) :
    PhysicalJetProjectiveLimit hT :=
  spacesPhysicalHeightEncode hT (spacesNemytskiiPhysical_heightMember hT hI hγ hF hF0 hFb k u v)

theorem spacesNemytskiiKernel_decode (hI : HasInterpolation (spacesPhysicalGrading hT))
    {γ : ℝ} (hγ : 0 < γ) {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hF0 : F 0 = 0)
    (hFb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv n F x| ≤ C)
    (k : ℕ) (u : PhysicalJetProjectiveLimit hT) (v : Fin k → PhysicalJetProjectiveLimit hT) :
    spacesPhysicalDecoded hT γ (spacesNemytskiiKernel hT hI hγ hF hF0 hFb k u v) =
      spacesNemytskiiPhysical hT γ F k u v :=
  spacesPhysicalDecoded_encode hT _

theorem spacesNemytskiiKernel_representative (hI : HasInterpolation (spacesPhysicalGrading hT))
    {γ : ℝ} (hγ : 0 < γ) {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hF0 : F 0 = 0)
    (hFb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv n F x| ≤ C)
    (k : ℕ) (u : PhysicalJetProjectiveLimit hT) (v : Fin k → PhysicalJetProjectiveLimit hT) :
    spacesPhysicalRepresentative hT (spacesNemytskiiKernel hT hI hγ hF hF0 hFb k u v) =
      spacesNemytskiiMaterial hT γ F k u v := by
  rw [← spacesPhysicalDecoded_pullback hT γ, spacesNemytskiiKernel_decode,
    spacesNemytskiiPhysical_pullback]

theorem spacesNemytskiiPhysical_apply (γ : ℝ) {F : ℝ → ℝ} (hF0 : F 0 = 0) (k : ℕ)
    (u : PhysicalJetProjectiveLimit hT) (v : Fin k → PhysicalJetProjectiveLimit hT) (p : PolarPoint) :
    spacesNemytskiiPhysical hT γ F k u v p =
      iteratedDeriv k F (spacesPhysicalDecoded hT γ u p) *
        ∏ i, spacesPhysicalDecoded hT γ (v i) p := by
  classical
  by_cases hp : p ∈ annularOpen D
  · have hr := hT.2.2.2.2.2.2.2.2.1 p.1 hp.1
    have hH : 0 < T.H p.1 := (hT.2.1 _ hp.1).2.1
    have hpow : T.H p.1 ^ γ * T.H p.1 ^ (((k : ℝ) - 1) * γ) = (T.H p.1 ^ γ) ^ k := by
      rw [← Real.rpow_add hH, ← Real.rpow_mul_natCast hH.le]
      congr 1
      ring
    simp only [spacesNemytskiiPhysical, spacesPhysicalPushforward, ite_eq_left hp,
      spacesNemytskiiMaterial_apply, hr, spacesPhysicalDecoded, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc
      T.H p.1 ^ γ * (T.H p.1 ^ (((k : ℝ) - 1) * γ) *
          iteratedDeriv k F (T.H p.1 ^ γ * spacesPhysicalRepresentative hT u (T.rho p.1, p.2)) *
            ∏ i, spacesPhysicalRepresentative hT (v i) (T.rho p.1, p.2)) =
        iteratedDeriv k F (T.H p.1 ^ γ * spacesPhysicalRepresentative hT u (T.rho p.1, p.2)) *
          ((T.H p.1 ^ γ * T.H p.1 ^ (((k : ℝ) - 1) * γ)) *
            ∏ i, spacesPhysicalRepresentative hT (v i) (T.rho p.1, p.2)) := by ring
      _ = _ := by rw [hpow]
  · simp only [spacesNemytskiiPhysical, spacesPhysicalPushforward, ite_eq_right hp,
      spacesPhysicalDecoded]
    cases k with
    | zero => simp only [iteratedDeriv_zero, hF0, zero_mul]
    | succ k => simp only [Fin.prod_univ_succ, zero_mul, mul_zero]

theorem spaces_nemytskii_kernel_tame (hI : HasInterpolation (spacesPhysicalGrading hT)) :
    ∃ base loss : ℕ, ∀ (γ : ℝ) (hγ : 0 < γ) (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (hF0 : F 0 = 0)
      (hFb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv n F x| ≤ C),
      ∀ k s : ℕ, ∀ R : ℝ, 1 ≤ R → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : PhysicalJetProjectiveLimit hT), spacesPhysicalGrading hT base u ≤ R →
      ∀ v : Fin k → PhysicalJetProjectiveLimit hT,
        spacesPhysicalGrading hT s (spacesNemytskiiKernel hT hI hγ hF hF0 hFb k u v) ≤
          C * spacesNemytskiiMajorant hT base (s + loss) u v := by
  classical
  obtain ⟨base, loss, hb⟩ := spaces_nemytskii_material_jet_tame hT hI
  refine ⟨base, loss, fun γ hγ F hF hF0 hFb k s R hR => ?_⟩
  have h (j : JetIndex s) := hb γ hγ F hF hF0 hFb k (j.val 0).val (j.val 1).val
    (j.val 2).val s j.property R hR
  choose C hC hbound using h
  refine ⟨∑ j, C j, Finset.sum_nonneg (fun j _ => hC j), fun u hu v => ?_⟩
  rw [spacesPhysicalGrading_eq_physicalNorm hT γ, spacesNemytskiiKernel_decode]
  apply (spaces_physicalNorm_le_jet_sum
    (spacesNemytskiiPhysical_heightMember hT hI hγ hF hF0 hFb k u v) s).trans
  calc
    (∑ j : JetIndex s, lpNorm (weightedPhysicalJet T γ (j.val 0).val (j.val 1).val (j.val 2).val
        (spacesNemytskiiPhysical hT γ F k u v)) 2 materialCylinderMeasure) ≤
        ∑ j : JetIndex s, C j * spacesNemytskiiMajorant hT base (s + loss) u v := by
      apply Finset.sum_le_sum
      intro j _
      change lpNorm (fun p => T.M (T.radius p.1) ^ (j.val 2).val *
        mixedDerivative (j.val 0).val (j.val 1).val
          (materialPullback T γ (spacesNemytskiiPhysical hT γ F k u v)) p) 2 materialCylinderMeasure ≤ _
      rw [spacesNemytskiiPhysical_pullback]
      exact (hbound j u hu v).2
    _ = _ := (Finset.sum_mul _ _ _).symm

end ContinuousFlexibility.Statements
