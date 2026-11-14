module

public import ContinuousFlexibility.Analysis.MaterialRadiusJets
public import ContinuousFlexibility.Analysis.PolynomialJetOperations
public import ContinuousFlexibility.Analysis.MaterialMixedMultiplier

/-!
# Uniform coefficients act on the actual material weighted energies

Ordinary Fréchet jets bounded on the physical annulus remain bounded
after the actual material-coordinate substitution. The angular
coordinate is a lift, so only positive jets of the coordinate map are
used. Evaluation on coordinate unit vectors identifies the resulting
bounds with the genuine mixed derivatives used in the physical norms.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology BigOperators

theorem mixedDerivative_abs_le_norm_iteratedFDeriv
    {U : Set PolarPoint} {f : PolarPoint → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (a b : ℕ) {p : PolarPoint} (hp : p ∈ U) :
    |mixedDerivative a b f p| ≤ ‖iteratedFDeriv ℝ (a + b) f p‖ := by
  let w : Fin (a + b) → Fin 2 :=
    Fin.addCases (fun _ : Fin a => 0) (fun _ : Fin b => 1)
  have hradial : (∑ i : Fin (a + b), if w i = 0 then 1 else 0) = a := by
    rw [Fin.sum_univ_add]
    simp [w]
  have hangular : (∑ i : Fin (a + b), if w i = 0 then 0 else 1) = b := by
    rw [Fin.sum_univ_add]
    simp [w]
  have heq := iteratedFDeriv_cylinderBasis_eq_mixedDerivative hU hf (a + b) hp w
  rw [hradial, hangular] at heq
  have hu (j : Fin 2) : ‖cylinderBasisVector j‖ = 1 := by
    unfold cylinderBasisVector
    split_ifs <;> norm_num [Prod.norm_def]
  rw [← heq, ← Real.norm_eq_abs]
  simpa only [hu, Finset.prod_const_one, mul_one] using
    (iteratedFDeriv ℝ (a + b) f p).le_opNorm (fun i => cylinderBasisVector (w i))

theorem materialCoordinate_positive_fderiv_bounded
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ p : PolarPoint,
      ‖iteratedFDeriv ℝ n (fun q : PolarPoint => (T.radius q.1, q.2)) p‖ ≤ A := by
  have hr : ContDiff ℝ ∞ T.radius := hT.2.2.2.2.2.2.1
  have hb (k : ℕ) (_hk : k ≤ n) :
      ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ (_ : Unit) r,
        |iteratedDeriv k T.radius r| ≤ A * (1 : ℝ) ^ P := by
    obtain ⟨A, hA, hbound⟩ := materialRadius_iteratedDeriv_bounded hT k
    exact ⟨A, 0, hA, le_rfl, fun _ r => by
      simpa only [Real.rpow_zero, mul_one] using hbound r⟩
  obtain ⟨A, P, hA, _, hbound⟩ := norm_iteratedFDeriv_scalar_coordinate_polynomial_bound
    (fun _ : Unit => (1 : ℝ)) (fun _ => le_rfl) (fun _ => univ)
    (fun _ => isOpen_univ) (fun _ => T.radius) (fun _ => hr)
    (ContinuousLinearMap.fst ℝ ℝ ℝ) n hb
  let L : PolarPoint →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  refine ⟨A + ‖L‖, add_nonneg hA (ContinuousLinearMap.opNorm_nonneg L), fun p => ?_⟩
  have hrad : ContDiffAt ℝ ∞ (fun q : PolarPoint => T.radius q.1) p :=
    hr.contDiffAt.comp p contDiffAt_fst
  rw [iteratedFDeriv_prodMk hrad
    (contDiffAt_snd : ContDiffAt ℝ ∞ (fun q : PolarPoint => q.2) p) (by simp),
    ContinuousMultilinearMap.opNorm_prod]
  apply max_le
  · have ha : ‖iteratedFDeriv ℝ n (fun q : PolarPoint => T.radius q.1) p‖ ≤ A := by
      simpa only [Real.one_rpow, mul_one, ContinuousLinearMap.coe_fst'] using
        hbound () p (mem_univ _)
    exact ha.trans (le_add_of_nonneg_right (ContinuousLinearMap.opNorm_nonneg L))
  · exact (norm_iteratedFDeriv_linear_of_pos L n hn p).trans (le_add_of_nonneg_left hA)

theorem materialCoordinate_comp_fderiv_bounded
    {D : ReferenceData} {T : MaterialData} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hT : IsMaterialData D T) {f : PolarPoint → F}
    (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (hbound : ∀ n : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ p ∈ annularOpen D,
      ‖iteratedFDeriv ℝ n f p‖ ≤ A) (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ p : PolarPoint,
      ‖iteratedFDeriv ℝ n (fun q => f (T.radius q.1, q.2)) p‖ ≤ A := by
  have hr : ContDiff ℝ ∞ T.radius := hT.2.2.2.2.2.2.1
  have hinside (r : ℝ) : T.radius r ∈ Ioo D.a D.b := (hT.2.2.2.2.2.2.2.1 r).1
  let g (p : PolarPoint) : PolarPoint := (T.radius p.1, p.2)
  have hg : ContDiff ℝ ∞ g := (hr.comp contDiff_fst).prodMk contDiff_snd
  have hout (k : ℕ) (_ : k ≤ n) :
      ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ (_ : Unit) p, p ∈ (univ : Set PolarPoint) →
        ‖iteratedFDeriv ℝ k f (g p)‖ ≤ A * (1 : ℝ) ^ P := by
    obtain ⟨A, hA, hb⟩ := hbound k
    exact ⟨A, 0, hA, le_rfl, fun _ p _ => by
      simpa only [Real.rpow_zero, mul_one] using hb (g p) ⟨hinside p.1, mem_univ _⟩⟩
  have hin (k : ℕ) (hk : 1 ≤ k) (_ : k ≤ n) :
      ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ (_ : Unit) p, p ∈ (univ : Set PolarPoint) →
        ‖iteratedFDeriv ℝ k g p‖ ≤ A * (1 : ℝ) ^ P := by
    obtain ⟨A, hA, hb⟩ := materialCoordinate_positive_fderiv_bounded hT k hk
    exact ⟨A, 0, hA, le_rfl, fun _ p _ => by
      simpa only [Real.rpow_zero, mul_one] using hb p⟩
  obtain ⟨A, P, hA, _, hb⟩ := norm_iteratedFDeriv_comp_polynomial_bound
    (fun _ : Unit => (1 : ℝ)) (fun _ => le_rfl) (fun _ => univ) (fun _ => annularOpen D)
    (fun _ => isOpen_univ) (fun _ => isOpen_Ioo.prod isOpen_univ)
    (fun _ => g) (fun _ => f) (fun _ => hg.contDiffOn) (fun _ => hf)
    (fun _ p _ => ⟨hinside p.1, mem_univ _⟩) n hout hin
  exact ⟨A, hA, fun p => by
    simpa only [Real.one_rpow, mul_one] using hb () p (mem_univ _)⟩

theorem materialCoordinate_comp_mixed_bounded
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {f : PolarPoint → ℝ} (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (hbound : ∀ n : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ p ∈ annularOpen D,
      ‖iteratedFDeriv ℝ n f p‖ ≤ A) (a b : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ p : PolarPoint,
      |mixedDerivative a b (fun q => f (T.radius q.1, q.2)) p| ≤ A := by
  have hr : ContDiff ℝ ∞ T.radius := hT.2.2.2.2.2.2.1
  have hinside (r : ℝ) : T.radius r ∈ Ioo D.a D.b := (hT.2.2.2.2.2.2.2.1 r).1
  have hg : ContDiff ℝ ∞ (fun q : PolarPoint => f (T.radius q.1, q.2)) :=
    hf.comp_contDiff ((hr.comp contDiff_fst).prodMk contDiff_snd)
      (fun p => ⟨hinside p.1, mem_univ _⟩)
  obtain ⟨A, hA, hb⟩ := materialCoordinate_comp_fderiv_bounded hT hf hbound (a + b)
  exact ⟨A, hA, fun p => (mixedDerivative_abs_le_norm_iteratedFDeriv
    isOpen_univ hg.contDiffOn a b (mem_univ p)).trans (hb p)⟩

theorem memLp_weightedPhysicalJet_mul_of_bounded_coefficient
    {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    {f u : PolarPoint → ℝ} (hT : IsMaterialData D T)
    (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (hbound : ∀ n : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ p ∈ annularOpen D,
      ‖iteratedFDeriv ℝ n f p‖ ≤ A)
    (hu : ContDiffOn ℝ ∞ u (annularOpen D))
    (hLp : ∀ a b c, MemLp (weightedPhysicalJet T γ a b c u) 2 materialCylinderMeasure)
    (a b c : ℕ) :
    MemLp (weightedPhysicalJet T γ a b c (fun p => f p * u p)) 2 materialCylinderMeasure := by
  let W (p : PolarPoint) : ℝ := T.M (T.radius p.1)
  let F (p : PolarPoint) : ℝ := f (T.radius p.1, p.2)
  let G : PolarPoint → ℝ := materialPullback T γ u
  have hr : ContDiff ℝ ∞ T.radius := hT.2.2.2.2.2.2.1
  have hinside (r : ℝ) : T.radius r ∈ Ioo D.a D.b := (hT.2.2.2.2.2.2.2.1 r).1
  have hW : Continuous W :=
    ((materialRadius_comp_contDiff hT (hT.1 T.M (by simp))).comp contDiff_fst).continuous
  have hWpos (p : PolarPoint) : 0 ≤ W p :=
    zero_le_one.trans (hT.2.1 _ (hinside p.1)).2.2.2
  have hF : ContDiff ℝ ∞ F :=
    hf.comp_contDiff ((hr.comp contDiff_fst).prodMk contDiff_snd)
      (fun p => ⟨hinside p.1, mem_univ _⟩)
  have hG : ContDiff ℝ ∞ G := contDiff_materialPullback hT hu
  have hFb (i j : ℕ) : ∃ K : ℝ, 0 ≤ K ∧
      ∀ p, |mixedDerivative i j F p| ≤ K * W p ^ 0 := by
    obtain ⟨K, hK, hb⟩ := materialCoordinate_comp_mixed_bounded hT hf hbound i j
    exact ⟨K, hK, fun p => by simpa only [pow_zero, mul_one] using hb p⟩
  have h := memLp_weighted_mixed_product hW hWpos hF hG 0 hFb hLp a b c
  have heq : materialPullback T γ (fun p => f p * u p) =
      (fun p => F p * G p) := by
    funext p
    dsimp only [materialPullback, F, G]
    ring
  have hjet : weightedPhysicalJet T γ a b c (fun p => f p * u p) =
      (fun p => W p ^ c * mixedDerivative a b (fun q => F q * G q) p) := by
    funext p
    change W p ^ c * mixedDerivative a b (materialPullback T γ (fun q => f q * u q)) p = _
    rw [heq]
  exact hjet.symm ▸ h

end ContinuousFlexibility.Statements
