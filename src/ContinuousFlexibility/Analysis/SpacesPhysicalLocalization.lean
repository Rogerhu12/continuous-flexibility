import ContinuousFlexibility.Analysis.SpacesRadialWeightOverlap
import ContinuousFlexibility.Analysis.SpacesHeightProductBounds

/-!
# Actual weighted localization of physical jets

The radial partition and its derivative overlap bounds give continuous
linear localization maps on every actual cylinder jet. A finite Leibniz
sum gives the prescribed weighted derivatives of each localized smooth
representative, with no loss of differential order.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped Topology ContDiff BigOperators ENNReal

/-- Multiplication by a radial function has a one-dimensional Leibniz
sum, while retaining the prescribed mixed derivative convention. -/
theorem spaces_mixedDerivative_radial_mul {χ : ℝ → ℝ} {v : PolarPoint → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hv : ContDiff ℝ ∞ v) (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (fun z => χ z.1 * v z) p =
      ∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ) *
        iteratedDeriv i χ p.1 * mixedDerivative (a - i) b v p := by
  have hslice : ContDiff ℝ ∞ (fun r => iteratedDeriv b (fun θ => v (r, θ)) p.2) := by
    convert (contDiff_mixedDerivative hv 0 b).comp
      (contDiff_id.prodMk (contDiff_const (c := p.2))) using 1
    funext r
    simp only [Function.comp_apply, id_eq, mixedDerivative, iteratedDeriv_zero]
  have he : (fun r => iteratedDeriv b (fun θ => χ r * v (r, θ)) p.2) =
      fun r => χ r * iteratedDeriv b (fun θ => v (r, θ)) p.2 := by
    funext r
    exact iteratedDeriv_const_mul_field (χ r) (fun θ => v (r, θ))
  unfold mixedDerivative
  rw [he, iteratedDeriv_fun_mul (hχ.of_le (by simp)).contDiffAt
    (hslice.of_le (by simp)).contDiffAt]

variable {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)

/-- The original weighted mixed jet as a continuous linear map. -/
def spacesPhysicalWeightedJet (a b c : ℕ) : PhysicalJetProjectiveLimit hT →L[ℝ] CylinderL2 :=
  (physicalJetCoordinate (a + b + c) (spaces_full_jet_index a b c (a + b + c) le_rfl)).comp
    ((physicalJetClosedSubmodule hT (a + b + c)).subtypeL.comp
      (projectiveCoordinate (fun s => physicalJetClosedSubmodule hT s)
        (physicalJetBond hT) (a + b + c)))

theorem spacesPhysicalWeightedJet_apply (a b c : ℕ) (u : PhysicalJetProjectiveLimit hT) :
    spacesPhysicalWeightedJet hT a b c u =
      (u.val (a + b + c)).val (spaces_full_jet_index a b c (a + b + c) le_rfl) := rfl

theorem spacesPhysicalWeightedJet_ae (a b c : ℕ) (u : PhysicalJetProjectiveLimit hT) :
    (spacesPhysicalWeightedJet hT a b c u : PolarPoint → ℝ) =ᵐ[materialCylinderMeasure]
      fun p => T.M (T.radius p.1) ^ c * mixedDerivative a b (spacesPhysicalRepresentative hT u) p := by
  rw [spacesPhysicalWeightedJet_apply]
  have hw : weightedPhysicalJet T 0 a b c (spacesPhysicalDecoded hT 0 u) =
      fun p => T.M (T.radius p.1) ^ c *
        mixedDerivative a b (spacesPhysicalRepresentative hT u) p := by
    funext p
    rw [weightedPhysicalJet, spacesPhysicalDecoded_pullback]
  rw [← hw]
  simpa only [spaces_full_jet_index, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons, Fin.isValue] using
    spacesPhysicalDecoded_level_ae hT 0 u (a + b + c)
      (spaces_full_jet_index a b c (a + b + c) le_rfl)

theorem spacesPhysicalWeightedJet_norm_le (a b c s : ℕ) (hs : a + b + c ≤ s)
    (u : PhysicalJetProjectiveLimit hT) :
    ‖spacesPhysicalWeightedJet hT a b c u‖ ≤ spacesPhysicalGrading hT s u := by
  rw [spacesPhysicalWeightedJet_apply]
  exact (PiLp.norm_apply_le _ _).trans
    (norm_coordinate_le_graded (fun n => physicalJetClosedSubmodule hT n)
      (physicalJetBond hT) hs u)

/-- The derivative cutoff with the center-to-point material weight ratio. -/
def spacesPhysicalLocalizationMultiplier (T : MaterialData) (i c : ℕ) (n : ℤ)
    (p : PolarPoint) : ℝ :=
  iteratedDeriv i (spacesRadialPartition n) p.1 *
    (T.M (T.radius n) ^ c / T.M (T.radius p.1) ^ c)

include hT in
theorem spacesPhysicalLocalizationMultiplier_continuous (i c : ℕ) (n : ℤ) :
    Continuous (spacesPhysicalLocalizationMultiplier T i c n) := by
  have hw : Continuous (fun p : PolarPoint => T.M (T.radius p.1) ^ c) := by
    exact continuous_physicalJetWeight hT (spaces_full_jet_index 0 0 c c (by omega))
  exact ((spacesRadialPartition_contDiff n).continuous_iteratedDeriv i (by simp)).comp
    continuous_fst |>.mul (continuous_const.div hw
      (fun p => pow_ne_zero c (spaces_material_M_pos hT p.1).ne'))

/-- One uniform overlap constant for this derivative and weight order. -/
def spacesPhysicalLocalizationOverlapConstant (i c : ℕ) : ℝ :=
  (spacesRadialPartition_weighted_derivative_overlap hT i c).choose

theorem spacesPhysicalLocalizationOverlapConstant_nonneg (i c : ℕ) :
    0 ≤ spacesPhysicalLocalizationOverlapConstant hT i c :=
  (spacesRadialPartition_weighted_derivative_overlap hT i c).choose_spec.1

theorem spacesPhysicalLocalizationMultiplier_square_bound (i c : ℕ)
    (s : Finset ℤ) (p : PolarPoint) :
    ∑ n ∈ s, spacesPhysicalLocalizationMultiplier T i c n p ^ 2 ≤
      spacesPhysicalLocalizationOverlapConstant hT i c ^ 2 :=
  (spacesRadialPartition_weighted_derivative_overlap hT i c).choose_spec.2 s p.1

/-- The actual bounded-overlap map on cylinder `L²` classes. -/
def spacesPhysicalLocalizationOverlap (i c : ℕ) :
    CylinderL2 →L[ℝ] lp (fun _ : ℤ => CylinderL2) 2 :=
  spacesLpOverlapAnalysis materialCylinderMeasure (spacesPhysicalLocalizationMultiplier T i c)
    (fun n => (spacesPhysicalLocalizationMultiplier_continuous hT i c n).aestronglyMeasurable)
    (spacesPhysicalLocalizationOverlapConstant hT i c)
    (spacesPhysicalLocalizationOverlapConstant_nonneg hT i c)
    (spacesPhysicalLocalizationMultiplier_square_bound hT i c)

theorem spacesPhysicalLocalizationOverlap_ae (i c : ℕ) (f : CylinderL2) (n : ℤ) :
    (spacesPhysicalLocalizationOverlap hT i c f n : PolarPoint → ℝ) =ᵐ[materialCylinderMeasure]
      fun p => spacesPhysicalLocalizationMultiplier T i c n p * f p := by
  rw [spacesPhysicalLocalizationOverlap, spacesLpOverlapAnalysis_apply]
  exact spacesLpMultiplier_ae _ _ _ _ _ _

theorem spacesPhysicalLocalizationOverlap_norm_le (i c : ℕ) (f : CylinderL2) :
    ‖spacesPhysicalLocalizationOverlap hT i c f‖ ≤
      spacesPhysicalLocalizationOverlapConstant hT i c * ‖f‖ :=
  spacesLpOverlapAnalysis_norm_le _ _ _ _ _ _ f

/-- The actual smooth function in one radial localization cell. -/
def spacesPhysicalLocalizedRepresentative (n : ℤ) (u : PhysicalJetProjectiveLimit hT)
    (p : PolarPoint) : ℝ :=
  spacesRadialPartition n p.1 * spacesPhysicalRepresentative hT u p

theorem spacesPhysicalLocalizedRepresentative_eq_zero (n : ℤ)
    (u : PhysicalJetProjectiveLimit hT) (p : PolarPoint) (hp : 1 ≤ |p.1 - (n : ℝ)|) :
    spacesPhysicalLocalizedRepresentative hT n u p = 0 := by
  by_cases hh : p.1 - (n : ℝ) ≤ 0
  · have hx : p.1 ≤ (n : ℝ) - 1 := by rw [abs_of_nonpos hh] at hp; linarith
    simp only [spacesPhysicalLocalizedRepresentative,
      spacesRadialPartition_eq_zero_left n hx, zero_mul]
  · have hx : (n : ℝ) + 1 ≤ p.1 := by
      rw [abs_of_nonneg (le_of_not_ge hh)] at hp
      linarith
    simp only [spacesPhysicalLocalizedRepresentative,
      spacesRadialPartition_eq_zero_right n hx, zero_mul]

theorem spacesPhysicalLocalizedRepresentative_isCylinderTest (n : ℤ)
    (u : PhysicalJetProjectiveLimit hT) :
    IsCylinderTest (spacesPhysicalLocalizedRepresentative hT n u) := by
  have hχ : Function.Periodic (fun p : PolarPoint => spacesRadialPartition n p.1)
      (0, Real.pi) := by
    intro p
    simp only [Prod.fst_add, add_zero]
  refine ⟨((spacesRadialPartition_contDiff n).comp contDiff_fst).mul
    (spacesPhysicalRepresentative_contDiff hT u),
    hχ.mul (spacesPhysicalRepresentative_periodic hT u), |(n : ℝ)| + 2, by positivity, ?_⟩
  intro p hp
  apply spacesPhysicalLocalizedRepresentative_eq_zero hT n u p
  have hab := abs_add_le (p.1 - (n : ℝ)) (n : ℝ)
  rw [sub_add_cancel] at hab
  linarith

theorem spacesPhysicalLocalizationOverlap_weightedJet_ae (a b c i : ℕ)
    (u : PhysicalJetProjectiveLimit hT) (n : ℤ) :
    (spacesPhysicalLocalizationOverlap hT i c
      (spacesPhysicalWeightedJet hT (a - i) b c u) n : PolarPoint → ℝ)
        =ᵐ[materialCylinderMeasure] fun p =>
          T.M (T.radius n) ^ c * iteratedDeriv i (spacesRadialPartition n) p.1 *
            mixedDerivative (a - i) b (spacesPhysicalRepresentative hT u) p := by
  filter_upwards [spacesPhysicalLocalizationOverlap_ae hT i c
      (spacesPhysicalWeightedJet hT (a - i) b c u) n,
    spacesPhysicalWeightedJet_ae hT (a - i) b c u] with p hp hq
  rw [hp, hq]
  have hn : T.M (T.radius p.1) ^ c ≠ 0 :=
    pow_ne_zero c (spaces_material_M_pos hT p.1).ne'
  dsimp only [spacesPhysicalLocalizationMultiplier]
  calc
    iteratedDeriv i (spacesRadialPartition n) p.1 *
        (T.M (T.radius n) ^ c / T.M (T.radius p.1) ^ c) *
        (T.M (T.radius p.1) ^ c * mixedDerivative (a - i) b
          (spacesPhysicalRepresentative hT u) p) =
      iteratedDeriv i (spacesRadialPartition n) p.1 *
        ((T.M (T.radius n) ^ c / T.M (T.radius p.1) ^ c) * T.M (T.radius p.1) ^ c) *
          mixedDerivative (a - i) b (spacesPhysicalRepresentative hT u) p := by ring
    _ = _ := by rw [div_mul_cancel₀ _ hn]; ring

/-- The complete localized weighted jet family, as a finite Leibniz sum
of bounded-overlap maps applied to the actual source coordinates. -/
def spacesPhysicalLocalizedJetFamily (a b c : ℕ) :
    PhysicalJetProjectiveLimit hT →L[ℝ] lp (fun _ : ℤ => CylinderL2) 2 :=
  ∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ) •
    (spacesPhysicalLocalizationOverlap hT i c).comp
      (spacesPhysicalWeightedJet hT (a - i) b c)

theorem spacesPhysicalLocalizedJetFamily_apply (a b c : ℕ) (u : PhysicalJetProjectiveLimit hT) :
    spacesPhysicalLocalizedJetFamily hT a b c u =
      ∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ) •
        spacesPhysicalLocalizationOverlap hT i c (spacesPhysicalWeightedJet hT (a - i) b c u) := by
  simp only [spacesPhysicalLocalizedJetFamily, sum_apply, smul_apply, ContinuousLinearMap.comp_apply]

theorem spacesPhysicalLocalizedJetFamily_row (a b c : ℕ) (u : PhysicalJetProjectiveLimit hT)
    (n : ℤ) :
    spacesPhysicalLocalizedJetFamily hT a b c u n =
      ∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ) •
        spacesPhysicalLocalizationOverlap hT i c (spacesPhysicalWeightedJet hT (a - i) b c u) n := by
  rw [spacesPhysicalLocalizedJetFamily_apply]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply]

/-- Each row represents exactly the requested weighted classical jet. -/
theorem spacesPhysicalLocalizedJetFamily_ae (a b c : ℕ) (u : PhysicalJetProjectiveLimit hT)
    (n : ℤ) :
    (spacesPhysicalLocalizedJetFamily hT a b c u n : PolarPoint → ℝ)
      =ᵐ[materialCylinderMeasure] fun p => T.M (T.radius n) ^ c *
        mixedDerivative a b (spacesPhysicalLocalizedRepresentative hT n u) p := by
  rw [spacesPhysicalLocalizedJetFamily_row]
  have hterm (i : ℕ) :
      (((a.choose i : ℝ) • spacesPhysicalLocalizationOverlap hT i c
        (spacesPhysicalWeightedJet hT (a - i) b c u) n : CylinderL2) : PolarPoint → ℝ)
        =ᵐ[materialCylinderMeasure] fun p =>
          (a.choose i : ℝ) * (T.M (T.radius n) ^ c *
            iteratedDeriv i (spacesRadialPartition n) p.1 *
              mixedDerivative (a - i) b (spacesPhysicalRepresentative hT u) p) := by
    filter_upwards [Lp.coeFn_smul (a.choose i : ℝ)
        (spacesPhysicalLocalizationOverlap hT i c (spacesPhysicalWeightedJet hT (a - i) b c u) n),
      spacesPhysicalLocalizationOverlap_weightedJet_ae hT a b c i u n] with p hp hq
    rw [hp, Pi.smul_apply, smul_eq_mul, hq]
  filter_upwards [Lp.coeFn_fun_finsetSum (Finset.range (a + 1))
      (fun i => (a.choose i : ℝ) • spacesPhysicalLocalizationOverlap hT i c
        (spacesPhysicalWeightedJet hT (a - i) b c u) n), ae_all_iff.mpr hterm] with p hp hq
  rw [hp]
  unfold spacesPhysicalLocalizedRepresentative
  rw [spaces_mixedDerivative_radial_mul (spacesRadialPartition_contDiff n)
      (spacesPhysicalRepresentative_contDiff hT u), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hq i]
  ring

theorem spacesPhysicalLocalizedJetFamily_derivative_ae (a b : ℕ)
    (u : PhysicalJetProjectiveLimit hT) (n : ℤ) :
    (spacesPhysicalLocalizedJetFamily hT a b 0 u n : PolarPoint → ℝ)
      =ᵐ[materialCylinderMeasure] mixedDerivative a b (spacesPhysicalLocalizedRepresentative hT n u) := by
  simpa only [pow_zero, one_mul] using spacesPhysicalLocalizedJetFamily_ae hT a b 0 u n

theorem spacesPhysicalLocalizedJetFamily_zero_ae (u : PhysicalJetProjectiveLimit hT) (n : ℤ) :
    (spacesPhysicalLocalizedJetFamily hT 0 0 0 u n : PolarPoint → ℝ)
      =ᵐ[materialCylinderMeasure] spacesPhysicalLocalizedRepresentative hT n u := by
  simpa only [spaces_mixedDerivative_zero] using
    spacesPhysicalLocalizedJetFamily_derivative_ae hT 0 0 u n

/-- The norm constant is the finite Leibniz sum of overlap constants. -/
def spacesPhysicalLocalizationConstant (a c : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ) * spacesPhysicalLocalizationOverlapConstant hT i c

theorem spacesPhysicalLocalizationConstant_nonneg (a c : ℕ) :
    0 ≤ spacesPhysicalLocalizationConstant hT a c :=
  Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _)
    (spacesPhysicalLocalizationOverlapConstant_nonneg hT i c)

theorem spacesPhysicalLocalizedJetFamily_norm_le (a b c s : ℕ) (hs : a + b + c ≤ s)
    (u : PhysicalJetProjectiveLimit hT) :
    ‖spacesPhysicalLocalizedJetFamily hT a b c u‖ ≤
      spacesPhysicalLocalizationConstant hT a c * spacesPhysicalGrading hT s u := by
  rw [spacesPhysicalLocalizedJetFamily_apply]
  calc
    ‖∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ) •
        spacesPhysicalLocalizationOverlap hT i c (spacesPhysicalWeightedJet hT (a - i) b c u)‖ ≤
        ∑ i ∈ Finset.range (a + 1), ‖(a.choose i : ℝ) •
          spacesPhysicalLocalizationOverlap hT i c (spacesPhysicalWeightedJet hT (a - i) b c u)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (a + 1), ((a.choose i : ℝ) *
        spacesPhysicalLocalizationOverlapConstant hT i c) * spacesPhysicalGrading hT s u := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg (a.choose i))]
      calc
        (a.choose i : ℝ) *
            ‖spacesPhysicalLocalizationOverlap hT i c (spacesPhysicalWeightedJet hT (a - i) b c u)‖ ≤
            (a.choose i : ℝ) * (spacesPhysicalLocalizationOverlapConstant hT i c *
              ‖spacesPhysicalWeightedJet hT (a - i) b c u‖) :=
          mul_le_mul_of_nonneg_left (spacesPhysicalLocalizationOverlap_norm_le hT i c _)
            (Nat.cast_nonneg _)
        _ ≤ (a.choose i : ℝ) * (spacesPhysicalLocalizationOverlapConstant hT i c *
              spacesPhysicalGrading hT s u) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (spacesPhysicalWeightedJet_norm_le hT (a - i) b c s (by omega) u)
              (spacesPhysicalLocalizationOverlapConstant_nonneg hT i c)) (Nat.cast_nonneg _)
        _ = _ := by ring
    _ = _ := by rw [spacesPhysicalLocalizationConstant, Finset.sum_mul]

theorem spacesPhysicalLocalizedJetFamily_bound (a b c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : PhysicalJetProjectiveLimit hT,
      ‖spacesPhysicalLocalizedJetFamily hT a b c u‖ ≤ C * spacesPhysicalGrading hT (a + b + c) u :=
  ⟨spacesPhysicalLocalizationConstant hT a c, spacesPhysicalLocalizationConstant_nonneg hT a c,
    spacesPhysicalLocalizedJetFamily_norm_le hT a b c (a + b + c) le_rfl⟩

theorem spacesPhysicalLocalizedJetFamily_weight (c : ℕ) (u : PhysicalJetProjectiveLimit hT)
    (n : ℤ) :
    spacesPhysicalLocalizedJetFamily hT 0 0 c u n =
      T.M (T.radius n) ^ c • spacesPhysicalLocalizedJetFamily hT 0 0 0 u n := by
  apply Lp.ext
  filter_upwards [spacesPhysicalLocalizedJetFamily_ae hT 0 0 c u n,
    spacesPhysicalLocalizedJetFamily_ae hT 0 0 0 u n,
    Lp.coeFn_smul (T.M (T.radius n) ^ c) (spacesPhysicalLocalizedJetFamily hT 0 0 0 u n)]
      with p hc h₀ hsmul
  rw [hc, hsmul, Pi.smul_apply, smul_eq_mul, h₀, pow_zero, one_mul]

end ContinuousFlexibility.Statements
