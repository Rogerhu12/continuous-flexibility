module

public import ContinuousFlexibility.Radial.InnerRadialActualAssembly
public import ContinuousFlexibility.Radial.InnerRadialGapDirichletBound
public import ContinuousFlexibility.Radial.InnerSupportedWeights
public import ContinuousFlexibility.Radial.InnerCoefficientCosts

/-!
# The weighted actual Dirichlet sum and its fixed coefficient loss

These estimates apply to the canonical physical Dirichlet map of the
actual model/gap dictionary. The isometric supported-space inclusion
identifies it with the same orthogonal ambient sum. The common local
power thirty-six and the actual reciprocal cell-weight comparisons
give loss thirty-seven, independently of the number of retained cells.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace

def innerRadialSupportedMultiplier (D : ReferenceData) {n : ℕ}
    (G : InnerRadialChainGeometry D n) (bordered : Bool)
    (W : ℝ → ℝ) (hW : Measurable W) (B : ℝ) (hbound : ∀ x, |W x| ≤ B) :
    InnerRadialPhysicalSource D G bordered →L[ℝ] InnerRadialPhysicalSource D G bordered :=
  innerSupportedWeightMultiplier (radialHilbertMeasure D) (innerRadialChainRegion D G)
    (innerRadialChainRegion_measurable D G) bordered W hW B hbound

theorem innerRadialSupportedMultiplier_apply (D : ReferenceData) {n : ℕ}
    (G : InnerRadialChainGeometry D n) (bordered : Bool)
    (W : ℝ → ℝ) (hW : Measurable W) (B : ℝ) (hbound : ∀ x, |W x| ≤ B)
    (F : InnerRadialPhysicalSource D G bordered) :
    (innerRadialSupportedMultiplier D G bordered W hW B hbound F).val =
      innerBorderFieldMap (radialHilbertMeasure D)
        (innerWeightMultiplier (radialHilbertMeasure D) W hW B hbound) F.val :=
  innerSupportedWeightMultiplier_apply _ _ _ _ _ _ _ _ _

namespace InnerRadialActualChain

variable {D : ReferenceData} {n : ℕ} {G : InnerRadialChainGeometry D n}
  {bordered : Bool} {j : ℝ} {central : Fin (n + 1)} {column : RadialModeL2 D}
  (A : InnerRadialActualChain D G bordered j central column)

local notation "sets" => (fun p : Fin (n + 1) => Ioo (G.left p) (G.right p))
local notation "H" => InnerRadialPhysicalSource D G bordered
local notation "ambient" => InnerBorderL2 (radialHilbertMeasure D)

/-- A local coefficient cost controls the genuine weighted physical
Dirichlet map with no extra supported-space or dimension factor. -/
theorem dirichlet_weighted_piece_cost (hw : ContDiff ℝ ∞ D.w)
    (W V : ℝ → ℝ) (hW : Measurable W) (hV : Measurable V) (CW CV : ℝ)
    (hWC : ∀ x, |W x| ≤ CW) (hVC : ∀ x, |V x| ≤ CV)
    (loss ratio base : Fin (n + 1) → ℝ)
    (hloss : ∀ p, 0 ≤ loss p) (hratio : ∀ p, 0 ≤ ratio p) (hbase : ∀ p, 0 < base p)
    (hcenterW : 1 ≤ loss central * ratio central * base central)
    (hcenterV : 1 ≤ ratio central / base central)
    (hlocalW : ∀ p x, x ∈ sets p → |W x| ≤ loss p * ratio p * base p)
    (hlocalV : ∀ p x, x ∈ sets p → |V x| ≤ ratio p / base p)
    {K : ℝ} (hK : 0 ≤ K)
    (hcost : ∀ p, loss p * (ratio p ^ 2 * ‖(A.piece p).dirichlet hw‖) ≤ K) :
    ‖innerRadialSupportedMultiplier D G bordered W hW CW hWC ∘L A.dirichlet hw ∘L
      innerRadialSupportedMultiplier D G bordered V hV CV hVC‖ ≤ K := by
  let MW := innerBorderFieldMap (radialHilbertMeasure D)
    (innerWeightMultiplier (radialHilbertMeasure D) W hW CW hWC)
  let MV := innerBorderFieldMap (radialHilbertMeasure D)
    (innerWeightMultiplier (radialHilbertMeasure D) V hV CV hVC)
  have hrestrict :
      ‖innerRadialSupportedMultiplier D G bordered W hW CW hWC ∘L A.dirichlet hw ∘L
        innerRadialSupportedMultiplier D G bordered V hV CV hVC‖ ≤
      ‖MW ∘L A.ambientDirichlet hw ∘L MV‖ := by
    apply innerIsometricOperator_norm_le (innerRadialPhysicalInclusion D G bordered)
      (innerRadialPhysicalInclusion D G bordered)
    intro F
    simp only [ContinuousLinearMap.comp_apply, innerRadialPhysicalInclusion_apply,
      innerRadialSupportedMultiplier_apply, A.dirichlet_ambient, MW, MV]
  apply hrestrict.trans
  exact innerBorderDirichletSum_localized_cost (radialHilbertMeasure D) sets central
    (fun p => (A.piece p).dirichlet hw) (fun _ => measurableSet_Ioo)
    (innerRadialChainPieces_disjoint D G) W V hW hV CW CV hWC hVC loss ratio base
    hloss hratio hbase hcenterW hcenterV hlocalW hlocalV hK hcost

/-- The actual cell comparisons and local power thirty-six give the
fixed localized loss thirty-seven. Only the constant depends on N. -/
theorem dirichlet_localized_coefficient_bound (hw : ContDiff ℝ ∞ D.w)
    (W₁ V : ℝ → ℝ) (hW₁ : Measurable W₁) (hV : Measurable V) (CW CV : ℝ)
    (hWC : ∀ x, |W₁ x| ≤ CW) (hVC : ∀ x, |V x| ≤ CV)
    (index : Fin (n + 1) → ℕ) (N : ℕ) (hindex : ∀ p, N ≤ index p)
    (hcenter : index central = N) (base : Fin (n + 1) → ℝ)
    (hbase : ∀ p, 0 < base p) (hbasecenter : base central = 1)
    (hlocalW : ∀ p x, x ∈ sets p → |W₁ x| ≤
      innerCoefficientLoss N 37 (index p) * sqrt (radialE (index p)) * base p)
    (hlocalV : ∀ p x, x ∈ sets p → |V x| ≤ sqrt (radialE (index p)) / base p)
    {K : ℝ} (hK : 0 ≤ K)
    (hcost : ∀ p, ‖(A.piece p).dirichlet hw‖ ≤ K * radialE (index p) ^ (36 : ℝ)) :
    ‖innerRadialSupportedMultiplier D G bordered W₁ hW₁ CW hWC ∘L A.dirichlet hw ∘L
      innerRadialSupportedMultiplier D G bordered V hV CV hVC‖ ≤ K * radialE N ^ (37 : ℝ) := by
  have hsqrt : 1 ≤ sqrt (radialE N) := by
    simpa only [sqrt_one, radialE] using sqrt_le_sqrt (one_le_exp_iff.mpr (radialQ_nonneg N))
  have hlosscenter : innerCoefficientLoss N 37 N = 1 := by
    rw [innerCoefficientLoss_eq_exp, sub_self, mul_zero, neg_zero, exp_zero]
  apply A.dirichlet_weighted_piece_cost hw W₁ V hW₁ hV CW CV hWC hVC
    (fun p => innerCoefficientLoss N 37 (index p)) (fun p => sqrt (radialE (index p))) base
    (fun p => (innerCoefficientLoss_pos N 37 (index p)).le)
    (fun p => sqrt_nonneg _) hbase
    (by simpa only [hlosscenter, hbasecenter, hcenter, one_mul, mul_one] using hsqrt)
    (by simpa only [hbasecenter, hcenter, div_one] using hsqrt)
    hlocalW hlocalV (mul_nonneg hK (rpow_nonneg (exp_pos _).le _))
  intro p
  simpa only [radialE, show (36 : ℝ) + 1 = 37 by norm_num] using
    inner_dirichlet_fixed_loss_cost hK (sqrt_nonneg (radialE (index p)))
      (norm_nonneg ((A.piece p).dirichlet hw)) le_rfl (hcost p) (hindex p)
      (by norm_num : (36 : ℝ) + 1 ≤ 37)

/-- With no output coefficient loss, all earlier cells are controlled
by the same largest transition coefficient. This applies to each sign. -/
theorem dirichlet_coarse_coefficient_bound (hw : ContDiff ℝ ∞ D.w)
    (W V : ℝ → ℝ) (hW : Measurable W) (hV : Measurable V) (CW CV : ℝ)
    (hWC : ∀ x, |W x| ≤ CW) (hVC : ∀ x, |V x| ≤ CV)
    (index : Fin (n + 1) → ℕ) (band : ℕ) (hindex : ∀ p, index p ≤ band)
    (base : Fin (n + 1) → ℝ) (hbase : ∀ p, 0 < base p) (hbasecenter : base central = 1)
    (hlocalW : ∀ p x, x ∈ sets p → |W x| ≤ sqrt (radialE (index p)) * base p)
    (hlocalV : ∀ p x, x ∈ sets p → |V x| ≤ sqrt (radialE (index p)) / base p)
    {K : ℝ} (hK : 0 ≤ K)
    (hcost : ∀ p, ‖(A.piece p).dirichlet hw‖ ≤ K * radialE (index p) ^ (36 : ℝ)) :
    ‖innerRadialSupportedMultiplier D G bordered W hW CW hWC ∘L A.dirichlet hw ∘L
      innerRadialSupportedMultiplier D G bordered V hV CV hVC‖ ≤ K * radialE band ^ (37 : ℝ) := by
  have hsqrt : 1 ≤ sqrt (radialE (index central)) := by
    simpa only [sqrt_one, radialE] using
      sqrt_le_sqrt (one_le_exp_iff.mpr (radialQ_nonneg (index central)))
  apply A.dirichlet_weighted_piece_cost hw W V hW hV CW CV hWC hVC
    (fun _ => 1) (fun p => sqrt (radialE (index p))) base (fun _ => zero_le_one)
    (fun p => sqrt_nonneg _) hbase
    (by simpa only [hbasecenter, one_mul, mul_one] using hsqrt)
    (by simpa only [hbasecenter, div_one] using hsqrt)
    (by simpa only [one_mul] using hlocalW) hlocalV
    (mul_nonneg hK (rpow_nonneg (exp_pos _).le _))
  intro p
  simpa only [radialE, one_mul, show (36 : ℝ) + 1 = 37 by norm_num] using
    inner_dirichlet_coarse_cost hK (sqrt_nonneg (radialE (index p)))
      (norm_nonneg ((A.piece p).dirichlet hw)) (by norm_num : (0 : ℝ) ≤ 36)
      le_rfl (hcost p) (hindex p)

end InnerRadialActualChain

end ContinuousFlexibility.Radial
