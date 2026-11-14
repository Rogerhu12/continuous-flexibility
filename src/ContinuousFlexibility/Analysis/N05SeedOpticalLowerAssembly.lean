module

public import ContinuousFlexibility.Analysis.N05SeedOpticalLowerTail
public import ContinuousFlexibility.Analysis.N05SeedOpticalLowerFiniteHead

/-!
# Optical lower bounds on every actual negative seed component

The finite central and small-index components use their genuine simple
zeros. Every remaining component uses the derived Morse estimate and the
same physical carrier index. No optical lower certificate is an input.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial.SeedReferenceConstruction

open Set Real
open ContinuousFlexibility.Statements

variable {q : ℝ} (P : SeedReferenceConstruction q)

def n05FiniteComponentPairs : Finset (ℝ × ℝ) := by
  classical
  exact insert (centralRadius (-sqrt centralOscillatorA), centralRadius (sqrt centralOscillatorA))
    (((Finset.univ : Finset Bool).product (Finset.range 100)).image fun z =>
      (P.n05TailScale z.1 * P.n05ModelLeft z.1 z.2,
        P.n05TailScale z.1 * P.n05ModelRight z.1 z.2))

theorem n05_central_mem_finite_pairs :
    (centralRadius (-sqrt centralOscillatorA), centralRadius (sqrt centralOscillatorA)) ∈
      P.n05FiniteComponentPairs := by
  classical
  exact Finset.mem_insert_self _ _

theorem n05_small_mem_finite_pairs (side : Bool) {n : ℕ} (hn : n < 100) :
    (P.n05TailScale side * P.n05ModelLeft side n,
      P.n05TailScale side * P.n05ModelRight side n) ∈ P.n05FiniteComponentPairs := by
  classical
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨(side, n),
    Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_range.mpr hn⟩, rfl⟩

/-- Only genuine negative components among the finite list are retained;
the list need not assume that every discarded model interval survived. -/
theorem n05_finite_optical_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ l h : ℝ,
      NegativeRadialComponent P.reference l h → (l, h) ∈ P.n05FiniteComponentPairs →
      ∀ r ∈ Icc l h,
        c * min (r - l) (h - r) ≤ -deriv P.reference.w r / (r * P.reference.w r) := by
  classical
  let pairs := P.n05FiniteComponentPairs.filter
    (fun z => NegativeRadialComponent P.reference z.1 z.2)
  have hcomponents (z : ℝ × ℝ) (hz : z ∈ pairs) :
      NegativeRadialComponent P.reference z.1 z.2 := (Finset.mem_filter.mp hz).2
  obtain ⟨c, hc, hbound⟩ := n05_seed_finite_negativeRadialComponents_optical_lower_bound
    P.accumulating.choose_spec.1 Prod.fst Prod.snd pairs hcomponents
  refine ⟨c, hc, fun l h hcomponent hp r hr => ?_⟩
  exact hbound (l, h) (Finset.mem_filter.mpr ⟨hp, hcomponent⟩) r hr

/-- Every actual cell meeting the interior controls the entire negative
component. This pointwise form also survives grouping cells of the same
index. The coefficient is chosen before the component and the cell. -/
theorem n05_actual_cell_optical_lower (hq : 0 < q) :
    ∃ B : ℝ, 0 < B ∧ ∀ (l h : ℝ) (j : ℕ),
      NegativeRadialComponent P.reference l h → (Ioo l h ∩ P.reference.cells j).Nonempty →
      ∀ r ∈ Icc l h,
        (B * radialE (P.reference.cellIndex j) ^ (12 : ℝ))⁻¹ *
            min (r - l) (h - r) ≤ -deriv P.reference.w r / (r * P.reference.w r) := by
  obtain ⟨Bt, hBt, htail⟩ := P.n05_tail_optical_lower
  obtain ⟨c, hc, hhead⟩ := P.n05_finite_optical_lower
  let B : ℝ := max Bt c⁻¹
  have hB : 0 < B := hBt.trans_le (le_max_left _ _)
  have hBtB : Bt ≤ B := le_max_left _ _
  have hciB : c⁻¹ ≤ B := le_max_right _ _
  refine ⟨B, hB, fun l h j hcomponent hmeeting r hr => ?_⟩
  have hE : 1 ≤ radialE (P.reference.cellIndex j) :=
    one_le_exp_iff.mpr ((sq_nonneg (P.reference.cellIndex j : ℝ)).trans
      (radial_nat_sq_le_Q _))
  have hEp : 0 < radialE (P.reference.cellIndex j) := exp_pos _
  have hEpow : 1 ≤ radialE (P.reference.cellIndex j) ^ (12 : ℝ) :=
    one_le_rpow hE (by norm_num)
  have hδ : 0 ≤ min (r - l) (h - r) :=
    le_min (sub_nonneg.mpr hr.1) (sub_nonneg.mpr hr.2)
  have hfinite (hp : (l, h) ∈ P.n05FiniteComponentPairs) :
      (B * radialE (P.reference.cellIndex j) ^ (12 : ℝ))⁻¹ *
          min (r - l) (h - r) ≤ -deriv P.reference.w r / (r * P.reference.w r) := by
    have hfactor : c⁻¹ ≤ B * radialE (P.reference.cellIndex j) ^ (12 : ℝ) := by
      calc
        c⁻¹ ≤ B := hciB
        _ = B * 1 := (mul_one _).symm
        _ ≤ B * radialE (P.reference.cellIndex j) ^ (12 : ℝ) :=
          mul_le_mul_of_nonneg_left hEpow hB.le
    have hInv := inv_anti₀ (inv_pos.mpr hc) hfactor
    rw [inv_inv] at hInv
    exact (mul_le_mul_of_nonneg_right hInv hδ).trans (hhead l h hcomponent hp r hr)
  rcases P.n05_component_cases hq hcomponent with hcentral | hmodel
  · apply hfinite
    rw [hcentral.1, hcentral.2]
    exact P.n05_central_mem_finite_pairs
  · obtain ⟨side, n, hn, hl, hh, hclosed⟩ := hmodel
    by_cases h100 : 100 ≤ n
    · have hmeeting' :
          (Ioo (P.n05TailScale side * P.n05ModelLeft side n)
            (P.n05TailScale side * P.n05ModelRight side n) ∩ P.reference.cells j).Nonempty := by
        simpa only [hl, hh] using hmeeting
      have hr' : r ∈ Icc (P.n05TailScale side * P.n05ModelLeft side n)
          (P.n05TailScale side * P.n05ModelRight side n) := by
        simpa only [hl, hh] using hr
      have hbound := htail side n j hn h100 hclosed hmeeting' r hr'
      have hInv := inv_anti₀ (mul_pos hBt (rpow_pos_of_pos hEp _))
        (mul_le_mul_of_nonneg_right hBtB (rpow_nonneg hEp.le (12 : ℝ)))
      apply (mul_le_mul_of_nonneg_right hInv hδ).trans
      simpa only [hl, hh] using hbound
    · apply hfinite
      rw [hl, hh]
      exact P.n05_small_mem_finite_pairs side (lt_of_not_ge h100)

/-- Whole-component carriers are a special case of the pointwise cell
theorem; the same constant is retained. -/
theorem n05_actual_carrier_optical_lower (hq : 0 < q) :
    ∃ B : ℝ, 0 < B ∧ ∀ (l h : ℝ) (j : ℕ),
      NegativeRadialComponent P.reference l h → Ioo l h ⊆ P.reference.cells j →
      ∀ r ∈ Icc l h,
        (B * radialE (P.reference.cellIndex j) ^ (12 : ℝ))⁻¹ *
            min (r - l) (h - r) ≤ -deriv P.reference.w r / (r * P.reference.w r) := by
  obtain ⟨B, hB, hbound⟩ := P.n05_actual_cell_optical_lower hq
  refine ⟨B, hB, fun l h j hcomponent hcarrier => ?_⟩
  have hmid : (l + h) / 2 ∈ Ioo l h := by
    constructor <;> linarith only [hcomponent.2.1]
  exact hbound l h j hcomponent ⟨(l + h) / 2, hmid, hcarrier hmid⟩

end ContinuousFlexibility.Radial.SeedReferenceConstruction
