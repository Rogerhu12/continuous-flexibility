module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledFamily
public import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledCollars

/-!
# One sample envelope for the chosen positive transport

The same numerical choices that define the actual coordinate and height
family have uniform material costs. In particular, the inverse kernel may
use the displayed fiber widths and radial lower bound without choosing a
second family. Every coefficient and exponent precedes the component.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

structure N04PositiveGeometryControlMaterialBounds
    {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}
    (G : N04PositiveGeometryControlData W X n) (C : ℝ) : Prop where
  input : ∀ i, G.M i ≤ C * W.U.E0 (W.U.sample (X.cell i)) ^ C
  inverse : ∀ i, G.Mσ i ≤ C * W.U.E0 (W.U.sample (X.cell i)) ^ C
  buffer_gaps : ∀ i,
    (G.buffer.centerLeft i - n04PositiveLeft i)⁻¹ ≤
      C * W.U.E0 (W.U.sample (X.cell i)) ^ C ∧
    (G.buffer.normalizationLeft i - G.buffer.centerLeft i)⁻¹ ≤
      C * W.U.E0 (W.U.sample (X.cell i)) ^ C ∧
    (G.buffer.normalizationRight i - G.buffer.normalizationLeft i)⁻¹ ≤
      C * W.U.E0 (W.U.sample (X.cell i)) ^ C ∧
    (G.buffer.centerRight i - G.buffer.normalizationRight i)⁻¹ ≤
      C * W.U.E0 (W.U.sample (X.cell i)) ^ C ∧
    (n04PositiveRight i - G.buffer.centerRight i)⁻¹ ≤
      C * W.U.E0 (W.U.sample (X.cell i)) ^ C
  span_inverse : ∀ i, |(n04PositiveRight i - n04PositiveLeft i)⁻¹| ≤
    C * W.U.E0 (W.U.sample (X.cell i)) ^ C
  angular_width : ∀ i,
    |(endpointAngularWidth (n + 1) (n04PositiveLeft i) (n04PositiveRight i)
      (G.buffer.centerLeft i) (G.buffer.centerRight i) (G.M i)⁻¹ (G.M i))⁻¹| ≤
        C * W.U.E0 (W.U.sample (X.cell i)) ^ C
  fiber_width : ∀ i side,
    |(endpointFiberWidths n (n04PositiveLeft i) (n04PositiveRight i)
      (G.buffer.centerLeft i) (G.buffer.centerRight i) ((G.M i)⁻¹ / 2)
      (G.Mσ i) side)⁻¹| ≤ C * W.U.E0 (W.U.sample (X.cell i)) ^ C
  radial_lower_inverse : ∀ i,
    |(endpointFiberLower n (n04PositiveLeft i) (n04PositiveRight i)
      (G.buffer.centerLeft i) (G.buffer.centerRight i) ((G.M i)⁻¹ / 2) (G.Mσ i))⁻¹| ≤
        C * W.U.E0 (W.U.sample (X.cell i)) ^ C
  height_width : ∀ i, |(G.δ i)⁻¹| ≤ C * W.U.E0 (W.U.sample (X.cell i)) ^ C
  lower_positive : ∀ i, 0 < G.lower i
  lower_inverse : ∀ i, |(G.lower i)⁻¹| ≤ C * W.U.E0 (W.U.sample (X.cell i)) ^ C
  upper : ∀ i, G.upper i ≤ C * W.U.E0 (W.U.sample (X.cell i)) ^ C

private theorem controlled_sample_envelope_mono {E A B : ℝ}
    (hE : 1 ≤ E) (hAB : A ≤ B) (hB : 0 ≤ B) :
    A * E ^ A ≤ B * E ^ B :=
  mul_le_mul hAB (Real.rpow_le_rpow_of_exponent_le hE hAB)
    (Real.rpow_nonneg (zero_le_one.trans hE) _) hB

private theorem controlled_fiber_width_positive (n : ℕ) {l r c d κ M : ℝ}
    (hlc : l < c) (hdr : d < r) (hκ : 0 < κ) (hM : 0 ≤ M) (side : Bool) :
    0 < endpointFiberWidths n l r c d κ M side := by
  have hL : 0 ≤ max (M + ((n + 1 : ℕ) : ℝ) * M) 1 :=
    zero_le_one.trans (le_max_right _ _)
  cases side
  · exact (prescribedEndpointWidth_margins n (sub_pos.mpr hlc) zero_lt_one hκ hM
      hL (sub_pos.mpr hlc)).1
  · exact (prescribedEndpointWidth_margins n (sub_pos.mpr hdr) zero_lt_one hκ hM
      hL (sub_pos.mpr hdr)).1

/-- All numerical costs concern the same selected buffer and actual
transport formulas, on the same state neighborhood. -/
theorem n04PositiveGeometry_controlledFamily_material_bounds
    {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}
    (G : N04PositiveGeometryControlledFamily W X n) :
    ∃ C : ℝ, 1 ≤ C ∧
      N04PositiveGeometryControlMaterialBounds G.toN04PositiveGeometryControlData C := by
  let E := fun i => W.U.E0 (W.U.sample (X.cell i))
  have hE (i) : 1 ≤ E i := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  let C₀ : ℝ := 1 + 2 * G.Cinput + G.Cbuffer
  have hC₀ : 1 ≤ C₀ := by
    dsimp only [C₀]
    linarith only [G.input_constant, G.buffer_constant]
  have hinputC₀ : G.Cinput ≤ C₀ := by
    dsimp only [C₀]
    linarith only [G.input_constant, G.buffer_constant]
  have htwoInputC₀ : 2 * G.Cinput ≤ C₀ := by
    dsimp only [C₀]
    linarith only [G.buffer_constant]
  have hbufferC₀ : G.Cbuffer ≤ C₀ := by
    dsimp only [C₀]
    linarith only [G.input_constant]
  let U := fun i => C₀ * E i ^ C₀
  have hU (i) : 1 ≤ U i := one_le_mul_of_one_le_of_one_le hC₀
    (Real.one_le_rpow (hE i) (zero_le_one.trans hC₀))
  have htwoMU (i) : 2 * G.M i ≤ U i := calc
    _ ≤ 2 * (G.Cinput * E i ^ G.Cinput) :=
      mul_le_mul_of_nonneg_left (G.input_cost i) (by norm_num)
    _ = (2 * G.Cinput) * E i ^ G.Cinput := by ring
    _ ≤ U i := mul_le_mul htwoInputC₀
      (Real.rpow_le_rpow_of_exponent_le (hE i) hinputC₀)
      (Real.rpow_nonneg (zero_le_one.trans (hE i)) _) (zero_le_one.trans hC₀)
  have hMU (i) : G.M i ≤ U i := by
    linarith only [htwoMU i, G.input_one i]
  have hbufferU (i) : G.Cbuffer * E i ^ G.Cbuffer ≤ U i :=
    controlled_sample_envelope_mono (hE i) hbufferC₀ (zero_le_one.trans hC₀)
  have hleftU (i) : (G.buffer.centerLeft i - n04PositiveLeft i)⁻¹ ≤ U i :=
    (G.buffer_cost i).1.trans (hbufferU i)
  have hrightU (i) : (n04PositiveRight i - G.buffer.centerRight i)⁻¹ ≤ U i :=
    (G.buffer_cost i).2.2.2.2.trans (hbufferU i)
  have hordered (i) : n04PositiveLeft i < G.buffer.centerLeft i ∧
      G.buffer.centerLeft i < G.buffer.centerRight i ∧
        G.buffer.centerRight i < n04PositiveRight i :=
    ⟨(G.buffer.ordered i).1,
      (G.buffer.ordered i).2.1.trans
        ((G.buffer.ordered i).2.2.1.trans (G.buffer.ordered i).2.2.2.1),
      (G.buffer.ordered i).2.2.2.2⟩
  have hκφ (i) : 0 < (G.M i)⁻¹ := inv_pos.mpr (zero_lt_one.trans_le (G.input_one i))
  have hκφU (i) : ((G.M i)⁻¹)⁻¹ ≤ U i := by
    simpa only [inv_inv] using hMU i
  have hκXU (i) : ((G.M i)⁻¹ / 2)⁻¹ ≤ U i := by
    rw [inv_div, div_eq_mul_inv, inv_inv]
    exact htwoMU i
  obtain ⟨A, hA, degree, hcollars⟩ :=
    n04PositiveGeometry_exists_wholePositiveCollar_polynomial_envelope
      n G.degree G.Cσ G.Clog G.inverse_constant G.log_constant.le
  have hcollar (i) := hcollars
    (l := n04PositiveLeft i) (r := n04PositiveRight i)
    (c := G.buffer.centerLeft i) (d := G.buffer.centerRight i)
    (κφ := (G.M i)⁻¹) (κX := (G.M i)⁻¹ / 2)
    (M := G.M i) (Mσ := G.Mσ i) (H := G.M i) (U := U i)
    (hordered i).1 (hordered i).2.1 (hordered i).2.2
    (hκφ i) (half_pos (hκφ i)) (G.input_one i) (G.inverse_one i)
    (G.input_one i) (hU i) (hMU i) (hMU i) (G.inverse_cost i)
    (hκφU i) (hκXU i) (hleftU i) (hrightU i)
  obtain ⟨Bcollar, hBcollar, hpackCollar⟩ :=
    n04PositiveGeometry_polynomial_sample_pack A C₀ degree
  obtain ⟨Binverse, hBinverse, hpackInverse⟩ :=
    n04PositiveGeometry_polynomial_sample_pack G.Cσ G.Cinput G.degree
  obtain ⟨Bupper, hBupper, hpackUpper⟩ :=
    n04PositiveGeometry_polynomial_sample_pack (Real.exp 2) G.Cinput 2
  let C : ℝ := 1 + C₀ + Bcollar + Binverse + Bupper
  have hC : 1 ≤ C := by dsimp only [C]; linarith only [hC₀, hBcollar, hBinverse, hBupper]
  have hC₀C : C₀ ≤ C := by dsimp only [C]; linarith only [hBcollar, hBinverse, hBupper]
  have hBcollarC : Bcollar ≤ C := by dsimp only [C]; linarith only [hC₀, hBinverse, hBupper]
  have hBinverseC : Binverse ≤ C := by dsimp only [C]; linarith only [hC₀, hBcollar, hBupper]
  have hBupperC : Bupper ≤ C := by dsimp only [C]; linarith only [hC₀, hBcollar, hBinverse]
  have hUC (i) : U i ≤ C * E i ^ C :=
    controlled_sample_envelope_mono (hE i) hC₀C (zero_le_one.trans hC)
  have hcollarCost (i) : A * U i ^ degree ≤ C * E i ^ C :=
    (hpackCollar (E i) (hE i)).trans
      (controlled_sample_envelope_mono (hE i) hBcollarC (zero_le_one.trans hC))
  have hinverseCost (i) : G.Mσ i ≤ C * E i ^ C := calc
    _ ≤ G.Cσ * G.M i ^ G.degree := G.inverse_cost i
    _ ≤ G.Cσ * (G.Cinput * E i ^ G.Cinput) ^ G.degree :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (zero_le_one.trans (G.input_one i)) (G.input_cost i) _)
        (zero_le_one.trans G.inverse_constant)
    _ ≤ Binverse * E i ^ Binverse := hpackInverse (E i) (hE i)
    _ ≤ C * E i ^ C :=
      controlled_sample_envelope_mono (hE i) hBinverseC (zero_le_one.trans hC)
  have hlowerPos (i) : 0 < G.toN04PositiveGeometryControlData.lower i := (hcollar i).2.2.1
  have hlowerCost (i) : (G.toN04PositiveGeometryControlData.lower i)⁻¹ ≤ C * E i ^ C :=
    (hcollar i).2.2.2.1.trans (hcollarCost i)
  refine ⟨C, hC, {
    input := fun i => (hMU i).trans (hUC i)
    inverse := hinverseCost
    buffer_gaps := ?_
    span_inverse := ?_
    angular_width := ?_
    fiber_width := ?_
    radial_lower_inverse := ?_
    height_width := ?_
    lower_positive := hlowerPos
    lower_inverse := ?_
    upper := ?_ }⟩
  · intro i
    have h := (hbufferU i).trans (hUC i)
    exact ⟨(G.buffer_cost i).1.trans h, (G.buffer_cost i).2.1.trans h,
      (G.buffer_cost i).2.2.1.trans h, (G.buffer_cost i).2.2.2.1.trans h,
      (G.buffer_cost i).2.2.2.2.trans h⟩
  · intro i
    have hspan : 0 < n04PositiveRight i - n04PositiveLeft i :=
      sub_pos.mpr ((hordered i).1.trans ((hordered i).2.1.trans (hordered i).2.2))
    rw [abs_of_nonneg (inv_nonneg.mpr hspan.le)]
    exact (((inv_le_inv₀ hspan (sub_pos.mpr (hordered i).1)).mpr
      (sub_le_sub_right ((hordered i).2.1.trans (hordered i).2.2).le _)).trans
        (hleftU i)).trans (hUC i)
  · intro i
    have hpos := (endpointAngularWidth_margins (n + 1)
      (hordered i).1 (hordered i).2.1 (hordered i).2.2
      (hκφ i) (zero_le_one.trans (G.input_one i))).1
    rw [abs_of_nonneg (inv_nonneg.mpr hpos.le)]
    exact (hcollar i).1.trans (hcollarCost i)
  · intro i side
    have hpos := controlled_fiber_width_positive n (hordered i).1 (hordered i).2.2
      (half_pos (hκφ i)) (zero_le_one.trans (G.inverse_one i)) side
    rw [abs_of_nonneg (inv_nonneg.mpr hpos.le)]
    exact ((hcollar i).2.1 side).trans (hcollarCost i)
  · intro i
    have hB := G.radial_lower_pos i
    have hhalf : (G.M i)⁻¹ / 2 ≤ 1 := by
      linarith only [inv_le_one_of_one_le₀ (G.input_one i)]
    have hle : G.toN04PositiveGeometryControlData.lower i ≤
        endpointFiberLower n (n04PositiveLeft i) (n04PositiveRight i)
          (G.buffer.centerLeft i) (G.buffer.centerRight i) ((G.M i)⁻¹ / 2) (G.Mσ i) := by
      simpa only [N04PositiveGeometryControlData.lower, mul_one] using
        mul_le_mul_of_nonneg_left hhalf hB.le
    rw [abs_of_nonneg (inv_nonneg.mpr hB.le)]
    exact ((inv_le_inv₀ hB (hlowerPos i)).mpr hle).trans (hlowerCost i)
  · intro i
    rw [abs_of_nonneg (inv_nonneg.mpr (G.width_pos i).le)]
    calc
      _ = (oneSidedEndpointHeightWidth n
          (min ((n04PositiveRight i - n04PositiveLeft i) / 4)
            (min (G.buffer.centerLeft i - n04PositiveLeft i)
              (n04PositiveRight i - G.buffer.centerRight i)))
          (G.Clog * G.M i ^ (2 * n + 1)))⁻¹ := by
            rw [G.width_inverse i, oneSidedEndpointHeightWidth, inv_inv]
      _ ≤ A * U i ^ degree := (hcollar i).2.2.2.2
      _ ≤ C * E i ^ C := hcollarCost i
  · intro i
    rw [abs_of_nonneg (inv_nonneg.mpr (hlowerPos i).le)]
    exact hlowerCost i
  · intro i
    change Real.exp 2 * G.M i ^ 2 ≤ C * E i ^ C
    calc
      _ ≤ Real.exp 2 * (G.Cinput * E i ^ G.Cinput) ^ 2 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (zero_le_one.trans (G.input_one i)) (G.input_cost i) _)
          (Real.exp_pos _).le
      _ ≤ Bupper * E i ^ Bupper := hpackUpper (E i) (hE i)
      _ ≤ C * E i ^ C :=
        controlled_sample_envelope_mono (hE i) hBupperC (zero_le_one.trans hC)

end ContinuousFlexibility.Analysis
