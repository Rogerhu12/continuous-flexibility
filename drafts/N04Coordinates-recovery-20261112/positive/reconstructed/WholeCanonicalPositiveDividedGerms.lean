import ContinuousFlexibility.Analysis.WholeCanonicalAtlasData
import ContinuousFlexibility.Analysis.CanonicalWholePositiveAmbientCubicDifference
import ContinuousFlexibility.Analysis.LocalMixedProductBounds

/-!
# The smooth cubic representative is the actual stored interior quotient

The selected atlas record is unchanged. Reference identity reduces its
reference positive coefficient to the actual physical coefficient. On
the open canonical piece, the nonzero cubic factor uniquely identifies
the stored divided difference with the proved smooth representative.
Its genuine germ transfers every ordinary mixed derivative there.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem n04WholeCanonicalAtlasData_positive_divided_germs
    {D : ReferenceData} {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
    (e : ℕ ≃ N04WholePieceIndex D)
    (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
    (F G : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
    (Q : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
    (N : Set ℝ) (z : AnnularState S × ℝ) (m : ℕ)
    (i : N04PositiveComponent D.a D.b (deriv D.w)) (hi : e m = .inr i)
    (hFref : F (C.referenceState, 0) i = id)
    (hGref : G (C.referenceState, 0) i = id)
    (hQref : Q (C.referenceState, 0) i = (fun _ => (1 : ℝ)))
    (divided : Fin 3 → PolarPoint → ℝ) (hdivided : ∀ v, ContDiff ℝ ∞ (divided v))
    (hfactor : ∀ v p,
      p ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i) ×ˢ (univ : Set ℝ) →
      wholePositivePrincipalDifference (L.coefficients z)
        (L.coefficients (C.referenceState, 0)) (G z i) (F z i) (Q z i) v p =
          ((p.1 - n04PositiveLeft i) * (n04PositiveRight i - p.1)) ^ 3 * divided v p)
    (v : Fin 3) {p : PolarPoint}
    (hp : p ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i) ×ˢ (univ : Set ℝ)) :
    let W := n04WholeCanonicalAtlasData C L K e cell F G Q N
    canonicalCoefficientComponent v (W.dividedDifference z m) =ᶠ[𝓝 p] divided v ∧
      ContDiffAt ℝ ∞ (canonicalCoefficientComponent v (W.dividedDifference z m)) p ∧
      ∀ a b : ℕ,
        mixedDerivative a b (canonicalCoefficientComponent v (W.dividedDifference z m)) p =
          mixedDerivative a b (divided v) p := by
  let W := n04WholeCanonicalAtlasData C L K e cell F G Q N
  obtain ⟨hleft, hright, _, _, _, _, _, _, _, _, hcurrent, _⟩ :=
    n04WholeCanonicalAtlasData_positive_fields C L K e cell F G Q N z m i hi
  change W.left m = n04PositiveLeft i at hleft
  change W.right m = n04PositiveRight i at hright
  change W.coefficients z m =
    wholePositiveCanonicalCoefficients (L.coefficients z) (G z i) (F z i) (Q z i) at hcurrent
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hreference, _⟩ :=
    n04WholeCanonicalAtlasData_positive_fields C L K e cell F G Q N
      (C.referenceState, 0) m i hi
  have href : W.coefficients (C.referenceState, 0) m = L.coefficients (C.referenceState, 0) :=
    hreference.trans
      (wholePositiveCanonicalFields_reference (L.coefficients (C.referenceState, 0))
        hGref hFref hQref).2.1
  have he : canonicalCoefficientComponent v (W.dividedDifference z m) =ᶠ[𝓝 p]
      divided v := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with q hq
    have hqW : q ∈ canonicalOpen S W m := by
      simpa only [canonicalOpen, hleft, hright] using hq
    have hs := n04WholeCanonicalAtlasData_factorization C L K e cell F G Q N z m q hqW
    have hstored : canonicalCoefficientComponent v (W.coefficients z m) q -
        canonicalCoefficientComponent v (W.coefficients (C.referenceState, 0) m) q =
        ((q.1 - W.left m) * (W.right m - q.1)) ^ 3 *
          canonicalCoefficientComponent v (W.dividedDifference z m) q := by
      unfold canonicalCoefficientComponent
      split_ifs
      · exact hs.1
      · exact hs.2.1
      · exact hs.2.2
    have hactual := hfactor v q hq
    have hden : ((q.1 - n04PositiveLeft i) * (n04PositiveRight i - q.1)) ^ 3 ≠ 0 :=
      pow_ne_zero 3 (mul_pos (sub_pos.mpr hq.1.1) (sub_pos.mpr hq.1.2)).ne'
    rw [hleft, hright, hcurrent, href] at hstored
    exact mul_left_cancel₀ hden (hstored.symm.trans hactual)
  exact ⟨he, (hdivided v).contDiffAt.congr_of_eventuallyEq he,
    fun a b => mixedDerivative_eq_of_germ he a b⟩

end ContinuousFlexibility.Analysis
