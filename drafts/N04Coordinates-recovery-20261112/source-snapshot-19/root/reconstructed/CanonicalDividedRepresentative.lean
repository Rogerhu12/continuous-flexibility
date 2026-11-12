import ContinuousFlexibility.Analysis.CanonicalFieldJetReduction
import ContinuousFlexibility.Analysis.PhysicalTransmissionTrace

/-!
# Identifying a removable representative with the stored divided field

The actual PartB factorization forces the chosen atlas's divided field
to equal any representative with the same numerator and boundary cube.
On the open canonical piece this is equality of complete functions, so
all ordinary mixed derivatives agree. No new divided field is installed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

theorem canonicalDividedComponent_matches_cubicRepresentative
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (hm : K.positive m = true) (v : Fin 3)
    {q : PolarPoint → ℝ} (hq : ContDiff ℝ ∞ q)
    (hfactor : ∀ p ∈ canonicalOpen S K m,
      canonicalCoefficientNumerator S C K z m v p =
        ((p.1 - K.left m) * (K.right m - p.1)) ^ 3 * q p) :
    EqOn (canonicalCoefficientComponent v (K.dividedDifference z m)) q
        (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (canonicalCoefficientComponent v (K.dividedDifference z m))
        (canonicalOpen S K m) ∧
      ∀ a b : ℕ,
        EqOn (mixedDerivative a b (canonicalCoefficientComponent v (K.dividedDifference z m)))
          (mixedDerivative a b q) (canonicalOpen S K m) := by
  have he : EqOn (canonicalCoefficientComponent v (K.dividedDifference z m)) q
      (canonicalOpen S K m) := by
    intro p hp
    have hd := pow_ne_zero 3 (canonicalBoundaryProduct_pos hp).ne'
    exact mul_left_cancel₀ hd
      ((canonicalCoefficientNumerator_factorization hK hz hs m hm v hp).symm.trans
        (hfactor p hp))
  exact ⟨he, hq.contDiffOn.congr he,
    fun a b => mixedDerivative_eqOn_of_isOpen (isOpen_Ioo.prod isOpen_univ) he a b⟩

end ContinuousFlexibility.Analysis
