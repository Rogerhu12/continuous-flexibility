import ContinuousFlexibility.Analysis.N04NegativeInverseRawEnvelope
import ContinuousFlexibility.Analysis.N04NegativeInverseMixedPrefix

/-!
# A normalized inverse point and height with a common coefficient

The two actual directional towers are bounded before any concrete
realization gauge or physical grading is supplied. The finite majorants
share one coefficient and the original positive parameter height.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

theorem n04NegativeInverse_normalized_pair_bound
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
    {U : Set X} {V W Ω : Set PolarPoint}
    {F G : X × PolarPoint → PolarPoint} {f : X × PolarPoint → ℝ}
    (JF : SmoothDirections (U ×ˢ V) F) (KG : SmoothDirections (U ×ˢ W) G)
    (JH : SmoothDirections (U ×ˢ V) f)
    (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W) (hΩ : IsOpen Ω)
    (hmap : MapsTo G (U ×ˢ W) V)
    (hJac : ∀ p ∈ U ×ˢ W, planeJacobian (fun y => F (p.1, y)) (G p) ≠ 0)
    (hright : ∀ p ∈ U ×ˢ W, F (p.1, G p) = p.2)
    (A : PolarPoint →L[ℝ] PolarPoint) (c : PolarPoint)
    (hAmap : MapsTo (fun q => c + A q) Ω W)
    (QH : SmoothDirections (U ×ˢ W) (fun p => f (p.1, G p)))
    (JP : SmoothDirections (U ×ˢ Ω) (fun p => G (p.1, c + A p.2)))
    (Q : SmoothDirections (U ×ˢ Ω) (fun p => f (p.1, G (p.1, c + A p.2))))
    (low high : Seminorm ℝ X) (k s shift : ℕ) (hk : 0 < k) (hshift : 1 ≤ shift)
    {z : X} (hz : z ∈ U) {q : PolarPoint} (hq : q ∈ Ω)
    {C Z H L R : ℝ} (hC : 1 ≤ C) (hZ : 0 ≤ Z)
    (hH : 0 ≤ H) (hHL : H ≤ L) (hL : 1 ≤ L) (hR : 1 ≤ R)
    (hmajorant : n04NegativeInverse_prefixMajorant (2 * C * C) C L (k + s) *
      C ^ (k + s) ≤ Z)
    (hpartition : ∀ n : ℕ, n ≤ k + s →
      n04NegativeInverse_partitionMajorant C
        (n04NegativeInverse_prefixMajorant (2 * C * C) C L (k + s)) L n *
          C ^ (k + s) ≤ Z)
    (hdet : |planeJacobian (fun y => F (z, y)) (G (z, c + A q))|⁻¹ ≤ C)
    (hA : ‖A‖ ≤ C)
    (hforward : N04NegativeInverseJet.UnitPrefix JF (z, G (z, c + A q))
      low high (k + s) k shift C H R
        (R ^ (1 / (((k + s + shift * k : ℕ) : ℝ) + 1))))
    (hscalar : N04NegativeInverseJet.UnitPrefix JH (z, G (z, c + A q))
      low high (k + s) k shift C H R
        (R ^ (1 / (((k + s + shift * k : ℕ) : ℝ) + 1))))
    (n : ℕ) (w : StateAngleWord n) (hw : w.stateArity = k) (hs : w.angleArity ≤ s)
    (v : Fin n → X × PolarPoint)
    (hlow : ∀ i, low (v i).1 ≤ 1) (hhigh : ∀ i, high (v i).1 ≤ R)
    (hphysical : ∀ i, ‖(v i).2‖ ≤ 1)
    (hstate : ∀ i, w.isState i = false → (v i).1 = 0)
    (hspatial : ∀ i, w.isState i = true → (v i).2 = 0) :
    let scale := R ^ (((w.angleArity + (shift + 1) * k - 1 : ℕ) : ℝ) /
      (((s + (shift + 1) * k : ℕ) : ℝ) + 1))
    ‖JP.D n (z, q) v‖ ≤ Z * H * scale ∧
      ‖Q.D n (z, q) v‖ ≤ Z * H * scale := by
  let t : ℝ := R ^ (1 / (((k + s + shift * k : ℕ) : ℝ) + 1))
  let M : ℝ := n04NegativeInverse_prefixMajorant (2 * C * C) C L (k + s)
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have ht : 1 ≤ t := Real.one_le_rpow hR (by positivity)
  have hM : 1 ≤ M := n04NegativeInverse_prefixMajorant_one_le
    (mul_nonneg (mul_nonneg (by norm_num) hC0) hC0) hC0 (zero_le_one.trans hL) (k + s)
  have hn : 0 < n := by have hsum := w.arity_sum; omega
  have hnN : n ≤ k + s := by have hsum := w.arity_sum; omega
  have hβN : w.angleArity ≤ k + s := by omega
  have hpoint := N04NegativeInverseJet.normalized_inverse_prefix_norm_le JF KG
    hU hV hW hΩ hmap hJac hright A c hAmap JP low high (k + s) k shift hshift hz hq
    hC0 hC0 hC0 hH hHL hL (zero_le_one.trans hR) (zero_le_one.trans ht)
    hdet hA hforward n hn hnN w hw.le v hlow hhigh hphysical hstate hspatial
  have hheightRaw := N04NegativeInverseJet.normalized_scalar_prefix_norm_le JF KG JH
    hU hV hW hΩ hmap hJac hright A c hAmap QH Q low high (k + s) k shift hshift hz hq
    hC0 hC0 hC0 hH hHL hL (zero_le_one.trans hR) (zero_le_one.trans ht)
    hdet hA hforward hscalar n hn hnN w hw.le v hlow hhigh hphysical hstate hspatial
  have hpointC : M * C ^ w.angleArity ≤ Z :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hC hβN) (zero_le_one.trans hM)).trans
      hmajorant
  have hheightC : n04NegativeInverse_partitionMajorant C M L n * C ^ w.angleArity ≤ Z :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hC hβN)
      (n04NegativeInverse_partitionMajorant_nonneg hC0 (zero_le_one.trans hM)
        (zero_le_one.trans hL) n)).trans (hpartition n hnN)
  have hden : k + s + shift * k = s + (shift + 1) * k := by
    simp only [Nat.add_mul, Nat.one_mul]
    omega
  have hfinish (a : ℝ) (ha : a ≤ Z * parameterHeightWeight H w.stateArity *
      t ^ (w.angleArity + shift * w.stateArity - 1)) :
      a ≤ Z * H * R ^ (((w.angleArity + (shift + 1) * k - 1 : ℕ) : ℝ) /
        (((s + (shift + 1) * k : ℕ) : ℝ) + 1)) := by
    rw [hw, parameterHeightWeight, if_neg (Nat.ne_of_gt hk)] at ha
    have hd : w.angleArity + shift * k - 1 ≤ w.angleArity + (shift + 1) * k - 1 := by
      simp only [Nat.add_mul, Nat.one_mul]
      omega
    have hp (d : ℕ) : t ^ d =
        R ^ ((d : ℝ) / (((s + (shift + 1) * k : ℕ) : ℝ) + 1)) := by
      dsimp only [t]
      rw [n04NegativeInverse_commonScale_pow (zero_le_one.trans hR), hden]
    calc
      a ≤ Z * H * t ^ (w.angleArity + shift * k - 1) := ha
      _ ≤ Z * H * t ^ (w.angleArity + (shift + 1) * k - 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht hd) (mul_nonneg hZ hH)
      _ = _ := by rw [hp]
  constructor
  · apply hfinish
    exact hpoint.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpointC (parameterHeightWeight_nonneg hH _))
      (pow_nonneg (zero_le_one.trans ht) _))
  · apply hfinish
    exact hheightRaw.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hheightC (parameterHeightWeight_nonneg hH _))
      (pow_nonneg (zero_le_one.trans ht) _))

end ContinuousFlexibility.Analysis
