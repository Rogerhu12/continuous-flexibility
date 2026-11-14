module

public import ContinuousFlexibility.Radial.TailClampedResistance
public import ContinuousFlexibility.Radial.TailMassResistanceData
public import ContinuousFlexibility.Radial.TailEdgeFluxMatrix
public import ContinuousFlexibility.Radial.TailPhysicalGreenContinuity

/-!
# The actual potential on a compact deep-tail edge

The resistance chart is formed from the original density, extended constantly
outside the edge. Its diagonal Green integral is bounded by the two actual
mass-resistance products in the deep-tail hypotheses.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- The transformed potential, on the actual resistance interval. -/
def tailClampedEdgePotential {p : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hp : ContinuousOn p (Icc a b))
    (hpos : ∀ x ∈ Icc a b, 0 < p x) (Λ : ℝ) :
    TailEdgeContinuous
      (tailResistanceChart (tailClampedDensity p a b hab) a a)
      (tailResistanceChart (tailClampedDensity p a b hab) a b) :=
  ⟨fun s => Λ * tailResistanceDensity (tailClampedDensity p a b hab) a s,
    continuous_const.mul (tailClampedResistanceDensity_continuousOn hab hp hpos).domRestrict⟩

theorem tailClampedEdgePotential_apply {p : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hp : ContinuousOn p (Icc a b))
    (hpos : ∀ x ∈ Icc a b, 0 < p x) (Λ : ℝ)
    (s : Icc (tailResistanceChart (tailClampedDensity p a b hab) a a)
      (tailResistanceChart (tailClampedDensity p a b hab) a b)) :
    tailClampedEdgePotential hab hp hpos Λ s =
      Λ * tailResistanceDensity (tailClampedDensity p a b hab) a s := rfl

/-- The integral-operator contraction size in the fixed physical interval
is exactly the contraction size in the moving resistance interval. -/
theorem tailPhysicalGreenWeight_diagonal_eq {p : ℝ → ℝ} {a b Λ : ℝ}
    (hab : a < b) (hp : ContinuousOn p (Icc a b))
    (hpos : ∀ x ∈ Icc a b, 0 < p x) :
    (∫ t in a..b, tailPhysicalGreenWeight p a b hab.le Λ t t) =
      tailEdgeDiagonalSize
        ((tailResistanceChart_strictMono (tailClampedDensity_continuous hab.le hp)
          (tailClampedDensity_pos hab.le hpos) a) hab)
        (tailClampedEdgePotential hab.le hp hpos Λ) := by
  let P := tailClampedDensity p a b hab.le
  let S := tailResistanceChart P a
  let ρ := tailResistanceDensity P a
  let q := tailClampedEdgePotential hab.le hp hpos Λ
  have hS := tailResistanceChart_strictMono (tailClampedDensity_continuous hab.le hp)
    (tailClampedDensity_pos hab.le hpos) a
  have hS0 : S a = 0 := intervalIntegral.integral_same
  have hG : Continuous (fun s => tailEdgeGreen (S a) (S b) s s) := by
    simp only [tailEdgeGreen_self]
    exact ((continuous_id.sub continuous_const).mul
      (continuous_const.sub continuous_id)).div_const _
  symm
  change tailEdgeDiagonalSize (hS hab) q = _
  calc
    _ = Λ * ∫ s in S a..S b, ρ s * tailEdgeGreen (S a) (S b) s s := by
      rw [tailEdgeDiagonalSize, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le (hS hab).le]
      intro s hs
      dsimp only
      rw [IccExtend_of_mem (hS hab).le q hs]
      change tailEdgeGreen (S a) (S b) s s * (Λ * ρ s) = _
      ring
    _ = Λ * ∫ x in a..b, p x * tailEdgeGreen (S a) (S b) (S x) (S x) := by
      exact congrArg (fun z : ℝ => Λ * z)
        (tailClampedResistance_mass_change hab.le hp hpos hG
          ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩)
    _ = _ := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le hab.le]
      intro x hx
      dsimp only [tailPhysicalGreenWeight, tailPhysicalGreenKernel]
      rw [tailClampedDensity_eq_of_mem hab.le hx]
      change Λ * (p x * tailEdgeGreen (S a) (S b) (S x) (S x)) =
        tailEdgeGreen 0 (S b) (S x) (S x) * (Λ * p x)
      rw [hS0]
      ring

/-- The contraction size is controlled by the original, untransformed
mass and resistance integrals on the two parts of the edge. -/
theorem tailClampedEdge_diagonal_le {p : ℝ → ℝ} {a b c Λ : ℝ}
    (hab : a < b) (hc : c ∈ Icc a b) (hp : ContinuousOn p (Icc a b))
    (hpos : ∀ x ∈ Icc a b, 0 < p x) (hΛ : 0 ≤ Λ) :
    tailEdgeDiagonalSize
      ((tailResistanceChart_strictMono (tailClampedDensity_continuous hab.le hp)
        (tailClampedDensity_pos hab.le hpos) a) hab)
      (tailClampedEdgePotential hab.le hp hpos Λ) ≤
      Λ * ((∫ x in a..c, (p x)⁻¹) * (∫ x in a..c, p x) +
        (∫ x in c..b, (p x)⁻¹) * (∫ x in c..b, p x)) := by
  let P : ℝ → ℝ := tailClampedDensity p a b hab.le
  let S : ℝ → ℝ := tailResistanceChart P a
  let ρ : ℝ → ℝ := tailResistanceDensity P a
  let q := tailClampedEdgePotential hab.le hp hpos Λ
  have hS : StrictMono S := tailResistanceChart_strictMono
    (tailClampedDensity_continuous hab.le hp) (tailClampedDensity_pos hab.le hpos) a
  have hρ : ContinuousOn ρ (Icc (S a) (S b)) :=
    tailClampedResistanceDensity_continuousOn hab.le hp hpos
  have hρpos (s : ℝ) : 0 ≤ ρ s :=
    (tailClampedResistanceDensity_pos hab.le hpos s).le
  have hδ : tailEdgeDiagonalSize (hS hab) q =
      Λ * (∫ s in S a..S b, ρ s * tailEdgeGreen (S a) (S b) s s) := by
    rw [tailEdgeDiagonalSize, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le (hS hab).le]
    intro s hs
    dsimp only
    rw [IccExtend_of_mem (hS hab).le q hs]
    dsimp only [q]
    rw [tailClampedEdgePotential_apply]
    change tailEdgeGreen (S a) (S b) s s * (Λ * ρ s) =
      Λ * (ρ s * tailEdgeGreen (S a) (S b) s s)
    ring
  have hmass (l r : ℝ) (hl : l ∈ Icc a b) (hr : r ∈ Icc a b) :
      (∫ s in S l..S r, ρ s) = ∫ x in l..r, p x := by
    simpa only [mul_one] using
      (tailClampedResistance_mass_change (V := fun _ => (1 : ℝ)) hab.le hp hpos
        continuous_const hl hr)
  have hres (l r : ℝ) (hl : l ∈ Icc a b) (hr : r ∈ Icc a b) :
      S r - S l = ∫ x in l..r, (p x)⁻¹ :=
    tailClampedResistanceChart_sub hab.le hp hpos hl hr
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hb : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  change tailEdgeDiagonalSize (hS hab) q ≤ _
  rw [hδ]
  calc
    _ ≤ Λ * ((S c - S a) * (∫ s in S a..S c, ρ s) +
        (S b - S c) * (∫ s in S c..S b, ρ s)) :=
      tailEdge_green_diagonal_le_mass_resistance (hS hab)
        (hS.monotone hc.1) (hS.monotone hc.2) hΛ hρ (fun s _ => hρpos s)
    _ = _ := by rw [hres a c ha hc, hres c b hc hb, hmass a c ha hc, hmass c b hc hb]

/-- Every genuine deep-tail edge has contraction size at most its stated
smallness constant, without a coordinate or density approximation. -/
theorem deepTailEdge_diagonal_small {T : DeepTailData} (hT : DeepTailHypotheses T)
    (n : ℕ) :
    let a := T.node n
    let b := T.node (n + 1)
    let hab := (deepTail_node_strictMono hT (Nat.lt_succ_self n))
    let hsub := deepTail_Icc_subset hT (deepTail_entrance_le_node hT n)
      (deepTail_node_lt_endpoint hT (n + 1))
    let hp := (deepTail_contDiffOn hT).continuousOn.mono hsub
    let hpos := fun x hx => deepTail_pos hT x (hsub hx)
    tailEdgeDiagonalSize
      ((tailResistanceChart_strictMono (tailClampedDensity_continuous hab.le hp)
        (tailClampedDensity_pos hab.le hpos) a) hab)
      (tailClampedEdgePotential hab.le hp hpos T.Λ) ≤ T.η := by
  dsimp only
  have hab := deepTail_node_strictMono hT (Nat.lt_succ_self n)
  have hsub := deepTail_Icc_subset hT (deepTail_entrance_le_node hT n)
    (deepTail_node_lt_endpoint hT (n + 1))
  have hp := (deepTail_contDiffOn hT).continuousOn.mono hsub
  have hpos := fun x hx => deepTail_pos hT x (hsub hx)
  have h := tailClampedEdge_diagonal_le (c := T.massEnd n) hab
    ⟨(deepTail_node_lt_massEnd hT n).le, (deepTail_massEnd_lt_succ_node hT n).le⟩
    hp hpos hT.2.2.1.le
  apply h.trans
  have hsmall := (hT.2.2.2.2.2.2.2.2.2.2 n).2.2.1
  change T.Λ * (tailInnerResistance T n * tailMass T n +
    tailResistance T n * tailGapMass T n) ≤ T.η
  calc
    _ = T.Λ * tailMass T n * tailInnerResistance T n +
        T.Λ * tailGapMass T n * tailResistance T n := by ring
    _ ≤ _ := hsmall

end ContinuousFlexibility.Radial
