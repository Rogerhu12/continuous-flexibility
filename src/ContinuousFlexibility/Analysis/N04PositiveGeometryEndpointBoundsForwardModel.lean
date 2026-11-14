module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsForwardBasis
public import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsOddPowerIdentity

/-!
# All positive-order coordinate words of the same root model

The radial coordinate is the radial variable times the two-thirds
power of the odd coefficient. A radial derivative therefore uses one
fewer odd-power trace. The other coordinate uses the four even traces,
and its pure angular words use the derivative of the original label.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

theorem n04PositiveGeometry_rootUnitTrace_even
    (G : ℝ × ℝ × ℝ → ℝ) (a : ℕ) (ha0 : 1 ≤ a) (ha : a ≤ 4) :
    n04PositiveGeometry_rootUnitTrace G ⟨a - 1, by omega⟩ =
      radialBoundaryJet (extendedRootEven G) 0 a := by
  have h (j : Fin 4) : n04PositiveGeometry_rootUnitTrace G ⟨j.val, by omega⟩ =
      radialBoundaryJet (extendedRootEven G) 0 (j.val + 1) := by
    fin_cases j <;> rfl
  simpa only [Nat.sub_add_cancel ha0] using h ⟨a - 1, by omega⟩

private theorem radialCoordinate_trace
    {χ : PolarPoint → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {θ : ℝ} (hpos : 0 < χ (0, θ)) (a : ℕ) :
    radialBoundaryJet (fun p => p.1 * ((3 / 2 : ℝ) * χ p) ^ (2 / 3 : ℝ)) 0 a θ =
      (a : ℝ) * (3 / 2 : ℝ) ^ (2 / 3 : ℝ) *
        radialBoundaryJet (fun p => χ p ^ (2 / 3 : ℝ)) 0 (a - 1) θ := by
  have hs : ContDiffAt ℝ ∞ (fun x : ℝ => χ (x, θ)) 0 :=
    hχ.contDiffAt.comp 0 (contDiffAt_id.prodMk contDiffAt_const)
  have hpow : ContDiffAt ℝ ∞
      (fun x : ℝ => ((3 / 2 : ℝ) * χ (x, θ)) ^ (2 / 3 : ℝ)) 0 :=
    (contDiffAt_const.mul hs).rpow_const_of_ne
      (mul_pos (by norm_num : (0 : ℝ) < 3 / 2) hpos).ne'
  have he : (fun x : ℝ => ((3 / 2 : ℝ) * χ (x, θ)) ^ (2 / 3 : ℝ)) =ᶠ[𝓝 0]
      (fun x => (3 / 2 : ℝ) ^ (2 / 3 : ℝ) * χ (x, θ) ^ (2 / 3 : ℝ)) := by
    filter_upwards [hs.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hpos)] with x hx
    exact Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3 / 2) (le_of_lt hx)
  change iteratedDeriv a
    (fun x : ℝ => x * (((3 / 2 : ℝ) * χ (x, θ)) ^ (2 / 3 : ℝ))) 0 = _
  rw [n06_iteratedDeriv_coord_mul_zero hpow, he.iteratedDeriv_eq (a - 1),
    iteratedDeriv_const_mul_field]
  exact (mul_assoc _ _ _).symm

/-- The complete finite coordinate word is expressed using the same
model's odd-power traces, even traces, and forward label slope. -/
theorem N04bRootCoordinateProperties.n04PositiveGeometry_chartBasis_eq
    {d c : PolarPoint → ℝ} {β : ℝ → ℝ} {Φ : ℝ → ℝ → ℝ}
    {R σ : ℝ} {G : ℝ × ℝ × ℝ → ℝ}
    (P : N04bRootCoordinateProperties d c β Φ R σ G)
    {n : ℕ} (hn : 1 ≤ n) (hn4 : n ≤ 4) (w : Fin n → Fin 2) (θ : ℝ) :
    iteratedFDeriv ℝ n (extendedRootEvenOddChart G) (0, θ)
        (fun i => cylinderBasisVector (w i)) =
      n04PositiveGeometry_forwardBasisValue ((3 / 2 : ℝ) ^ (2 / 3 : ℝ))
        (fun j => radialBoundaryJet
          (fun p => extendedRootOddCoefficient G p ^ (2 / 3 : ℝ)) 0 j)
        (n04PositiveGeometry_rootUnitTrace G) (deriv β)
        (n04PositiveGeometry_planeWordRadial w)
        (n04PositiveGeometry_planeWordAngular w) θ := by
  let Ω : Set PolarPoint := (extendedRootOddCoefficient G) ⁻¹' Ioi 0
  have hΩ : IsOpen Ω := isOpen_Ioi.preimage P.n06_extendedOdd_smooth.continuous
  have haxis (η : ℝ) : (0, η) ∈ Ω := by
    change 0 < extendedRootOddCoefficient G (0, η)
    rw [extendedRootOddCoefficient_of_nonneg G (le_refl (0 : ℝ))]
    exact P.odd_positive η
  have hrad : ContDiffOn ℝ ∞ (extendedRootRadialCoordinate G) Ω := by
    intro p hp
    have hpow : ContDiffAt ℝ ∞ (extendedRootRadialFactor G) p :=
      (contDiffAt_const.mul P.n06_extendedOdd_smooth.contDiffAt).rpow_const_of_ne
        (mul_pos (by norm_num : (0 : ℝ) < 3 / 2) hp).ne'
    exact (contDiffAt_fst.mul hpow).contDiffWithinAt
  have heven : ContDiffOn ℝ ∞ (extendedRootEven G) Ω :=
    P.n06_extendedEven_smooth.contDiffOn
  have ha : n04PositiveGeometry_planeWordRadial w ≤ 4 := by
    have hc := n04PositiveGeometry_planeWord_orders w
    omega
  change iteratedFDeriv ℝ n
    (fun p => (extendedRootRadialCoordinate G p, extendedRootEven G p)) (0, θ) _ = _
  rw [iteratedFDeriv_prodMk (hrad.contDiffAt (hΩ.mem_nhds (haxis θ)))
    P.n06_extendedEven_smooth.contDiffAt (by simp : (n : ℕ∞ω) ≤ ∞),
    ContinuousMultilinearMap.prod_apply,
    n04PositiveGeometry_axisBasis_eq_radialTrace hΩ hrad 0 haxis,
    n04PositiveGeometry_axisBasis_eq_radialTrace hΩ heven 0 haxis]
  by_cases ha0 : n04PositiveGeometry_planeWordRadial w = 0
  · have hb : 1 ≤ n04PositiveGeometry_planeWordAngular w := by
      have hc := n04PositiveGeometry_planeWord_orders w
      omega
    have he : radialBoundaryJet (extendedRootEven G) 0 0 = β := by
      funext η
      simpa only [radialBoundaryJet, iteratedDeriv_zero, extendedRootEvenOddChart] using
        congrArg Prod.snd (P.extended_chart_zero η)
    have hr : radialBoundaryJet (extendedRootRadialCoordinate G) 0 0 = fun _ => 0 := by
      funext η
      simp only [radialBoundaryJet, iteratedDeriv_zero, extendedRootRadialCoordinate, zero_mul]
    simp only [n04PositiveGeometry_forwardBasisValue, if_pos ha0, ha0, hr, he,
      iteratedDeriv_fun_const_zero]
    exact congrArg (fun t : ℝ => ((0 : ℝ), t)) (by
      rw [← iteratedDeriv_succ', Nat.sub_add_cancel hb])
  · have ha1 : 1 ≤ n04PositiveGeometry_planeWordRadial w := by omega
    have hr : radialBoundaryJet (extendedRootRadialCoordinate G) 0
        (n04PositiveGeometry_planeWordRadial w) = fun η =>
      ((n04PositiveGeometry_planeWordRadial w : ℕ) : ℝ) *
        (3 / 2 : ℝ) ^ (2 / 3 : ℝ) * radialBoundaryJet
          (fun p => extendedRootOddCoefficient G p ^ (2 / 3 : ℝ)) 0
            (n04PositiveGeometry_planeWordRadial w - 1) η := by
      funext η
      exact radialCoordinate_trace P.n06_extendedOdd_smooth (haxis η) _
    rw [n04PositiveGeometry_forwardBasisValue, if_neg ha0, dif_pos ha, hr]
    simp only [iteratedDeriv_const_mul_field]
    rw [n04PositiveGeometry_rootUnitTrace_even G _ ha1 ha]

end ContinuousFlexibility.Analysis
