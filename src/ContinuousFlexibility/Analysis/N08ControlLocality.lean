import ContinuousFlexibility.Analysis.N08ScalarFormula

/-!
# Component locality of the actual controlled coefficients

Disjointness of the negative components makes the profile on component
`m` depend only on its own control mean.  The primitive can change by a
constant when other controls change, but its first spatial derivatives
do not.  Consequently all three actual corrected coefficients have the
same component locality.  No reference-cell placement is used.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped Topology ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem n08_control_zero_on_other_component
    (hC : controlGeometryConditions D S C) {m n : ℕ} (hnm : n ≠ m)
    {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) : C.control n r = 0 := by
  obtain ⟨_, _, hdisjoint, _, _, hcontrol, _⟩ := hC
  by_contra hne
  exact Set.disjoint_left.mp (hdisjoint n m hnm) ((hcontrol n).2.2 hne) hr

theorem n08_stateControlSum_on_component
    (hC : controlGeometryConditions D S C) (x : AnnularState S) (m : ℕ)
    {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) :
    stateControlSum C x r = stateKappa S x m * C.control m r := by
  rw [stateControlSum, tsum_eq_single m]
  intro n hnm
  rw [n08_control_zero_on_other_component hC hnm hr, mul_zero]

theorem n08_stateProfile_on_component
    (hC : controlGeometryConditions D S C) (x : AnnularState S) (m : ℕ)
    {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) :
    stateProfile D S C x r = D.w r *
      Real.exp (x.2.1 * D.chi r + stateKappa S x m * C.control m r) := by
  change D.w r * Real.exp (x.2.1 * D.chi r + stateControlSum C x r) = _
  rw [n08_stateControlSum_on_component hC x m hr]

theorem n08_stateProfile_component_germ
    (hC : controlGeometryConditions D S C) {x y : AnnularState S} {m : ℕ}
    (hν : x.2.1 = y.2.1) (hκ : stateKappa S x m = stateKappa S y m)
    {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) :
    stateProfile D S C x =ᶠ[𝓝 r] stateProfile D S C y := by
  filter_upwards [isOpen_Ioo.mem_nhds hr] with t ht
  rw [n08_stateProfile_on_component hC x m ht,
    n08_stateProfile_on_component hC y m ht, hν, hκ]

theorem n08_heightRadial_stateHeight
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (x : AnnularState S) (q : ℝ) (p : PolarPoint) :
    heightRadial (stateHeight D S C (x, q)) p =
      stateProfile D S C x p.1 + q * heightRadial (stateU S x) p := by
  change heightRadial (heightFamily
    (Radial.radialHeightField (stateRadialHeight D S C x)) (stateU S x) q) p = _
  rw [heightRadial_heightFamily
    ((Radial.contDiff_radialHeightField (n08_stateRadialHeight_contDiff hT hS hN x)).differentiable
      (by simp)) ((n08_stateU_contDiff hT hS x).differentiable (by simp))]
  simp only [heightFamily,
    Radial.heightRadial_radialHeightField (n08_stateRadialHeight_hasDerivAt hT hS hN x),
    Radial.radialHeightField]

theorem n08_heightAngular_stateHeight
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (x : AnnularState S) (q : ℝ) (p : PolarPoint) :
    heightAngular (stateHeight D S C (x, q)) p = q * heightAngular (stateU S x) p := by
  change heightAngular (heightFamily
    (Radial.radialHeightField (stateRadialHeight D S C x)) (stateU S x) q) p = _
  rw [heightAngular_heightFamily
    ((Radial.contDiff_radialHeightField (n08_stateRadialHeight_contDiff hT hS hN x)).differentiable
      (by simp)) ((n08_stateU_contDiff hT hS x).differentiable (by simp))]
  simp only [heightFamily,
    Radial.heightAngular_radialHeightField (n08_stateRadialHeight_hasDerivAt hT hS hN x), zero_add]

/-- Equality of the actual first jets implies equality of the corrected
coefficients, including the residual correction in the angular coefficient. -/
theorem n08_polarCoefficients_eq_of_germs
    {w v : ℝ → ℝ} {h k : PolarPoint → ℝ} {p : PolarPoint}
    (hw : w =ᶠ[𝓝 p.1] v)
    (hk : heightRadial h =ᶠ[𝓝 p] heightRadial k)
    (hp : heightAngular h =ᶠ[𝓝 p] heightAngular k) :
    polarLinearA w h p = polarLinearA v k p ∧
      polarLinearB w h p = polarLinearB v k p ∧
      polarCorrectedC w h p = polarCorrectedC v k p := by
  have hE : profileEnergy w =ᶠ[𝓝 p] profileEnergy v := by
    have hwp := hw.comp_tendsto (continuous_fst.continuousAt : ContinuousAt Prod.fst p)
    filter_upwards [hwp] with x hx
    simp only [Function.comp_apply] at hx
    change radialEnergy (w x.1) = radialEnergy (v x.1)
    rw [hx]
  have hEr : radialPartial (profileEnergy w) p = radialPartial (profileEnergy v) p := by
    rw [radialPartial, radialPartial, hE.fderiv_eq (𝕜 := ℝ)]
  have hkr : radialPartial (heightRadial h) p = radialPartial (heightRadial k) p := by
    rw [radialPartial, radialPartial, hk.fderiv_eq (𝕜 := ℝ)]
  have hpr : radialPartial (heightAngular h) p = radialPartial (heightAngular k) p := by
    rw [radialPartial, radialPartial, hp.fderiv_eq (𝕜 := ℝ)]
  have hpt : angularPartial (heightAngular h) p = angularPartial (heightAngular k) p := by
    rw [angularPartial, angularPartial, hp.fderiv_eq (𝕜 := ℝ)]
  simp only [polarLinearA, polarLinearB, polarCorrectedC, polarScale, polarDiscriminant,
    hE.eq_of_nhds, hk.eq_of_nhds, hp.eq_of_nhds, hEr, hkr, hpr, hpt, and_self]

theorem n08_originalCoefficients_component_eq
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    {x y : AnnularState S} {m : ℕ} (hheight : x.1 = y.1)
    (hν : x.2.1 = y.2.1) (hκ : stateKappa S x m = stateKappa S y m)
    (q : ℝ) {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) (θ : ℝ) :
    (originalCoefficients D S C (x, q)).a (r, θ) =
        (originalCoefficients D S C (y, q)).a (r, θ) ∧
      (originalCoefficients D S C (x, q)).b (r, θ) =
        (originalCoefficients D S C (y, q)).b (r, θ) ∧
      (originalCoefficients D S C (x, q)).c (r, θ) =
        (originalCoefficients D S C (y, q)).c (r, θ) := by
  have hw := n08_stateProfile_component_germ hN.2.2.2.1 hν hκ hr
  have hU : stateU S x = stateU S y := congrArg (heightPairField S) hheight
  have hk : heightRadial (stateHeight D S C (x, q)) =ᶠ[𝓝 (r, θ)]
      heightRadial (stateHeight D S C (y, q)) := by
    have hwp := hw.comp_tendsto
      (continuous_fst.continuousAt : ContinuousAt Prod.fst (r, θ))
    filter_upwards [hwp] with p hp
    simp only [Function.comp_apply] at hp
    rw [n08_heightRadial_stateHeight hT hS hN, n08_heightRadial_stateHeight hT hS hN, hp, hU]
  have hp : heightAngular (stateHeight D S C (x, q)) =ᶠ[𝓝 (r, θ)]
      heightAngular (stateHeight D S C (y, q)) := by
    filter_upwards [] with p
    rw [n08_heightAngular_stateHeight hT hS hN, n08_heightAngular_stateHeight hT hS hN, hU]
  exact n08_polarCoefficients_eq_of_germs hw hk hp

theorem n08_minusCharacteristicSpeed_component_eq
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    {x y : AnnularState S} {m : ℕ} (hheight : x.1 = y.1)
    (hν : x.2.1 = y.2.1) (hκ : stateKappa S x m = stateKappa S y m)
    (q : ℝ) {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) (θ : ℝ) :
    minusCharacteristicSpeed (originalCoefficients D S C (x, q)) (r, θ) =
      minusCharacteristicSpeed (originalCoefficients D S C (y, q)) (r, θ) := by
  obtain ⟨ha, hb, hc⟩ := n08_originalCoefficients_component_eq hT hS hN hheight hν hκ q hr θ
  rw [minusCharacteristicSpeed, minusCharacteristicSpeed, ha, hb, hc]

end ContinuousFlexibility.Statements
