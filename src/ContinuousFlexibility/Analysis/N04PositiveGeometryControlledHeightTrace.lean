import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledHeightProduct
import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledHeightFormula
import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledDiscSamplePrefix
import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsOddPowerIdentity
import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsCommonContext

/-!
# Actual radial traces of every power of the root height

One unit model is fixed at each state before the angle and the exponent.
Its genuine height agrees with the finite product of the odd power,
fixed reference radicand, and actual discriminant power. The original
atlas has these same radial jets by its common root context.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology BigOperators

def n04PositiveGeometry_rootHeightPowerDomain (G : ℝ × ℝ × ℝ → ℝ) (R : ℝ) :
    Set PolarPoint :=
  (Ioo (-R - R) (R + R) ×ˢ (univ : Set ℝ)) ∩
    {p | 0 < extendedRootOddCoefficient G p}

theorem n04PositiveGeometry_rootHeightPowerDomain_isOpen
    {G : ℝ × ℝ × ℝ → ℝ} (hχ : ContDiff ℝ ∞ (extendedRootOddCoefficient G)) (R : ℝ) :
    IsOpen (n04PositiveGeometry_rootHeightPowerDomain G R) :=
  (isOpen_Ioo.prod isOpen_univ).inter (isOpen_lt continuous_const hχ.continuous)

theorem n04PositiveGeometry_rootHeightPowerDomain_axis
    {G : ℝ × ℝ × ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (hχ : ∀ θ, 0 < extendedRootOddCoefficient G (0, θ)) (θ : ℝ) :
    (0, θ) ∈ n04PositiveGeometry_rootHeightPowerDomain G R :=
  ⟨⟨⟨by linarith only [hR], by linarith only [hR]⟩, mem_univ _⟩, hχ θ⟩

theorem n04PositiveGeometry_rootDividedHeight_rpow_contDiffOn
    {wref g w : ℝ → ℝ} {h : PolarPoint → ℝ} {r σ R : ℝ}
    {G : ℝ × ℝ × ℝ → ℝ}
    (hwref : ContDiff ℝ ∞ wref) (hg : ContDiff ℝ ∞ g)
    (hw : ContDiff ℝ ∞ w) (hh : ContDiff ℝ ∞ h)
    (hstrip : RootCoefficientStripConditions wref g w h r σ R)
    (hχ : ContDiff ℝ ∞ (extendedRootOddCoefficient G)) (γ : ℝ) :
    ContDiffOn ℝ ∞ (fun p => rootDividedHeight 1
      (rootCoefficientRadialFactor wref g w h r σ) G p ^ γ)
      (n04PositiveGeometry_rootHeightPowerDomain G R) := by
  intro p hp
  have hs := hstrip p hp.1
  have hV := contDiffAt_rootCoefficientRadialFactor hwref hg hw hh
    hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1
  have hVp : 0 < rootCoefficientRadialFactor wref g w h r σ p := by
    rw [rootCoefficientRadialFactor_eq hs.1 hs.2.1 hs.2.2.1
      hs.2.2.2.1 hs.2.2.2.2.1.ne']
    exact div_pos (rootProfileRadicand_pos hs.1 hs.2.1 hs.2.2.1)
      (pow_pos hs.2.2.2.1 2)
  have hheight := contDiffAt_rootDividedHeight zero_lt_one hV hχ.contDiffAt hVp hp.2
  exact (hheight.1.rpow_const_of_ne hheight.2.ne').contDiffWithinAt

private theorem discriminant_contDiffAt
    {w : ℝ → ℝ} {h : PolarPoint → ℝ} (hw : ContDiff ℝ ∞ w)
    (hh : ContDiff ℝ ∞ h) {p : PolarPoint} (hr : p.1 ≠ 0) :
    ContDiffAt ℝ ∞ (polarDiscriminant w h) p := by
  have hk := contDiffAt_heightRadial (x := p) hh.contDiffAt (m := ∞) (by simp)
  have ht := contDiffAt_heightAngular (x := p) hh.contDiffAt (m := ∞) (by simp) hr
  have hE : ContDiffAt ℝ ∞ (profileEnergy w) p :=
    contDiffAt_const.add ((hw.contDiffAt.comp p contDiffAt_fst).pow 2)
  exact (hE.mul (contDiffAt_const.sub (ht.pow 2))).sub (hk.pow 2)

/-- The exact finite radial product formula holds for the actual unit
height, on the positive germ supplied by its genuine root strip. -/
theorem n04PositiveGeometry_rootDividedHeight_rpow_radialTrace
    {wref g w : ℝ → ℝ} {h : PolarPoint → ℝ} {r σ R : ℝ}
    {G : ℝ × ℝ × ℝ → ℝ} {θ : ℝ}
    (hwref : ContDiff ℝ ∞ wref) (hg : ContDiff ℝ ∞ g)
    (hw : ContDiff ℝ ∞ w) (hh : ContDiff ℝ ∞ h) (hR : 0 < R)
    (hstrip : RootCoefficientStripConditions wref g w h r σ R)
    (hχ : ContDiff ℝ ∞ (extendedRootOddCoefficient G))
    (hχpos : 0 < extendedRootOddCoefficient G (0, θ)) (γ : ℝ) (n : ℕ) :
    radialBoundaryJet (fun p => rootDividedHeight 1
      (rootCoefficientRadialFactor wref g w h r σ) G p ^ γ) 0 n θ =
      n04PositiveGeometry_rootHeightProductTrace n
        (fun j => (3 / 2 : ℝ) ^ (γ / 6) * iteratedDeriv j
          (fun t => rootProfileRadicand wref g r σ t ^ (-γ / 4)) 0)
        (fun j => radialBoundaryJet (fun p => extendedRootOddCoefficient G p ^ (γ / 6))
          0 j θ)
        (fun j => radialBoundaryJet (fun p => polarDiscriminant w h
          (rootProfileShift r σ p) ^ (γ / 2)) 0 j θ) := by
  let A : ℝ → ℝ := fun t => rootProfileRadicand wref g r σ t ^ (-γ / 4)
  let O : PolarPoint → ℝ := fun p => extendedRootOddCoefficient G p ^ (γ / 6)
  let V : PolarPoint → ℝ := fun p => polarDiscriminant w h (rootProfileShift r σ p) ^ (γ / 2)
  let c : ℝ := (3 / 2 : ℝ) ^ (γ / 6)
  have hzero : ((0, θ) : PolarPoint) ∈ Ioo (-R - R) (R + R) ×ˢ (univ : Set ℝ) :=
    ⟨⟨by linarith only [hR], by linarith only [hR]⟩, mem_univ _⟩
  have hs := hstrip (0, θ) hzero
  have hA : ContDiffAt ℝ ∞ A 0 :=
    (contDiffAt_rootProfileRadicand hwref hg hs.1.ne').rpow_const_of_ne
      (rootProfileRadicand_pos hs.1 hs.2.1 hs.2.2.1).ne'
  have hO : ContDiffAt ℝ ∞ O (0, θ) := hχ.contDiffAt.rpow_const_of_ne hχpos.ne'
  have hshift : ContDiff ℝ ∞ (rootProfileShift r σ) :=
    (contDiff_const.add (contDiff_const.mul contDiff_fst)).prodMk contDiff_snd
  have hV : ContDiffAt ℝ ∞ V (0, θ) :=
    ((discriminant_contDiffAt hw hh hs.1.ne').comp (0, θ)
      hshift.contDiffAt).rpow_const_of_ne hs.2.2.2.1.ne'
  have hpair : Tendsto (fun x : ℝ => (x, θ)) (𝓝 0) (𝓝 (0, θ)) :=
    (continuous_id.prodMk continuous_const).continuousAt
  have hnear := hpair.eventually
    ((n04PositiveGeometry_rootHeightPowerDomain_isOpen hχ R).mem_nhds
      (show (0, θ) ∈ n04PositiveGeometry_rootHeightPowerDomain G R from ⟨hzero, hχpos⟩))
  have he : (fun x => rootDividedHeight 1
      (rootCoefficientRadialFactor wref g w h r σ) G (x, θ) ^ γ) =ᶠ[𝓝 0]
      (fun x => (c * A x) * (O (x, θ) * V (x, θ))) := by
    filter_upwards [hnear] with x hx
    have hd := hstrip (x, θ) hx.1
    rw [n04PositiveGeometry_rootDividedHeight_rpow_eq hd.1 hd.2.1 hd.2.2.1
      hd.2.2.2.1 hd.2.2.2.2.1.ne' hx.2 γ]
    dsimp only [c, A, O, V]
    ring
  have hca : ContDiffAt ℝ ∞ (fun x => c * A x) 0 := contDiffAt_const.mul hA
  have hp := n04PositiveGeometry_radialBoundaryJet_threeFactors hca hO hV n
  exact (he.iteratedDeriv_eq n).trans (by
    simpa only [radialBoundaryJet, n04PositiveGeometry_rootHeightProductTrace,
      iteratedDeriv_const_mul_field, A, c, O, V] using hp)

private theorem heightProductTrace_congr_odd {n : ℕ}
    (a f f' g : ℕ → ℝ) (he : ∀ j, j ≤ n → f j = f' j) :
    n04PositiveGeometry_rootHeightProductTrace n a f g =
      n04PositiveGeometry_rootHeightProductTrace n a f' g := by
  unfold n04PositiveGeometry_rootHeightProductTrace
  apply Finset.sum_congr rfl
  intro c _
  exact congrArg (fun t : ℝ =>
    ((n.choose c.1.val : ℝ) * ((n - c.1.val).choose c.2.val : ℝ) * a c.1.val) *
      (t * g (n - c.1.val - c.2.val))) (he c.2.val (by omega))

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

def n04PositiveGeometry_rootHeightPowerTrace
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (g : ℝ → ℝ) (m : ℕ) (side : Bool) (γ : ℝ) (n : ℕ)
    (y : (StateDirections S × ℝ) × ℝ) : ℝ :=
  n04PositiveGeometry_rootHeightProductTrace n
    (fun j => (3 / 2 : ℝ) ^ (γ / 6) * iteratedDeriv j
      (fun t => rootProfileRadicand D.w g (n01ComponentRoot C m side)
        (n01ComponentRootOrientation side) t ^ (-γ / 4)) 0)
    (fun j => n04PositiveGeometry_rootOddPowerTrace D S C g m side (γ / 6) j y)
    (fun j => n04PositiveGeometry_rootDiscPowerTrace D S C (γ / 2)
      (n01ComponentRoot C m side) (n01ComponentRootOrientation side) j y)

def n04PositiveGeometry_rootOddPowerTrace_joint
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hε : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hg0 : 0 < g 0)
    (m : ℕ) (side : Bool) (hr : n01ComponentRoot C m side ∈ radialCore D)
    (hroot : deriv D.w (n01ComponentRoot C m side) = 0)
    {R : ℝ} (hR : 0 < R)
    (hstrip : ∀ z ∈ sectorNeighborhood S base ε ε,
      RootCoefficientStripConditions D.w g
        (stateProfile D S C (liftSectorParameter S C z).1)
        (stateHeight D S C (liftSectorParameter S C z))
        (n01ComponentRoot C m side) (n01ComponentRootOrientation side) R)
    (γ : ℝ) (n : ℕ) (hn : n ≤ 3) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (n04PositiveGeometry_rootOddPowerTrace D S C g m side γ n) :=
  n04PositiveGeometry_rootPowerTrace_joint (sectorNeighborhood_isOpen S base ε ε)
    (fun j hj => n04PositiveGeometry_rootOddTrace_joint hT hS hN hε
      g hg hg0 m side hr hroot j (hj.trans hn)) γ
    (fun y hy => n04PositiveGeometry_rootOddTrace_zero_pos hT hS hN hflow
      g m side hR hy.1 (hstrip y.1 hy.1) y.2)

def n04PositiveGeometry_rootHeightPowerTrace_joint
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hε : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hg0 : 0 < g 0)
    (m : ℕ) (side : Bool) (hr : n01ComponentRoot C m side ∈ radialCore D)
    (hroot : deriv D.w (n01ComponentRoot C m side) = 0)
    {R : ℝ} (hR : 0 < R)
    (hstrip : ∀ z ∈ sectorNeighborhood S base ε ε,
      RootCoefficientStripConditions D.w g
        (stateProfile D S C (liftSectorParameter S C z).1)
        (stateHeight D S C (liftSectorParameter S C z))
        (n01ComponentRoot C m side) (n01ComponentRootOrientation side) R)
    (γ : ℝ) (n : ℕ) (hn : n ≤ 3) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (n04PositiveGeometry_rootHeightPowerTrace D S C g m side γ n) :=
  n04PositiveGeometry_rootHeightProductTrace_joint (sectorNeighborhood_isOpen S base ε ε) _
    (fun j hj => n04PositiveGeometry_rootOddPowerTrace_joint hT hS hN hε hflow
      g hg hg0 m side hr hroot hR hstrip (γ / 6) j (hj.trans hn))
    (fun j _ => n04PositiveGeometry_rootDiscPowerTrace_joint hT hS hN hε hr hroot
      (γ / 2) (n01ComponentRootOrientation side) j)

theorem n04PositiveGeometry_actual_unitHeightPowerTrace_eq
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (side : Bool) (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    {R : ℝ} (hR : 0 < R)
    (hstrip : RootCoefficientStripConditions D.w g
      (stateProfile D S C (liftSectorParameter S C z).1)
      (stateHeight D S C (liftSectorParameter S C z))
      (n01ComponentRoot C m side) (n01ComponentRootOrientation side) R)
    {δ : ℝ} (hδ : δ ≠ 0) (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ)
    (hΘ : N04FlowEquations (rootRescaledField
      (localizedRootDrift D S C (n01ComponentRoot C m side)
        (n01ComponentRootOrientation side) hR (liftSectorParameter S C z))
      (localizedRootSpeed D S C g (n01ComponentRoot C m side)
        (n01ComponentRootOrientation side) hR (liftSectorParameter S C z)) δ) Θ)
    (γ : ℝ) (n : ℕ) (hn : n ≤ 3) :
    radialBoundaryJet (fun p => rootDividedHeight 1
      (rootCoefficientRadialFactor D.w g
        (stateProfile D S C (liftSectorParameter S C z).1)
        (stateHeight D S C (liftSectorParameter S C z))
        (n01ComponentRoot C m side) (n01ComponentRootOrientation side))
      (rootInverseCoordinate (rootFlowParameterUnscale Θ δ)
        (n01RootLabel S C (liftSectorParameter S C z) m side)) p ^ γ) 0 n =
      fun θ => n04PositiveGeometry_rootHeightPowerTrace D S C g m side γ n (z, θ) := by
  classical
  have P := n04PositiveGeometry_actual_unitRootCoordinate_properties hT hS hN hflow
    (liftSectorParameter_mem_stateNeighborhood (C := C) hz le_rfl)
    (hN.2.2.1.liftSectorParameter_sector z) m side g hg hR hstrip hδ Θ hΘ
  funext θ
  have hpos : 0 < extendedRootOddCoefficient
      (rootInverseCoordinate (rootFlowParameterUnscale Θ δ)
        (n01RootLabel S C (liftSectorParameter S C z) m side)) (0, θ) := by
    rw [extendedRootOddCoefficient_of_nonneg _ (le_refl (0 : ℝ))]
    exact P.odd_positive θ
  have hmodel := n04PositiveGeometry_rootDividedHeight_rpow_radialTrace
    hN.1.1.choose_spec.1.2.2.1.1 hg
    (contDiff_stateProfile_of_n01 hS hT hN _)
    (contDiff_stateHeight_of_n01 hS hT hN _)
    hR hstrip P.n06_extendedOdd_smooth hpos γ n
  exact hmodel.trans (heightProductTrace_congr_odd _ _ _ _ (fun j hj =>
    congrFun (n04PositiveGeometry_actual_oddPowerTrace_eq hT hS hN hflow hz
      m side g hg hR hstrip hδ Θ hΘ (γ / 6) j (hj.trans hn)) θ))

end ContinuousFlexibility.Analysis
