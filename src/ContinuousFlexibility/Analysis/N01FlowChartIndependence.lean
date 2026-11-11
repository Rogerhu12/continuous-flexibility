import ContinuousFlexibility.Analysis.CharacteristicODEUniqueness
import ContinuousFlexibility.Analysis.N01ReturnChartRegularity
import ContinuousFlexibility.Analysis.StateControlCofiniteClosure
import ContinuousFlexibility.Analysis.MaterialHeightRegularity

/-!
# Ordinary-flow independence of the left chart

Changing only the chart coordinate leaves the physical profile, height,
and characteristic coefficients unchanged.  The specified ordinary flow
is therefore unchanged by ODE uniqueness.  At a turning radius the
square root is separated into a continuous radial coefficient and a
smooth angular factor; no radial differentiability of that square root
is needed.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem stateProfile_eq_of_physical_coordinates
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {x y : AnnularState S} (hν : x.2.1 = y.2.1) (hκ : x.2.2.1 = y.2.2.1) :
    stateProfile D S C x = stateProfile D S C y := by
  funext r
  simp only [stateProfile, stateKappa, hν, hκ]

theorem originalCoefficients_eq_of_physical_coordinates
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {z z' : AnnularState S × ℝ}
    (hu : z.1.1 = z'.1.1) (hν : z.1.2.1 = z'.1.2.1)
    (hκ : z.1.2.2.1 = z'.1.2.2.1) (hq : z.2 = z'.2) :
    originalCoefficients D S C z = originalCoefficients D S C z' := by
  have hw := stateProfile_eq_of_physical_coordinates (D := D) (C := C) hν hκ
  have hh : stateHeight D S C z = stateHeight D S C z' := by
    funext p
    simp only [stateHeight, stateRadialHeight, hw, stateU, hu, hq]
  simp only [originalCoefficients, hw, hh]

/-- The actual radial primitive is smooth because its actual derivative
is the already established smooth controlled profile. -/
theorem N01Properties.stateRadialHeight_contDiff
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (x : AnnularState S) :
    ContDiff ℝ ∞ (stateRadialHeight D S C x) := by
  have hw := contDiff_stateProfile_of_n01 hS hT hN01 x
  have hderiv (r : ℝ) :
      HasDerivAt (stateRadialHeight D S C x) (stateProfile D S C x r) r :=
    intervalIntegral.integral_hasDerivAt_right (hw.continuous.intervalIntegrable D.b r)
      hw.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hw.continuous.continuousAt
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun r => (hderiv r).differentiableAt, ?_⟩
  have heq : deriv (stateRadialHeight D S C x) = stateProfile D S C x :=
    funext fun r => (hderiv r).deriv
  rw [heq]
  exact hw

theorem N01Properties.stateHeight_contDiff
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (z : AnnularState S × ℝ) : ContDiff ℝ ∞ (stateHeight D S C z) := by
  have hu : ContDiff ℝ ∞ (stateU S z.1) :=
    physical_height_with_cutoff_contDiff hT hS (by norm_num : (0 : ℝ) < 3 / 4)
      z.1.1.1 z.1.1.2
  have hrad := N01Properties.stateRadialHeight_contDiff hN01 hS hT z.1
  exact (hrad.comp contDiff_fst).add (contDiff_const.mul hu)

/-- The square root of the corrected determinant has all of its possible
turning-point singularity in a scalar function of the radius. -/
theorem minusCharacteristicSpeed_separated
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {z : AnnularState S × ℝ} {p : PolarPoint}
    (hw : DifferentiableAt ℝ (stateProfile D S C z.1) p.1) (hr : p.1 ≠ 0)
    (hD : 0 < polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p)
    (hQ : heightQ (profileEnergy (stateProfile D S C z.1) p)
      (heightRadial (stateHeight D S C z) p)
      (angularPartial (heightAngular (stateHeight D S C z)) p) ≠ 0) :
    minusCharacteristicSpeed (originalCoefficients D S C z) p =
      (originalCoefficients D S C z).b p / (originalCoefficients D S C z).a p -
        Real.sqrt (-(stateProfile D S C z.1 p.1 *
          deriv (stateProfile D S C z.1) p.1 / p.1)) *
        (1 / (polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p *
          (originalCoefficients D S C z).a p)) := by
  have hdet := polar_corrected_determinant (stateHeight D S C z) hw hr hD hQ
  have hdisc : (originalCoefficients D S C z).b p ^ 2 -
      (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p =
      -(stateProfile D S C z.1 p.1 * deriv (stateProfile D S C z.1) p.1 / p.1) /
        polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p ^ 2 := by
    change polarLinearB _ _ p ^ 2 - polarLinearA _ _ p * polarCorrectedC _ _ p = _
    rw [← neg_sub, hdet, neg_div]
  rw [minusCharacteristicSpeed, hdisc, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq hD.le]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The coefficient inequalities in N01 give the actual positive radial
coefficient and discriminant, and their smoothness on the annular interior. -/
theorem N01Properties.characteristic_coefficient_regular
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    0 < (originalCoefficients D S C z).a p ∧
    0 < polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p ∧
    (heightQ (profileEnergy (stateProfile D S C z.1) p)
      (heightRadial (stateHeight D S C z) p)
      (angularPartial (heightAngular (stateHeight D S C z)) p) ≠ 0) ∧
    ContDiffAt ℝ ∞ (originalCoefficients D S C z).a p ∧
    ContDiffAt ℝ ∞ (originalCoefficients D S C z).b p ∧
    ContDiffAt ℝ ∞ (polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z)) p := by
  have hw := contDiff_stateProfile_of_n01 hS hT hN01 z.1
  have hh := N01Properties.stateHeight_contDiff hN01 hS hT z
  obtain ⟨_, hgeom⟩ := hN01.1.1
  have hr : p.1 ≠ 0 := (hgeom.1.1.trans hp.1.1).ne'
  have hwpos : 0 < stateProfile D S C z.1 p.1 := by
    exact mul_pos (hgeom.1.2.2.2.2.1 p.1 hp.1) (Real.exp_pos _)
  rcases hN01 with ⟨_, _, _, _, _, _, _, _, _, hbound, _⟩
  rcases hbound z hz hsector p hp with ⟨_, _, hQlo, _, hDlo, _⟩
  have hQpos : 0 < heightQ (profileEnergy (stateProfile D S C z.1) p)
      (heightRadial (stateHeight D S C z) p)
      (angularPartial (heightAngular (stateHeight D S C z)) p) :=
    (div_pos_iff_of_pos_right hwpos).mp (lt_of_lt_of_le (by norm_num) hQlo)
  have hDpos : 0 < polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p :=
    lt_of_lt_of_le (by norm_num) hDlo
  have ha : 0 < (originalCoefficients D S C z).a p :=
    mul_pos hQpos (one_div_pos.mpr (mul_pos hDpos (Real.sqrt_pos.mpr hDpos)))
  obtain ⟨hA, hB, _⟩ := contDiffAt_heightLinearCoefficients hw.contDiffAt hh.contDiffAt
    hr hDpos hQpos.ne'
  have hk := contDiffAt_heightRadial hh.contDiffAt (m := ∞) (by simp)
  have ht := contDiffAt_heightAngular hh.contDiffAt (m := ∞) (by simp) hr
  have hE : ContDiffAt ℝ ∞ (profileEnergy (stateProfile D S C z.1)) p :=
    contDiffAt_const.add ((hw.contDiffAt.comp p contDiffAt_fst).pow 2)
  have hDreg : ContDiffAt ℝ ∞
      (polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z)) p :=
    (hE.mul (contDiffAt_const.sub (ht.pow 2))).sub (hk.pow 2)
  exact ⟨ha, hDpos, hQpos.ne', hA, hB, hDreg⟩

/-- Changing only the left-chart coordinate cannot change the actual
ordinary characteristic flow specified by N01. -/
theorem N01Properties.minusFlow_eq_of_physical_coordinates
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {z z' : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hz' : z' ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    (hu : z.1.1 = z'.1.1) (hν : z.1.2.1 = z'.1.2.1)
    (hκ : z.1.2.2.1 = z'.1.2.2.1) (hq : z.2 = z'.2)
    (m : ℕ) (θ : ℝ) :
    EqOn (fun r => C.minusFlow z m r θ) (fun r => C.minusFlow z' m r θ)
      (Icc (C.left m) (C.right m)) := by
  have hw := contDiff_stateProfile_of_n01 hS hT hN01 z.1
  have hphysical := originalCoefficients_eq_of_physical_coordinates
    (D := D) (C := C) hu hν hκ hq
  have hcontrol : controlGeometryConditions D S C := hN01.2.2.2.1
  have hflow : ordinaryFlowConditions D S C (stateNeighborhood S C base ε) :=
    hN01.2.2.2.2.2.2.1
  have hcore {p : PolarPoint} (hp : p.1 ∈ Icc (C.left m) (C.right m)) :
      p ∈ annularOpen D :=
    ⟨⟨(hcontrol.1 m).1.trans_le hp.1, hp.2.trans_lt (hcontrol.1 m).2.2⟩, mem_univ _⟩
  obtain ⟨_, hgeom⟩ := hN01.1.1
  have hr {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m)) : r ≠ 0 :=
    (hgeom.1.1.trans (hcore (p := (r, 0)) hr).1.1).ne'
  let A : PolarPoint → ℝ := fun p =>
    (originalCoefficients D S C z).b p / (originalCoefficients D S C z).a p
  let B : PolarPoint → ℝ := fun p =>
    1 / (polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p *
      (originalCoefficients D S C z).a p)
  let k : ℝ → ℝ := fun r =>
    Real.sqrt (-(stateProfile D S C z.1 r * deriv (stateProfile D S C z.1) r / r))
  have hk : ContinuousOn k (Icc (C.left m) (C.right m)) :=
    ((hw.continuous.continuousOn.mul (hw.continuous_deriv (by simp)).continuousOn).div
      continuousOn_id (fun r hr' => hr hr')).neg.sqrt
  have hA : ∀ p ∈ Icc (C.left m) (C.right m) ×ˢ (univ : Set ℝ),
      ContDiffAt ℝ ∞ A p := by
    intro p hp
    obtain ⟨ha, _, _, hA, hB, _⟩ :=
      N01Properties.characteristic_coefficient_regular hN01 hS hT hz hsector (hcore (p := p) hp.1)
    exact hB.div hA ha.ne'
  have hB : ∀ p ∈ Icc (C.left m) (C.right m) ×ˢ (univ : Set ℝ),
      ContDiffAt ℝ ∞ B p := by
    intro p hp
    obtain ⟨ha, hD, _, hA, _, hDreg⟩ :=
      N01Properties.characteristic_coefficient_regular hN01 hS hT hz hsector (hcore (p := p) hp.1)
    exact contDiffAt_const.div (hDreg.mul hA) (mul_ne_zero hD.ne' ha.ne')
  have hs (p : PolarPoint) (hp : p.1 ∈ Icc (C.left m) (C.right m)) :
      minusCharacteristicSpeed (originalCoefficients D S C z) p = A p - k p.1 * B p := by
    obtain ⟨_, hD, hQ, _⟩ :=
      N01Properties.characteristic_coefficient_regular hN01 hS hT hz hsector (hcore (p := p) hp)
    exact minusCharacteristicSpeed_separated (hw.differentiable (by simp) p.1) (hr hp) hD hQ
  apply Analysis.ode_solution_unique_of_separated_radial_speed
    (A := A) (B := B) (k := k) (hcontrol.1 m).2.1 hk hA hB
    (hflow z hz m θ).2.1 ?_ (hflow z' hz' m θ).2.1 ?_
    ((hflow z hz m θ).1.trans (hflow z' hz' m θ).1.symm)
  · intro r hr'
    simpa only [hs (r, C.minusFlow z m r θ) ⟨hr'.1.le, hr'.2.le⟩] using
      (hflow z hz m θ).2.2.1 r hr'
  · intro r hr'
    have hderiv := (hflow z' hz' m θ).2.2.1 r hr'
    rw [← hphysical] at hderiv
    simpa only [hs (r, C.minusFlow z' m r θ) ⟨hr'.1.le, hr'.2.le⟩] using
      hderiv

/-- The specified inverse return is likewise independent of the chart,
because N01 makes it the two-sided inverse of the same actual return. -/
theorem N01Properties.minusReturnInverse_eq_of_physical_coordinates
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {z z' : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hz' : z' ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (hsector' : stateSector S z'.1)
    (hu : z.1.1 = z'.1.1) (hν : z.1.2.1 = z'.1.2.1)
    (hκ : z.1.2.2.1 = z'.1.2.2.1) (hq : z.2 = z'.2) (m : ℕ) :
    C.minusReturnInverse z m = C.minusReturnInverse z' m := by
  have hfloweq := N01Properties.minusFlow_eq_of_physical_coordinates hN01 hS hT hz hz'
    hsector hu hν hκ hq m
  rcases hN01 with ⟨_, _, _, hcontrol, _, _, _, _, hInv, _⟩
  funext θ
  have hr : C.right m ∈ Icc (C.left m) (C.right m) :=
    ⟨(hcontrol.1 m).2.1.le, le_rfl⟩
  calc
    C.minusReturnInverse z m θ = C.minusReturnInverse z m
        (C.minusFlow z' m (C.right m) (C.minusReturnInverse z' m θ)) := by
      rw [(hInv z' hz' hsector' m θ).1]
    _ = C.minusReturnInverse z m
        (C.minusFlow z m (C.right m) (C.minusReturnInverse z' m θ)) := by
      rw [hfloweq (C.minusReturnInverse z' m θ) hr]
    _ = C.minusReturnInverse z' m θ :=
      (hInv z hz hsector m (C.minusReturnInverse z' m θ)).2.1

end ContinuousFlexibility.Statements
