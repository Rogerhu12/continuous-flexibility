import ContinuousFlexibility.Analysis.N01FlowChartIndependence

/-!
# Locality of the actual ordinary return

The characteristic ODE only sees the height on its own open radial
component.  Equality near each spatial point is propagated through the
actual Fréchet derivatives and then through ODE uniqueness.  In
particular a smooth radial cutoff which is one on that component does
not change its actual return, provided the resulting state remains in
the N01 neighborhood.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility

theorem radialPartial_eventuallyEq
    {f g : PolarPoint → ℝ} {p : PolarPoint} (h : f =ᶠ[𝓝 p] g) :
    radialPartial f =ᶠ[𝓝 p] radialPartial g := by
  exact (h.fderiv (𝕜 := ℝ)).mono fun q hq =>
    congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (1, 0)) hq

theorem angularPartial_eventuallyEq
    {f g : PolarPoint → ℝ} {p : PolarPoint} (h : f =ᶠ[𝓝 p] g) :
    angularPartial f =ᶠ[𝓝 p] angularPartial g := by
  exact (h.fderiv (𝕜 := ℝ)).mono fun q hq =>
    congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (0, 1)) hq

/-- All three corrected coefficients depend only on the actual local
profile and height germs.  No smoothness or nonvanishing premise is
needed for this locality statement about total derivatives. -/
theorem polar_coefficients_eq_of_eventuallyEq
    {w v : ℝ → ℝ} {f g : PolarPoint → ℝ} {p : PolarPoint}
    (hw : w =ᶠ[𝓝 p.1] v) (hf : f =ᶠ[𝓝 p] g) :
    polarLinearA w f p = polarLinearA v g p ∧
      polarLinearB w f p = polarLinearB v g p ∧
      polarCorrectedC w f p = polarCorrectedC v g p := by
  have hE : profileEnergy w =ᶠ[𝓝 p] profileEnergy v := by
    filter_upwards [hw.comp_tendsto continuous_fst.continuousAt] with q hq
    have hq' : w q.1 = v q.1 := by simpa only [Function.comp_apply] using hq
    exact congrArg radialEnergy hq'
  have hk : heightRadial f =ᶠ[𝓝 p] heightRadial g :=
    radialPartial_eventuallyEq hf
  have ht : heightAngular f =ᶠ[𝓝 p] heightAngular g := by
    filter_upwards [angularPartial_eventuallyEq hf] with q hq
    simp only [heightAngular, hq]
  have hEr := (radialPartial_eventuallyEq hE).eq_of_nhds
  have hkr := (radialPartial_eventuallyEq hk).eq_of_nhds
  have htr := (radialPartial_eventuallyEq ht).eq_of_nhds
  have htt := (angularPartial_eventuallyEq ht).eq_of_nhds
  have hE0 := hE.eq_of_nhds
  have hk0 := hk.eq_of_nhds
  have ht0 := ht.eq_of_nhds
  simp only [polarLinearA, polarLinearB, polarCorrectedC, polarScale,
    polarDiscriminant, hE0, hk0, ht0, hEr, hkr, htr, htt, and_self]

end ContinuousFlexibility

namespace ContinuousFlexibility.Statements

/-- Actual ODE uniqueness on one component needs equality of its speed
only in the open component; endpoint equality follows by continuity. -/
theorem N01Properties.minusFlow_eq_of_characteristic_speed
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {z z' : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hz' : z' ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    (m : ℕ) (θ : ℝ)
    (hspeed : ∀ r ∈ Ioo (C.left m) (C.right m), ∀ t : ℝ,
      minusCharacteristicSpeed (originalCoefficients D S C z) (r, t) =
        minusCharacteristicSpeed (originalCoefficients D S C z') (r, t)) :
    EqOn (fun r => C.minusFlow z m r θ) (fun r => C.minusFlow z' m r θ)
      (Icc (C.left m) (C.right m)) := by
  have hw := contDiff_stateProfile_of_n01 hS hT hN01 z.1
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
    rw [← hspeed r hr' (C.minusFlow z' m r θ)] at hderiv
    simpa only [hs (r, C.minusFlow z' m r θ) ⟨hr'.1.le, hr'.2.le⟩] using
      hderiv


/-- Physical height changes away from one component do not alter its
actual coefficients inside that component. -/
theorem originalCoefficients_eq_of_height_locality
    {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {z z' : AnnularState S × ℝ}
    {l r : ℝ}
    (hν : z.1.2.1 = z'.1.2.1) (hκ : z.1.2.2.1 = z'.1.2.2.1)
    (hq : z.2 = z'.2)
    (hu : ∀ t ∈ Ioo l r, ∀ θ, stateU S z.1 (t, θ) = stateU S z'.1 (t, θ))
    {p : PolarPoint} (hp : p.1 ∈ Ioo l r) :
    (originalCoefficients D S C z).a p = (originalCoefficients D S C z').a p ∧
      (originalCoefficients D S C z).b p = (originalCoefficients D S C z').b p ∧
      (originalCoefficients D S C z).c p = (originalCoefficients D S C z').c p := by
  have hw := stateProfile_eq_of_physical_coordinates (D := D) (C := C) hν hκ
  have hh : stateHeight D S C z =ᶠ[𝓝 p] stateHeight D S C z' := by
    filter_upwards [(continuous_fst.tendsto p) (isOpen_Ioo.mem_nhds hp)] with q hq'
    simp only [stateHeight, stateRadialHeight, hw, hq, hu q.1 hq' q.2]
  exact polar_coefficients_eq_of_eventuallyEq
    (Filter.Eventually.of_forall fun t => congrFun hw t) hh

theorem N01Properties.minusFlow_eq_of_height_locality
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {z z' : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hz' : z' ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    (hν : z.1.2.1 = z'.1.2.1) (hκ : z.1.2.2.1 = z'.1.2.2.1)
    (hq : z.2 = z'.2) (m : ℕ)
    (hu : ∀ r ∈ Ioo (C.left m) (C.right m), ∀ θ,
      stateU S z.1 (r, θ) = stateU S z'.1 (r, θ)) (θ : ℝ) :
    EqOn (fun r => C.minusFlow z m r θ) (fun r => C.minusFlow z' m r θ)
      (Icc (C.left m) (C.right m)) := by
  apply N01Properties.minusFlow_eq_of_characteristic_speed hN01 hS hT hz hz'
    hsector m θ
  intro r hr t
  obtain ⟨ha, hb, hc⟩ := originalCoefficients_eq_of_height_locality
    (D := D) (C := C) hν hκ hq hu (p := (r, t)) hr
  simp only [minusCharacteristicSpeed, ha, hb, hc]

/-- The inverse return inherits the same genuine physical locality. -/
theorem N01Properties.minusReturnInverse_eq_of_height_locality
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {z z' : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hz' : z' ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (hsector' : stateSector S z'.1)
    (hν : z.1.2.1 = z'.1.2.1) (hκ : z.1.2.2.1 = z'.1.2.2.1)
    (hq : z.2 = z'.2) (m : ℕ)
    (hu : ∀ r ∈ Ioo (C.left m) (C.right m), ∀ θ,
      stateU S z.1 (r, θ) = stateU S z'.1 (r, θ)) :
    C.minusReturnInverse z m = C.minusReturnInverse z' m := by
  have hfloweq := N01Properties.minusFlow_eq_of_height_locality hN01 hS hT hz hz'
    hsector hν hκ hq m hu
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
      have heq := hfloweq (C.minusReturnInverse z' m θ) hr
      change C.minusFlow z m (C.right m) (C.minusReturnInverse z' m θ) =
        C.minusFlow z' m (C.right m) (C.minusReturnInverse z' m θ) at heq
      exact congrArg (C.minusReturnInverse z m) heq.symm
    _ = C.minusReturnInverse z' m θ :=
      (hInv z hz hsector m (C.minusReturnInverse z' m θ)).2.1

end ContinuousFlexibility.Statements
