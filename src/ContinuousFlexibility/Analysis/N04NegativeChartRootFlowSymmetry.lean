import ContinuousFlexibility.Analysis.N04NegativeChartRootFlowFactory
import ContinuousFlexibility.Analysis.ReturnCoefficientParity

/-!
# Reflection on the actual physical root fibers

Only the values on the closed physical radial interval enter the ODE
uniqueness argument. The finite-plot representatives may have arbitrary
smooth extensions outside that interval. Both inverse samples belong to
the same forward/reverse flow package.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

private theorem normalizedFactors_reflect
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (C : NonlinearGeometryData S)
    (z : AnnularState S × ℝ) (r θ : ℝ) :
    normalizedSpeedFactor D S C 0 z (r, -θ) =
        -normalizedSpeedFactor D S C 0 z (r, θ) ∧
      normalizedSpeedFactor D S C 1 z (r, -θ) =
        normalizedSpeedFactor D S C 1 z (r, θ) := by
  let w := stateProfile D S C z.1
  let h := stateHeight D S C z
  have hh : ∀ s η, h (s, -η) = h (s, η) := stateHeight_even_of_physical hS C z
  have hk : ∀ s η, heightRadial h (s, -η) = heightRadial h (s, η) :=
    radialPartial_of_even h hh
  have hp : ∀ s η, heightAngular h (s, -η) = -heightAngular h (s, η) := by
    intro s η
    simp only [heightAngular, angularPartial_of_even h hh, neg_div]
  have hpr := radialPartial_of_odd (heightAngular h) hp r θ
  have hpt := angularPartial_of_odd (heightAngular h) hp r θ
  have hE : profileEnergy w (r, -θ) = profileEnergy w (r, θ) := rfl
  have hQ : heightQ (profileEnergy w (r, -θ)) (heightRadial h (r, -θ))
      (angularPartial (heightAngular h) (r, -θ)) =
      heightQ (profileEnergy w (r, θ)) (heightRadial h (r, θ))
        (angularPartial (heightAngular h) (r, θ)) := by rw [hE, hk, hpt]
  have hD : polarDiscriminant w h (r, -θ) = polarDiscriminant w h (r, θ) := by
    simp only [polarDiscriminant, heightDiscriminant, hE, hk, hp, neg_sq]
  constructor
  · change profileEnergy w (r, -θ) * radialPartial (heightAngular h) (r, -θ) /
      (w r * (heightQ (profileEnergy w (r, -θ)) (heightRadial h (r, -θ))
        (angularPartial (heightAngular h) (r, -θ)) / w r)) = _
    rw [hE, hpr, hQ]
    simp only [normalizedSpeedFactor, if_pos rfl, mul_neg, neg_div, w, h]
  · change Real.sqrt (polarDiscriminant w h (r, -θ)) /
      (heightQ (profileEnergy w (r, -θ)) (heightRadial h (r, -θ))
        (angularPartial (heightAngular h) (r, -θ)) / w r) = _
    rw [hD, hQ]
    rfl

namespace N04RealizationStart.NegativeOpticalFactors

variable {W : N04RealizationStart} {e : ℕ ≃ N04PieceIndex W.D}
  (F : NegativeOpticalFactors W e)

theorem fullHalfFields_reflect (z : AnnularState W.S × ℝ)
    (m : ℕ) (side : Bool) (r θ : ℝ) :
    F.fullHalfDrift z m side (r, -θ) = -F.fullHalfDrift z m side (r, θ) ∧
      F.fullHalfSpeed z m side (r, -θ) = F.fullHalfSpeed z m side (r, θ) := by
  have hh := normalizedFactors_reflect W.hS W.C z
    (inwardComponentPoint (W.C.left m) (W.C.right m) side r) θ
  constructor
  · simpa only [fullHalfDrift, negativeInwardPoint, mul_neg] using
      congrArg (fun a => -n01ComponentRootOrientation side * a) hh.1
  · exact congrArg (fun a => F.opticalSpeed z m side r * a) hh.2

end N04RealizationStart.NegativeOpticalFactors

/-- Coefficient reflection is needed only along this fixed physical
fiber, including its root endpoint. -/
theorem n04NegativeChart_rootFlow_reflect_on_fiber
    {d c : PolarPoint → ℝ} {δ x : ℝ}
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
    (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    (hdp : ∀ r, Function.Periodic (fun θ => d (r, θ)) Real.pi)
    (hcp : ∀ r, Function.Periodic (fun θ => c (r, θ)) Real.pi)
    (hΘ : N04FlowEquations (rootRescaledField d c δ) Θ)
    (hδx : 0 ≤ δ * x)
    (hpar : ∀ r ∈ Icc (0 : ℝ) (δ * x), ∀ θ,
      d (r, -θ) = -d (r, θ) ∧ c (r, -θ) = c (r, θ))
    (ζ θ : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Θ (x, -ζ) t (-θ) = -Θ (x, ζ) t θ := by
  have hF : ContDiff ℝ ∞ (fun q : PolarPoint =>
      rootRescaledField d c δ (q.1, ((x, -ζ), q.2))) :=
    (contDiff_rootRescaledField hd hc δ).comp
      (contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd))
  obtain ⟨K, hK⟩ := exists_uniform_angle_lipschitz_of_contDiff
    (a := 0) (b := 1) hF Real.pi_ne_zero
    (fun r => rootRescaledField_periodic hdp hcp δ r (x, -ζ))
  have href (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) (η : ℝ) :
      rootRescaledField d c δ (r, ((x, -ζ), -η)) =
        -rootRescaledField d c δ (r, ((x, ζ), η)) := by
    have hr2 : r ^ 2 ≤ 1 := by
      simpa only [pow_two, one_mul] using mul_le_mul hr.2 hr.2 hr.1 zero_le_one
    have hrad : δ * x * r ^ 2 ∈ Icc (0 : ℝ) (δ * x) :=
      ⟨mul_nonneg hδx (sq_nonneg r),
        by simpa only [mul_one] using mul_le_mul_of_nonneg_left hr2 hδx⟩
    have hp := hpar _ hrad η
    simp only [rootRescaledField, rootRegularizedField, hp.1, hp.2]
    ring
  apply eqOn_scalarFlow_of_same_initial
    (u := fun r => Θ (x, -ζ) r (-θ)) (v := fun r => -Θ (x, ζ) r θ)
    hK (fun r hr => hΘ.2 (x, -ζ) (-θ) r hr) _ _ ht
  · intro r hr
    simpa only [href r hr] using (hΘ.2 (x, ζ) θ r hr).fun_neg
  · rw [hΘ.1, hΘ.1]

namespace NegativeChartRootFlowData

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] {d c : P × PolarPoint → ℝ} {δ : ℝ}
  (A : NegativeChartRootFlowData d c δ)

/-- The endpoint reflection belongs to the very same inverse flow used
for the quantitative state variations. -/
theorem inverse_reflect_on_fiber
    (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    (hdp : ∀ y r, Function.Periodic (fun θ => d (y, (r, θ))) Real.pi)
    (hcp : ∀ y r, Function.Periodic (fun θ => c (y, (r, θ))) Real.pi)
    (y : P) {x : ℝ} (hδx : 0 ≤ δ * x)
    (hpar : ∀ r ∈ Icc (0 : ℝ) (δ * x), ∀ θ,
      d (y, (r, -θ)) = -d (y, (r, θ)) ∧ c (y, (r, -θ)) = c (y, (r, θ)))
    (ζ θ : ℝ) :
    A.inverse y (x, -ζ) 1 (-θ) = -A.inverse y (x, ζ) 1 θ := by
  have hinj : Function.Injective (A.flow y (x, -ζ) 1) :=
    Function.LeftInverse.injective (fun η => (A.endpoint_inverse y (x, -ζ) η).2)
  apply hinj
  rw [(A.endpoint_inverse y (x, -ζ) (-θ)).1]
  have hr := n04NegativeChart_rootFlow_reflect_on_fiber
    (hd.comp (contDiff_const.prodMk contDiff_id))
    (hc.comp (contDiff_const.prodMk contDiff_id)) (hdp y) (hcp y)
    (A.flow_equations y) hδx hpar ζ (A.inverse y (x, ζ) 1 θ)
    (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩)
  exact (hr.trans (congrArg Neg.neg (A.endpoint_inverse y (x, ζ) θ).1)).symm

end NegativeChartRootFlowData
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.NegativeChartRootFlowData.inverse_reflect_on_fiber'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.NegativeChartRootFlowData.inverse_reflect_on_fiber
