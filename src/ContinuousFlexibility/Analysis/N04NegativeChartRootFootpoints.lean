module

public import ContinuousFlexibility.Analysis.N04NegativeChartControlledCollar
public import ContinuousFlexibility.Analysis.N04NegativeChartRootFlowSymmetry
public import ContinuousFlexibility.Analysis.N03FixedRootInverseIdentification
public import ContinuousFlexibility.Analysis.N04bRootTravelMatching

/-!
# The supplied root flow has the literal corrected footpoints

The scale may be any positive number below the single material collar.
All initial angles agree with the stored corrected flow on the entire
normalized closed interval. The inverse is the same reversed flow already
used for estimates. The right endpoint retains its exact travel shift.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis.N04RealizationStart

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable (W : N04RealizationStart)

theorem negativeInwardPoint_root_add (m : ℕ) (side : Bool) (t θ : ℝ) :
    W.negativeInwardPoint m side (t, θ) =
      (n01ComponentRoot W.C m side + n01ComponentRootOrientation side * t, θ) := by
  cases side <;> simp only [negativeInwardPoint, inwardComponentPoint,
    n01ComponentRoot, n01ComponentRootOrientation, Bool.false_eq_true, ↓reduceIte,
    one_mul, neg_one_mul, sub_eq_add_neg]

namespace NegativeOpticalFactors

variable {W : N04RealizationStart} {e : ℕ ≃ N04PieceIndex W.D}
  (F : NegativeOpticalFactors W e)
  {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {d c : P × PolarPoint → ℝ} {δ : ℝ}

/-- No new flow is selected when the quantitative root solution is
identified with every actual corrected trajectory. -/
theorem fullHalfFields_stored_flow
    (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    (hdp : ∀ y r, Function.Periodic (fun θ => d (y, (r, θ))) Real.pi)
    (hcp : ∀ y r, Function.Periodic (fun θ => c (y, (r, θ))) Real.pi)
    (A : NegativeChartRootFlowData d c δ) (y : P)
    {z : AnnularState W.S × ℝ}
    (hz : z ∈ stateNeighborhood W.S W.C W.base (W.ε / 2))
    (hs : stateSector W.S z.1) (m : ℕ) (side : Bool)
    {R : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hδc : δ * R ≤ W.negativeMaterialCollar m)
    (hrep : ∀ p : PolarPoint, p.1 ∈ Icc (0 : ℝ) (W.negativeOpticalWidth m side) →
      d (y, p) = F.fullHalfDrift z m side p ∧
      c (y, p) = F.fullHalfSpeed z m side p) :
    RootStoredFlowAgreementOn W.C W.L z m side δ R (A.flow y) := by
  let r := n01ComponentRoot W.C m side
  let σ := n01ComponentRootOrientation side
  have hz' : z ∈ stateNeighborhood W.S W.C W.base W.ε :=
    stateNeighborhood_mono W.S W.C le_rfl (by linarith [W.ε_pos]) hz
  have hhalf := (W.negativeMaterialCollar_bounds m).2.2.2 side
  have hw := W.negativeOpticalWidth_pos m side
  have hδhalf : δ * R ≤ W.negativeOpticalWidth m side := by linarith only [hδc, hhalf, hw]
  have hδwidth : δ * R < W.C.right m - W.C.left m :=
    hδhalf.trans_lt (W.negativeOpticalWidth_lt_component m side)
  intro ι x hx
  let f : ℝ → ℝ := fun t => W.L.minusFlow z m (r + σ * t) ι
  have hstored := W.through03.2.2.2.2.2.1 z hz' hs m ι
  have hmap : MapsTo (fun t : ℝ => r + σ * t)
      (Icc (0 : ℝ) (δ * R)) (Icc (W.C.left m) (W.C.right m)) := by
    intro t ht
    cases side <;> simp only [r, σ, n01ComponentRoot, n01ComponentRootOrientation,
      Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul]
      <;> constructor <;> linarith only [ht.1, ht.2, hδwidth]
  have hcont : ContinuousOn f (Icc (0 : ℝ) (δ * R)) :=
    hstored.2.1.comp (continuous_const.add
      (continuous_const.mul continuous_id)).continuousOn hmap
  have hode : ∀ t ∈ Ioo (0 : ℝ) (δ * R), HasDerivAt f
      (rootPhysicalSpeed (fun p => d (y, p)) (fun p => c (y, p)) (-σ) (t, f t)) t := by
    intro t ht
    have hp : r + σ * t ∈ Ioo (W.C.left m) (W.C.right m) := by
      cases side <;> simp only [r, σ, n01ComponentRoot, n01ComponentRootOrientation,
        Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul]
        <;> constructor <;> linarith only [ht.1, ht.2, hδwidth]
    have he := F.fullHalfFields_corrected_minus_speed hz m side
      (p := (t, f t)) ⟨ht.1, ht.2.le.trans hδc⟩
    rw [W.negativeInwardPoint_root_add] at he
    have hv := hrep (t, f t) ⟨ht.1.le, ht.2.le.trans hδhalf⟩
    have hraw : rootPhysicalSpeed (fun p => d (y, p)) (fun p => c (y, p))
        (-σ) (t, f t) = σ *
        minusCharacteristicSpeed (W.L.coefficients z) (r + σ * t, f t) := by
      dsimp only [rootPhysicalSpeed]
      rw [hv.1, hv.2, he]
      ring
    have hlin : HasDerivAt (fun s : ℝ => r + σ * s) σ t := by
      simpa only [mul_one, id_eq] using ((hasDerivAt_id t).const_mul σ).const_add r
    have hh := (hstored.2.2.1 (r + σ * t) hp).comp t hlin
    change HasDerivAt f
      (minusCharacteristicSpeed (W.L.coefficients z) (r + σ * t, f t) * σ) t at hh
    apply hh.congr_deriv
    rw [hraw]
    ring
  have hinit : f 0 = W.L.minusFlow z m r ι := by simp only [f, mul_zero, add_zero]
  exact rootRescaledFlow_eq_storedTrajectory hR hδ Real.pi_ne_zero
    (hd.comp (contDiff_const.prodMk contDiff_id))
    (hc.comp (contDiff_const.prodMk contDiff_id)) (hdp y) (hcp y)
    (A.flow_equations y) hinit hcont hode hx

/-- At the right root the actual odd return label subtracts precisely
the total travel. It is not replaced by a raw composed left label. -/
theorem fullHalfFields_inverse_root_label
    (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    (hdp : ∀ y r, Function.Periodic (fun θ => d (y, (r, θ))) Real.pi)
    (hcp : ∀ y r, Function.Periodic (fun θ => c (y, (r, θ))) Real.pi)
    (A : NegativeChartRootFlowData d c δ) (y : P)
    {z : AnnularState W.S × ℝ}
    (hz : z ∈ stateNeighborhood W.S W.C W.base (W.ε / 2))
    (hs : stateSector W.S z.1) (m : ℕ) (side : Bool)
    {R : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hδc : δ * R ≤ W.negativeMaterialCollar m)
    (hrep : ∀ p : PolarPoint, p.1 ∈ Icc (0 : ℝ) (W.negativeOpticalWidth m side) →
      d (y, p) = F.fullHalfDrift z m side p ∧
      c (y, p) = F.fullHalfSpeed z m side p)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) R) (θ : ℝ) :
    n01RootLabel W.S W.C z m side
      (A.inverse y (x, ((-n01ComponentRootOrientation side) * Real.sqrt δ) *
        x ^ (3 / 2 : ℝ)) 1 θ) =
      stateLeftChart W.S z.1 m (Function.invFun (W.L.minusFlow z m
        (n01ComponentRoot W.C m side + n01ComponentRootOrientation side * (δ * x))) θ) -
        if side then W.C.travel m else 0 := by
  let r := n01ComponentRoot W.C m side
  let σ := n01ComponentRootOrientation side
  let v : ℝ × ℝ := (x, (-σ * Real.sqrt δ) * x ^ (3 / 2 : ℝ))
  have hz' : z ∈ stateNeighborhood W.S W.C W.base W.ε :=
    stateNeighborhood_mono W.S W.C le_rfl (by linarith [W.ε_pos]) hz
  have hH : Function.Bijective (W.L.minusFlow z m r) := by
    cases side
    · have he : W.L.minusFlow z m (W.C.left m) = id :=
        funext fun ι => (W.through03.2.2.2.2.2.1 z hz' hs m ι).1
      simpa only [r, n01ComponentRoot, Bool.false_eq_true, ↓reduceIte, he] using
        (Function.bijective_id : Function.Bijective (id : ℝ → ℝ))
    · exact (n04b_corrected_return_geometry W.hT W.hS W.through03 hz' hs m).2.2.2.1
  have hinj : Function.Injective (A.flow y v 1) :=
    Function.LeftInverse.injective (fun η => (A.endpoint_inverse y v η).2)
  have hmatch := F.fullHalfFields_stored_flow hd hc hdp hcp A y hz hs m side hR hδ hδc hrep
  have he : W.L.minusFlow z m r
      (Function.invFun (W.L.minusFlow z m (r + σ * (δ * x))) θ) =
      A.inverse y v 1 θ :=
    invFun_reanchored_eq_of_full_agreement hH hinj
      (fun ι => hmatch ι x hx) (A.endpoint_inverse y v θ).1
  have hlabel (ι : ℝ) : n01RootLabel W.S W.C z m side (W.L.minusFlow z m r ι) =
      stateLeftChart W.S z.1 m ι - if side then W.C.travel m else 0 := by
    cases side
    · change stateLeftChart W.S z.1 m (W.L.minusFlow z m (W.C.left m) ι) =
        stateLeftChart W.S z.1 m ι - 0
      rw [(W.through03.2.2.2.2.2.1 z hz' hs m ι).1, sub_zero]
    · exact (W.through03.2.2.2.2.2.1 z hz' hs m ι).2.2.2.1
  exact (congrArg (n01RootLabel W.S W.C z m side) he.symm).trans (hlabel _)

end NegativeOpticalFactors
end ContinuousFlexibility.Analysis.N04RealizationStart

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.fullHalfFields_inverse_root_label'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.fullHalfFields_inverse_root_label
