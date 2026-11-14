module

public import ContinuousFlexibility.Analysis.N04NegativeGeometryHeightPerturbation
public import ContinuousFlexibility.Analysis.SectorParameterGeometry

/-!
# Exact positive-piece values of an admissible gauge

Admissibility supplies the inverse identities at every lifted sector
parameter.  At zero the pulled height is the strictly positive reference
height.  A reference chart carries every physical interior point to a
point of the canonical unit strip, with exactly the prescribed inverse
image.  These facts require no parameter-smoothness assertion.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

/-- The inverse relation needed by the exact pulled-height formula is
part of admissibility on the lifted parameter neighborhood. -/
theorem n04NegativeGeometry_admissible_lift_leftInverse
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {b : ℕ} {ε : ℝ} (hG : G.Admissible b ε)
    (z : Parameter (G.S η)) (hz : z ∈ sectorNeighborhood (G.S η) b ε ε)
    (i : N04PositiveComponent G.W.D.a G.W.D.b (deriv G.W.D.w)) :
    Function.LeftInverse (G.σ (G.lift η z) i) (G.τ (G.lift η z) i) := by
  have hm := hG.2.2.2.2.2
  have hmatching := hm.choose_spec.choose_spec.choose_spec.2
  have hz' : liftSectorParameter G.W.S G.W.C z ∈
      stateNeighborhood G.W.S G.W.C b ε :=
    liftSectorParameter_mem_stateNeighborhood hz le_rfl
  have hs : stateSector G.W.S (liftSectorParameter G.W.S G.W.C z).1 :=
    G.W.through03.1.1.2.2.1.liftSectorParameter_sector z
  exact (hmatching (liftSectorParameter G.W.S G.W.C z) hz' hs i).geometry.left_inverse

theorem n04NegativeGeometry_gauge_lift_zero
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space) :
    G.lift η (0 : Parameter (G.S η)) = G.ref η :=
  (liftSectorParameter_eq_affine (G.S η) (G.C η) 0).trans
    ((congrArg (fun w : AnnularState (G.S η) × ℝ => ((G.C η).referenceState, 0) + w)
      (ContinuousLinearMap.map_zero (sectorParameterInclusion (G.S η)))).trans (add_zero _))

/-- The positive pulled height at parameter zero is exactly the
reference radial height at the reference inverse point. -/
theorem n04NegativeGeometry_gauge_pulledHeight_zero
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {b : ℕ} {ε : ℝ} (hG : G.Admissible b ε)
    (m : ℕ) (i : N04PositiveComponent G.W.D.a G.W.D.b (deriv G.W.D.w))
    (hi : G.e m = .inr i) (y : PolarPoint) :
    G.pulledHeight η 0 m y = G.H i (positiveReferenceCylinderInverse (G.Y i) y).1 := by
  have href := hG.2.2.2.2.1 i
  have hlift := n04NegativeGeometry_gauge_lift_zero G η
  have hστ : Function.LeftInverse
      (G.σ (G.lift η (0 : Parameter (G.S η))) i)
      (G.τ (G.lift η (0 : Parameter (G.S η))) i) := by
    rw [hlift]
    change Function.LeftInverse
      (G.σ (G.W.C.referenceState, 0) i) (G.τ (G.W.C.referenceState, 0) i)
    rw [href.1, href.2.1]
    exact fun _ => rfl
  rw [n04NegativeGeometry_gauge_pulledHeight_positive G η 0 m i hi hστ y, hlift]
  change G.H i (positiveReferenceCylinderInverse (G.Y i) y).1 /
    G.Q (G.W.C.referenceState, 0) i (positiveReferenceCylinderInverse (G.Y i) y) = _
  rw [href.2.2, div_one]

theorem n04NegativeGeometry_gauge_pulledHeight_zero_pos
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {b : ℕ} {ε : ℝ} (hG : G.Admissible b ε)
    (m : ℕ) (i : N04PositiveComponent G.W.D.a G.W.D.b (deriv G.W.D.w))
    (hi : G.e m = .inr i) (y : PolarPoint) : 0 < G.pulledHeight η 0 m y := by
  rw [n04NegativeGeometry_gauge_pulledHeight_zero G η hG m i hi y]
  exact (hG.2.2.2.1 i).1.height_positive (positiveReferenceCylinderInverse (G.Y i) y)

/-- Every physical interior point has a canonical unit-strip point with
that exact reference inverse image. -/
theorem n04NegativeGeometry_canonical_point_of_physical
    {G : N04RealizationGauge} {b : ℕ} {ε : ℝ} (hG : G.Admissible b ε)
    (i : N04PositiveComponent G.W.D.a G.W.D.b (deriv G.W.D.w))
    (r : ℝ) (hr : r ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i)) :
    ∃ y : unitStrip, positiveReferenceCylinderInverse (G.Y i) y.val = (r, 0) := by
  have href := (hG.2.2.2.1 i).1
  have hy : positiveReferenceCylinderChart (G.Y i) (r, 0) ∈ unitStrip :=
    href.maps_open ⟨hr, mem_univ (0 : ℝ)⟩
  exact ⟨⟨positiveReferenceCylinderChart (G.Y i) (r, 0), hy⟩, href.left_inverse (r, 0)⟩

/-- The center used by the explicit interior bump has such a canonical
point, since it lies strictly to the left of the central buffer. -/
theorem n04NegativeGeometry_canonical_point_at_buffer_center
    {G : N04RealizationGauge} {b : ℕ} {ε : ℝ} (hG : G.Admissible b ε)
    (B : N04PositiveNormalizationBuffer G.W.D.a G.W.D.b
      (deriv G.W.D.w) (tsupport G.W.D.chi))
    (i : N04PositiveComponent G.W.D.a G.W.D.b (deriv G.W.D.w)) :
    ∃ y : unitStrip, positiveReferenceCylinderInverse (G.Y i) y.val =
      ((n04PositiveLeft i + B.centerLeft i) / 2, 0) := by
  have h := B.ordered i
  have hright : B.centerLeft i < n04PositiveRight i :=
    h.2.1.trans (h.2.2.1.trans (h.2.2.2.1.trans h.2.2.2.2))
  exact n04NegativeGeometry_canonical_point_of_physical hG i _
    ⟨by linarith [h.1], by linarith [h.1]⟩

end ContinuousFlexibility.Analysis

/--
info: 'ContinuousFlexibility.Analysis.n04NegativeGeometry_gauge_pulledHeight_zero_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ContinuousFlexibility.Analysis.n04NegativeGeometry_gauge_pulledHeight_zero_pos
