import ContinuousFlexibility.Analysis.N07bAtlasEnergy

/-!
# The actual reference physical representative

Keeping a current canonical unknown fixed changes its physical representative
at the reference state. This module constructs that representative from the
prescribed charts. The a.e. unique open atlas makes the piecewise definition
unambiguous on every open piece. The frozen normalization region then gives
exact preservation of the physical row.

These identities do not assert transmission across the piece boundaries or
membership in the reference graph's weighted endpoint class.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

/-- Pull a current canonical unknown back through one reference chart, retaining
the same free left constant. -/
def n07bReferencePiecePullback {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (a : ℝ) (η : PolarPoint → ℝ)
    (p : PolarPoint) : ℝ :=
  a * S.chiLeft p.1 + K.height (C.referenceState, 0) m p *
    canonicalHeight S K z m (fun x => η x - a * S.chiLeft x.1)
      (K.chart (C.referenceState, 0) m p)

/-- The global reference representative uses the actual physical piece
containing the point. Off the open atlas it retains the original field. -/
def n07bReferencePullback {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (a : ℝ) (η : PolarPoint → ℝ)
    (p : PolarPoint) : ℝ := by
  classical
  exact if h : ∃ m, p ∈ physicalPieceOpen S K m then
    n07bReferencePiecePullback C K z h.choose a η p
  else η p

/-- The definition selects the given piece at every point of that piece. -/
theorem n07bReferencePullback_on_piece
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartA D S C K base ε)
    (z : AnnularState S × ℝ) (a : ℝ) (η : PolarPoint → ℝ)
    {m : ℕ} {p : PolarPoint} (hp : p ∈ physicalPieceOpen S K m) :
    n07bReferencePullback C K z a η p =
      n07bReferencePiecePullback C K z m a η p := by
  classical
  have hex : ∃ n, p ∈ physicalPieceOpen S K n := ⟨m, hp⟩
  have hm : hex.choose = m := by
    by_contra hne
    exact Set.disjoint_left.mp (n07b_physicalIntervals_pairwiseDisjoint hK hne)
      hex.choose_spec.1 hp.1
  simp only [n07bReferencePullback, dif_pos hex, hm]

/-- The reference and current canonical unknowns are exactly the same on
the canonical interior; this is an identity of the actual coordinate formulas. -/
theorem n07bReferencePullback_canonicalHeight
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartA D S C K base ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsectorRef : stateSector S C.referenceState)
    (z : AnnularState S × ℝ) (a : ℝ) (η : PolarPoint → ℝ) (m : ℕ)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    canonicalHeight S K (C.referenceState, 0) m
      (fun x => n07bReferencePullback C K z a η x - a * S.chiLeft x.1) p =
        canonicalHeight S K z m (fun x => η x - a * S.chiLeft x.1) p := by
  have hcharts := hK.2.2.2.2.2.2.2.1 (C.referenceState, 0) href hsectorRef m
  have hx := hcharts.2.1 hp
  have hheight := (hcharts.2.2.2.2.2.2.2 _ hx).1.ne'
  change (n07bReferencePullback C K z a η (K.inverseChart (C.referenceState, 0) m p) -
      a * S.chiLeft (K.inverseChart (C.referenceState, 0) m p).1) /
      K.height (C.referenceState, 0) m (K.inverseChart (C.referenceState, 0) m p) = _
  rw [n07bReferencePullback_on_piece hK z a η hx]
  simp only [n07bReferencePiecePullback, add_sub_cancel_left,
    hcharts.2.2.2.1 p hp]
  exact mul_div_cancel_left₀ _ hheight

/-- The normalization region is physically unchanged by the actual reference
pullback, even at points outside the open atlas. -/
theorem n07bReferencePullback_eq_on_normalizationRegion
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (a : ℝ) (η : PolarPoint → ℝ)
    {p : PolarPoint} (hp : p.1 ∈ K.normalizationRegion) :
    n07bReferencePullback C K z a η p = η p := by
  classical
  by_cases hex : ∃ m, p ∈ physicalPieceOpen S K m
  · obtain ⟨m, hm⟩ := hex
    have hcharts := hK.2.2.2.2.2.2.2.1 z hz hsector m
    have hfixed := hK.2.2.1 z hz hsector m p hm hp
    have hinverse : K.inverseChart z m (K.chart (C.referenceState, 0) m p) = p := by
      rw [← hfixed.1]
      exact hcharts.2.2.1 p hm
    have hheight := (hcharts.2.2.2.2.2.2.2 p hm).1.ne'
    rw [n07bReferencePullback_on_piece hK z a η hm]
    simp only [n07bReferencePiecePullback, canonicalHeight, hinverse, ← hfixed.2]
    field_simp [hheight]
    <;> ring
  · simp only [n07bReferencePullback, dif_neg hex]

/-- The reference row is preserved pointwise under its physical integral.
No integrability or boundary trace premise is needed for this identity. -/
theorem n07bReferencePullback_referenceRow
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (a : ℝ) (η : PolarPoint → ℝ) :
    referenceRow D (n07bReferencePullback C K z a η) = referenceRow D η := by
  have heq : (fun r => referenceColumn D r *
      referenceMode (n07bReferencePullback C K z a η) 2 r) =
      (fun r => referenceColumn D r * referenceMode η 2 r) := by
    funext r
    by_cases hc : referenceColumn D r = 0
    · simp only [hc, zero_mul]
    · have hr : r ∈ K.normalizationRegion := hK.2.1 hc
      have hfield : (fun θ => n07bReferencePullback C K z a η (r, θ) *
          Radial.cosineMode 2 θ) = (fun θ => η (r, θ) * Radial.cosineMode 2 θ) := by
        funext θ
        rw [n07bReferencePullback_eq_on_normalizationRegion hK hz hsector a η hr]
      simp only [referenceMode, hfield]
  exact congrArg (fun g : ℝ → ℝ => ∫ r in D.a..D.b, g r) heq

end ContinuousFlexibility.Analysis
