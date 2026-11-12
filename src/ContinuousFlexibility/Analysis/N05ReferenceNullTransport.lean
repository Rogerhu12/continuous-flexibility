import ContinuousFlexibility.Analysis.N05ReferenceNullPDE
import ContinuousFlexibility.Analysis.N05OpticalPrimitive
import ContinuousFlexibility.Analysis.N05RadialTransport

/-!
# Exact optical transport on the actual negative cut halves

Each physical cut half has its closed endpoints strictly inside the radial
core.  The actual characteristic equations therefore admit the ordinary
optical integral as a primitive all the way to their root and cut.  The
transport formula below uses the actual chart, with one sign parameter for
both null coordinates and one orientation parameter for both halves.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}

theorem n05_cut_physical_closed_subset_core
    (hgeom : controlGeometryConditions D S C)
    (h04 : N04Properties D T S C L K base loss ε) (m : ℕ) (right : Bool) :
    Icc (K.physicalLeft (if right then (K.cutPair m).2 else (K.cutPair m).1))
        (K.physicalRight (if right then (K.cutPair m).2 else (K.cutPair m).1)) ⊆
      radialCore D := by
  rcases h04 with ⟨_, _, _, hpieces, _, _, _, _, _, _, _, hcuts, _⟩
  obtain ⟨_, _, hleft, hright, hmeet, _⟩ := hcuts m
  have hL := (hpieces (K.cutPair m).1).1
  have hR := (hpieces (K.cutPair m).2).1
  have hinterval := hgeom.1 m
  intro r hr
  cases right with
  | false =>
    change K.physicalLeft (K.cutPair m).1 ≤ r ∧ r ≤ K.physicalRight (K.cutPair m).1 at hr
    constructor
    · exact hinterval.1.trans_le (by simpa only [hleft] using hr.1)
    · have hcut : K.physicalRight (K.cutPair m).1 < C.right m := by
        simpa only [← hmeet, hright] using hR
      exact hr.2.trans_lt (hcut.trans hinterval.2.2)
  | true =>
    change K.physicalLeft (K.cutPair m).2 ≤ r ∧ r ≤ K.physicalRight (K.cutPair m).2 at hr
    constructor
    · have hcut : C.left m < K.physicalLeft (K.cutPair m).2 := by
        simpa only [hleft, hmeet] using hL
      exact (hinterval.1.trans hcut).trans_le hr.1
    · exact (show r ≤ C.right m by simpa only [hright] using hr.2).trans_lt hinterval.2.2

theorem n05_cut_reference_signed_null_PDE
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (m : ℕ) (right : Bool) {x : PolarPoint}
    (hx : x ∈ physicalPieceOpen S K
      (if right then (K.cutPair m).2 else (K.cutPair m).1))
    {σ : ℝ} (hσ : σ ^ 2 = 1) :
    let Ψ := K.chart (C.referenceState, 0)
      (if right then (K.cutPair m).2 else (K.cutPair m).1)
    let orientation : ℝ := if right then -1 else 1
    radialPartial (n05NullCoordinate Ψ σ) x =
      (σ * orientation) * opticalSpeed D.w x.1 * angularPartial (n05NullCoordinate Ψ σ) x := by
  have hp := n05_cut_reference_null_PDE hT hS h m right hx
  have hs : σ = 1 ∨ σ = -1 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by simpa only [one_pow] using hσ)
  rcases hs with rfl | rfl
  · simpa only [one_mul] using hp.1
  · simpa only [neg_one_mul] using hp.2

/-- Genuine transport along the reference optical characteristics, including
the physical root and cut endpoints of the selected half. -/
theorem n05_cut_reference_null_transport
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (m : ℕ) (right : Bool) {σ : ℝ} (hσ : σ ^ 2 = 1)
    {x y : ℝ}
    (hx : x ∈ Icc
      (K.physicalLeft (if right then (K.cutPair m).2 else (K.cutPair m).1))
      (K.physicalRight (if right then (K.cutPair m).2 else (K.cutPair m).1)))
    (hy : y ∈ Icc
      (K.physicalLeft (if right then (K.cutPair m).2 else (K.cutPair m).1))
      (K.physicalRight (if right then (K.cutPair m).2 else (K.cutPair m).1))) (θ : ℝ) :
    let i := if right then (K.cutPair m).2 else (K.cutPair m).1
    let Ψ := K.chart (C.referenceState, 0) i
    let orientation : ℝ := if right then -1 else 1
    n05NullCoordinate Ψ σ (x, θ) =
      n05NullCoordinate Ψ σ
        (y, θ + (σ * orientation) * opticalTravel D.w (K.physicalLeft i) x -
          (σ * orientation) * opticalTravel D.w (K.physicalLeft i) y) := by
  let i := if right then (K.cutPair m).2 else (K.cutPair m).1
  let Ψ := K.chart (C.referenceState, 0) i
  let orientation : ℝ := if right then -1 else 1
  let A : ℝ → ℝ := fun r => (σ * orientation) * opticalTravel D.w (K.physicalLeft i) r
  have h01 := h.1.1.1
  have h04 := h.2.2.2.2
  rcases h04 with ⟨_, _, _, hpieces, _, hnegative, _, _, hclosed, _, _, hcuts, _⟩
  have hcore : Icc (K.physicalLeft i) (K.physicalRight i) ⊆ radialCore D :=
    n05_cut_physical_closed_subset_core h01.2.2.2.1 h.2.2.2.2 m right
  have hl : K.physicalLeft i ∈ radialCore D :=
    hcore ⟨le_rfl, (hpieces i).1.le⟩
  have hmem : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    n05_referenceState_mem h01.2.1
  have hsector := n05_referenceState_sector h01.2.2.1
  have hneg : K.positive i = false := by
    cases right
    · exact (hcuts m).1
    · exact (hcuts m).2.1
  have hchart (p : PolarPoint)
      (hp : p.1 ∈ Icc (K.physicalLeft i) (K.physicalRight i)) :
      ContDiffAt ℝ ∞ Ψ p := (hclosed (C.referenceState, 0) hmem hsector i p hp).1
  have hN : ContinuousOn (n05NullCoordinate Ψ σ)
      (Icc (K.physicalLeft i) (K.physicalRight i) ×ˢ univ) := by
    intro p hp
    have hΨ := (hchart p hp.1).continuousAt
    exact (hΨ.snd.add (continuousAt_const.mul
      (n05TricomiTime_continuous.continuousAt.comp
        (f := fun q : PolarPoint => (Ψ q).1) hΨ.fst))).continuousWithinAt
  have hNd (p : PolarPoint)
      (hp : p.1 ∈ Ioo (K.physicalLeft i) (K.physicalRight i)) :
      DifferentiableAt ℝ (n05NullCoordinate Ψ σ) p := by
    have hpClosed : p.1 ∈ Icc (K.physicalLeft i) (K.physicalRight i) :=
      ⟨hp.1.le, hp.2.le⟩
    have hpos := n05_negative_reference_radius_pos hT hS h hneg hpClosed
      ⟨hcore hpClosed, mem_univ _⟩ (hnegative i hneg p.1 hp)
    exact (n05NullCoordinate_contDiffAt (hchart p hpClosed) hpos σ).differentiableAt (by simp)
  have hA : ContinuousOn A (Icc (K.physicalLeft i) (K.physicalRight i)) :=
    continuousOn_const.mul ((n05_opticalTravel_continuousOn_core h01.1.1 hl).mono hcore)
  have hAd (r : ℝ) (hr : r ∈ Ioo (K.physicalLeft i) (K.physicalRight i)) :
      HasDerivAt A ((σ * orientation) * opticalSpeed D.w r) r :=
    (n05_opticalTravel_hasDerivAt_core h01.1.1 hl
      (hcore ⟨hr.1.le, hr.2.le⟩)).const_mul (σ * orientation)
  exact n05_radial_transport hN hNd hA hAd
    (fun p hp => n05_cut_reference_signed_null_PDE hT hS h m right
      (x := p) ⟨hp, mem_univ _⟩ hσ) hx hy θ

end ContinuousFlexibility.Statements
