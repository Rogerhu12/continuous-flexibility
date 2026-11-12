import ContinuousFlexibility.Analysis.N07bTransportReferenceGraph
import ContinuousFlexibility.Analysis.N07bReferencePieceRegularity
import ContinuousFlexibility.Analysis.MaterialHeightRegularity

/-!
# The actual reference representative from primitive transport geometry

The source-independent transport fields supply the physical representative,
its flat extension, and the actual reference graph. The original physical
cutoff is retained; the reference graph lemma accounts for its compact
difference from the radial reference cutoff.

The same representative agrees with the genuine smooth formula on each
reference piece. Consequently its canonical height is exactly the current
canonical height, and its actual reference forcing has the smooth closed-piece
representatives used by the canonical energy construction. No graph or
canonical-space membership is a premise.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open ContinuousFlexibility.Radial
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- On an actual reference piece the zero extension is the genuine
chart-and-height pullback, independently of its chosen interface values. -/
theorem n07bReferenceTransportRemainder_eqOn_piece
    (hK : N04PartA D S C K base ε)
    {τ : PolarPoint → PolarPoint} {q : PolarPoint → ℝ}
    (hτpiece : ∀ m, ∀ p ∈ referencePhysicalPieceOpen S K m,
      τ p = K.inverseChart z m (K.chart (C.referenceState, 0) m p))
    (hqpiece : ∀ m, ∀ p ∈ referencePhysicalPieceOpen S K m,
      q p = K.height (C.referenceState, 0) m p / K.height z m (τ p))
    (u : PolarPoint → ℝ) (m : ℕ) :
    EqOn (n07bReferenceTransportRemainder D τ q u)
      (n07bReferencePieceRemainder C K z m u) (referencePhysicalPieceOpen S K m) := by
  intro p hp
  have hcore : p ∈ annularOpen D :=
    ⟨(hK.referenceBounds m).2.2 hp.1, mem_univ _⟩
  change n07bReferenceTransportRemainder D τ q u p =
    n07bReferencePieceRemainder C K z m u p
  rw [n07bReferenceTransportRemainder_on τ q u hcore,
    n07bReferencePieceRemainder_eq, hqpiece m p hp, hτpiece m p hp]

/-- Agreement with the physical piece formula is enough for exact equality
of the two actual canonical heights. -/
theorem n07b_canonicalHeight_eqOn_of_piece_remainder
    (hK : N04PartA D S C K base ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    (m : ℕ) (u R : PolarPoint → ℝ)
    (hR : EqOn R (n07bReferencePieceRemainder C K z m u)
      (referencePhysicalPieceOpen S K m)) :
    EqOn (canonicalHeight S K (C.referenceState, 0) m R)
      (canonicalHeight S K z m u) (canonicalOpen S K m) := by
  intro p hp
  have hcharts := hK.charts (C.referenceState, 0) href hsref m
  have hx := hcharts.2.1 hp
  have hxref : K.inverseChart (C.referenceState, 0) m p ∈
      referencePhysicalPieceOpen S K m := by
    rw [← hK.referenceDomain m]
    exact hx
  have hheight := (hcharts.2.2.2.2.2.2.2 _ hx).1.ne'
  change R (K.inverseChart (C.referenceState, 0) m p) /
    K.height (C.referenceState, 0) m (K.inverseChart (C.referenceState, 0) m p) = _
  rw [hR hxref]
  simp only [n07bReferencePieceRemainder, hcharts.2.2.2.1 p hp]
  exact mul_div_cancel_left₀ _ hheight

/-- Primitive geometric transport constructs an actual reference graph
representative for every physical height. The canonical identities and
closed-piece forcing representatives are retained for the fixed graph
identification; the graph is a conclusion, not an input. -/
theorem n07b_exists_referenceTransport_of_primitive_geometry
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hborder : RadialTrueBorder D) (hχ : CutoffConditions D S.chiLeft)
    (hK : N04PartA D S C K base ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    (hgeom : CanonicalPrimitiveGeometry D T S C L K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {u : PolarPoint → ℝ} (hu : HeightMember D T (3 / 4 : ℝ) u)
    {γ : ℝ} (hγ : 0 < γ) (hγβ : γ < (3 / 4 : ℝ))
    (a μ M₀ M₁ : ℝ)
    (hrow : referenceRow D (fun p => u p + a * S.chiLeft p.1) = 0) :
    ∃ (τ : PolarPoint → PolarPoint) (q R η : PolarPoint → ℝ),
      R = n07bReferenceTransportRemainder D τ q u ∧
      η = (fun p => R p + a * S.chiLeft p.1) ∧
      ContDiff ℝ 2 R ∧ ContDiff ℝ 2 η ∧
      Function.Periodic R (0, Real.pi) ∧
      (∀ r θ, R (r, -θ) = R (r, θ)) ∧
      Function.Periodic η (0, Real.pi) ∧
      (∀ r θ, η (r, -θ) = η (r, θ)) ∧
      (∀ m, EqOn R (n07bReferencePieceRemainder C K z m u)
        (referencePhysicalPieceOpen S K m)) ∧
      (∀ m, EqOn (canonicalHeight S K (C.referenceState, 0) m
          (fun p => η p - a * S.chiLeft p.1))
        (canonicalHeight S K z m u) (canonicalOpen S K m)) ∧
      (∀ m, EqOn (canonicalSource S K (C.referenceState, 0) m
          (fun p => radialPDE D.w (fun r θ => R (r, θ)) p.1 p.2))
        (n07bReferencePieceCanonicalSource D C K z m u) (canonicalOpen S K m)) ∧
      (∀ m p, p ∈ canonicalClosed S K m →
        ContDiffAt ℝ ∞ (n07bReferencePieceCanonicalSource D C K z m u) p) ∧
      ReferenceGraph D γ M₀ M₁ (η, μ) (n07bReferenceForcing D μ η, 0) := by
  obtain ⟨δ, hγδ, hδβ⟩ := exists_between hγβ
  obtain ⟨τ, q, hτ, hq, hmap, hτp, hqp, hτe, hqe, hpiece,
    C₀, A, hC₀, hA, hqjet, hτjet, hHratio, hMratio⟩ := hgeom.transport z hz hs
  have hτpiece : ∀ m, ∀ p ∈ referencePhysicalPieceOpen S K m,
      τ p = K.inverseChart z m (K.chart (C.referenceState, 0) m p) :=
    fun m p hp => (hpiece m p hp).1
  have hqpiece : ∀ m, ∀ p ∈ referencePhysicalPieceOpen S K m,
      q p = K.height (C.referenceState, 0) m p / K.height z m (τ p) :=
    fun m p hp => (hpiece m p hp).2
  let R : PolarPoint → ℝ := n07bReferenceTransportRemainder D τ q u
  let η : PolarPoint → ℝ := fun p => R p + a * S.chiLeft p.1
  obtain ⟨hR, _, KR, hKR, hjet⟩ :=
    n07bReferenceTransportRemainder_regular hT hu (hγ.trans hγδ) hδβ
      hq hτ hmap hC₀.le hC₀.le hC₀.le hA hqjet hτjet hHratio hMratio
  have hRp : Function.Periodic R (0, Real.pi) :=
    n07bReferenceTransportRemainder_periodic hτp hqp hu.2.2.1
  have hRe : ∀ r θ, R (r, -θ) = R (r, θ) :=
    n07bReferenceTransportRemainder_even hτe hqe hu.2.1
  have hη : ContDiff ℝ 2 η :=
    hR.add (contDiff_const.mul ((hχ.1.comp contDiff_fst).of_le (by simp)))
  have hηp : Function.Periodic η (0, Real.pi) := by
    intro p
    simp only [η, hRp p, Prod.fst_add, add_zero]
  have hηe : ∀ r θ, η (r, -θ) = η (r, θ) := by
    intro r θ
    simp only [η, hRe r θ]
  have hηext : η = n07bReferenceTransportExtension D S τ q a u := by
    funext p
    change R p + a * S.chiLeft p.1 = a * S.chiLeft p.1 + R p
    ring
  have hprofile : RadialProfileGeometry D := hD.choose_spec.1
  have hrowη : referenceRow D η = 0 := by
    rw [hηext]
    exact (n07bReferenceTransportExtension_referenceRow hτpiece hqpiece hK
      hprofile.2.1.le hz hs a u).trans hrow
  have hgraph : ReferenceGraph D γ M₀ M₁ (η, μ)
      (n07bReferenceForcing D μ η, 0) :=
    n07b_referenceGraph_of_remainder_jets hD hT hborder hχ hγ hγδ hKR
      hR hRp hRe (fun x hx n hn => hjet n hn x hx) a μ M₀ M₁ hrowη
  have hRpiece : ∀ m, EqOn R (n07bReferencePieceRemainder C K z m u)
      (referencePhysicalPieceOpen S K m) :=
    n07bReferenceTransportRemainder_eqOn_piece hK hτpiece hqpiece u
  have hηrem : (fun p => η p - a * S.chiLeft p.1) = R := by
    funext p
    dsimp only [η]
    ring
  have huSmooth : ContDiff ℝ ∞ u :=
    (heightMember_contDiff_and_flatJets hT (by norm_num : 0 < (3 / 4 : ℝ)) hu).1
  refine ⟨τ, q, R, η, rfl, rfl, hR, hη, hRp, hRe, hηp, hηe, hRpiece, ?_, ?_, ?_, hgraph⟩
  · intro m
    rw [hηrem]
    exact n07b_canonicalHeight_eqOn_of_piece_remainder hK href hsref m u R (hRpiece m)
  · intro m
    exact n07bReferencePieceCanonicalSource_eqOn hK href hsref m u R (hRpiece m)
  · intro m p hp
    exact n07bReferencePieceCanonicalSource_contDiffAt_closed
      hK href hsref hz hs hprofile m huSmooth hp

end ContinuousFlexibility.Analysis
