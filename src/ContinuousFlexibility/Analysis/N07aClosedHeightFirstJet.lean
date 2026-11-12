import ContinuousFlexibility.Analysis.N07aClosedChartDifferentials
import ContinuousFlexibility.Analysis.N07aReferenceClosedJetMatching

/-!
# The actual physical first jets and their primitive transport

The covectors are computed from the canonical closed jets and the actual
forward chart. They are derivatives within the genuine state-dependent
closures. Common reference first jets transfer through the invertible,
source-independent primitive transport to common current first jets.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open N07aClosedJets
open scoped ContDiff Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- The genuine first physical covector of the closed height remainder. -/
def n07aClosedPhysicalHeightGradient (K : CanonicalData S) (z : AnnularState S × ℝ)
    (m : ℕ) {v : PolarPoint → ℝ}
    (J : ClosedJetTower (K.left m) (K.right m) v) (p : PolarPoint) :
    PolarPoint →L[ℝ] ℝ :=
  K.height z m p •
      (scalarGradient (J.value 1 0 (K.chart z m p))
        (J.value 0 1 (K.chart z m p))).comp (fderiv ℝ (K.chart z m) p) +
    J.value 0 0 (K.chart z m p) • fderiv ℝ (K.height z m) p

theorem n07aClosedPhysicalHeight_hasFDerivWithinAt
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {v : PolarPoint → ℝ}
    (J : ClosedJetTower (K.left m) (K.right m) v)
    {p : PolarPoint} (hp : p ∈ physicalPieceClosed S K z m) :
    HasFDerivWithinAt (n07aClosedPhysicalHeight K z m J)
      (n07aClosedPhysicalHeightGradient K z m J p) (physicalPieceClosed S K z m) p := by
  have hb := h04.1.boundary z hz hs m
  have hfields := hb.2.2.2.2.1 p hp
  have hchart := (hfields.1.differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
  have hjet := (J.derivative 0 0 _ (hb.1 hp)).comp p hchart hb.1
  have hh := (hfields.2.1.differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
  exact hh.mul hjet

/-- Reference closed strips have unique differentiation, so their within
first derivative is precisely the computed physical covector. -/
theorem n07aClosedPhysicalHeight_reference_fderivWithin
    (h04 : N04Properties D T S C L K base loss ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    (m : ℕ) {v : PolarPoint → ℝ}
    (J : ClosedJetTower (K.left m) (K.right m) v)
    {p : PolarPoint} (hp : p ∈ closedStrip (K.physicalLeft m) (K.physicalRight m)) :
    fderivWithin ℝ (n07aClosedPhysicalHeight K (C.referenceState, 0) m J)
      (closedStrip (K.physicalLeft m) (K.physicalRight m)) p =
        n07aClosedPhysicalHeightGradient K (C.referenceState, 0) m J p := by
  have hp' : p ∈ physicalPieceClosed S K (C.referenceState, 0) m := by
    rwa [n07a_referencePhysicalPieceClosed h04 m]
  have hd := n07aClosedPhysicalHeight_hasFDerivWithinAt h04 href hsref m J hp'
  rw [n07a_referencePhysicalPieceClosed h04 m] at hd
  exact hd.fderivWithin
    (((uniqueDiffOn_Icc (h04.1.referenceBounds m).1).prod uniqueDiffOn_univ) p hp)

/-- The actual chart transition maps each reference closure into the
corresponding current closure. -/
theorem n07a_canonicalCurrentPoint_mapsTo_closed
    (h04 : N04Properties D T S C L K base loss ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ) :
    MapsTo (canonicalCurrentPoint C K z m)
      (physicalPieceClosed S K (C.referenceState, 0) m) (physicalPieceClosed S K z m) :=
  fun _ hp => (h04.1.boundary z hz hs m).2.1
    ((h04.1.boundary (C.referenceState, 0) href hsref m).1 hp)

/-- Exact value and first-covector transport, evaluated on the closed piece. -/
theorem n07aClosedPhysicalHeight_transition_firstJet
    (h04 : N04Properties D T S C L K base loss ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {v : PolarPoint → ℝ}
    (J : ClosedJetTower (K.left m) (K.right m) v)
    {p : PolarPoint} (hp : p ∈ physicalPieceClosed S K (C.referenceState, 0) m) :
    let Ti := canonicalCurrentPoint C K z m
    let ρi := fun x => K.height (C.referenceState, 0) m x / K.height z m (Ti x)
    n07aClosedPhysicalHeight K (C.referenceState, 0) m J p =
      ρi p * n07aClosedPhysicalHeight K z m J (Ti p) ∧
    n07aClosedPhysicalHeightGradient K (C.referenceState, 0) m J p =
      ρi p • (n07aClosedPhysicalHeightGradient K z m J (Ti p)).comp (fderiv ℝ Ti p) +
        n07aClosedPhysicalHeight K z m J (Ti p) • fderiv ℝ ρi p := by
  let Ti := canonicalCurrentPoint C K z m
  let ρi := fun x => K.height (C.referenceState, 0) m x / K.height z m (Ti x)
  have hmap := n07a_canonicalCurrentPoint_mapsTo_closed h04 href hsref hz hs m
  have hT := n07a_canonicalCurrentPoint_contDiffAt_closed h04 href hsref hz hs m hp
  have hBref := h04.1.boundary (C.referenceState, 0) href hsref m
  have hBcur := h04.1.boundary z hz hs m
  have hhi := hBref.2.2.2.2.1 p hp
  have hhc := hBcur.2.2.2.2.1 (Ti p) (hmap hp)
  have hρ : ContDiffAt ℝ ∞ ρi p :=
    hhi.2.1.div (hhc.2.1.comp p hT) hhc.2.2.2.ne'
  have he : EqOn (n07aClosedPhysicalHeight K (C.referenceState, 0) m J)
      (fun x => ρi x * n07aClosedPhysicalHeight K z m J (Ti x))
      (physicalPieceClosed S K (C.referenceState, 0) m) := by
    intro x hx
    have hFx := hBcur.2.2.2.1 (K.chart (C.referenceState, 0) m x) (hBref.1 hx)
    have hhx := (hBcur.2.2.2.2.1 (Ti x) (hmap hx)).2.2.2.ne'
    change K.height (C.referenceState, 0) m x * J.value 0 0
        (K.chart (C.referenceState, 0) m x) =
      (K.height (C.referenceState, 0) m x / K.height z m (Ti x)) *
        (K.height z m (Ti x) * J.value 0 0 (K.chart z m (Ti x)))
    change K.chart z m (Ti x) = K.chart (C.referenceState, 0) m x at hFx
    rw [hFx]
    field_simp [hhx]
  have hDcur := (n07aClosedPhysicalHeight_hasFDerivWithinAt h04 hz hs m J (hmap hp)).comp p
    (hT.differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt hmap
  have hDpull := ((hρ.differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt.mul hDcur).
    congr he (he hp)
  have hDref := n07aClosedPhysicalHeight_hasFDerivWithinAt h04 href hsref m J hp
  have hpcc : p ∈ closedStrip (K.physicalLeft m) (K.physicalRight m) := by
    rwa [← n07a_referencePhysicalPieceClosed h04 m]
  have hud : UniqueDiffWithinAt ℝ (physicalPieceClosed S K (C.referenceState, 0) m) p := by
    rw [n07a_referencePhysicalPieceClosed h04 m]
    exact ((uniqueDiffOn_Icc (h04.1.referenceBounds m).1).prod uniqueDiffOn_univ) p hpcc
  exact ⟨he hp, (hDref.fderivWithin hud).symm.trans (hDpull.fderivWithin hud)⟩

private theorem n07a_firstJet_transport_cancel
    {q w₀ w₁ r₀ r₁ : ℝ} {dq : PolarPoint →L[ℝ] ℝ}
    {A₀ A₁ B₀ B₁ : PolarPoint →L[ℝ] ℝ} {dτ : PolarPoint →L[ℝ] PolarPoint}
    (hq : q ≠ 0) (hτ : Function.Surjective dτ)
    (hr₀ : r₀ = q * w₀) (hr₁ : r₁ = q * w₁)
    (hA₀ : A₀ = q • B₀.comp dτ + w₀ • dq)
    (hA₁ : A₁ = q • B₁.comp dτ + w₁ • dq)
    (hr : r₀ = r₁) (hA : A₀ = A₁) : w₀ = w₁ ∧ B₀ = B₁ := by
  have hw : w₀ = w₁ := mul_left_cancel₀ hq (hr₀.symm.trans (hr.trans hr₁))
  refine ⟨hw, ?_⟩
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨t, ht⟩ := hτ v
  have he := congrArg (fun A : PolarPoint →L[ℝ] ℝ => A t) hA
  rw [hA₀, hA₁] at he
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul, hw, ht] at he
  exact mul_left_cancel₀ hq (add_right_cancel he)

/-- Equal reference value and first jets imply equal actual current jets
at their common image under the primitive transport. -/
theorem n07aClosedPhysicalHeight_current_firstJets
    (h04 : N04Properties D T S C L K base loss ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {τ : PolarPoint → PolarPoint} {q : PolarPoint → ℝ}
    (hτ : ContDiffOn ℝ 3 τ (annularOpen D))
    (hq : ContDiffOn ℝ 3 q (annularOpen D))
    (hpiece : ∀ m, ∀ p ∈ referencePhysicalPieceOpen S K m,
      τ p = canonicalCurrentPoint C K z m p ∧
        q p = K.height (C.referenceState, 0) m p / K.height z m (τ p))
    (i j : ℕ) {vi vj : PolarPoint → ℝ}
    (Ji : ClosedJetTower (K.left i) (K.right i) vi)
    (Jj : ClosedJetTower (K.left j) (K.right j) vj)
    {p : PolarPoint}
    (hpi : p ∈ physicalPieceClosed S K (C.referenceState, 0) i)
    (hpj : p ∈ physicalPieceClosed S K (C.referenceState, 0) j)
    (hpD : p ∈ annularOpen D)
    (hvalue : n07aClosedPhysicalHeight K (C.referenceState, 0) i Ji p =
      n07aClosedPhysicalHeight K (C.referenceState, 0) j Jj p)
    (hfirst : n07aClosedPhysicalHeightGradient K (C.referenceState, 0) i Ji p =
      n07aClosedPhysicalHeightGradient K (C.referenceState, 0) j Jj p) :
    n07aClosedPhysicalHeight K z i Ji (τ p) = n07aClosedPhysicalHeight K z j Jj (τ p) ∧
      n07aClosedPhysicalHeightGradient K z i Ji (τ p) =
        n07aClosedPhysicalHeightGradient K z j Jj (τ p) := by
  have hi := n07a_primitiveTransport_closed_firstJet h04 href hsref hz hs hτ hq hpiece i hpi hpD
  have hj := n07a_primitiveTransport_closed_firstJet h04 href hsref hz hs hτ hq hpiece j hpj hpD
  have hTi := n07aClosedPhysicalHeight_transition_firstJet h04 href hsref hz hs i Ji hpi
  have hTj := n07aClosedPhysicalHeight_transition_firstJet h04 href hsref hz hs j Jj hpj
  rw [← hi.2.1.1, ← hi.2.1.2, ← hi.1.1, ← hi.1.2] at hTi
  rw [← hj.2.1.1, ← hj.2.1.2, ← hj.1.1, ← hj.1.2] at hTj
  exact n07a_firstJet_transport_cancel hi.2.2.1 hi.2.2.2
    hTi.1 hTj.1 hTi.2 hTj.2 hvalue hfirst

end ContinuousFlexibility.Analysis
