import ContinuousFlexibility.Analysis.N05CanonicalSourceLift
import ContinuousFlexibility.Analysis.N05ReferenceNormalizerJets
import ContinuousFlexibility.Geometry.EuclideanRigidity
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# Angular transport through the actual reference coordinates

The genuine source multiplier, with radial zero extension, commutes with
every angular derivative. Canonical compact tests pull back to actual
physical tests. Their angular jets therefore satisfy the full-period weak
identity and belong to every fixed reference source weight.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators
open ContinuousFlexibility.Radial

def n05CanonicalAngularTransport (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S) (m : ℕ)
    (φ : PolarPoint → ℝ) : PolarPoint → ℝ := by
  classical
  exact fun p => if p.1 ∈ Ioo (K.physicalLeft m) (K.physicalRight m) then
    |deriv (fun r => (K.chart (C.referenceState, 0) m (r, 0)).1) p.1| /
      K.height (C.referenceState, 0) m (p.1, 0) *
        φ ((K.chart (C.referenceState, 0) m (p.1, 0)).1, p.2)
    else 0

theorem n05CanonicalAngularTransport_angular (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S) (m : ℕ)
    (φ : PolarPoint → ℝ) (j : ℕ) (p : PolarPoint) :
    mixedDerivative 0 j (n05CanonicalAngularTransport S C K m φ) p =
      n05CanonicalAngularTransport S C K m (mixedDerivative 0 j φ) p := by
  classical
  simp only [mixedDerivative, iteratedDeriv_zero]
  by_cases hr : p.1 ∈ Ioo (K.physicalLeft m) (K.physicalRight m)
  · simp only [n05CanonicalAngularTransport, if_pos hr, iteratedDeriv_const_mul_field]
  · simp only [n05CanonicalAngularTransport, if_neg hr, iteratedDeriv_const_zero]

theorem n05CanonicalAngularTransport_periodic (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S) (m : ℕ)
    {φ : PolarPoint → ℝ} (hφ : Function.Periodic φ (0, Real.pi)) :
    Function.Periodic (n05CanonicalAngularTransport S C K m φ) (0, Real.pi) := by
  classical
  intro p
  have hp := hφ ((K.chart (C.referenceState, 0) m (p.1, 0)).1, p.2)
  simp only [Prod.mk_add_mk, add_zero] at hp
  simp only [n05CanonicalAngularTransport, Prod.fst_add, Prod.snd_add, add_zero, hp]

theorem n05CanonicalAngularTransport_periodic_two_pi (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S) (m : ℕ)
    {φ : PolarPoint → ℝ} (hφ : Function.Periodic φ (0, Real.pi)) :
    Function.Periodic (n05CanonicalAngularTransport S C K m φ) (0, 2 * Real.pi) := by
  intro p
  have hp := n05CanonicalAngularTransport_periodic S C K m hφ
  have he : p + ((0, 2 * Real.pi) : PolarPoint) =
      (p + (0, Real.pi)) + (0, Real.pi) := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, add_zero] <;> ring
  rw [he, hp, hp]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
  (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
  (hcoordinates : N05ControlledReferenceCoordinates D S C K)

include h hcoordinates in
theorem n05CanonicalAngularTransport_eq_actual (m : ℕ) (φ : PolarPoint → ℝ)
    {p : PolarPoint} (hp : p ∈ physicalPieceOpen S K m) :
    n05CanonicalAngularTransport S C K m φ p =
      |planeJacobian (K.chart (C.referenceState, 0) m) p| /
        K.height (C.referenceState, 0) m p * φ (K.chart (C.referenceState, 0) m p) := by
  classical
  simp only [n05CanonicalAngularTransport, if_pos hp.1,
    n05_reference_planeJacobian_radial h hcoordinates m hp,
    (hcoordinates.1 m p hp).1, (hcoordinates.1 m p hp).2]

include h hcoordinates in
/-- The actual inverse image of the canonical radial support is compact
inside the physical piece; no properness assumption is added. -/
theorem n05CanonicalAngularTransport_compact_support (m : ℕ)
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) :
    ∃ J : Set ℝ, IsCompact J ∧ J ⊆ Ioo (K.physicalLeft m) (K.physicalRight m) ∧
      ∀ r, r ∉ J → ∀ θ, n05CanonicalAngularTransport S C K m φ (r, θ) = 0 := by
  classical
  obtain ⟨J, hJ, hJI, hzero⟩ := hφ.2.2
  have hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    n05_referenceState_mem h.1.1.1.2.1
  have hs : stateSector S C.referenceState := n05_referenceState_sector h.1.1.1.2.2.1
  rcases h.2.2.2.2 with ⟨_, _, _, _, _, _, _, hcharts, _⟩
  obtain ⟨_, hΨ, hleft, _, _, hΨc, _, _⟩ := hcharts (C.referenceState, 0) hz hs m
  let ρ : ℝ → ℝ := fun x => (K.inverseChart (C.referenceState, 0) m (x, 0)).1
  have hρ : ContinuousOn ρ J :=
    (hΨc.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun x hx => ⟨hJI hx, mem_univ (0 : ℝ)⟩)).fst
  refine ⟨ρ '' J, hJ.image_of_continuousOn hρ, ?_, ?_⟩
  · rintro r ⟨x, hx, rfl⟩
    exact (hΨ ⟨hJI hx, mem_univ (0 : ℝ)⟩).1
  · intro r hr θ
    by_cases hri : r ∈ Ioo (K.physicalLeft m) (K.physicalRight m)
    · have hξ : (K.chart (C.referenceState, 0) m (r, 0)).1 ∉ J := by
        intro hx
        apply hr
        refine ⟨(K.chart (C.referenceState, 0) m (r, 0)).1, hx, ?_⟩
        have hp : (r, (0 : ℝ)) ∈ physicalPieceOpen S K m := ⟨hri, mem_univ _⟩
        have he := congrArg (fun q : PolarPoint => q.1) (hleft (r, 0) hp)
        simpa only [(hcoordinates.1 m (r, 0) hp).1] using he
      simp only [n05CanonicalAngularTransport, if_pos hri, hzero _ hξ θ, mul_zero]
    · simp only [n05CanonicalAngularTransport, if_neg hri]

include h hcoordinates in
/-- The same multiplier is a legitimate physical test pullback. -/
theorem n05CanonicalAngularTransport_test (m : ℕ)
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) :
    RadialTest D (n05CanonicalAngularTransport S C K m φ) := by
  obtain ⟨J, hJ, hJI, hzero⟩ :=
    n05CanonicalAngularTransport_compact_support h hcoordinates m hφ
  have hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    n05_referenceState_mem h.1.1.1.2.1
  have hs : stateSector S C.referenceState := n05_referenceState_sector h.1.1.1.2.2.1
  have h04 := h.2.2.2.2
  rcases h04 with ⟨_, _, _, hpieces, _, _, _, hcharts, _⟩
  obtain ⟨_, _, _, _, hc, _, hh, hn⟩ := hcharts (C.referenceState, 0) hz hs m
  have hd : ContDiff ℝ ∞ (n05CanonicalAngularTransport S C K m φ) := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    by_cases hp : p ∈ physicalPieceOpen S K m
    · have hnear := (isOpen_Ioo.prod isOpen_univ).mem_nhds hp
      have hca := hc.contDiffAt hnear
      have hha := hh.contDiffAt hnear
      have hactual : ContDiffAt ℝ ∞ (fun q =>
          |planeJacobian (K.chart (C.referenceState, 0) m) q| /
            K.height (C.referenceState, 0) m q * φ (K.chart (C.referenceState, 0) m q)) p :=
        (((contDiffAt_planeJacobian hca).abs (hn p hp).2.1).div hha
          (hn p hp).1.ne').mul (hφ.1.contDiffAt.comp p hca)
      apply hactual.congr_of_eventuallyEq
      filter_upwards [hnear] with q hq
      exact n05CanonicalAngularTransport_eq_actual h hcoordinates m φ hq
    · have hpJ : p.1 ∉ J := fun hj => hp ⟨hJI hj, mem_univ _⟩
      have hnear : ∀ᶠ q : PolarPoint in 𝓝 p, q.1 ∉ J :=
        (hJ.isClosed.isOpen_compl.preimage continuous_fst).mem_nhds hpJ
      apply contDiffAt_const.congr_of_eventuallyEq
      filter_upwards [hnear] with q hq
      exact hzero q.1 hq q.2
  exact ⟨hd, n05CanonicalAngularTransport_periodic_two_pi S C K m hφ.2.1,
    J, hJ, fun r hr => (hpieces m).2.2 (hJI hr), hzero⟩

include h hcoordinates in
/-- Every angular order uses the same preassigned material exponent. -/
theorem n05CanonicalAngularTransport_sourceDerivativeMember
    (hD : IsAccumulatingProfile D) (m : ℕ)
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) (γ M : ℝ) (j : ℕ) :
    SourceDerivativeMember D γ M
      (n05CanonicalAngularTransport S C K m (mixedDerivative 0 j φ)) := by
  have ht := n05CanonicalAngularTransport_test h hcoordinates m hφ
  obtain ⟨J, hJ, hJI, hzero⟩ := n05_angularJet_compact_radial_support (D := D) ht.2.2 j
  have hj := r11b_compact_sourceDerivativeMember hD hJ hJI
    (contDiff_mixedDerivative ht.1 0 j).continuous (fun r _ hr => hzero r hr) γ M
  have he : mixedDerivative 0 j (n05CanonicalAngularTransport S C K m φ) =
      n05CanonicalAngularTransport S C K m (mixedDerivative 0 j φ) :=
    funext (n05CanonicalAngularTransport_angular S C K m φ j)
  rw [he] at hj
  exact hj

include h hcoordinates in
/-- The identity uses all genuine 2π-periodic physical tests. -/
theorem n05CanonicalAngularTransport_weak (m : ℕ)
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) (j : ℕ) :
    n05_weakReferenceAngularJet D (n05CanonicalAngularTransport S C K m φ)
      (n05CanonicalAngularTransport S C K m (mixedDerivative 0 j φ)) j := by
  have ht := n05CanonicalAngularTransport_test h hcoordinates m hφ
  have hw := n05_referenceAngularJet_weak_of_smooth_slices D
    (n05CanonicalAngularTransport S C K m φ)
    (fun r => ht.1.comp (contDiff_const.prodMk contDiff_id))
    (fun r θ => by simpa only [Prod.mk_add_mk, add_zero] using ht.2.1 (r, θ)) j
  have he : mixedDerivative 0 j (n05CanonicalAngularTransport S C K m φ) =
      n05CanonicalAngularTransport S C K m (mixedDerivative 0 j φ) :=
    funext (n05CanonicalAngularTransport_angular S C K m φ j)
  rw [he] at hw
  exact hw

include h hcoordinates in
theorem n05CanonicalAngularTransport_finite_weak (q : Finset ℕ)
    (φ : ℕ → PolarPoint → ℝ) (hφ : ∀ m ∈ q, CanonicalTest S K m (φ m)) (j : ℕ) :
    n05_weakReferenceAngularJet D
      (fun p => ∑ m ∈ q, n05CanonicalAngularTransport S C K m (φ m) p)
      (fun p => ∑ m ∈ q,
        n05CanonicalAngularTransport S C K m (mixedDerivative 0 j (φ m)) p) j := by
  have ht (m : ℕ) (hm : m ∈ q) :=
    n05CanonicalAngularTransport_test h hcoordinates m (hφ m hm)
  have hd : ContDiff ℝ ∞
      (fun p => ∑ m ∈ q, n05CanonicalAngularTransport S C K m (φ m) p) :=
    ContDiff.sum (fun m hm => (ht m hm).1)
  have hp : Function.Periodic
      (fun p => ∑ m ∈ q, n05CanonicalAngularTransport S C K m (φ m) p)
      (0, 2 * Real.pi) := by
    intro p
    exact Finset.sum_congr rfl (fun m hm => (ht m hm).2.1 p)
  have hw := n05_referenceAngularJet_weak_of_smooth_slices D
    (fun p => ∑ m ∈ q, n05CanonicalAngularTransport S C K m (φ m) p)
    (fun r => hd.comp (contDiff_const.prodMk contDiff_id))
    (fun r θ => by simpa only [Prod.mk_add_mk, add_zero] using hp (r, θ)) j
  have he : mixedDerivative 0 j
      (fun p => ∑ m ∈ q, n05CanonicalAngularTransport S C K m (φ m) p) =
      fun p => ∑ m ∈ q,
        n05CanonicalAngularTransport S C K m (mixedDerivative 0 j (φ m)) p := by
    funext p
    rw [spaces_mixedDerivative_sum (fun m hm => (ht m hm).1)]
    exact Finset.sum_congr rfl (fun m _ => n05CanonicalAngularTransport_angular S C K m (φ m) j p)
  rw [he] at hw
  exact hw

end ContinuousFlexibility.Statements
