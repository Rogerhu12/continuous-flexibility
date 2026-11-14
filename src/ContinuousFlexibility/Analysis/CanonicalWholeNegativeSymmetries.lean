module

public import ContinuousFlexibility.Analysis.CanonicalWholeNegativeTransport
public import ContinuousFlexibility.Analysis.CanonicalNegativeTravelSymmetries

/-!
# The true closed negative transport has the physical symmetries

The stored whole-component map and height agree with the actual travel
formulas in the open component and are ordinarily smooth at both roots.
Continuity extends their actual periodicity and reflection to those roots.
No value of the totalized travel inverse at a root is used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

private theorem equivariance_on_closed_strip_of_open
    {E : Type*} [TopologicalSpace E] [T2Space E] {a b : ℝ}
    (hab : a < b) (F : PolarPoint → E)
    (σ : PolarPoint → PolarPoint) (Ψ : E → E)
    (hr : ∀ p, (σ p).1 = p.1) (hσ : Continuous σ) (hΨ : Continuous Ψ)
    (hF : ∀ p, p.1 ∈ Icc a b → ContinuousAt F p)
    (he : ∀ p, p.1 ∈ Ioo a b → F (σ p) = Ψ (F p))
    {p : PolarPoint} (hp : p.1 ∈ Icc a b) : F (σ p) = Ψ (F p) := by
  let U : Set PolarPoint := Ioo a b ×ˢ (univ : Set ℝ)
  have hpU : p ∈ closure U := by
    simpa only [U, closure_prod_eq, closure_Ioo hab.ne, closure_univ] using
      (show p ∈ Icc a b ×ˢ (univ : Set ℝ) from ⟨hp, mem_univ _⟩)
  haveI : NeBot (𝓝[U] p) := mem_closure_iff_nhdsWithin_neBot.mp hpU
  have hs : (σ p).1 ∈ Icc a b := by simpa only [hr p] using hp
  have hleft : ContinuousAt (F ∘ σ) p := (hF (σ p) hs).comp hσ.continuousAt
  have hright : ContinuousAt (Ψ ∘ F) p := hΨ.continuousAt.comp (hF p hp)
  have hnear : (F ∘ σ) =ᶠ[𝓝[U] p] (Ψ ∘ F) := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact he q hq.1
  exact tendsto_nhds_unique_of_eventuallyEq
    (hleft.mono_left nhdsWithin_le_nhds) (hright.mono_left nhdsWithin_le_nhds) hnear

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
  (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
  (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
  (hfield : N04bFieldRegularity D S C L base ε) (e : ℕ ≃ N04PieceIndex D)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hs : stateSector S z.1) (m : ℕ)

include hT hS hN hfield e hz hs

theorem canonicalWholeNegativeTransport_symmetries_closed
    {p : PolarPoint} (hp : p ∈ Icc (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    canonicalWholeNegativeTransport C K z m (p + (0, Real.pi)) =
        canonicalWholeNegativeTransport C K z m p + (0, Real.pi) ∧
      canonicalWholeNegativeTransport C K z m (p.1, -p.2) =
        ((canonicalWholeNegativeTransport C K z m p).1,
          -(canonicalWholeNegativeTransport C K z m p).2) := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  let τ : PolarPoint → PolarPoint := canonicalWholeNegativeTransport C K z m
  have hab : C.left m < C.right m := (hN.1.1.2.2.2.1.1 m).2.1
  have hτ (q : PolarPoint) (hq : q.1 ∈ Icc (C.left m) (C.right m)) :
      ContinuousAt τ q :=
    (canonicalWholeNegativeTransport_closed_regular hT hS hN hfield e hz hs m
      ⟨hq, mem_univ _⟩).1.continuousAt
  have he : EqOn τ (n04CoordinatesNegativeTravelTransition S C L z m)
      (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :=
    (canonicalWholeNegativeTransport_eq_travel hT hS hN hfield e hz hs m).1
  constructor
  · refine equivariance_on_closed_strip_of_open hab τ
      (fun q => q + (0, Real.pi)) (fun q => q + (0, Real.pi))
      (fun q => by simp only [Prod.fst_add, add_zero])
      (continuous_id.add continuous_const) (continuous_id.add continuous_const) hτ ?_ (p := p) hp.1
    intro q hq
    have hqU : q ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) := ⟨hq, mem_univ _⟩
    have hqS : q + (0, Real.pi) ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) :=
      ⟨by simpa only [Prod.fst_add, add_zero] using hq, mem_univ _⟩
    rw [he hqS, he hqU]
    exact (n04CoordinatesNegativeTravelTransition_symmetries hT hS hN hfield hz hs m hqU).1
  · refine equivariance_on_closed_strip_of_open hab τ
      (fun q => (q.1, -q.2)) (fun q => (q.1, -q.2)) (fun _ => rfl)
      (continuous_fst.prodMk continuous_snd.neg) (continuous_fst.prodMk continuous_snd.neg)
      hτ ?_ (p := p) hp.1
    intro q hq
    have hqU : q ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) := ⟨hq, mem_univ _⟩
    have hqR : (q.1, -q.2) ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) :=
      ⟨hq, mem_univ _⟩
    rw [he hqR, he hqU]
    exact (n04CoordinatesNegativeTravelTransition_symmetries hT hS hN hfield hz hs m hqU).2

theorem canonicalWholeNegativeHeightRatio_symmetries_closed
    {p : PolarPoint} (hp : p ∈ Icc (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    canonicalWholeNegativeHeightRatio C K z m (p + (0, Real.pi)) =
        canonicalWholeNegativeHeightRatio C K z m p ∧
      canonicalWholeNegativeHeightRatio C K z m (p.1, -p.2) =
        canonicalWholeNegativeHeightRatio C K z m p := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  let Q : PolarPoint → ℝ := canonicalWholeNegativeHeightRatio C K z m
  have hab : C.left m < C.right m := (hN.1.1.2.2.2.1.1 m).2.1
  have hQ (q : PolarPoint) (hq : q.1 ∈ Icc (C.left m) (C.right m)) :
      ContinuousAt Q q :=
    (canonicalWholeNegativeTransport_closed_regular hT hS hN hfield e hz hs m
      ⟨hq, mem_univ _⟩).2.1.continuousAt
  have he : EqOn Q (n04CoordinatesNegativeTravelHeightRatio S C L z m)
      (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :=
    (canonicalWholeNegativeTransport_eq_travel hT hS hN hfield e hz hs m).2
  constructor
  · refine equivariance_on_closed_strip_of_open hab Q (fun q => q + (0, Real.pi)) id
      (fun q => by simp only [Prod.fst_add, add_zero])
      (continuous_id.add continuous_const) continuous_id hQ ?_ (p := p) hp.1
    intro q hq
    have hqU : q ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) := ⟨hq, mem_univ _⟩
    have hqS : q + (0, Real.pi) ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) :=
      ⟨by simpa only [Prod.fst_add, add_zero] using hq, mem_univ _⟩
    rw [he hqS, he hqU]
    exact (n04CoordinatesNegativeTravelHeightRatio_symmetries hT hS hN hfield hz hs m hqU).1
  · refine equivariance_on_closed_strip_of_open hab Q (fun q => (q.1, -q.2)) id
      (fun _ => rfl) (continuous_fst.prodMk continuous_snd.neg) continuous_id hQ ?_ (p := p) hp.1
    intro q hq
    have hqU : q ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) := ⟨hq, mem_univ _⟩
    have hqR : (q.1, -q.2) ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) :=
      ⟨hq, mem_univ _⟩
    rw [he hqR, he hqU]
    exact (n04CoordinatesNegativeTravelHeightRatio_symmetries hT hS hN hfield hz hs m hqU).2

end ContinuousFlexibility.Analysis
