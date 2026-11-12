import ContinuousFlexibility.Analysis.WholeCanonicalGlobalRegularity
import ContinuousFlexibility.Analysis.CanonicalWholeNegativeSymmetries

/-!
# Physical symmetries of the same globally selected relative fields

The radius selector only evaluates a negative field on its own closed
component and a positive field on its open component. Thus their actual
symmetries on those sets suffice, without any condition on arbitrary
totalized negative values elsewhere. The fallback is the identity/one.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

theorem n04WholeComponentField_equivariant_on_pieces
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {E : Type*} (Fneg : ℕ → PolarPoint → E)
    (Fpos : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → E)
    (fallback : PolarPoint → E) (σ : PolarPoint → PolarPoint) (Ψ : E → E)
    (hr : ∀ p, (σ p).1 = p.1)
    (hneg : ∀ m p, p.1 ∈ Icc (C.left m) (C.right m) → Fneg m (σ p) = Ψ (Fneg m p))
    (hpos : ∀ i p, p.1 ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i) →
      Fpos i (σ p) = Ψ (Fpos i p))
    (hfb : ∀ p, fallback (σ p) = Ψ (fallback p)) (p : PolarPoint) :
    n04WholeComponentField C Fneg Fpos fallback (σ p) =
      Ψ (n04WholeComponentField C Fneg Fpos fallback p) := by
  classical
  simp only [n04WholeComponentField, hr p]
  split_ifs with hn hp
  · exact hneg (Classical.choose hn) p (Classical.choose_spec hn)
  · exact hpos (Classical.choose hp) p (Classical.choose_spec hp)
  · exact hfb p

theorem n04WholeCanonical_global_relative_symmetries
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e : ℕ ≃ N04PieceIndex D) (n : ℕ)
    (j : ∀ i : N04PositiveComponent D.a D.b (deriv D.w),
      ∀ side, N04PositiveEndpointSource C i side)
    (τ σ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
    (Q : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
    (c d J H : N04PositiveComponent D.a D.b (deriv D.w) → ℝ)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1)
    (hm : ∀ i,
      let K := n04bActualTypedAtlas hT hS hN hfield e
      WholePositiveTransportMatching n
        (fun side => n04PositiveSourceMap (j i side) K z)
        (fun side => n04PositiveSourceHeight (j i side) K z)
        (τ i) (σ i) (Q i) (n04PositiveLeft i) (n04PositiveRight i)
        (c i) (d i) (J i) (H i)) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    let F := n04WholeComponentField C (canonicalWholeNegativeTransport C K z) τ id
    let q := n04WholeComponentField C (canonicalWholeNegativeHeightRatio C K z) Q
      (fun _ => (1 : ℝ))
    (∀ p, F (p + (0, Real.pi)) = F p + (0, Real.pi)) ∧
      Function.Periodic q (0, Real.pi) ∧
      (∀ p, F (p.1, -p.2) = ((F p).1, -(F p).2)) ∧
      ∀ r θ, q (r, -θ) = q (r, θ) := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  have hnegF (m : ℕ) (p : PolarPoint) (hp : p.1 ∈ Icc (C.left m) (C.right m)) :=
    canonicalWholeNegativeTransport_symmetries_closed hT hS hN hfield e hz hs m
      (p := p) ⟨hp, mem_univ _⟩
  have hnegQ (m : ℕ) (p : PolarPoint) (hp : p.1 ∈ Icc (C.left m) (C.right m)) :=
    canonicalWholeNegativeHeightRatio_symmetries_closed hT hS hN hfield e hz hs m
      (p := p) ⟨hp, mem_univ _⟩
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p
    exact n04WholeComponentField_equivariant_on_pieces
      (canonicalWholeNegativeTransport C K z) τ id
      (fun p => p + (0, Real.pi)) (fun p => p + (0, Real.pi))
      (fun p => by simp only [Prod.fst_add, add_zero])
      (fun m p hp => (hnegF m p hp).1)
      (fun i p _ => (hm i).geometry.period_add p) (fun _ => rfl) p
  · intro p
    exact n04WholeComponentField_equivariant_on_pieces
      (canonicalWholeNegativeHeightRatio C K z) Q (fun _ => (1 : ℝ))
      (fun p => p + (0, Real.pi)) id
      (fun p => by simp only [Prod.fst_add, add_zero])
      (fun m p hp => (hnegQ m p hp).1)
      (fun i p _ => by simpa only [Prod.mk_add_mk, add_zero, id_eq] using
        (hm i).height_period p.1 p.2) (fun _ => rfl) p
  · intro p
    exact n04WholeComponentField_equivariant_on_pieces
      (canonicalWholeNegativeTransport C K z) τ id
      (fun p => (p.1, -p.2)) (fun p => (p.1, -p.2)) (fun _ => rfl)
      (fun m p hp => (hnegF m p hp).2)
      (fun i p _ => (hm i).geometry.reflect p) (fun _ => rfl) p
  · intro r θ
    exact n04WholeComponentField_equivariant_on_pieces
      (canonicalWholeNegativeHeightRatio C K z) Q (fun _ => (1 : ℝ))
      (fun p => (p.1, -p.2)) id (fun _ => rfl)
      (fun m p hp => (hnegQ m p hp).2)
      (fun i p _ => (hm i).height_even p.1 p.2) (fun _ => rfl) (r, θ)

end ContinuousFlexibility.Analysis
