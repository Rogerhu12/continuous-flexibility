import ContinuousFlexibility.Analysis.CanonicalPositiveAmbientSource
import ContinuousFlexibility.Analysis.WholePositiveAmbientRadialIdentity
import ContinuousFlexibility.Analysis.WholeComponentMaterialRatios
import ContinuousFlexibility.Analysis.CanonicalWholePositiveTransport

/-!
# Material ratios for the same actual one-sided positive construction

The existing matching certificate supplies the actual geometry and root
values. Ambient identities follow from the certified actual source, and
the numerical widths follow from their displayed formulas. No factory
is called again: the original M_sigma, angular interpolation, height,
inverse and every finite matching jet are retained. The arbitrary exits
can include the separately constructed normalization buffer.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem endpointFiberWidths_positive_gap
    (n : ℕ) {l r c d κ M : ℝ}
    (hlc : l < c) (hdr : d < r) (hκ : 0 < κ) (hM : 0 ≤ M) (side : Bool) :
    0 < endpointFiberWidths n l r c d κ M side ∧
      2 * endpointFiberWidths n l r c d κ M side <
        (if side then r else c) - (if side then d else l) := by
  have hspan : 0 < (if side then r else c) - (if side then d else l) := by
    cases side with
    | false => exact sub_pos.mpr hlc
    | true => exact sub_pos.mpr hdr
  have h := prescribedEndpointWidth_margins n
    (span := (if side then r else c) - (if side then d else l))
    (ρ := 1) (κ := κ) (M := M)
    (Mslope := max (M + ((n + 1 : ℕ) : ℝ) * M) 1)
    (m := (if side then r else c) - (if side then d else l))
    hspan zero_lt_one hκ hM (zero_le_one.trans (le_max_right _ _)) hspan
  exact ⟨h.1, h.2.2.2.1⟩

theorem WholePositiveTransportMatching.root_radial
    {n : ℕ} {F : Bool → PolarPoint → PolarPoint} {q : Bool → PolarPoint → ℝ}
    {τ σ : PolarPoint → PolarPoint} {Q : PolarPoint → ℝ} {l r c d J H : ℝ}
    (h : WholePositiveTransportMatching n F q τ σ Q l r c d J H)
    (hF : ∀ side θ, (F side (if side then r else l, θ)).1 = if side then r else l) :
    ∀ side θ, (τ (if side then r else l, θ)).1 = if side then r else l := by
  intro side θ
  have he := congrArg
    (fun A : PolarPoint [×0]→L[ℝ] PolarPoint => A (fun i => Fin.elim0 i))
    (h.coordinate_jets side 0 (Nat.zero_le _) θ)
  have hvalue : τ (if side then r else l, θ) = F side (if side then r else l, θ) := by
    simpa only [iteratedFDeriv_zero_apply] using he
  exact (congrArg Prod.fst hvalue).trans (hF side θ)

theorem canonicalWholePositiveTransport_material_ratios
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε) (e : ℕ ≃ N04PieceIndex D) :
    ∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧ ∀ (n : ℕ)
      (i : N04PositiveComponent D.a D.b (deriv D.w))
      (j : ∀ side, N04PositiveEndpointSource C i side)
      (c d κφ κX M Mσ J H : ℝ) (Q : PolarPoint → ℝ),
      let l := n04PositiveLeft i
      let r := n04PositiveRight i
      l < c → c < d → d < r →
      (l ≠ D.a → c - l ≤ Statements.endpointDistance D l / 2) →
      (r ≠ D.b → r - d ≤ Statements.endpointDistance D r / 2) →
      0 < κX → 0 ≤ Mσ →
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      let K := n04bActualTypedAtlas hT hS hN hfield e
      let F := fun side => n04PositiveSourceMap (j side) K z
      let q := fun side => n04PositiveSourceHeight (j side) K z
      let ψ := fun side p => (F side p).2
      let X := fun side p => (F side p).1
      let τ := oneSidedWholeComponentTransport n ψ X l r c d κφ κX M Mσ
      let σ := oneSidedWholeComponentTransportInverse n ψ X l r c d κφ κX M Mσ
      WholePositiveTransportMatching n F q τ σ Q l r c d J H →
      ∀ p ∈ Ioo l r ×ˢ (univ : Set ℝ),
        T.H (τ p).1 / T.H p.1 ≤ B * T.E0 p.1 ^ A ∧
          T.M (τ p).1 / T.M p.1 ≤ B * T.E0 p.1 ^ A := by
  obtain ⟨B, A, hB, hA, hweights⟩ :=
    wholeComponentTransport_material_ratios_of_capped_collars hT hN.1.1.1.1
  refine ⟨B, A, hB, hA, ?_⟩
  intro n i j c d κφ κX M Mσ J H Q
  dsimp only
  intro hlc hcd hdr hcapL hcapR hκX hMσ z hz hs hm
  let K := n04bActualTypedAtlas hT hS hN hfield e
  let l := n04PositiveLeft i
  let r := n04PositiveRight i
  let F : Bool → PolarPoint → PolarPoint := fun side => n04PositiveSourceMap (j side) K z
  let ψ : Bool → PolarPoint → ℝ := fun side p => (F side p).2
  let X : Bool → PolarPoint → ℝ := fun side p => (F side p).1
  let τ := oneSidedWholeComponentTransport n ψ X l r c d κφ κX M Mσ
  have hG := n04b_profileGeometry_of_through03 hN
  have hf : Continuous (deriv D.w) := hG.2.2.1.1.continuous_deriv (by simp)
  have hends := n04PositiveComponent_bounds hf i
  have hsource (side : Bool) (θ : ℝ) :
      (F side (if side then r else l, θ)).1 = if side then r else l :=
    (n04Coordinates_actualAtlas_positiveEndpoint_of_source
      hT hS hN hfield e (j side) hz hs).root_radial θ
  have hη (side : Bool) := endpointFiberWidths_positive_gap n
    (l := l) (r := r) (c := c) (d := d) (κ := κX) (M := Mσ) hlc hdr hκX hMσ side
  have hambient (side : Bool)
      (hroot : (if side then r else l) = (if side then D.b else D.a))
      (p : PolarPoint)
      (hp : p ∈ Icc (if side then d else l) (if side then r else c) ×ˢ (univ : Set ℝ)) :
      (τ p).1 = p.1 := by
    have hid : F side = (id : PolarPoint → PolarPoint) :=
      (n04PositiveSource_ambient_fields hN.1.1.2.2.2.1 (j side) hroot K z).1
    have hX : ∀ θ, X side =ᶠ[𝓝 (if side then r else l, θ)]
        (Prod.fst : PolarPoint → ℝ) := by
      intro θ
      change (fun q => (F side q).1) =ᶠ[𝓝 (if side then r else l, θ)] Prod.fst
      rw [hid]
      exact Filter.EventuallyEq.rfl
    apply oneSidedWholeComponentTransport_radial_eq_of_side_germ
      (ψ := ψ) (X := X) (κφ := κφ) (κX := κX) (M := M) (Mσ := Mσ)
      n hcd side hX (hη side).1 (hη side).2 p
    cases side with
    | false => exact hp.1.2
    | true => exact hp.1.1
  exact hweights hends.1 hlc hcd hdr hends.2.2 hm.geometry
    (hm.root_radial hsource) hcapL hcapR hambient

end ContinuousFlexibility.Analysis
