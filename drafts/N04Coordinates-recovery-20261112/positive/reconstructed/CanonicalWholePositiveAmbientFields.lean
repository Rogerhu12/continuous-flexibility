import ContinuousFlexibility.Analysis.WholePositiveAmbientIdentity
import ContinuousFlexibility.Analysis.CanonicalPositiveAmbientSource

/-!
# Ambient identity for the same actual positive interpolation

The certified endpoint source is necessarily the identity/one source at
an ambient endpoint. The displayed widths, the actual interpolation and
its existing inverse certificate therefore give identity on that whole
side of the middle, and genuine ordinary germs of all four fields.
No value or smoothness of a totalized physical coefficient is used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem n04PositiveSource_ambient_interpolation_fields
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hC : controlGeometryConditions D S C) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (n : ℕ)
    {i : N04PositiveComponent D.a D.b (deriv D.w)}
    (j : ∀ side, N04PositiveEndpointSource C i side)
    {c d κφ κX M Mσ δ J H : ℝ}
    (hlc : n04PositiveLeft i < c) (hcd : c < d) (hdr : d < n04PositiveRight i)
    (hκφ : 0 < κφ) (hκX : 0 < κX) (hM : 0 ≤ M) (hMσ : 0 ≤ Mσ)
    (hδ : 0 < δ)
    (hδρ : δ ≤ min ((n04PositiveRight i - n04PositiveLeft i) / 4)
      (min (c - n04PositiveLeft i) (n04PositiveRight i - d))) :
    let l := n04PositiveLeft i
    let r := n04PositiveRight i
    let F := fun side => n04PositiveSourceMap (j side) K z
    let q := fun side => n04PositiveSourceHeight (j side) K z
    let ψ := fun side p => (F side p).2
    let X := fun side p => (F side p).1
    let τ := oneSidedWholeComponentTransport n ψ X l r c d κφ κX M Mσ
    let σ := oneSidedWholeComponentTransportInverse n ψ X l r c d κφ κX M Mσ
    let Q := positiveHeightTaylorInterpolation n l r δ (fun _ => 1) q
    WholePositiveTransportMatching n F q τ σ Q l r c d J H →
    ∀ side, n04PositiveEndpoint i side = (if side then D.b else D.a) →
      (∀ p : PolarPoint, (if side then d ≤ p.1 else p.1 ≤ c) →
        τ p = p ∧ σ p = p ∧ Q p = 1 ∧ wholePositiveChartHeight σ Q p = 1) ∧
      ∀ θ,
        τ =ᶠ[𝓝 (n04PositiveEndpoint i side, θ)] (id : PolarPoint → PolarPoint) ∧
        σ =ᶠ[𝓝 (n04PositiveEndpoint i side, θ)] (id : PolarPoint → PolarPoint) ∧
        Q =ᶠ[𝓝 (n04PositiveEndpoint i side, θ)] (fun _ => (1 : ℝ)) ∧
        wholePositiveChartHeight σ Q =ᶠ[𝓝 (n04PositiveEndpoint i side, θ)]
          (fun _ => (1 : ℝ)) := by
  dsimp only
  intro hm side hroot
  let l := n04PositiveLeft i
  let r := n04PositiveRight i
  let F := fun side => n04PositiveSourceMap (j side) K z
  let q := fun side => n04PositiveSourceHeight (j side) K z
  let ψ : Bool → PolarPoint → ℝ := fun side p => (F side p).2
  let X : Bool → PolarPoint → ℝ := fun side p => (F side p).1
  let τ := oneSidedWholeComponentTransport n ψ X l r c d κφ κX M Mσ
  let σ := oneSidedWholeComponentTransportInverse n ψ X l r c d κφ κX M Mσ
  let Q := positiveHeightTaylorInterpolation n l r δ (fun _ => 1) q
  have hsource := n04PositiveSource_ambient_fields hC (j side) hroot K z
  have hψ : ∀ θ, ψ side =ᶠ[𝓝 (if side then r else l, θ)]
      (Prod.snd : PolarPoint → ℝ) := by
    intro θ
    have he : ψ side = (Prod.snd : PolarPoint → ℝ) := by
      funext p
      exact congrArg Prod.snd (congrFun hsource.1 p)
    exact Filter.EventuallyEq.of_eq he
  have hX : ∀ θ, X side =ᶠ[𝓝 (if side then r else l, θ)]
      (Prod.fst : PolarPoint → ℝ) := by
    intro θ
    have he : X side = (Prod.fst : PolarPoint → ℝ) := by
      funext p
      exact congrArg Prod.fst (congrFun hsource.1 p)
    exact Filter.EventuallyEq.of_eq he
  have hq : ∀ θ, q side =ᶠ[𝓝 (if side then r else l, θ)] (fun _ => (1 : ℝ)) :=
    fun _ => Filter.EventuallyEq.of_eq hsource.2
  have hang := endpointAngularWidth_margins (n + 1) hlc hcd hdr hκφ hM
  have hspan : 0 < (if side then r else c) - (if side then d else l) := by
    cases side with
    | false => exact sub_pos.mpr hlc
    | true => exact sub_pos.mpr hdr
  have hη := prescribedEndpointWidth_margins n
    (span := (if side then r else c) - (if side then d else l))
    (ρ := 1) (κ := κX) (M := Mσ)
    (Mslope := max (Mσ + ((n + 1 : ℕ) : ℝ) * Mσ) 1)
    (m := (if side then r else c) - (if side then d else l))
    hspan zero_lt_one hκX hMσ (zero_le_one.trans (le_max_right _ _)) hspan
  have hτ : ∀ p : PolarPoint, (if side then d ≤ p.1 else p.1 ≤ c) → τ p = p :=
    oneSidedWholeComponentTransport_eq_on_identity_side n hcd side hψ hX
      hang.1 hang.2.2.2.1.le hang.2.2.2.2.1.le hη.1 hη.2.2.2.1
  have hQ : ∀ p : PolarPoint, (if side then d ≤ p.1 else p.1 ≤ c) → Q p = 1 :=
    positiveHeightTaylorInterpolation_one_on_identity_side n hcd hδ
      (hδρ.trans ((min_le_right _ _).trans (min_le_left _ _)))
      (hδρ.trans ((min_le_right _ _).trans (min_le_right _ _))) side hq
  constructor
  · intro p hp
    have ht : τ p = p := hτ p hp
    have hs : σ p = p := (congrArg σ ht.symm).trans (hm.geometry.left_inverse p)
    have hheight : wholePositiveChartHeight σ Q p = 1 := by
      simp only [wholePositiveChartHeight, hs, hQ p hp, inv_one]
    exact ⟨ht, hs, hQ p hp, hheight⟩
  · intro θ
    exact wholePositiveFields_identity_germs_of_side hlc hdr side
      hm.geometry.left_inverse hτ hQ θ

end ContinuousFlexibility.Analysis
