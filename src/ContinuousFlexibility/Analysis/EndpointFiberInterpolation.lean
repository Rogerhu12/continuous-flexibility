module

public import ContinuousFlexibility.Analysis.PositiveReferenceCollarPrescribedWidth
public import ContinuousFlexibility.Analysis.PrescribedEndpointWidth
public import ContinuousFlexibility.Analysis.PositiveFiberInterpolationSymmetry
public import ContinuousFlexibility.Analysis.TwoEndpointFiberGluing

/-!
# An actual radial fiber from two endpoint jet families

The two endpoint values are their physical radii.  The positive first
normal jets and bounded finite normal jets choose displayed collar widths
before the family index.  The integral construction supplies a genuine
positive radial derivative everywhere and matches the identity between
the two exits as a joint germ.  No determinant condition is needed at the
physical endpoints, so they may be turning radii.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

def endpointFiberWidths (n : ℕ) (l r c d κ M : ℝ) (side : Bool) : ℝ :=
  let a := if side then d else l
  let b := if side then r else c
  prescribedEndpointWidth n (b - a) 1 κ M
    (max (M + ((n + 1 : ℕ) : ℝ) * M) 1) (b - a)

def endpointFiberLower (n : ℕ) (l r c d κ M : ℝ) : ℝ :=
  let η := endpointFiberWidths n l r c d κ M
  min (prescribedPositiveCollarLower l c (η false) (c - l) κ 1)
    (min 1 (prescribedPositiveCollarLower d r (η true) (r - d) κ 1))

def endpointFiberCollar (n : ℕ) (l r c d : ℝ) (η : Bool → ℝ)
    (A : Bool → ℕ → ℝ → ℝ) (side : Bool) : PolarPoint → ℝ :=
  let a := if side then d else l
  let b := if side then r else c
  positiveReferenceCollarCoordinate n a b (η side) a (b - a) side
    (A side) Prod.fst

def endpointFiberInterpolation (n : ℕ) (l r c d : ℝ) (η : Bool → ℝ)
    (A : Bool → ℕ → ℝ → ℝ) : PolarPoint → ℝ :=
  twoEndpointFiberCoordinate c d (endpointFiberCollar n l r c d η A) Prod.fst

theorem twoEndpointFiberCoordinate_reference_germ_on_middle
    {Y : Bool → PolarPoint → ℝ} {Ref : PolarPoint → ℝ} {c d : ℝ}
    (hcd : c < d)
    (hmatch : ∀ side θ, Y side =ᶠ[𝓝 (if side then d else c, θ)] Ref)
    {x : ℝ} (hx : x ∈ Icc c d) (θ : ℝ) :
    twoEndpointFiberCoordinate c d Y Ref =ᶠ[𝓝 (x, θ)] Ref := by
  have hright (α : ℝ) : Ref =ᶠ[𝓝 (d, α)] Y true := (hmatch true α).symm
  have hleft (α : ℝ) : Y false =ᶠ[𝓝 (c, α)] radialGermGlue d Ref (Y true) := by
    have hi := radialGermGlue_eventuallyEq hright (c, α)
    change radialGermGlue d Ref (Y true) =ᶠ[𝓝 (c, α)]
      (if c < d then Ref else Y true) at hi
    rw [if_pos hcd] at hi
    exact (hmatch false α).trans hi.symm
  have ho := radialGermGlue_eventuallyEq hleft (x, θ)
  change twoEndpointFiberCoordinate c d Y Ref =ᶠ[𝓝 (x, θ)]
    (if x < c then Y false else radialGermGlue d Ref (Y true)) at ho
  rw [if_neg (not_lt_of_ge hx.1)] at ho
  have hi := radialGermGlue_eventuallyEq hright (x, θ)
  change radialGermGlue d Ref (Y true) =ᶠ[𝓝 (x, θ)]
    (if x < d then Ref else Y true) at hi
  by_cases hxd : x < d
  · rw [if_pos hxd] at hi
    exact ho.trans hi
  · have he : x = d := le_antisymm hx.2 (le_of_not_gt hxd)
    rw [if_neg hxd] at hi
    exact (ho.trans hi).trans (by simpa only [he, ↓reduceIte] using hmatch true θ)

theorem endpointFiberInterpolation_family
    {ι : Type*} {n : ℕ} {A : ι → Bool → ℕ → ℝ → ℝ}
    {l r c d κ M : ℝ}
    (hlc : l < c) (hcd : c < d) (hdr : d < r)
    (hκ : 0 < κ) (hM : 0 ≤ M)
    (hA : ∀ i side j, j ≤ n + 1 → ContDiff ℝ ∞ (A i side j))
    (hvalue : ∀ i side θ, A i side 0 θ = if side then r else l)
    (hlow : ∀ i side θ, κ ≤ A i side 1 θ)
    (hbound : ∀ i side j, 1 ≤ j → j ≤ n + 1 → ∀ θ, |A i side j θ| ≤ M)
    (hperiod : ∀ i side j, j ≤ n + 1 → Function.Periodic (A i side j) Real.pi)
    (heven : ∀ i side j, j ≤ n + 1 → ∀ θ, A i side j (-θ) = A i side j θ) :
    let η := endpointFiberWidths n l r c d κ M
    let B := endpointFiberLower n l r c d κ M
    (∀ side, 0 < η side) ∧
      (∀ side, 2 * η side < (if side then r else c) - (if side then d else l)) ∧
      0 < B ∧ ∀ i,
      let Y := endpointFiberInterpolation n l r c d η (A i)
      ContDiff ℝ ∞ Y ∧
      (∀ x θ, B ≤ deriv (fun t => Y (t, θ)) x) ∧
      (∀ θ, Y (l, θ) = l) ∧ (∀ θ, Y (r, θ) = r) ∧
      (∀ x θ, Y (x, θ + Real.pi) = Y (x, θ)) ∧
      (∀ x θ, Y (x, -θ) = Y (x, θ)) ∧
      (∀ x ∈ Icc c d, ∀ θ, Y =ᶠ[𝓝 (x, θ)] (Prod.fst : PolarPoint → ℝ)) ∧
      ∀ side k, k ≤ n + 1 → ∀ θ,
        radialBoundaryJet Y (if side then r else l) k θ = A i side k θ := by
  let a : Bool → ℝ := fun side => if side then d else l
  let b : Bool → ℝ := fun side => if side then r else c
  let η : Bool → ℝ := endpointFiberWidths n l r c d κ M
  let Y : ι → Bool → PolarPoint → ℝ := fun i =>
    endpointFiberCollar n l r c d η (A i)
  let B : Bool → ℝ := fun side =>
    prescribedPositiveCollarLower (a side) (b side) (η side)
      (b side - a side) κ 1
  have hab (side : Bool) : a side < b side := by
    cases side <;> assumption
  have hmarg (side : Bool) := prescribedEndpointWidth_margins n
    (sub_pos.mpr (hab side)) zero_lt_one hκ hM
    (zero_le_one.trans (le_max_right (M + ((n + 1 : ℕ) : ℝ) * M) 1))
    (sub_pos.mpr (hab side))
  have hcollar (side : Bool) :
      0 < B side ∧ ∀ i,
      ContDiff ℝ ∞ (Y i side) ∧
      (∀ x θ, B side ≤ deriv (fun t => Y i side (t, θ)) x) ∧
      (∀ (s : Bool) θ, Y i side (if s then b side else a side, θ) =
        if s then a side + (b side - a side) else a side) ∧
      (∀ k ≤ n + 1, ∀ θ,
        radialBoundaryJet (Y i side) (if side then b side else a side) k θ =
          A i side k θ) ∧
      (∀ s, s ≠ side → ∀ θ,
        Y i side =ᶠ[𝓝 (if s then b side else a side, θ)]
          (Prod.fst : PolarPoint → ℝ)) := by
    apply positiveReferenceCollar_family_of_width side
      (hab side) zero_lt_one hκ hM zero_lt_one zero_le_one (sub_pos.mpr (hab side))
      (hmarg side).1 (hmarg side).2.1 (hmarg side).2.2.1
      (hmarg side).2.2.2.1 (hmarg side).2.2.2.2.1 (hmarg side).2.2.2.2.2
      (fun i j hj => hA i side j hj)
    · intro i θ
      cases side with
      | false => exact hvalue i false θ
      | true =>
        calc
          A i true 0 θ = r := hvalue i true θ
          _ = a true + (b true - a true) := by simp only [a, b, ↓reduceIte]; ring
    · exact fun i θ => hlow i side θ
    · exact fun i j hj hjn θ => hbound i side j hj hjn θ
    · exact contDiff_fst
    · intro s hs θ
      cases side <;> cases s <;> simp_all [a, b]
    · intro s hs x hx θ
      exact le_of_eq radialPartial_fst.symm
    · intro s hs x hx θ
      simp only [radialPartial_fst, abs_one, le_refl]
  have hη (side : Bool) : 0 < η side := (hmarg side).1
  have hηgap (side : Bool) : 2 * η side < b side - a side :=
    (hmarg side).2.2.2.1
  have hY (i : ι) (side : Bool) : ContDiff ℝ ∞ (Y i side) :=
    ((hcollar side).2 i).1
  have hYlow (i : ι) (side : Bool) (p : PolarPoint) :
      B side ≤ radialPartial (Y i side) p := by
    have h := ((hcollar side).2 i).2.1 p.1 p.2
    rwa [deriv_cylinder_radial_slice ((hY i side).differentiable (by simp))] at h
  have hmatch (i : ι) (side : Bool) (θ : ℝ) :
      Y i side =ᶠ[𝓝 (if side then d else c, θ)] (Prod.fst : PolarPoint → ℝ) := by
    have hs : (!side) ≠ side := by cases side <;> decide
    have h := ((hcollar side).2 i).2.2.2.2 (!side) hs θ
    cases side <;> simpa only [a, b, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ite_false, ite_true] using h
  have hg (i : ι) := twoEndpointFiberCoordinate_geometry hcd (hY i) contDiff_fst
    (hmatch i) (fun side => (hcollar side).1) zero_lt_one (hYlow i)
    (fun p => le_of_eq radialPartial_fst.symm)
  dsimp only
  refine ⟨hη, hηgap, lt_min (hcollar false).1 (lt_min zero_lt_one (hcollar true).1), ?_⟩
  intro i
  let W := endpointFiberInterpolation n l r c d η (A i)
  have hW : ContDiff ℝ ∞ W := (hg i).1
  have hboundary (side : Bool) (k : ℕ) (hk : k ≤ n + 1) (θ : ℝ) :
      radialBoundaryJet W (if side then r else l) k θ = A i side k θ := by
    have he := twoEndpointFiberCoordinate_endpoint_germ hlc hcd hdr (hmatch i) side θ
    have hline : Tendsto (fun x : ℝ => (x, θ)) (𝓝 (if side then r else l))
        (𝓝 (if side then r else l, θ)) :=
      (continuous_id.prodMk continuous_const).tendsto _
    have hd := ((he.comp_tendsto hline).iteratedDeriv k).eq_of_nhds
    change radialBoundaryJet W (if side then r else l) k θ =
      radialBoundaryJet (Y i side) (if side then r else l) k θ at hd
    have hj := ((hcollar side).2 i).2.2.2.1 k hk θ
    cases side <;> exact hd.trans hj
  have hsymm (χ : ℝ → ℝ)
      (hInv : ∀ side j, j ≤ n + 1 → ∀ θ, A i side j (χ θ) = A i side j θ)
      (x θ : ℝ) : W (x, χ θ) = W (x, θ) := by
    apply twoEndpointFiberCoordinate_angleInvariant c d χ
    · intro side s α
      exact positiveReferenceCollarCoordinate_angleInvariant
        (fun j hj => hA i side j hj) contDiff_fst χ
        (fun j hj β => hInv side j hj β) (fun _ _ => rfl)
        (a side) (b side) (η side) (a side) (b side - a side) side s α
    · exact fun _ _ => rfl
  refine ⟨hW, ?_, ?_, ?_, ?_, ?_, ?_, hboundary⟩
  · intro x θ
    rw [deriv_cylinder_radial_slice (hW.differentiable (by simp)) x θ]
    exact (hg i).2.2 (x, θ)
  · intro θ
    simpa only [W, η, radialBoundaryJet, iteratedDeriv_zero,
      Bool.false_eq_true, ↓reduceIte] using
      (hboundary false 0 (Nat.zero_le _) θ).trans (hvalue i false θ)
  · intro θ
    simpa only [W, η, radialBoundaryJet, iteratedDeriv_zero,
      Bool.false_eq_true, ↓reduceIte] using
      (hboundary true 0 (Nat.zero_le _) θ).trans (hvalue i true θ)
  · exact hsymm (fun θ => θ + Real.pi) (fun side j hj θ => hperiod i side j hj θ)
  · exact hsymm (fun θ => -θ) (fun side j hj θ => heven i side j hj θ)
  · exact fun x hx θ => twoEndpointFiberCoordinate_reference_germ_on_middle hcd
      (hmatch i) hx θ

end ContinuousFlexibility.Analysis
