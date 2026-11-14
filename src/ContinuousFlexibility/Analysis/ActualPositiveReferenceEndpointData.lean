module

public import ContinuousFlexibility.Analysis.ActualReferenceNegativeEndpointData
public import ContinuousFlexibility.Analysis.WholePositiveEndpointFields

/-!
# Actual reference data at a positive component's certified endpoints

An interior source uses the original opposite negative half. Its radial
chart is translated to the fixed positive endpoint and oriented toward
increasing physical radius. The ambient branch is the displayed affine
coordinate with height one. The certified source and the original atlas
are retained throughout; no reference interpolation is assumed here.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def n04PositiveReferenceSourceCoordinate
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {i : N04PositiveComponent D.a D.b (deriv D.w)} {side : Bool}
    (j : N04PositiveEndpointSource C i side) (K : CanonicalData S) :
    PolarPoint → ℝ :=
  match j.val with
  | none => fun p => (if side then (1 : ℝ) else 0) +
      (p.1 - n04PositiveEndpoint i side)
  | some m => fun p => (if side then (1 : ℝ) else 0) +
      (if side then (1 : ℝ) else -1) *
        (K.chart (C.referenceState, 0)
          (if side then (K.cutPair m).1 else (K.cutPair m).2) p).1

def n04PositiveReferenceSourceHeight
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {i : N04PositiveComponent D.a D.b (deriv D.w)} {side : Bool}
    (j : N04PositiveEndpointSource C i side) (K : CanonicalData S) :
    PolarPoint → ℝ :=
  match j.val with
  | none => fun _ => 1
  | some m => K.height (C.referenceState, 0)
      (if side then (K.cutPair m).1 else (K.cutPair m).2)

/-- All inputs to the finite radial reference factory come from the same
actual stored atlas and the given certified endpoint source. -/
theorem n04Coordinates_actual_positive_reference_source_data
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε) (e : ℕ ≃ N04PieceIndex D)
    {i : N04PositiveComponent D.a D.b (deriv D.w)} {side : Bool}
    (j : N04PositiveEndpointSource C i side) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    let a := n04PositiveSourceLeft j
    let b := n04PositiveSourceRight j
    let c := n04PositiveEndpoint i side
    let y := n04PositiveReferenceSourceCoordinate j K
    let h := n04PositiveReferenceSourceHeight j K
    a < b ∧ c ∈ Icc a b ∧
      ContDiffOn ℝ ∞ y (Ioo a b ×ˢ (univ : Set ℝ)) ∧
      ContDiffOn ℝ ∞ h (Ioo a b ×ˢ (univ : Set ℝ)) ∧
      (∀ θ, ContDiffAt ℝ ∞ y (c, θ)) ∧
      (∀ θ, ContDiffAt ℝ ∞ h (c, θ)) ∧
      (∀ x ∈ Ioo a b, ∀ θ, y (x, θ) = y (x, 0)) ∧
      (∀ x ∈ Ioo a b, ∀ θ, h (x, θ) = h (x, 0)) ∧
      y (c, 0) = (if side then (1 : ℝ) else 0) ∧
      0 < deriv (fun r : ℝ => y (r, 0)) c ∧ 0 < h (c, 0) := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  let c := n04PositiveEndpoint i side
  let v : ℝ := if side then 1 else 0
  let s : ℝ := if side then 1 else -1
  rcases j with ⟨o, ho⟩
  cases o with
  | none =>
      have hD := n04b_profileGeometry_of_through03 hN
      have hf : Continuous (deriv D.w) := hD.2.2.1.1.continuous_deriv (by simp)
      have hlr : n04PositiveLeft i < n04PositiveRight i :=
        (n04PositiveComponent_bounds hf i).2.1
      have hc : c ∈ Icc (n04PositiveLeft i) (n04PositiveRight i) := by
        cases side
        · exact ⟨le_rfl, hlr.le⟩
        · exact ⟨hlr.le, le_rfl⟩
      refine ⟨hlr, hc, ?_, contDiff_const.contDiffOn, ?_,
        fun _ => contDiffAt_const, ?_, ?_, ?_, ?_, zero_lt_one⟩
      · exact (contDiff_const.add (contDiff_fst.sub contDiff_const)).contDiffOn
      · intro θ
        exact contDiffAt_const.add (contDiffAt_fst.sub contDiffAt_const)
      · intro x hx θ
        rfl
      · intro x hx θ
        rfl
      · change v + (c - c) = v
        rw [sub_self, add_zero]
      · have hd : HasDerivAt (fun r : ℝ => v + (r - c)) 1 c :=
          ((hasDerivAt_id c).sub_const c).const_add v
        change 0 < deriv (fun r : ℝ => v + (r - c)) c
        rw [hd.deriv]
        exact zero_lt_one
  | some m =>
      let k := if side then (K.cutPair m).1 else (K.cutPair m).2
      have hk : e.symm (.inl (m, !side)) = k := by
        cases side <;> rfl
      change n04PositiveEndpoint i side =
        (if side then C.left m else C.right m) at ho
      have hc : c = (if !side then C.right m else C.left m) := by
        change n04PositiveEndpoint i side = _
        rw [ho]
        cases side <;> rfl
      have hs : (if !side then (-1 : ℝ) else 1) = s := by
        cases side <;> rfl
      have hopen := n04Coordinates_actual_reference_negative_radial_fields
        hT hS hN hfield e m (!side)
      have hroot := n04Coordinates_actual_reference_negative_endpoint_data
        hT hS hN hfield e m (!side)
      simp only [hk] at hopen
      simp only [hk, ← hc, hs] at hroot
      have hab : C.left m < C.right m := (hN.1.1.2.2.2.1.1 m).2.1
      have hcI : c ∈ Icc (C.left m) (C.right m) := by
        rw [hc]
        cases side
        · exact ⟨hab.le, le_rfl⟩
        · exact ⟨le_rfl, hab.le⟩
      refine ⟨hab, hcI, ?_, hopen.2.1, ?_,
        fun θ => (hroot.1 θ).2.1, ?_, ?_, ?_, ?_, (hroot.1 0).2.2.2.1⟩
      · exact contDiffOn_const.add (contDiffOn_const.mul hopen.1.fst)
      · intro θ
        exact contDiffAt_const.add (contDiffAt_const.mul (hroot.1 θ).1.fst)
      · intro x hx θ
        have he : (K.chart (C.referenceState, 0) k (x, θ)).1 =
            (K.chart (C.referenceState, 0) k (x, 0)).1 := by
          have hf := congrArg (fun q : PolarPoint => q.1)
            (hopen.2.2.1 (x, θ) ⟨hx, mem_univ _⟩)
          exact hf
        change v + s * (K.chart (C.referenceState, 0) k (x, θ)).1 =
          v + s * (K.chart (C.referenceState, 0) k (x, 0)).1
        rw [he]
      · intro x hx θ
        exact hopen.2.2.2.1 (x, θ) ⟨hx, mem_univ _⟩
      · have he : (K.chart (C.referenceState, 0) k (c, 0)).1 = 0 :=
          congrArg Prod.fst (hroot.1 0).2.2.1
        change v + s * (K.chart (C.referenceState, 0) k (c, 0)).1 = v
        rw [he, mul_zero, add_zero]
      · have hdF : DifferentiableAt ℝ
            (fun r : ℝ => (K.chart (C.referenceState, 0) k (r, 0)).1) c :=
          (hasDerivAt_radial_slice
            ((hroot.1 0).1.differentiableAt (by simp)).fst).differentiableAt
        have hd : HasDerivAt
            (fun r : ℝ => v + s * (K.chart (C.referenceState, 0) k (r, 0)).1)
            (s * deriv (fun r : ℝ => (K.chart (C.referenceState, 0) k (r, 0)).1) c) c :=
          (hdF.hasDerivAt.const_mul s).const_add v
        change 0 < deriv
          (fun r : ℝ => v + s * (K.chart (C.referenceState, 0) k (r, 0)).1) c
        rw [hd.deriv]
        exact hroot.2

end ContinuousFlexibility.Analysis

