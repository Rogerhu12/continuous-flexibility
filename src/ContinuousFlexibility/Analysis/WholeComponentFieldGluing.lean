import ContinuousFlexibility.Analysis.WholeComponentRootNeighbors
import ContinuousFlexibility.Analysis.FiniteJetRadialGluing

/-!
# Actual finite-order gluing across every component root

Closed negative fields and smooth positive fields are selected by the
actual radius. The genuine neighboring component supplies a two-sided
open strip at each root. Matching only the indicated finite full jets
therefore gives ordinary finite regularity of the stored global field.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem n04WholeComponentField_contDiffAt_root
    (n : ℕ) (hN : N01Properties D T S C base loss ε)
    (Fneg : ℕ → PolarPoint → E)
    (Fpos : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → E)
    (fallback : PolarPoint → E)
    (hneg : ∀ m p, p.1 ∈ Icc (C.left m) (C.right m) → ContDiffAt ℝ n (Fneg m) p)
    (hpos : ∀ i, ContDiff ℝ n (Fpos i))
    (hmatch : ∀ m side i,
      n04PositiveEndpoint i (!side) = (if side then C.right m else C.left m) →
      ∀ θ k, k ≤ n →
        iteratedFDeriv ℝ k (Fneg m) (if side then C.right m else C.left m, θ) =
        iteratedFDeriv ℝ k (Fpos i) (if side then C.right m else C.left m, θ))
    (m : ℕ) (side : Bool) (θ : ℝ) :
    ContDiffAt ℝ n (n04WholeComponentField C Fneg Fpos fallback)
      (if side then C.right m else C.left m, θ) := by
  classical
  have hD : RadialProfileGeometry D := (Classical.choose_spec hN.1.1).1
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  have hprofile : Continuous (deriv D.w) := hD.2.2.1.1.continuous_deriv (by simp)
  obtain ⟨i, hi⟩ := n04NegativeEndpoint_exists_positive_neighbor hN m side
  let a : ℝ := if side then C.left m else n04PositiveLeft i
  let b : ℝ := if side then n04PositiveRight i else C.right m
  let c : ℝ := if side then C.right m else C.left m
  let f : PolarPoint → E := if side then Fneg m else Fpos i
  let g : PolarPoint → E := if side then Fpos i else Fneg m
  have hnp (η : ℝ) (k : ℕ) (hk : k ≤ n) :
      iteratedFDeriv ℝ k (Fneg m) (c, η) = iteratedFDeriv ℝ k (Fpos i) (c, η) :=
    hmatch m side i hi η k hk
  have hvalue (η : ℝ) : Fneg m (c, η) = Fpos i (c, η) := by
    have he := congrArg (fun A : PolarPoint [×0]→L[ℝ] E => A (fun j => Fin.elim0 j))
      (hnp η 0 (Nat.zero_le n))
    simpa only [iteratedFDeriv_zero_apply] using he
  have hc : c ∈ Ioo a b := by
    have hgap := (n04PositiveComponent_bounds hprofile i).2.1
    cases side
    · change n04PositiveRight i = C.left m at hi
      exact ⟨hgap.trans_eq hi, (hC.1 m).2.1⟩
    · change n04PositiveLeft i = C.right m at hi
      exact ⟨(hC.1 m).2.1, hi.symm.trans_lt hgap⟩
  have hf : ∀ p : PolarPoint, a < p.1 → p.1 ≤ c → p.1 < b → ContDiffAt ℝ n f p := by
    intro p ha hc' hb
    cases side
    · exact (hpos i).contDiffAt
    · exact hneg m p ⟨ha.le, hc'⟩
  have hg : ∀ p : PolarPoint, a < p.1 → c ≤ p.1 → p.1 < b → ContDiffAt ℝ n g p := by
    intro p ha hc' hb
    cases side
    · exact hneg m p ⟨hc', hb.le⟩
    · exact (hpos i).contDiffAt
  have hfg (η : ℝ) (k : ℕ) (hk : k ≤ n) :
      iteratedFDeriv ℝ k f (c, η) = iteratedFDeriv ℝ k g (c, η) := by
    cases side
    · exact (hnp η k hk).symm
    · exact hnp η k hk
  have hlocal (p : PolarPoint) (hp : p.1 ∈ Ioo a b) :
      n04WholeComponentField C Fneg Fpos fallback p = if p.1 ≤ c then f p else g p := by
    cases side
    · change n04PositiveRight i = C.left m at hi
      change p.1 ∈ Ioo (n04PositiveLeft i) (C.right m) at hp
      change _ = if p.1 ≤ C.left m then Fpos i p else Fneg m p
      by_cases hle : p.1 ≤ C.left m
      · rw [if_pos hle]
        rcases lt_or_eq_of_le hle with hlt | he
        · exact n04WholeComponentField_eq_positive hprofile hC Fneg Fpos fallback
            ⟨hp.1, hlt.trans_eq hi.symm⟩
        · rw [n04WholeComponentField_eq_negative hN Fneg Fpos fallback
            (show p.1 ∈ Icc (C.left m) (C.right m) from ⟨he.ge, hp.2.le⟩)]
          have hep : p = (C.left m, p.2) := Prod.ext he rfl
          rw [hep]
          exact hvalue p.2
      · rw [if_neg hle]
        exact n04WholeComponentField_eq_negative hN Fneg Fpos fallback
          ⟨(lt_of_not_ge hle).le, hp.2.le⟩
    · change n04PositiveLeft i = C.right m at hi
      change p.1 ∈ Ioo (C.left m) (n04PositiveRight i) at hp
      change _ = if p.1 ≤ C.right m then Fneg m p else Fpos i p
      by_cases hle : p.1 ≤ C.right m
      · rw [if_pos hle]
        exact n04WholeComponentField_eq_negative hN Fneg Fpos fallback ⟨hp.1.le, hle⟩
      · rw [if_neg hle]
        exact n04WholeComponentField_eq_positive hprofile hC Fneg Fpos fallback
          ⟨hi.trans_lt (lt_of_not_ge hle), hp.2⟩
  exact contDiffAt_of_local_radial_piecewise_matching_full_jets n hf hg hfg hlocal hc

/-- This is a conclusion about the actual radius-selected global field.
Only component regularity and finite true-root matching are hypotheses. -/
theorem n04WholeComponentField_contDiffOn
    (n : ℕ) (hN : N01Properties D T S C base loss ε)
    (Fneg : ℕ → PolarPoint → E)
    (Fpos : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → E)
    (fallback : PolarPoint → E)
    (hneg : ∀ m p, p.1 ∈ Icc (C.left m) (C.right m) → ContDiffAt ℝ n (Fneg m) p)
    (hpos : ∀ i, ContDiff ℝ n (Fpos i))
    (hmatch : ∀ m side i,
      n04PositiveEndpoint i (!side) = (if side then C.right m else C.left m) →
      ∀ θ k, k ≤ n →
        iteratedFDeriv ℝ k (Fneg m) (if side then C.right m else C.left m, θ) =
        iteratedFDeriv ℝ k (Fpos i) (if side then C.right m else C.left m, θ)) :
    ContDiffOn ℝ n (n04WholeComponentField C Fneg Fpos fallback) (annularOpen D) := by
  have hD : RadialProfileGeometry D := (Classical.choose_spec hN.1.1).1
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  have hprofile : Continuous (deriv D.w) := hD.2.2.1.1.continuous_deriv (by simp)
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  rcases n04_wholeComponent_cover hD hC hp.1 with ⟨m, hm⟩ | ⟨i, hi⟩
  · by_cases hl : p.1 = C.left m
    · have he : p = (C.left m, p.2) := Prod.ext hl rfl
      rw [he]
      exact n04WholeComponentField_contDiffAt_root n hN Fneg Fpos fallback
        hneg hpos hmatch m false p.2
    by_cases hr : p.1 = C.right m
    · have he : p = (C.right m, p.2) := Prod.ext hr rfl
      rw [he]
      exact n04WholeComponentField_contDiffAt_root n hN Fneg Fpos fallback
        hneg hpos hmatch m true p.2
    have hpin : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) :=
      ⟨⟨lt_of_le_of_ne hm.1 (Ne.symm hl), lt_of_le_of_ne hm.2 hr⟩, mem_univ _⟩
    have he : n04WholeComponentField C Fneg Fpos fallback =ᶠ[𝓝 p] Fneg m := by
      filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hpin] with q hq
      exact n04WholeComponentField_eq_negative hN Fneg Fpos fallback
        ⟨hq.1.1.le, hq.1.2.le⟩
    exact (hneg m p hm).congr_of_eventuallyEq he
  · have hpin : p ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i) ×ˢ (univ : Set ℝ) :=
      ⟨hi, mem_univ _⟩
    have he : n04WholeComponentField C Fneg Fpos fallback =ᶠ[𝓝 p] Fpos i := by
      filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hpin] with q hq
      exact n04WholeComponentField_eq_positive hprofile hC Fneg Fpos fallback hq.1
    exact (hpos i).contDiffAt.congr_of_eventuallyEq he

end ContinuousFlexibility.Analysis
