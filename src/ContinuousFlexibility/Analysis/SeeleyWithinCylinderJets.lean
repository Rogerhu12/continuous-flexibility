module

public import ContinuousFlexibility.Analysis.SeeleyCylinderExtension
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.TangentCone.Prod
public import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
# Joint extension from actual derivatives within the half-plane

This file constructs the jet input to the cylinder Seeley theorem from
ContDiffOn on the closed half-plane. The partials are actual derivatives
within that set. Schwarz symmetry within the half-plane makes the two
directions commute, including at its boundary. Only bounds on these
actual within-jets are additional input; no derivative of an extension
and no smoothness outside the half-plane is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

variable {ι : Type*}

def seeleyHalfPlane : Set (ℝ × ℝ) := Ici (0 : ℝ) ×ˢ univ

theorem uniqueDiffOn_seeleyHalfPlane : UniqueDiffOn ℝ seeleyHalfPlane :=
  (uniqueDiffOn_Ici (0 : ℝ)).prod uniqueDiffOn_univ

private theorem mem_closure_interior_seeleyHalfPlane {p : ℝ × ℝ}
    (hp : p ∈ seeleyHalfPlane) : p ∈ closure (interior seeleyHalfPlane) := by
  simpa only [seeleyHalfPlane, interior_prod_eq, interior_Ici, interior_univ,
    closure_prod_eq, closure_Ioi, closure_univ] using hp

/-- Directional differentiation is taken within the closed half-plane. -/
def seeleyWithinPartial (v : ℝ × ℝ) (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderivWithin ℝ f seeleyHalfPlane p v

/-- The actual within mixed jets, with radial partials outside angular ones. -/
def seeleyWithinMixedJet (f : ℝ × ℝ → ℝ) (a b : ℕ) : ℝ × ℝ → ℝ :=
  (seeleyWithinPartial (1, 0))^[a] ((seeleyWithinPartial (0, 1))^[b] f)

@[simp] theorem seeleyWithinMixedJet_zero_zero (f : ℝ × ℝ → ℝ) :
    seeleyWithinMixedJet f 0 0 = f := by
  simp only [seeleyWithinMixedJet, Function.iterate_zero_apply]

theorem contDiffOn_seeleyWithinPartial
    {f : ℝ × ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f seeleyHalfPlane) (v : ℝ × ℝ) :
    ContDiffOn ℝ ∞ (seeleyWithinPartial v f) seeleyHalfPlane :=
  (hf.fderivWithin uniqueDiffOn_seeleyHalfPlane (m := ∞) (by simp)).clm_apply contDiffOn_const

private theorem contDiffOn_iterate_seeleyWithinPartial
    {f : ℝ × ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f seeleyHalfPlane)
    (v : ℝ × ℝ) (n : ℕ) :
    ContDiffOn ℝ ∞ ((seeleyWithinPartial v)^[n] f) seeleyHalfPlane := by
  induction n with
  | zero => exact hf
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact contDiffOn_seeleyWithinPartial ih v

theorem contDiffOn_seeleyWithinMixedJet
    {f : ℝ × ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f seeleyHalfPlane) (a b : ℕ) :
    ContDiffOn ℝ ∞ (seeleyWithinMixedJet f a b) seeleyHalfPlane :=
  contDiffOn_iterate_seeleyWithinPartial
    (contDiffOn_iterate_seeleyWithinPartial hf (0, 1) b) (1, 0) a

private theorem seeleyWithinPartial_congr
    {f g : ℝ × ℝ → ℝ} (he : EqOn f g seeleyHalfPlane)
    (v : ℝ × ℝ) {p : ℝ × ℝ} (hp : p ∈ seeleyHalfPlane) :
    seeleyWithinPartial v f p = seeleyWithinPartial v g p :=
  congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L v) (fderivWithin_congr' he hp)

/-- Actual second within-partials commute at every point of the closed
half-plane, because every such point is accumulated by its interior. -/
theorem seeleyWithinPartial_commute
    {f : ℝ × ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f seeleyHalfPlane)
    (v w : ℝ × ℝ) {p : ℝ × ℝ} (hp : p ∈ seeleyHalfPlane) :
    seeleyWithinPartial v (seeleyWithinPartial w f) p =
      seeleyWithinPartial w (seeleyWithinPartial v f) p := by
  have hd : DifferentiableWithinAt ℝ (fderivWithin ℝ f seeleyHalfPlane)
      seeleyHalfPlane p :=
    ((hf.fderivWithin uniqueDiffOn_seeleyHalfPlane (m := ∞) (by simp)).differentiableOn
      (by simp)) p hp
  have hsym := (hf p hp).isSymmSndFDerivWithinAt (by simp)
    uniqueDiffOn_seeleyHalfPlane (mem_closure_interior_seeleyHalfPlane hp) hp
  unfold seeleyWithinPartial
  rw [fderivWithin_clm_apply (uniqueDiffOn_seeleyHalfPlane p hp) hd
      (differentiableWithinAt_const w),
    fderivWithin_clm_apply (uniqueDiffOn_seeleyHalfPlane p hp) hd
      (differentiableWithinAt_const v)]
  simpa only [fderivWithin_const_apply, ContinuousLinearMap.comp_zero,
    zero_add, ContinuousLinearMap.flip_apply] using hsym v w

theorem seeleyWithinMixedJet_succ_radial (f : ℝ × ℝ → ℝ) (a b : ℕ) :
    seeleyWithinMixedJet f (a + 1) b =
      seeleyWithinPartial (1, 0) (seeleyWithinMixedJet f a b) := by
  simp only [seeleyWithinMixedJet, Function.iterate_succ_apply']

theorem seeleyWithinPartial_angular_mixedJet
    {f : ℝ × ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f seeleyHalfPlane)
    (a b : ℕ) {p : ℝ × ℝ} (hp : p ∈ seeleyHalfPlane) :
    seeleyWithinPartial (0, 1) (seeleyWithinMixedJet f a b) p =
      seeleyWithinMixedJet f a (b + 1) p := by
  induction a generalizing p with
  | zero =>
      simp only [seeleyWithinMixedJet, Function.iterate_zero_apply,
        Function.iterate_succ_apply']
  | succ a ih =>
      rw [seeleyWithinMixedJet_succ_radial, seeleyWithinMixedJet_succ_radial]
      calc
        seeleyWithinPartial (0, 1)
            (seeleyWithinPartial (1, 0) (seeleyWithinMixedJet f a b)) p =
          seeleyWithinPartial (1, 0)
            (seeleyWithinPartial (0, 1) (seeleyWithinMixedJet f a b)) p :=
          seeleyWithinPartial_commute (contDiffOn_seeleyWithinMixedJet hf a b)
            (0, 1) (1, 0) hp
        _ = seeleyWithinPartial (1, 0) (seeleyWithinMixedJet f a (b + 1)) p :=
          seeleyWithinPartial_congr (fun _ hq => ih hq) (1, 0) hp

/-- ContDiffOn and bounds on explicitly defined within-jets discharge all
of the actual derivative hypotheses of the joint Seeley construction. -/
theorem isBoundedCylinderHalfLineJet_of_contDiffOn
    {f : ℝ × ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f seeleyHalfPlane)
    (hbound : ∀ a b, ∃ M : ℝ, ∀ p, 0 ≤ p.1 →
      ‖seeleyWithinMixedJet f a b p‖ ≤ M) :
    IsBoundedCylinderHalfLineJet (seeleyWithinMixedJet f) where
  continuous a b :=
    (contDiffOn_seeleyWithinMixedJet hf a b).continuousOn.mono
      (fun p hp => ⟨hp, mem_univ _⟩)
  radial a b r θ hr := by
    have hp : (r, θ) ∈ seeleyHalfPlane := ⟨hr.le, mem_univ _⟩
    have hd := ((contDiffOn_seeleyWithinMixedJet hf a b).differentiableOn
      (by simp) (r, θ) hp).hasFDerivWithinAt
    have hline : HasDerivAt (fun x : ℝ => (x, θ)) (1, 0) r :=
      (hasDerivAt_id' r).prodMk (hasDerivAt_const r θ)
    have hmem : ∀ᶠ x in 𝓝 r, (x, θ) ∈ seeleyHalfPlane := by
      filter_upwards [isOpen_Ioi.mem_nhds hr] with x hx
      simpa only [seeleyHalfPlane, Set.mem_prod, Set.mem_Ici, Set.mem_univ, and_true]
        using (le_of_lt hx : (0 : ℝ) ≤ x)
    rw [seeleyWithinMixedJet_succ_radial]
    exact hd.comp_hasDerivAt r hline hmem
  angular a b r θ hr := by
    have hp : (r, θ) ∈ seeleyHalfPlane := ⟨hr, mem_univ _⟩
    have hd := ((contDiffOn_seeleyWithinMixedJet hf a b).differentiableOn
      (by simp) (r, θ) hp).hasFDerivWithinAt
    have hline : HasDerivAt (fun t : ℝ => (r, t)) (0, 1) θ :=
      (hasDerivAt_const θ r).prodMk (hasDerivAt_id' θ)
    rw [← seeleyWithinPartial_angular_mixedJet hf a b hp]
    exact hd.comp_hasDerivAt θ hline (Eventually.of_forall fun _ => ⟨hr, mem_univ _⟩)
  bounded := hbound

/-- The input needs smoothness only within the half-plane. The constructed
extension is jointly smooth on the whole plane. -/
theorem contDiff_seeleyCylinderExtend_of_contDiffOn (S : SeeleyData ι)
    {f : ℝ × ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f seeleyHalfPlane)
    (hbound : ∀ a b, ∃ M : ℝ, ∀ p, 0 ≤ p.1 →
      ‖seeleyWithinMixedJet f a b p‖ ≤ M) :
    ContDiff ℝ ∞ (seeleyCylinderExtend S f) :=
  contDiff_seeleyCylinderExtend S (isBoundedCylinderHalfLineJet_of_contDiffOn hf hbound)

/-- At and inside the boundary, all actual mixed jets of the extension
equal the actual within-jets of the original function. -/
theorem iteratedDeriv_seeleyCylinderExtend_eq_withinJet (S : SeeleyData ι)
    {f : ℝ × ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f seeleyHalfPlane)
    (hbound : ∀ a b, ∃ M : ℝ, ∀ p, 0 ≤ p.1 →
      ‖seeleyWithinMixedJet f a b p‖ ≤ M)
    (a b : ℕ) {p : ℝ × ℝ} (hp : 0 ≤ p.1) :
    iteratedDeriv a
      (fun r => iteratedDeriv b (fun θ => seeleyCylinderExtend S f (r, θ)) p.2) p.1 =
      seeleyWithinMixedJet f a b p := by
  simpa only [seeleyWithinMixedJet_zero_zero,
    seeleyCylinderJet_of_nonneg S (seeleyWithinMixedJet f) a b hp] using
      iteratedDeriv_seeleyCylinderExtend S
        (isBoundedCylinderHalfLineJet_of_contDiffOn hf hbound) a b p

end ContinuousFlexibility.Analysis
