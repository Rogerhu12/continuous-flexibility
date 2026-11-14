module

public import ContinuousFlexibility.Analysis.ProjectiveJetContinuity

/-!
# Joint projective jet continuity from order-dependent local bounds

For each fixed parameter-jet order, target coordinate, and base point,
one convex open neighborhood suffices. The neighborhoods may depend on
all three. In particular, no single neighborhood supporting estimates
for infinitely many parameter orders is required.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {F : ℕ → Type*} [∀ s, NormedAddCommGroup (F s)] [∀ s, NormedSpace ℝ (F s)]
  {bond : ∀ s, F (s + 1) →L[ℝ] F s} {U : Set E}

/-- Only the next jet on one local convex neighborhood is needed for
continuity of a fixed target coordinate of the evaluated current jet. -/
theorem continuousAt_projectiveJet_of_local_bound
    (A : ∀ n : ℕ, E → E [×n]→L[ℝ] ProjectiveLimit F bond)
    (hline : ∀ n x, x ∈ U → ∀ (v : Fin n → E) (w : E),
      HasProjectiveLineDerivAt (fun y => A n y v) (A (n + 1) x (Fin.cons w v)) x w)
    (n s : ℕ) (V : Set E) (hV : IsOpen V) (hc : Convex ℝ V) (hVU : V ⊆ U)
    (p : Seminorm ℝ E) (hp : Continuous p) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ y ∈ V, ∀ v : Fin (n + 1) → E,
      ‖(A (n + 1) y v).val s‖ ≤ B * (1 + p y) * ∏ i, p (v i))
    {x : E} (hx : x ∈ V) (v : Fin n → E) :
    ContinuousAt (fun z : E × (Fin n → E) => (A n z.1 z.2).val s) (x, v) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  let err : E × (Fin n → E) → ℝ := fun z =>
    B * (1 + p x + p (z.1 - x)) * (p (z.1 - x) * ∏ j, p (z.2 j)) +
      ‖(A n x z.2).val s - (A n x v).val s‖
  have hpbase : Continuous (fun z : E × (Fin n → E) => p (z.1 - x)) :=
    hp.comp (continuous_fst.sub continuous_const)
  have hpdirs : Continuous (fun z : E × (Fin n → E) => ∏ j, p (z.2 j)) :=
    continuous_finsetProd _ (fun j _ => hp.comp ((continuous_apply j).comp continuous_snd))
  have hfixed : Continuous (fun z : E × (Fin n → E) => (A n x z.2).val s) :=
    (projectiveCoordinate F bond s).continuous.comp
      ((A n x).cont.comp continuous_snd)
  have herr : Continuous err :=
    ((continuous_const.mul (continuous_const.add hpbase)).mul (hpbase.mul hpdirs)).add
      (hfixed.sub continuous_const).norm
  have herr0 : err (x, v) = 0 := by
    simp only [err, sub_self, map_zero, mul_zero, zero_mul, norm_zero, add_zero]
  have hmem : ∀ᶠ z : E × (Fin n → E) in 𝓝 (x, v), z.1 ∈ V :=
    continuous_fst.continuousAt.eventually (hV.mem_nhds hx)
  have hupper : ∀ᶠ z : E × (Fin n → E) in 𝓝 (x, v),
      ‖(A n z.1 z.2).val s - (A n x v).val s‖ ≤ err z := by
    filter_upwards [hmem] with z hz
    have hbase := projectiveJet_base_variation_le A
      (fun k y hy dirs w => hline k y (hVU hy) dirs w)
      hc n s p hB hbound hx hz z.2
    exact (norm_sub_le_norm_sub_add_norm_sub ((A n z.1 z.2).val s) ((A n x z.2).val s)
      ((A n x v).val s)).trans (add_le_add hbase le_rfl)
  exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hupper
    (by simpa only [herr0] using herr.tendsto (x, v))

/-- The coordinate neighborhood may depend on the jet order, target
coordinate, and base point. Their separate continuity statements give
continuity in the original projective-limit topology. -/
theorem continuousOn_projectiveJets_of_local_seminorm_bounds
    (A : ∀ n : ℕ, E → E [×n]→L[ℝ] ProjectiveLimit F bond)
    (hline : ∀ n x, x ∈ U → ∀ (v : Fin n → E) (w : E),
      HasProjectiveLineDerivAt (fun y => A n y v) (A (n + 1) x (Fin.cons w v)) x w)
    (hbound : ∀ n s x, x ∈ U →
      ∃ V : Set E, IsOpen V ∧ Convex ℝ V ∧ x ∈ V ∧ V ⊆ U ∧
        ∃ p : Seminorm ℝ E, ∃ B : ℝ, Continuous p ∧ 0 ≤ B ∧
          ∀ y ∈ V, ∀ v : Fin (n + 1) → E,
            ‖(A (n + 1) y v).val s‖ ≤ B * (1 + p y) * ∏ i, p (v i))
    (n : ℕ) :
    ContinuousOn (fun z : E × (Fin n → E) => A n z.1 z.2) (U ×ˢ univ) := by
  rintro ⟨x, v⟩ hx
  apply ContinuousAt.continuousWithinAt
  rw [ContinuousAt, tendsto_projectiveLimit_iff]
  intro s
  obtain ⟨V, hV, hc, hxV, hVU, p, B, hp, hB, hb⟩ := hbound n s x hx.1
  exact continuousAt_projectiveJet_of_local_bound A hline n s V hV hc hVU p hp hB hb hxV v

def smoothDirectionsOfLocalProjectiveJetBounds
    {f : E → ProjectiveLimit F bond}
    (A : ∀ n : ℕ, E → E [×n]→L[ℝ] ProjectiveLimit F bond)
    (hU : IsOpen U)
    (hzero : ∀ x ∈ U, A 0 x Fin.elim0 = f x)
    (hline : ∀ n x, x ∈ U → ∀ (v : Fin n → E) (w : E),
      HasProjectiveLineDerivAt (fun y => A n y v) (A (n + 1) x (Fin.cons w v)) x w)
    (hbound : ∀ n s x, x ∈ U →
      ∃ V : Set E, IsOpen V ∧ Convex ℝ V ∧ x ∈ V ∧ V ⊆ U ∧
        ∃ p : Seminorm ℝ E, ∃ B : ℝ, Continuous p ∧ 0 ≤ B ∧
          ∀ y ∈ V, ∀ v : Fin (n + 1) → E,
            ‖(A (n + 1) y v).val s‖ ≤ B * (1 + p y) * ∏ i, p (v i)) :
    SmoothDirections U f where
  open_domain := hU
  D := A
  zero := hzero
  continuous := continuousOn_projectiveJets_of_local_seminorm_bounds A hline hbound
  derivative := hline

end ContinuousFlexibility.Analysis
