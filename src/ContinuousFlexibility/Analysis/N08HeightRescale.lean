import ContinuousFlexibility.Analysis.N08CircleHeightLocality
import ContinuousFlexibility.Analysis.N08CircleJetComparison
import ContinuousFlexibility.Analysis.N08FlowHeightVariation

/-!
# Comparing different parameters through the same height derivative

On one component a localized height equals the decaying height coordinate.
Changing that height at a fixed nonzero parameter reproduces the original
scaled height up to a constant. The actual flow locality theorem therefore
identifies the same control diagonal, with no new derivative hypothesis.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology

set_option backward.isDefEq.respectTransparency false

private theorem n08_seminorm_update_bound
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Seminorm ℝ E) (a x v : E) (t : ℝ) :
    p (x + n08RealSMul t v - a) ≤ p (x - a) + |t| * p v := by
  change p (x + t • v - a) ≤ p (x - a) + |t| * p v
  have he : x + t • v - a = (x - a) + t • v := by abel
  rw [he]
  exact (map_add_le_add p _ _).trans_eq (by rw [map_smul_eq_mul, Real.norm_eq_abs])

private theorem n08_seminorm_update_difference
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Seminorm ℝ E) (x v : E) (s t : ℝ) :
    p ((x + n08RealSMul t v) - (x + n08RealSMul s v)) = |t - s| * p v := by
  change p ((x + t • v) - (x + s • v)) = |t - s| * p v
  have he : (x + t • v) - (x + s • v) = (t - s) • v := by
    rw [sub_smul]
    abel
  rw [he, map_smul_eq_mul, Real.norm_eq_abs]

private theorem n08_heightDirection_grading
    {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) (s : ℕ) (u : E) :
    pairGrading (pairGrading p realGrading)
      (pairGrading realGrading (pairGrading q q)) s ((u, 0), (0, (0, 0))) = p s u := by
  change (p s u + realGrading s 0) + (realGrading s 0 + (q s 0 + q s 0)) = _
  simp only [map_zero, add_zero, zero_add]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}

def n08LocalHeightState (S : PhysicalSpacesData) (x : AnnularState S)
    (h : (S.height (3 / 4 : ℝ)).Space) (t : ℝ) : AnnularState S :=
  x + n08StateSMul S t ((h, 0), (0, (0, 0)))

private theorem n08LocalHeightState_eq_heightLine (S : PhysicalSpacesData)
    (x : AnnularState S) (h : (S.height (3 / 4 : ℝ)).Space) (t : ℝ) :
    n08LocalHeightState S x h t = n08HeightLine S x (h, 0) t := rfl

private theorem n08LocalHeightState_eq_affine (S : PhysicalSpacesData)
    (x : AnnularState S) (h : (S.height (3 / 4 : ℝ)).Space) (t : ℝ) :
    n08LocalHeightState S x h t = x + n08RealSMul t ((h, 0), (0, (0, 0))) := rfl

theorem n08LocalHeightState_tail (S : PhysicalSpacesData) (x : AnnularState S)
    (h : (S.height (3 / 4 : ℝ)).Space) (t : ℝ) :
    (n08LocalHeightState S x h t).2 = x.2 := by
  rw [n08LocalHeightState_eq_heightLine, n08HeightLine_eq]

theorem n08LocalHeightState_sector (S : PhysicalSpacesData) {x : AnnularState S}
    (hs : stateSector S x) (h : (S.height (3 / 4 : ℝ)).Space) (t : ℝ) :
    stateSector S (n08LocalHeightState S x h t) := by
  rw [n08LocalHeightState_eq_heightLine]
  exact n08HeightLine_sector hs (h, 0) t

theorem n08_decayingHeightDirection_grading (S : PhysicalSpacesData) (s : ℕ)
    (h : (S.height (3 / 4 : ℝ)).Space) :
    stateGrading S s ((h, 0), (0, (0, 0))) = (S.height (3 / 4 : ℝ)).grading s h :=
  n08_heightDirection_grading (S.height (3 / 4 : ℝ)).grading
    (S.circle (3 / 4 : ℝ)).grading s h

theorem n08LocalHeightState_grading_bound (S : PhysicalSpacesData)
    (a x : AnnularState S) (h : (S.height (3 / 4 : ℝ)).Space) (s : ℕ) (t : ℝ) :
    stateGrading S s (n08LocalHeightState S x h t - a) ≤
      stateGrading S s (x - a) + |t| * (S.height (3 / 4 : ℝ)).grading s h := by
  rw [n08LocalHeightState_eq_affine]
  have hb := n08_seminorm_update_bound (stateGrading S s) a x ((h, 0), (0, (0, 0))) t
  exact hb.trans_eq (congrArg (fun c : ℝ => stateGrading S s (x - a) + |t| * c)
    (n08_decayingHeightDirection_grading S s h))

theorem n08LocalHeightState_difference_grading (S : PhysicalSpacesData)
    (x : AnnularState S) (h : (S.height (3 / 4 : ℝ)).Space) (s : ℕ) (t u : ℝ) :
    stateGrading S s (n08LocalHeightState S x h t - n08LocalHeightState S x h u) =
      |t - u| * (S.height (3 / 4 : ℝ)).grading s h := by
  rw [n08LocalHeightState_eq_affine S x h t, n08LocalHeightState_eq_affine S x h u]
  have he := n08_seminorm_update_difference (stateGrading S s) x ((h, 0), (0, (0, 0))) u t
  exact he.trans (congrArg (fun a : ℝ => |t - u| * a)
    (n08_decayingHeightDirection_grading S s h))

theorem n08LocalHeightState_field (S : PhysicalSpacesData) (x : AnnularState S)
    (h : (S.height (3 / 4 : ℝ)).Space) (t : ℝ) (p : PolarPoint) :
    stateU S (n08LocalHeightState S x h t) p =
      stateU S x p + t * (S.height (3 / 4 : ℝ)).decode h p := by
  rw [n08LocalHeightState_eq_heightLine]
  simpa only [heightFamily, heightPairField, zero_mul, add_zero] using
    congrFun (n08HeightLine_stateU x (h, 0) t) p

theorem n08LocalHeightState_scaled_germ (S : PhysicalSpacesData)
    (x : AnnularState S) (h : (S.height (3 / 4 : ℝ)).Space)
    {q q' t r θ c : ℝ} (hscale : q' * t = q)
    (hh : (S.height (3 / 4 : ℝ)).decode h =ᶠ[𝓝 (r, θ)]
      (S.height (3 / 4 : ℝ)).decode x.1.1)
    (hc : S.chiLeft =ᶠ[𝓝 r] (fun _ => c)) :
    (fun p => q * stateU S x p) =ᶠ[𝓝 (r, θ)]
      (fun p => q' * stateU S (n08LocalHeightState S x h (t - 1)) p +
        (q - q') * x.1.2 * c) := by
  have hcp := hc.comp_tendsto (continuous_fst.tendsto (r, θ))
  filter_upwards [hh, hcp] with p hp hχ
  change S.chiLeft p.1 = c at hχ
  rw [n08LocalHeightState_field, hp]
  change q * ((S.height (3 / 4 : ℝ)).decode x.1.1 p + x.1.2 * S.chiLeft p.1) =
    q' * (((S.height (3 / 4 : ℝ)).decode x.1.1 p + x.1.2 * S.chiLeft p.1) +
      (t - 1) * (S.height (3 / 4 : ℝ)).decode x.1.1 p) + (q - q') * x.1.2 * c
  rw [hχ, ← hscale]
  ring

/-- Rescaling uses the same actual diagonal at a fixed comparison
parameter. The hypotheses only describe the actual localized height. -/
theorem n08CircleDiagonal_height_rescale
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hR : N02Properties D T S C R base ε)
    {x : AnnularState S} {q q' t : ℝ} {m : ℕ}
    (h : (S.height (3 / 4 : ℝ)).Space) (hscale : q' * t = q)
    (hx : (x, q) ∈ stateNeighborhood S C base ε)
    (hy : (n08LocalHeightState S x h (t - 1), q') ∈ stateNeighborhood S C base ε)
    (hs : stateSector S x)
    (hh : ∀ r ∈ Ioo (C.left m) (C.right m), ∀ θ,
      (S.height (3 / 4 : ℝ)).decode h =ᶠ[𝓝 (r, θ)]
        (S.height (3 / 4 : ℝ)).decode x.1.1)
    (hχ : ∀ r ∈ Ioo (C.left m) (C.right m), ∃ c : ℝ,
      S.chiLeft =ᶠ[𝓝 r] (fun _ => c)) :
    n08CircleDiagonal hS hR (x, q) m =
      n08CircleDiagonal hS hR (n08LocalHeightState S x h (t - 1), q') m := by
  have htail := n08LocalHeightState_tail S x h (t - 1)
  apply n08CircleDiagonal_eq_of_local_height hT hS hN hR
    (x := x) (y := n08LocalHeightState S x h (t - 1)) (q := q) (q' := q') (m := m) hx hy hs
    (n08LocalHeightState_sector S hs h (t - 1))
  · exact (congrArg (fun y : ℝ × (CircleSpace S × CircleSpace S) => y.1) htail).symm
  · exact (congrArg (fun y : ℝ × (CircleSpace S × CircleSpace S) =>
      angularMean ((S.circle (3 / 4 : ℝ)).decode y.2.1 m)) htail).symm
  · intro r hr θ
    obtain ⟨c, hc⟩ := hχ r hr
    exact ⟨(q - q') * x.1.2 * c, n08LocalHeightState_scaled_germ S x h hscale (hh r hr θ) hc⟩
  · exact (congrArg (fun y : ℝ × (CircleSpace S × CircleSpace S) => fun θ : ℝ =>
      θ + (S.circle (3 / 4 : ℝ)).decode y.2.2 m θ) htail).symm

end ContinuousFlexibility.Statements
