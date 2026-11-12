import ContinuousFlexibility.Analysis.N07aLpParameterJets

/-!
# Genuine L² towers from locally dominated pointwise towers

The values are the actual L² classes of the pointwise derivatives. Local
majorants prove their joint continuity and justify each genuine line
derivative. The analytic majorants remain explicit in this internal bridge.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology ENNReal
open ContinuousFlexibility.Statements

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [FirstCountableTopology E]
  {U : Set E} {f : E → α → ℝ}

def n07aLpJetField (J : ∀ a : α, SmoothDirections U (fun x => f x a))
    (k : ℕ) (x : E) (v : Fin k → E) : α → ℝ := by
  classical
  exact if x ∈ U then (fun a => (J a).D k x v) else 0

theorem n07aLpJetField_memLp
    (J : ∀ a : α, SmoothDirections U (fun x => f x a))
    (hmem : ∀ k x, x ∈ U → ∀ v : Fin k → E,
      MemLp (fun a => (J a).D k x v) 2 μ)
    (k : ℕ) (x : E) (v : Fin k → E) :
    MemLp (n07aLpJetField J k x v) 2 μ := by
  classical
  by_cases hx : x ∈ U
  · simpa only [n07aLpJetField, ite_eq_left hx] using hmem k x hx v
  · simp only [n07aLpJetField, ite_eq_right hx]
    exact MemLp.zero

def n07aLpJetMultilinear
    (J : ∀ a : α, SmoothDirections U (fun x => f x a))
    (hmem : ∀ k x, x ∈ U → ∀ v : Fin k → E,
      MemLp (fun a => (J a).D k x v) 2 μ)
    (k : ℕ) (x : E) : MultilinearMap ℝ (fun _ : Fin k => E) (Lp ℝ 2 μ) where
  toFun v := (n07aLpJetField_memLp J hmem k x v).toLp (n07aLpJetField J k x v)
  map_update_add' v i u w := by
    classical
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    filter_upwards [] with a
    by_cases hx : x ∈ U
    · simp only [n07aLpJetField, ite_eq_left hx, Pi.add_apply,
        ContinuousMultilinearMap.map_update_add]
    · simp only [n07aLpJetField, ite_eq_right hx, Pi.add_apply, Pi.zero_apply, add_zero]
  map_update_smul' v i c u := by
    classical
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    filter_upwards [] with a
    by_cases hx : x ∈ U
    · simp only [n07aLpJetField, ite_eq_left hx, Pi.smul_apply,
        ContinuousMultilinearMap.map_update_smul]
    · simp only [n07aLpJetField, ite_eq_right hx, Pi.smul_apply, Pi.zero_apply, smul_zero]

theorem n07aLpJetMultilinear_continuousOn
    (J : ∀ a : α, SmoothDirections U (fun x => f x a))
    (hmem : ∀ k x, x ∈ U → ∀ v : Fin k → E,
      MemLp (fun a => (J a).D k x v) 2 μ)
    (hbound : ∀ k (p : E × (Fin k → E)), p.1 ∈ U →
      ∃ g : α → ℝ, MemLp g 2 μ ∧
        ∀ᶠ q in 𝓝[U ×ˢ univ] p, ∀ a, |(J a).D k q.1 q.2| ≤ g a)
    (k : ℕ) :
    ContinuousOn (fun p : E × (Fin k → E) => n07aLpJetMultilinear J hmem k p.1 p.2)
      (U ×ˢ univ) := by
  classical
  change ContinuousOn
    (fun p : E × (Fin k → E) => (n07aLpJetField_memLp J hmem k p.1 p.2).toLp
      (n07aLpJetField J k p.1 p.2)) (U ×ˢ univ)
  apply n07a_continuousOn_toLp
    (f := fun p : E × (Fin k → E) => n07aLpJetField J k p.1 p.2)
    (fun p => n07aLpJetField_memLp J hmem k p.1 p.2)
  · intro a
    exact ((J a).continuous k).congr fun p hp => by
      simp only [n07aLpJetField, ite_eq_left hp.1]
  · intro p hp
    obtain ⟨g, hg, hb⟩ := hbound k p hp.1
    refine ⟨g, hg, ?_⟩
    filter_upwards [hb, self_mem_nhdsWithin] with q hq hqU
    filter_upwards [] with a
    simpa only [n07aLpJetField, ite_eq_left hqU.1] using hq a

def n07aLpJetContinuousMultilinear
    (J : ∀ a : α, SmoothDirections U (fun x => f x a))
    (hmem : ∀ k x, x ∈ U → ∀ v : Fin k → E,
      MemLp (fun a => (J a).D k x v) 2 μ)
    (hbound : ∀ k (p : E × (Fin k → E)), p.1 ∈ U →
      ∃ g : α → ℝ, MemLp g 2 μ ∧
        ∀ᶠ q in 𝓝[U ×ˢ univ] p, ∀ a, |(J a).D k q.1 q.2| ≤ g a)
    (k : ℕ) (x : E) : E [×k]→L[ℝ] (Lp ℝ 2 μ) where
  toMultilinearMap := n07aLpJetMultilinear J hmem k x
  cont := by
    classical
    by_cases hx : x ∈ U
    · exact continuousOn_univ.mp
        ((n07aLpJetMultilinear_continuousOn J hmem hbound k).comp
          (continuous_const.prodMk continuous_id).continuousOn
          (fun _ _ => ⟨hx, mem_univ _⟩))
    · have he : (n07aLpJetMultilinear J hmem k x : (Fin k → E) → Lp ℝ 2 μ) =
          fun _ => 0 := by
        funext v
        change (n07aLpJetField_memLp J hmem k x v).toLp
          (n07aLpJetField J k x v) = 0
        simp only [n07aLpJetField, ite_eq_right hx, MemLp.toLp_zero]
      change Continuous (n07aLpJetMultilinear J hmem k x : (Fin k → E) → Lp ℝ 2 μ)
      rw [he]
      exact continuous_const

theorem n07aLpJetContinuousMultilinear_apply
    (J : ∀ a : α, SmoothDirections U (fun x => f x a))
    (hmem : ∀ k x, x ∈ U → ∀ v : Fin k → E,
      MemLp (fun a => (J a).D k x v) 2 μ)
    (hbound : ∀ k (p : E × (Fin k → E)), p.1 ∈ U →
      ∃ g : α → ℝ, MemLp g 2 μ ∧
        ∀ᶠ q in 𝓝[U ×ˢ univ] p, ∀ a, |(J a).D k q.1 q.2| ≤ g a)
    (k : ℕ) (x : E) (v : Fin k → E) :
    n07aLpJetContinuousMultilinear J hmem hbound k x v =
      (n07aLpJetField_memLp J hmem k x v).toLp (n07aLpJetField J k x v) := rfl

/-- The pointwise derivative along the original affine line, after the
irrelevant exterior values have been set to zero. -/
theorem n07aLpJetField_hasDerivAt
    (J : ∀ a : α, SmoothDirections U (fun x => f x a))
    (k : ℕ) (x w : E) (v : Fin k → E) (a : α) {t : ℝ}
    (ht : x + t • w ∈ U) :
    HasDerivAt (fun s => n07aLpJetField J k (x + s • w) v a)
      (n07aLpJetField J (k + 1) (x + t • w) (Fin.cons w v) a) t := by
  classical
  have hd := (J a).derivative k (x + t • w) ht v w
  have hc : Continuous (fun s : ℝ => x + (t + s) • w) :=
    continuous_const.add ((continuous_const.add continuous_id).smul continuous_const)
  have hnear : ∀ᶠ s in 𝓝[≠] (0 : ℝ), x + (t + s) • w ∈ U := by
    have h := (hc.tendsto 0).eventually
      ((J a).open_domain.mem_nhds (by simpa only [add_zero] using ht))
    exact h.filter_mono nhdsWithin_le_nhds
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  simp only [HasProjectiveLineDerivAt, HasProjectiveCurveDerivAt,
    zero_add, zero_smul, add_zero] at hd
  simp only [n07aLpJetField, ite_eq_left ht]
  apply hd.congr'
  filter_upwards [hnear] with s hs
  have hs' : x + (t • w + s • w) ∈ U := by
    simpa only [add_smul] using hs
  simp only [n07aLpJetField, add_smul, add_assoc, ite_eq_left hs']

def n07aLpSmoothDirections
    (hU : IsOpen U) (J : ∀ a : α, SmoothDirections U (fun x => f x a))
    (hmem : ∀ k x, x ∈ U → ∀ v : Fin k → E,
      MemLp (fun a => (J a).D k x v) 2 μ)
    (hbound : ∀ k (p : E × (Fin k → E)), p.1 ∈ U →
      ∃ g : α → ℝ, MemLp g 2 μ ∧
        ∀ᶠ q in 𝓝[U ×ˢ univ] p, ∀ a, |(J a).D k q.1 q.2| ≤ g a) :
    SmoothDirections U (fun x => n07aLpJetMultilinear J hmem 0 x Fin.elim0) where
  open_domain := hU
  D := n07aLpJetContinuousMultilinear J hmem hbound
  zero := fun _ _ => rfl
  continuous := n07aLpJetMultilinear_continuousOn J hmem hbound
  derivative := by
    classical
    intro k x hx v w
    obtain ⟨g, hg, hb⟩ := hbound (k + 1) (x, Fin.cons w v) hx
    have hdom : U ×ˢ (univ : Set (Fin (k + 1) → E)) ∈ 𝓝 (x, Fin.cons w v) :=
      (hU.prod isOpen_univ).mem_nhds ⟨hx, mem_univ _⟩
    rw [nhdsWithin_eq_nhds.mpr hdom] at hb
    have hc : Continuous (fun t : ℝ => (x + t • w, (Fin.cons w v : Fin (k + 1) → E))) := by
      apply Continuous.prodMk
      · exact continuous_const.add (continuous_id.smul continuous_const)
      · exact continuous_const
    have hct : Tendsto
        (fun t : ℝ => (x + t • w, (Fin.cons w v : Fin (k + 1) → E))) (𝓝 0)
        (𝓝 (x, (Fin.cons w v : Fin (k + 1) → E))) := by
      simpa only [zero_smul, add_zero] using hc.tendsto 0
    have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), x + t • w ∈ U ∧
        ∀ a, |(J a).D (k + 1) (x + t • w) (Fin.cons w v)| ≤ g a :=
      ((hct.eventually hdom).mono (fun _ ht => ht.1)).and (hct.eventually hb)
    obtain ⟨δ, hδ, hδb⟩ := Metric.mem_nhds_iff.mp hnear
    have hinterval (t : ℝ) (ht : t ∈ Ioo (-δ) δ) :
        x + t • w ∈ U ∧
        ∀ a, |(J a).D (k + 1) (x + t • w) (Fin.cons w v)| ≤ g a := by
      apply hδb
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using abs_lt.mpr ht
    have hd := spaces_hasDerivAt_toLp_of_dominated_deriv (t₀ := 0)
      (df := fun t => n07aLpJetField J (k + 1) (x + t • w) (Fin.cons w v))
      (fun t => n07aLpJetField_memLp J hmem k (x + t • w) v)
      (by simpa only [zero_smul, add_zero] using
        n07aLpJetField_memLp J hmem (k + 1) x (Fin.cons w v)) hδ hg
      (Filter.Eventually.of_forall fun a t ht =>
        n07aLpJetField_hasDerivAt J k x w v a
          (hinterval t (by simpa only [zero_sub, zero_add] using ht)).1)
      (Filter.Eventually.of_forall fun a t ht => by
        have hh := hinterval t (by simpa only [zero_sub, zero_add] using ht)
        simpa only [n07aLpJetField, ite_eq_left hh.1] using hh.2 a)
    simpa only [HasProjectiveLineDerivAt, HasProjectiveCurveDerivAt,
      n07aLpJetContinuousMultilinear_apply, zero_add, zero_smul, add_zero] using
      hasDerivAt_iff_tendsto_slope_zero.mp hd

/-- Each lifted derivative is the actual L² class of the original
pointwise directional derivative. -/
theorem n07aLpSmoothDirections_D_ae
    (hU : IsOpen U) (J : ∀ a : α, SmoothDirections U (fun x => f x a))
    (hmem : ∀ k x, x ∈ U → ∀ v : Fin k → E,
      MemLp (fun a => (J a).D k x v) 2 μ)
    (hbound : ∀ k (p : E × (Fin k → E)), p.1 ∈ U →
      ∃ g : α → ℝ, MemLp g 2 μ ∧
        ∀ᶠ q in 𝓝[U ×ˢ univ] p, ∀ a, |(J a).D k q.1 q.2| ≤ g a)
    (k : ℕ) {x : E} (hx : x ∈ U) (v : Fin k → E) :
    (((n07aLpSmoothDirections hU J hmem hbound).D k x v) : α → ℝ) =ᵐ[μ]
      (fun a => (J a).D k x v) := by
  classical
  change ((n07aLpJetField_memLp J hmem k x v).toLp
    (n07aLpJetField J k x v) : α → ℝ) =ᵐ[μ] _
  filter_upwards [(n07aLpJetField_memLp J hmem k x v).coeFn_toLp] with a ha
  simpa only [n07aLpJetField, ite_eq_left hx] using ha

end ContinuousFlexibility.Analysis
