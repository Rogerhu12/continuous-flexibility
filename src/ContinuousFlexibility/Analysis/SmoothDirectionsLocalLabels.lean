import ContinuousFlexibility.Analysis.SmoothDirectionsAngularJets

/-!
# Parameter jets with a local spatial label

The spatial label is allowed to range over an open subset. Uniform
seminorm bounds and continuity of the actual scalar functions imply
continuity of their given parameter jets. No continuity of higher jets
is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {U : Set E}

theorem UniformScalarJetSeminormBounds.reindex
    {ι κ : Type*} {f : ι → E → ℝ} {J : ∀ i, SmoothDirections U (f i)}
    (h : UniformScalarJetSeminormBounds J) (c : κ → ι) :
    UniformScalarJetSeminormBounds (fun k => J (c k)) := by
  intro n
  obtain ⟨p, B, hp, hB, hb⟩ := h n
  exact ⟨p, B, hp, hB, fun k x hx v => hb (c k) x hx v⟩

theorem smoothDirections_label_jet_continuous
    {Y : Type*} [TopologicalSpace Y] {f : Y → E → ℝ}
    (J : ∀ y, SmoothDirections U (f y)) (hU : IsOpen U) (hc : Convex ℝ U)
    (hf : ∀ x ∈ U, Continuous (fun y => f y x))
    (hbound : UniformScalarJetSeminormBounds J)
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) :
    Continuous (fun y => (J y).D n x v) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  change Tendsto (fun z => (J z).D n x v) (𝓝 y) (𝓝 ((J y).D n x v))
  obtain ⟨K, hK⟩ := exists_smoothDirections_of_uniform_seminorm_bounds
    (l := 𝓝 y) J hU hc (fun z hz => (hf z hz).tendsto y) hbound
  have heq : K.D n x = (J y).D n x := K.unique (J y) n x hx
  simpa only [heq] using hK n x hx v

/-- The actual parameter jet on the spatial domain, extended by zero
only to make spatial differentiation a function on the ambient space. -/
def localScalarJet {Y : Type*} {V : Set Y} {f : Y → E → ℝ}
    (J : ∀ y, y ∈ V → SmoothDirections U (f y))
    (n : ℕ) (x : E) (v : Fin n → E) (y : Y) : ℝ := by
  classical
  exact if hy : y ∈ V then (J y hy).D n x v else 0

theorem localScalarJet_of_mem {Y : Type*} {V : Set Y} {f : Y → E → ℝ}
    (J : ∀ y, y ∈ V → SmoothDirections U (f y))
    (n : ℕ) (x : E) (v : Fin n → E) {y : Y} (hy : y ∈ V) :
    localScalarJet J n x v y = (J y hy).D n x v := by
  simp only [localScalarJet, dif_pos hy]

theorem localScalarJet_continuousOn_of_uniform_bounds
    {Y : Type*} [TopologicalSpace Y] {V : Set Y} {f : Y → E → ℝ}
    (J : ∀ y, y ∈ V → SmoothDirections U (f y))
    (hU : IsOpen U) (hc : Convex ℝ U)
    (hf : ∀ x ∈ U, ContinuousOn (fun y => f y x) V)
    (hbound : UniformScalarJetSeminormBounds (fun y : V => J y y.property))
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) :
    ContinuousOn (localScalarJet J n x v) V := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hh := smoothDirections_label_jet_continuous (fun y : V => J y y.property)
    hU hc (fun z hz => (hf z hz).domRestrict) hbound n x hx v
  convert hh using 1
  funext y
  exact localScalarJet_of_mem J n x v y.property

/-- A neighborhood may depend on the spatial point. The seminorm in
each bound may depend on the parameter order. -/
def LocalUniformScalarJetSeminormBounds
    {Y : Type*} [TopologicalSpace Y] {V : Set Y} {f : Y → E → ℝ}
    (J : ∀ y, y ∈ V → SmoothDirections U (f y)) : Prop :=
  ∀ y ∈ V, ∃ W : Set Y, ∃ hWV : W ⊆ V,
    IsOpen W ∧ y ∈ W ∧
      UniformScalarJetSeminormBounds (fun z : W => J z (hWV z.property))

theorem localScalarJet_continuousOn_of_local_uniform_bounds
    {Y : Type*} [TopologicalSpace Y] {V : Set Y} {f : Y → E → ℝ}
    (J : ∀ y, y ∈ V → SmoothDirections U (f y))
    (hU : IsOpen U) (hc : Convex ℝ U)
    (hf : ∀ x ∈ U, ContinuousOn (fun y => f y x) V)
    (hbound : LocalUniformScalarJetSeminormBounds J)
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) :
    ContinuousOn (localScalarJet J n x v) V := by
  intro y hy
  obtain ⟨W, hWV, hW, hyW, hb⟩ := hbound y hy
  let K : ∀ z, z ∈ W → SmoothDirections U (f z) := fun z hz => J z (hWV hz)
  have hcont := localScalarJet_continuousOn_of_uniform_bounds K hU hc
    (fun z hz => (hf z hz).mono hWV) hb n x hx v
  apply ContinuousAt.continuousWithinAt
  apply (hcont.continuousAt (hW.mem_nhds hyW)).congr_of_eventuallyEq
  filter_upwards [hW.mem_nhds hyW] with z hz
  rw [localScalarJet_of_mem J n x v (hWV hz), localScalarJet_of_mem K n x v hz]

end ContinuousFlexibility.Analysis
