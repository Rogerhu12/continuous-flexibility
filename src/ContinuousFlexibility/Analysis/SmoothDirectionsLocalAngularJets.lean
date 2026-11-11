import ContinuousFlexibility.Analysis.SmoothDirectionsLocalLabels
import Mathlib.Topology.Order.ProjIcc

/-!
# Local spatial differentiation of actual parameter jets

The angular fundamental theorem is used only on a closed subinterval of
the spatial domain. Clamping the label supplies global continuity for
the integral argument without assuming derivatives at the endpoints.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped Topology BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {U : Set E}

private theorem local_angular_integral_identity_next_jet
    {f g : ℝ → E → ℝ}
    (J : ∀ θ, SmoothDirections U (f θ)) (K : ∀ θ, SmoothDirections U (g θ))
    (hU : IsOpen U) (hbound : UniformScalarJetSeminormBounds K)
    (hcont : ∀ n x, x ∈ U → ∀ v : Fin n → E,
      Continuous (fun θ => (K θ).D n x v))
    {l h : ℝ} {n : ℕ}
    (hangular : ∀ θ ∈ Ioo l h, ∀ x, x ∈ U → ∀ v : Fin n → E,
      HasDerivAt (fun ψ => (J ψ).D n x v) ((K θ).D n x v) θ)
    (x : E) (hx : x ∈ U) (v : Fin n → E) (w : E)
    {a b : ℝ} (ha : a ∈ Ioo l h) (hb : b ∈ Ioo l h) :
    (J b).D (n + 1) x (Fin.cons w v) - (J a).D (n + 1) x (Fin.cons w v) =
      ∫ θ in a..b, (K θ).D (n + 1) x (Fin.cons w v) := by
  have hab : uIcc a b ⊆ Ioo l h := by
    intro θ hθ
    exact ⟨(lt_min ha.1 hb.1).trans_le hθ.1, hθ.2.trans_lt (max_lt ha.2 hb.2)⟩
  have hI := hasDerivAt_integral_directional_jet K hU hbound hcont n x hx v w a b
  have hx0 : x + (0 : ℝ) • w ∈ U := by simpa only [zero_smul, add_zero] using hx
  have hD : HasDerivAt
      (fun t : ℝ => (J b).D n (x + t • w) v - (J a).D n (x + t • w) v)
      ((J b).D (n + 1) x (Fin.cons w v) - (J a).D (n + 1) x (Fin.cons w v)) 0 := by
    simpa only [zero_smul, add_zero] using
      ((J b).hasDerivAt_line_jet x w n v hx0).fun_sub
        ((J a).hasDerivAt_line_jet x w n v hx0)
  have hline : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), x + t • w ∈ U :=
    (continuous_const.add (continuous_id.smul continuous_const)).continuousAt.eventually
      (hU.mem_nhds hx0)
  have heq : (fun t : ℝ => ∫ θ in a..b, (K θ).D n (x + t • w) v) =ᶠ[𝓝 (0 : ℝ)]
      (fun t : ℝ => (J b).D n (x + t • w) v - (J a).D n (x + t • w) v) := by
    filter_upwards [hline] with t ht
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun θ hθ => hangular θ (hab hθ) _ ht v) ((hcont n _ ht v).intervalIntegrable a b)
  exact hD.unique (hI.congr_of_eventuallyEq heq.symm)

/-- Only the zeroth-order spatial derivative is a premise. All higher
parameter orders follow by differentiating the actual local FTC identity. -/
theorem smoothDirections_local_angular_jet_hasDerivAt
    {f g : ℝ → E → ℝ}
    (J : ∀ θ, SmoothDirections U (f θ)) (K : ∀ θ, SmoothDirections U (g θ))
    (hU : IsOpen U) (hc : Convex ℝ U)
    (hf : ∀ x ∈ U, Continuous (fun θ => f θ x))
    (hg : ∀ x ∈ U, Continuous (fun θ => g θ x))
    (hJ : UniformScalarJetSeminormBounds J) (hK : UniformScalarJetSeminormBounds K)
    {l h : ℝ}
    (hangular : ∀ θ ∈ Ioo l h, ∀ x, x ∈ U →
      HasDerivAt (fun ψ => f ψ x) (g θ x) θ) :
    ∀ n θ, θ ∈ Ioo l h → ∀ x, x ∈ U → ∀ v : Fin n → E,
      HasDerivAt (fun ψ => (J ψ).D n x v) ((K θ).D n x v) θ := by
  have hcontK : ∀ n x, x ∈ U → ∀ v : Fin n → E,
      Continuous (fun θ => (K θ).D n x v) :=
    fun n x hx v => smoothDirections_label_jet_continuous K hU hc hg hK n x hx v
  intro n
  induction n with
  | zero =>
      intro θ hθ x hx v
      have hv : v = Fin.elim0 := Subsingleton.elim _ _
      have heq : (fun ψ => (J ψ).D 0 x v) = (fun ψ => f ψ x) := by
        funext ψ
        rw [hv, (J ψ).zero x hx]
      rw [heq, hv, (K θ).zero x hx]
      exact hangular θ hθ x hx
  | succ n ih =>
      intro θ hθ x hx v
      have hidentity (ψ : ℝ) (hψ : ψ ∈ Ioo l h) :
          (J ψ).D (n + 1) x v - (J θ).D (n + 1) x v =
            ∫ t in θ..ψ, (K t).D (n + 1) x v := by
        simpa only [Fin.cons_self_tail] using
          local_angular_integral_identity_next_jet J K hU hK hcontK ih
            x hx (Fin.tail v) (v 0) hθ hψ
      have hI := ((hcontK (n + 1) x hx v).integral_hasStrictDerivAt θ θ).hasDerivAt
      have heq : (fun ψ => (J ψ).D (n + 1) x v) =ᶠ[𝓝 θ]
          (fun ψ => (J θ).D (n + 1) x v +
            ∫ t in θ..ψ, (K t).D (n + 1) x v) := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with ψ hψ
        linarith only [hidentity ψ hψ]
      exact (hI.const_add ((J θ).D (n + 1) x v)).congr_of_eventuallyEq heq

/-- The tower need only be defined on the spatial label domain. Bounds
are required on one closed interval inside it. -/
theorem localScalarJet_hasDerivAt_on_Ioo
    {V : Set ℝ} {f g : ℝ → E → ℝ}
    (J : ∀ θ, θ ∈ V → SmoothDirections U (f θ))
    (K : ∀ θ, θ ∈ V → SmoothDirections U (g θ))
    (hU : IsOpen U) (hc : Convex ℝ U) {l h : ℝ} (hlh : l < h)
    (hsub : Icc l h ⊆ V)
    (hf : ∀ x ∈ U, ContinuousOn (fun θ => f θ x) (Icc l h))
    (hg : ∀ x ∈ U, ContinuousOn (fun θ => g θ x) (Icc l h))
    (hJ : UniformScalarJetSeminormBounds
      (fun θ : Icc l h => J θ (hsub θ.property)))
    (hK : UniformScalarJetSeminormBounds
      (fun θ : Icc l h => K θ (hsub θ.property)))
    (hangular : ∀ θ ∈ Ioo l h, ∀ x, x ∈ U →
      HasDerivAt (fun ψ => f ψ x) (g θ x) θ)
    (n : ℕ) {θ : ℝ} (hθ : θ ∈ Ioo l h) (x : E) (hx : x ∈ U) (v : Fin n → E) :
    HasDerivAt (localScalarJet J n x v) (localScalarJet K n x v θ) θ := by
  let c : ℝ → Icc l h := projIcc l h hlh.le
  let Jc : ∀ ψ, SmoothDirections U (f (c ψ)) := fun ψ => J (c ψ) (hsub (c ψ).property)
  let Kc : ∀ ψ, SmoothDirections U (g (c ψ)) := fun ψ => K (c ψ) (hsub (c ψ).property)
  have hccont : Continuous (fun ψ => (c ψ : ℝ)) :=
    continuous_subtype_val.comp continuous_projIcc
  have hceq (ψ : ℝ) (hψ : ψ ∈ Icc l h) : (c ψ : ℝ) = ψ := by
    exact congrArg Subtype.val (projIcc_of_mem hlh.le hψ)
  have hfc : ∀ z ∈ U, Continuous (fun ψ => f (c ψ) z) :=
    fun z hz => (hf z hz).comp_continuous hccont (fun ψ => (c ψ).property)
  have hgc : ∀ z ∈ U, Continuous (fun ψ => g (c ψ) z) :=
    fun z hz => (hg z hz).comp_continuous hccont (fun ψ => (c ψ).property)
  have hderiv : ∀ ψ ∈ Ioo l h, ∀ z, z ∈ U →
      HasDerivAt (fun t => f (c t) z) (g (c ψ) z) ψ := by
    intro ψ hψ z hz
    rw [hceq ψ ⟨hψ.1.le, hψ.2.le⟩]
    apply (hangular ψ hψ z hz).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hψ] with t ht
    rw [hceq t ⟨ht.1.le, ht.2.le⟩]
  have hd := smoothDirections_local_angular_jet_hasDerivAt Jc Kc hU hc hfc hgc
    (hJ.reindex c) (hK.reindex c) hderiv n θ hθ x hx v
  have hvalue : (Kc θ).D n x v = localScalarJet K n x v θ := by
    rw [localScalarJet_of_mem K n x v (hsub ⟨hθ.1.le, hθ.2.le⟩)]
    simp only [Kc, c, projIcc_of_mem hlh.le (show θ ∈ Icc l h from ⟨hθ.1.le, hθ.2.le⟩)]
  apply (hd.congr_deriv hvalue).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hθ] with ψ hψ
  rw [localScalarJet_of_mem J n x v (hsub ⟨hψ.1.le, hψ.2.le⟩)]
  simp only [Jc, c, projIcc_of_mem hlh.le (show ψ ∈ Icc l h from ⟨hψ.1.le, hψ.2.le⟩)]

/-- Local bounds in an arbitrary spatial label suffice along every
continuous spatial curve for which the zeroth derivative is known. -/
theorem localScalarJet_hasDerivAt_along
    {Y : Type*} [TopologicalSpace Y] {V : Set Y} {f g : Y → E → ℝ}
    (J : ∀ y, y ∈ V → SmoothDirections U (f y))
    (K : ∀ y, y ∈ V → SmoothDirections U (g y))
    (hU : IsOpen U) (hc : Convex ℝ U)
    (hf : ∀ x ∈ U, ContinuousOn (fun y => f y x) V)
    (hg : ∀ x ∈ U, ContinuousOn (fun y => g y x) V)
    (hJ : LocalUniformScalarJetSeminormBounds J)
    (hK : LocalUniformScalarJetSeminormBounds K)
    (σ : ℝ → Y) (hσ : Continuous σ)
    (hderiv : ∀ t, σ t ∈ V → ∀ x, x ∈ U →
      HasDerivAt (fun r => f (σ r) x) (g (σ t) x) t)
    (n : ℕ) {t : ℝ} (ht : σ t ∈ V) (x : E) (hx : x ∈ U) (v : Fin n → E) :
    HasDerivAt (fun r => localScalarJet J n x v (σ r))
      (localScalarJet K n x v (σ t)) t := by
  obtain ⟨WJ, hJV, hWJ, htJ, hbJ⟩ := hJ (σ t) ht
  obtain ⟨WK, hKV, hWK, htK, hbK⟩ := hK (σ t) ht
  have hnear : σ ⁻¹' (WJ ∩ WK) ∈ 𝓝 t :=
    hσ.continuousAt.preimage_mem_nhds ((hWJ.inter hWK).mem_nhds ⟨htJ, htK⟩)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let l : ℝ := t - δ / 2
  let h : ℝ := t + δ / 2
  have hlh : l < h := by dsimp only [l, h]; linarith
  have htI : t ∈ Ioo l h := by constructor <;> dsimp only [l, h] <;> linarith
  have hclosed : ∀ r ∈ Icc l h, σ r ∈ WJ ∩ WK := by
    intro r hr
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    have hrd : |r - t| ≤ δ / 2 := by
      apply abs_le.mpr
      dsimp only [l, h] at hr
      constructor <;> linarith only [hr.1, hr.2]
    exact hrd.trans_lt (by linarith)
  let Vσ : Set ℝ := σ ⁻¹' V
  let Jσ : ∀ r, r ∈ Vσ → SmoothDirections U (f (σ r)) := fun r hr => J (σ r) hr
  let Kσ : ∀ r, r ∈ Vσ → SmoothDirections U (g (σ r)) := fun r hr => K (σ r) hr
  have hsub : Icc l h ⊆ Vσ := fun r hr => hJV (hclosed r hr).1
  have hjb : UniformScalarJetSeminormBounds
      (fun r : Icc l h => Jσ r (hsub r.property)) :=
    hbJ.reindex (fun r : Icc l h => (⟨σ r, (hclosed r r.property).1⟩ : WJ))
  have hkb : UniformScalarJetSeminormBounds
      (fun r : Icc l h => Kσ r (hsub r.property)) :=
    hbK.reindex (fun r : Icc l h => (⟨σ r, (hclosed r r.property).2⟩ : WK))
  have hd := localScalarJet_hasDerivAt_on_Ioo Jσ Kσ hU hc hlh hsub
    (fun z hz => (hf z hz).comp hσ.continuousOn hsub)
    (fun z hz => (hg z hz).comp hσ.continuousOn hsub) hjb hkb
    (fun r hr z hz => hderiv r (hsub ⟨hr.1.le, hr.2.le⟩) z hz)
    n htI x hx v
  simpa only [localScalarJet, Jσ, Kσ, Vσ, mem_preimage] using hd

end ContinuousFlexibility.Analysis
