import ContinuousFlexibility.Analysis.N05ReferenceCanonicalSymbols
import ContinuousFlexibility.Geometry.EuclideanRigidity
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Extending the actual reference symbols to the closed physical pieces

The operator tests identify the reference symbol away from the reflection
circles.  Continuity of the actual chart and height extends these identities
first through every reflection circle, then to both physical endpoints.
No regularity of the corrected coefficients at exceptional points is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Continuous functions are determined by their values away from the
reflection angles.  The two endpoints of each chamber are treated together. -/
theorem n05_continuous_eq_of_nonreflection
    {E : Type*} [TopologicalSpace E] [T2Space E] {f g : ℝ → E}
    (hf : Continuous f) (hg : Continuous g)
    (heq : ∀ θ, θ ∉ Set.range (fun n : ℤ => (n : ℝ) * (Real.pi / 2)) →
      f θ = g θ) : f = g := by
  funext θ
  by_cases hθ : θ ∈ Set.range (fun n : ℤ => (n : ℝ) * (Real.pi / 2))
  · obtain ⟨n, rfl⟩ := hθ
    have hπ : 0 < Real.pi / 2 := half_pos Real.pi_pos
    have hgap : (n : ℝ) * (Real.pi / 2) <
        ((n : ℝ) + 1) * (Real.pi / 2) :=
      mul_lt_mul_of_pos_right (by linarith) hπ
    have hchamber : EqOn f g
        (Ioo ((n : ℝ) * (Real.pi / 2)) (((n : ℝ) + 1) * (Real.pi / 2))) := by
      intro t ht
      apply heq t
      rintro ⟨k, rfl⟩
      have hlo : (n : ℝ) < (k : ℝ) := lt_of_mul_lt_mul_right ht.1 hπ.le
      have hhi : (k : ℝ) < (n : ℝ) + 1 := lt_of_mul_lt_mul_right ht.2 hπ.le
      have hlo' : n < k := by exact_mod_cast hlo
      have hhi' : k < n + 1 := by exact_mod_cast hhi
      omega
    apply hchamber.closure hf hg
    rw [closure_Ioo hgap.ne]
    exact ⟨le_rfl, hgap.le⟩
  · exact heq θ hθ

/-- Equality off the reflection circles in an open strip extends to the
whole closed strip when both actual functions are continuous there. -/
theorem n05_eqOn_closed_strip_of_nonreflection
    {E : Type*} [TopologicalSpace E] [T2Space E]
    {f g : PolarPoint → E} {a b : ℝ} (hab : a < b)
    (hf : ∀ p : PolarPoint, p.1 ∈ Icc a b → ContinuousAt f p)
    (hg : ∀ p : PolarPoint, p.1 ∈ Icc a b → ContinuousAt g p)
    (heq : ∀ p : PolarPoint, p.1 ∈ Ioo a b →
      p.2 ∉ Set.range (fun n : ℤ => (n : ℝ) * (Real.pi / 2)) → f p = g p) :
    ∀ p : PolarPoint, p.1 ∈ Icc a b → f p = g p := by
  have hinterior (r : ℝ) (hr : r ∈ Ioo a b) (θ : ℝ) :
      f (r, θ) = g (r, θ) := by
    have hfθ : Continuous (fun t : ℝ => f (r, t)) :=
      continuous_iff_continuousAt.mpr fun t =>
        (hf (r, t) ⟨hr.1.le, hr.2.le⟩).comp
          (continuousAt_const.prodMk continuousAt_id)
    have hgθ : Continuous (fun t : ℝ => g (r, t)) :=
      continuous_iff_continuousAt.mpr fun t =>
        (hg (r, t) ⟨hr.1.le, hr.2.le⟩).comp
          (continuousAt_const.prodMk continuousAt_id)
    exact congrFun (n05_continuous_eq_of_nonreflection hfθ hgθ
      (fun t ht => heq (r, t) hr ht)) θ
  intro p hp
  have hfR : ContinuousOn (fun r : ℝ => f (r, p.2)) (Icc a b) := fun r hr =>
    ((hf (r, p.2) hr).comp (f := fun t : ℝ => (t, p.2))
      (continuousAt_id.prodMk continuousAt_const)).continuousWithinAt
  have hgR : ContinuousOn (fun r : ℝ => g (r, p.2)) (Icc a b) := fun r hr =>
    ((hg (r, p.2) hr).comp (f := fun t : ℝ => (t, p.2))
      (continuousAt_id.prodMk continuousAt_const)).continuousWithinAt
  have hR : EqOn (fun r : ℝ => f (r, p.2)) (fun r : ℝ => g (r, p.2)) (Ioo a b) :=
    fun r hr => hinterior r hr p.2
  have hclosure : Icc a b ⊆ closure (Ioo a b) := by
    simpa only [closure_Ioo hab.ne] using (Subset.rfl : Icc a b ⊆ Icc a b)
  exact hR.of_subset_closure hfR hgR Ioo_subset_Icc_self hclosure hp

/-- The reference coefficient formulas are smooth wherever the actual radius
is nonzero, including the endpoints of every physical piece. -/
theorem n05_radialReference_contDiffAt_of_ne_zero
    {D : ReferenceData} (hD : IsAccumulatingProfile D) {p : PolarPoint}
    (hr : p.1 ≠ 0) :
    ContDiffAt ℝ ∞ (n05RadialReferenceCoefficients D).a p ∧
      ContDiffAt ℝ ∞ (n05RadialReferenceCoefficients D).b p ∧
      ContDiffAt ℝ ∞ (n05RadialReferenceCoefficients D).c p := by
  obtain ⟨B, hB⟩ := hD
  have hw : ContDiff ℝ ∞ D.w := hB.1.2.2.1.1
  have hdw : ContDiff ℝ ∞ (deriv D.w) := (contDiff_infty_iff_deriv.mp hw).2
  exact ⟨hw.contDiffAt.comp p contDiffAt_fst, contDiffAt_const,
    (hdw.contDiffAt.comp p contDiffAt_fst).div contDiffAt_fst hr⟩

/-- The actual principal bilinear expression is smooth on smooth data. -/
theorem n05_contDiffAt_principalPair
    {A : SymmetricCoefficients} {f g : PolarPoint → ℝ} {p : PolarPoint}
    (ha : ContDiffAt ℝ ∞ A.a p) (hb : ContDiffAt ℝ ∞ A.b p)
    (hc : ContDiffAt ℝ ∞ A.c p)
    (hf : ContDiffAt ℝ ∞ f p) (hg : ContDiffAt ℝ ∞ g p) :
    ContDiffAt ℝ ∞ (n05PrincipalPair A f g) p := by
  have hfr : ContDiffAt ℝ ∞ (radialPartial f) p := contDiffAt_radialPartial hf (by simp)
  have hft : ContDiffAt ℝ ∞ (angularPartial f) p := contDiffAt_angularPartial hf (by simp)
  have hgr : ContDiffAt ℝ ∞ (radialPartial g) p := contDiffAt_radialPartial hg (by simp)
  have hgt : ContDiffAt ℝ ∞ (angularPartial g) p := contDiffAt_angularPartial hg (by simp)
  exact (((ha.mul hfr).mul hgr).add
    (hb.mul ((hfr.mul hgt).add (hft.mul hgr)))).add ((hc.mul hft).mul hgt)

theorem n05_physical_closed_radius_pos
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (h04 : N04Properties D T S C L K base loss ε)
    {m : ℕ} {r : ℝ} (hr : r ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
    0 < r := by
  rcases h04 with ⟨_, _, _, hpieces, _⟩
  obtain ⟨B, hB⟩ := hD
  have hsub := closure_mono (hpieces m).2.2
  rw [closure_Ioo (hpieces m).1.ne, closure_Ioo hB.1.2.1.ne] at hsub
  exact hB.1.1.trans_le (hsub hr).1

/-- The determinant identity holds at every angle and at both physical
endpoints of each negative piece. -/
theorem n05_negative_reference_determinant_closed
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {m : ℕ} (hm : K.positive m = false) {x : PolarPoint}
    (hx : x.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
    K.height (C.referenceState, 0) m x ^ 4 *
        (D.w x.1 * (deriv D.w x.1 / x.1)) =
      -(K.chart (C.referenceState, 0) m x).1 := by
  have h04 := h.2.2.2.2
  rcases h04 with ⟨_, _, _, hpieces, _, _, _, _, hclosed, _⟩
  have h01 := h.1.1.1
  have hmem : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    n05_referenceState_mem h01.2.1
  have hsector := n05_referenceState_sector h01.2.2.1
  have hF (p : PolarPoint)
      (hp : p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
      ContinuousAt (fun q : PolarPoint =>
        K.height (C.referenceState, 0) m q ^ 4 *
          (D.w q.1 * (deriv D.w q.1 / q.1))) p := by
    obtain ⟨_, hh, _, _⟩ := hclosed (C.referenceState, 0) hmem hsector m p hp
    obtain ⟨ha, _, hc⟩ := n05_radialReference_contDiffAt_of_ne_zero h01.1.1 (p := p)
      (n05_physical_closed_radius_pos h01.1.1 h.2.2.2.2 hp).ne'
    exact ((hh.pow 4).mul (ha.mul hc)).continuousAt
  have hG (p : PolarPoint)
      (hp : p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
      ContinuousAt (fun q : PolarPoint => -(K.chart (C.referenceState, 0) m q).1) p :=
    (hclosed (C.referenceState, 0) hmem hsector m p hp).1.fst.neg.continuousAt
  exact n05_eqOn_closed_strip_of_nonreflection (hpieces m).1 hF hG
    (fun p hp hθ => n05_negative_reference_determinant_nonreflection hT hS h hm
      (x := p) ⟨hp, mem_univ _⟩ hθ) x hx

/-- All three principal entries extend through every reflection circle and
to both physical endpoints, using only the actual smooth chart and height. -/
theorem n05_negative_reference_symbol_closed
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {m : ℕ} (hm : K.positive m = false) {x : PolarPoint}
    (hx : x.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
    let z := (C.referenceState, 0)
    let ξ := fun y => (K.chart z m y).1
    let φ := fun y => (K.chart z m y).2
    K.height z m x ^ 2 * n05PrincipalPair (n05RadialReferenceCoefficients D) ξ ξ x =
        |planeJacobian (K.chart z m) x| ∧
      K.height z m x ^ 2 * n05PrincipalPair (n05RadialReferenceCoefficients D) ξ φ x = 0 ∧
      K.height z m x ^ 2 * n05PrincipalPair (n05RadialReferenceCoefficients D) φ φ x =
        |planeJacobian (K.chart z m) x| * (-ξ x) := by
  let z : AnnularState S × ℝ := (C.referenceState, 0)
  let Ψ : PolarPoint → PolarPoint := K.chart z m
  let ξ : PolarPoint → ℝ := fun y => (Ψ y).1
  let φ : PolarPoint → ℝ := fun y => (Ψ y).2
  change K.height z m x ^ 2 * n05PrincipalPair (n05RadialReferenceCoefficients D) ξ ξ x =
      |planeJacobian Ψ x| ∧
    K.height z m x ^ 2 * n05PrincipalPair (n05RadialReferenceCoefficients D) ξ φ x = 0 ∧
    K.height z m x ^ 2 * n05PrincipalPair (n05RadialReferenceCoefficients D) φ φ x =
      |planeJacobian Ψ x| * (-ξ x)
  have h04 := h.2.2.2.2
  rcases h04 with ⟨_, _, _, hpieces, _, _, _, _, hclosed, _⟩
  have h01 := h.1.1.1
  have hmem : z ∈ stateNeighborhood S C base ε := n05_referenceState_mem h01.2.1
  have hsector := n05_referenceState_sector h01.2.2.1
  have hΨ (p : PolarPoint)
      (hp : p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
      ContDiffAt ℝ ∞ Ψ p := (hclosed z hmem hsector m p hp).1
  have hξ (p : PolarPoint)
      (hp : p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
      ContDiffAt ℝ ∞ ξ p := (hΨ p hp).fst
  have hφ (p : PolarPoint)
      (hp : p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
      ContDiffAt ℝ ∞ φ p := (hΨ p hp).snd
  have hpair (f g : PolarPoint → ℝ)
      (hf : ∀ p : PolarPoint, p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m) →
        ContDiffAt ℝ ∞ f p)
      (hg : ∀ p : PolarPoint, p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m) →
        ContDiffAt ℝ ∞ g p)
      (p : PolarPoint) (hp : p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
      ContinuousAt (fun q : PolarPoint => K.height z m q ^ 2 *
        n05PrincipalPair (n05RadialReferenceCoefficients D) f g q) p := by
    have hh := (hclosed z hmem hsector m p hp).2.1
    obtain ⟨ha, hb, hc⟩ := n05_radialReference_contDiffAt_of_ne_zero h01.1.1 (p := p)
      (n05_physical_closed_radius_pos h01.1.1 h.2.2.2.2 hp).ne'
    exact ((hh.pow 2).mul
      (n05_contDiffAt_principalPair ha hb hc (hf p hp) (hg p hp))).continuousAt
  have hJ (p : PolarPoint)
      (hp : p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
      ContinuousAt (fun q : PolarPoint => |planeJacobian Ψ q|) p :=
    (contDiffAt_planeJacobian (hΨ p hp)).continuousAt.abs
  have hnon (p : PolarPoint)
      (hp : p.1 ∈ Ioo (K.physicalLeft m) (K.physicalRight m))
      (hθ : p.2 ∉ Set.range (fun n : ℤ => (n : ℝ) * (Real.pi / 2))) :=
    n05_negative_reference_symbol_nonreflection hT hS h hm (x := p) ⟨hp, mem_univ _⟩ hθ
  refine ⟨?_, ?_, ?_⟩
  · exact n05_eqOn_closed_strip_of_nonreflection (hpieces m).1
      (hpair ξ ξ hξ hξ) hJ (fun p hp hθ => (hnon p hp hθ).1) x hx
  · exact n05_eqOn_closed_strip_of_nonreflection (hpieces m).1
      (hpair ξ φ hξ hφ) (fun _ _ => continuousAt_const)
      (fun p hp hθ => (hnon p hp hθ).2.1) x hx
  · exact n05_eqOn_closed_strip_of_nonreflection (hpieces m).1
      (hpair φ φ hφ hφ) (fun p hp => (hJ p hp).mul (hξ p hp).continuousAt.neg)
      (fun p hp hθ => (hnon p hp hθ).2.2) x hx

/-- A physical profile root on the boundary maps to the actual Tricomi root. -/
theorem n05_negative_reference_root_image
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {m : ℕ} (hm : K.positive m = false) {x : PolarPoint}
    (hx : x.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m))
    (hroot : deriv D.w x.1 = 0) :
    (K.chart (C.referenceState, 0) m x).1 = 0 := by
  have heq := n05_negative_reference_determinant_closed hT hS h hm hx
  rw [hroot, zero_div, mul_zero, mul_zero] at heq
  linarith only [heq]

end ContinuousFlexibility.Statements

