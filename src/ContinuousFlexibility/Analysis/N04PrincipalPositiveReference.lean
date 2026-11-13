import ContinuousFlexibility.Analysis.N04PrincipalPositiveDensity
import ContinuousFlexibility.Analysis.WholeReferenceGaugeReferencePrincipal

/-!
# Reference inverse factors for the principal formulas

The inverse point at the reference state lies in the fixed physical
interval.  Evaluating the frozen reference-atom bounds there controls
both the pulled height and its reciprocal.  The genuine inverse
Jacobian identity similarly exchanges the two Jacobian atoms.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint CanonicalGeometry
open scoped ContDiff Topology

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

/-- A canonical point has a reference inverse point represented in the
same fixed physical unit strip used by the geometry atoms. -/
theorem n04PrincipalPositive_reference_inverse_unitPoint {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (m : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalOpen (G.S η) (G.V η) m) :
    ∃ q : unitStrip, physicalUnitPoint (G.V η) m q.val =
      (G.V η).inverseChart (G.ref η) m p := by
  have hA := (G.n04PrincipalPositive_admissible_parts h η).1
  have hz : G.ref η ∈ stateNeighborhood (G.S η) (G.C η) b ε :=
    reference_mem_stateNeighborhood (G.S η) (G.C η) b h.2.1
  have hs : stateSector (G.S η) (G.C η).referenceState :=
    G.W.through03.1.1.2.2.1.stateSector
  let x := (G.V η).inverseChart (G.ref η) m p
  have hx : x ∈ referencePhysicalPieceOpen (G.S η) (G.V η) m := by
    rw [← hA.referenceDomain m]
    exact (hA.charts (G.ref η) hz hs m).2.1 hp
  have hlen : 0 < (G.V η).physicalRight m - (G.V η).physicalLeft m :=
    sub_pos.mpr (hA.referenceBounds m).1
  let q : PolarPoint :=
    ((x.1 - (G.V η).physicalLeft m) /
      ((G.V η).physicalRight m - (G.V η).physicalLeft m), x.2)
  have hq : q ∈ unitStrip := by
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩
    · exact div_pos (sub_pos.mpr hx.1.1) hlen
    · exact (div_lt_one hlen).mpr (sub_lt_sub_right hx.1.2 _)
  refine ⟨⟨q, hq⟩, ?_⟩
  apply Prod.ext
  · dsimp only [physicalUnitPoint, q]
    rw [mul_div_cancel₀ _ hlen.ne']
    ring
  · rfl

/-- One coefficient-power bound controls the reference pulled height and
its reciprocal on every canonical piece. -/
theorem n04PrincipalPositive_reference_pulledHeight_bounds {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η)) :
    ∃ B : ℝ, 0 < B ∧ ∀ m p, p ∈ canonicalOpen (G.S η) (G.V η) m →
      0 < (G.V η).height (G.ref η) m ((G.V η).inverseChart (G.ref η) m p) ∧
      |(G.V η).height (G.ref η) m ((G.V η).inverseChart (G.ref η) m p)| ≤
        B * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ B ∧
      |((G.V η).height (G.ref η) m ((G.V η).inverseChart (G.ref η) m p))⁻¹| ≤
        B * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ B := by
  have hb := href.2 0
  refine ⟨hb.choose, hb.choose_spec.1, ?_⟩
  intro m p hp
  have hq := G.n04PrincipalPositive_reference_inverse_unitPoint h η m hp
  let q := hq.choose
  have he := hq.choose_spec
  have hA := (G.n04PrincipalPositive_admissible_parts h η).1
  have hz : G.ref η ∈ stateNeighborhood (G.S η) (G.C η) b ε :=
    reference_mem_stateNeighborhood (G.S η) (G.C η) b h.2.1
  have hs : stateSector (G.S η) (G.C η).referenceState :=
    G.W.through03.1.1.2.2.1.stateSector
  have hc := hA.charts (G.ref η) hz hs m
  have hx := hc.2.1 hp
  have hpheight := (hc.2.2.2.2.2.2.2 _ hx).1
  have hheight := hb.choose_spec.2 m .height q.val q.property 0 0 (by omega)
  have hinverse := hb.choose_spec.2 m .heightInverse q.val q.property 0 0 (by omega)
  simp only [spaces_mixedDerivative_zero, atom] at hheight hinverse
  rw [he] at hheight hinverse
  exact ⟨hpheight, hheight, hinverse⟩

/-- The inverse Jacobian and its reciprocal have reference bounds from
the original Jacobian atoms at the actual reference inverse point. -/
theorem n04PrincipalPositive_reference_inverseJacobian_bounds {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η)) :
    ∃ B : ℝ, 0 < B ∧ ∀ m p, p ∈ canonicalOpen (G.S η) (G.V η) m →
      |planeJacobian ((G.V η).inverseChart (G.ref η) m) p| ≤
        B * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ B ∧
      |planeJacobian ((G.V η).inverseChart (G.ref η) m) p|⁻¹ ≤
        B * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ B := by
  have hb := href.2 0
  refine ⟨hb.choose, hb.choose_spec.1, ?_⟩
  intro m p hp
  have hq := G.n04PrincipalPositive_reference_inverse_unitPoint h η m hp
  let q := hq.choose
  have he := hq.choose_spec
  have hA := (G.n04PrincipalPositive_admissible_parts h η).1
  have hz : G.ref η ∈ stateNeighborhood (G.S η) (G.C η) b ε :=
    reference_mem_stateNeighborhood (G.S η) (G.C η) b h.2.1
  have hs : stateSector (G.S η) (G.C η).referenceState :=
    G.W.through03.1.1.2.2.1.stateSector
  have hc := hA.charts (G.ref η) hz hs m
  let F := (G.V η).chart (G.ref η) m
  let I := (G.V η).inverseChart (G.ref η) m
  let x := I p
  have hx : x ∈ physicalPieceOpen (G.S η) (G.V η) (G.ref η) m := hc.2.1 hp
  have hFx : F x = p := hc.2.2.2.1 p hp
  have hΩ : IsOpen (physicalPieceOpen (G.S η) (G.V η) (G.ref η) m) :=
    (hA.domains (G.ref η) hz hs m).1
  have hU : IsOpen (canonicalOpen (G.S η) (G.V η) m) :=
    isOpen_Ioo.prod isOpen_univ
  have hF : DifferentiableAt ℝ F x :=
    ((hc.2.2.2.2.1 x hx).contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)
  have hI : DifferentiableAt ℝ I (F x) := by
    rw [hFx]
    exact ((hc.2.2.2.2.2.1 p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hinverse : I ∘ F =ᶠ[𝓝 x] (id : PolarPoint → PolarPoint) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact hc.2.2.1 y hy
  have hJ : planeJacobian F x ≠ 0 := (hc.2.2.2.2.2.2.2 x hx).2.1
  have hprod := planeJacobian_inverse_mul_of_germ hF hI hinverse
  rw [hFx] at hprod
  have hJI : planeJacobian I p = 1 / planeJacobian F x :=
    (eq_div_iff hJ).mpr hprod
  have hforward := hb.choose_spec.2 m .jacobian q.val q.property 0 0 (by omega)
  have hforwardInv := hb.choose_spec.2 m .jacobianInverse q.val q.property 0 0 (by omega)
  simp only [spaces_mixedDerivative_zero, atom, abs_abs, abs_inv] at hforward hforwardInv
  rw [he] at hforward hforwardInv
  change |planeJacobian I p| ≤ _ ∧ |planeJacobian I p|⁻¹ ≤ _
  rw [hJI, one_div, abs_inv, inv_inv]
  exact ⟨hforwardInv, hforward⟩

end N04RealizationGauge

end ContinuousFlexibility.Analysis
