import ContinuousFlexibility.Analysis.N06RelativeConstruction
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Extending the N06 perturbation from a dense source core

The perturbation is first a linear map on a dense core of the source space. A uniform norm
bound gives its continuous extension on that same source space. Closed relations then pass
from the core to the whole space. The final theorem keeps both the analytic bound and the
closedness of the physical relation as explicit hypotheses.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

section DenseCore

variable {Core E X : Type*} [AddCommGroup Core] [Module ℝ Core]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The bounded extension on the original source space, not a newly chosen completion. -/
def n06DenseExtension (i : Core →ₗ[ℝ] E) (R₀ : Core →ₗ[ℝ] E) : E →L[ℝ] E :=
  R₀.extendOfNorm i

theorem n06DenseExtension_on_core (i : Core →ₗ[ℝ] E) (R₀ : Core →ₗ[ℝ] E)
    (hdense : DenseRange i) {q : ℝ}
    (hbound : ∀ f : Core, ‖R₀ f‖ ≤ q * ‖i f‖) (f : Core) :
    n06DenseExtension i R₀ (i f) = R₀ f :=
  LinearMap.extendOfNorm_eq hdense ⟨q, hbound⟩ f

theorem norm_n06DenseExtension_le (i : Core →ₗ[ℝ] E) (R₀ : Core →ₗ[ℝ] E)
    (hdense : DenseRange i) {q : ℝ} (hq : 0 ≤ q)
    (hbound : ∀ f : Core, ‖R₀ f‖ ≤ q * ‖i f‖) :
    ‖n06DenseExtension i R₀‖ ≤ q :=
  LinearMap.opNorm_extendOfNorm_le hdense hq hbound

/-- A closed relation verified on the dense core holds for the extended operator. -/
theorem n06DenseExtension_closedRelation (i : Core →ₗ[ℝ] E) (R₀ : Core →ₗ[ℝ] E)
    (hdense : DenseRange i) {q : ℝ}
    (hbound : ∀ f : Core, ‖R₀ f‖ ≤ q * ‖i f‖)
    (G : E →L[ℝ] X) (Rel : X → E → Prop)
    (hclosed : IsClosed {p : X × E | Rel p.1 p.2})
    (hcore : ∀ f : Core, Rel (G (i f)) (i f + R₀ f)) (F : E) :
    Rel (G F) (F + n06DenseExtension i R₀ F) := by
  refine hdense.induction_on
    (p := fun F => Rel (G F) (F + n06DenseExtension i R₀ F)) F ?_ ?_
  · exact hclosed.preimage
      (G.continuous.prodMk (continuous_id.add (n06DenseExtension i R₀).continuous))
  · intro f
    rw [n06DenseExtension_on_core i R₀ hdense hbound]
    exact hcore f

end DenseCore

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis

section FixedGraph

variable {S : PhysicalSpacesData} {K : CanonicalData S} {V : VolumeModelData S K}
  {b : ℕ}

/-- The existing graph's source projection is continuous for its inherited product norm. -/
def n06SourceProjection (B : CanonicalDomainData S K V b) :
    B.Space →L[ℝ] V.level (3 / 4 : ℝ) 0 b :=
  (ContinuousLinearMap.snd ℝ (CanonicalUnknown S K) (V.level (3 / 4 : ℝ) 0 b)).comp
    B.graph.subtypeL

theorem n06SourceProjection_apply (B : CanonicalDomainData S K V b) (u : B.Space) :
    n06SourceProjection B u = u.val.2 := by
  simp only [n06SourceProjection, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_snd', Submodule.subtypeL_apply]

/-- The fixed-domain perturbed operator obtained from its relative source operator. -/
def n06OperatorFromRelative (B : CanonicalDomainData S K V b)
    (R : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b) :
    B.Space →L[ℝ] V.level (3 / 4 : ℝ) 0 b :=
  (ContinuousLinearMap.id ℝ (V.level (3 / 4 : ℝ) 0 b) + R).comp (n06SourceProjection B)

theorem n06OperatorFromRelative_apply (B : CanonicalDomainData S K V b)
    (R : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b) (u : B.Space) :
    n06OperatorFromRelative B R u = u.val.2 + R u.val.2 := by
  simp only [n06OperatorFromRelative, ContinuousLinearMap.comp_apply,
    add_apply, ContinuousLinearMap.id_apply, n06SourceProjection_apply]

theorem n06RelativeOperator_fromRelative (B : CanonicalDomainData S K V b)
    (R : AnnularState S × ℝ →
      V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b)
    (hright : ∀ F, (B.inverse F).val.2 = F) (z : AnnularState S × ℝ) :
    n06RelativeOperator (fun z => n06OperatorFromRelative B (R z)) z = R z := by
  apply ContinuousLinearMap.ext
  intro F
  simp only [n06RelativeOperator, sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    n06OperatorFromRelative_apply, hright]
  abel

/-- The physical specialization of the dense closed-relation argument, separated from the
neighborhood assembly so that the relation remains a fixed local predicate. -/
theorem n06OperatorFromDense_physical
    [CompleteSpace (V.level (3 / 4 : ℝ) 0 b)]
    (D : ReferenceData) (C : NonlinearGeometryData S) (L : ReturnCorrectionData S)
    (B : CanonicalDomainData S K V b) (z : AnnularState S × ℝ)
    {Core : Type*} [AddCommGroup Core] [Module ℝ Core]
    (i : Core →ₗ[ℝ] V.level (3 / 4 : ℝ) 0 b)
    (R₀ : Core →ₗ[ℝ] V.level (3 / 4 : ℝ) 0 b) (hdense : DenseRange i)
    {q : ℝ} (hbound : ∀ f : Core, ‖R₀ f‖ ≤ q * ‖i f‖)
    (hleft : ∀ u : B.Space, B.inverse u.val.2 = u)
    (hclosed : IsClosed {p : B.Space × V.level (3 / 4 : ℝ) 0 b |
      PerturbedCanonicalRelation D S C K L z p.1.val.1
        (V.forget (3 / 4 : ℝ) 0 b p.2)})
    (hcore : ∀ f : Core, PerturbedCanonicalRelation D S C K L z (B.inverse (i f)).val.1
      (V.forget (3 / 4 : ℝ) 0 b (i f + R₀ f))) :
    ∀ u : B.Space, PerturbedCanonicalRelation D S C K L z u.val.1
      (V.forget (3 / 4 : ℝ) 0 b
        (n06OperatorFromRelative B (n06DenseExtension i R₀) u)) := by
  let Rel : B.Space → V.level (3 / 4 : ℝ) 0 b → Prop :=
    fun u F => PerturbedCanonicalRelation D S C K L z u.val.1
      (V.forget (3 / 4 : ℝ) 0 b F)
  have hc : IsClosed {p : B.Space × V.level (3 / 4 : ℝ) 0 b | Rel p.1 p.2} := hclosed
  have hi : ∀ f : Core, Rel (B.inverse (i f)) (i f + R₀ f) := hcore
  have hall (F : V.level (3 / 4 : ℝ) 0 b) :
      Rel (B.inverse F) (F + n06DenseExtension i R₀ F) := by
    refine hdense.induction_on
      (p := fun G => Rel (B.inverse G) (G + n06DenseExtension i R₀ G)) F ?_ ?_
    · exact hc.preimage
        (B.inverse.continuous.prodMk
          (continuous_id.add (n06DenseExtension i R₀).continuous))
    · intro f
      rw [n06DenseExtension_on_core i R₀ hdense hbound]
      exact hi f
  intro u
  change Rel u (n06OperatorFromRelative B (n06DenseExtension i R₀) u)
  rw [n06OperatorFromRelative_apply]
  have h := hall u.val.2
  rw [hleft] at h
  exact h

/-- A bounded core perturbation satisfying a closed physical relation constructs N06's
operator and relative inverse on the source and graph already selected by N05. -/
theorem n06_exists_relativeData_of_denseCore
    (D : ReferenceData) (T : MaterialData) (C : NonlinearGeometryData S)
    (L : ReturnCorrectionData S) (B : CanonicalDomainData S K V b)
    (base : ℕ) (ε : ℝ) (hN05 : N05Properties D T S C K V b B)
    {Core : Type*} [AddCommGroup Core] [Module ℝ Core]
    (i : Core →ₗ[ℝ] V.level (3 / 4 : ℝ) 0 b) (hdense : DenseRange i)
    (R₀ : AnnularState S × ℝ → Core →ₗ[ℝ] V.level (3 / 4 : ℝ) 0 b)
    (q : ℝ) (hq : 0 ≤ q) (hqhalf : q < (1 / 2 : ℝ)) (hε : 0 < ε)
    (hbound : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ f : Core, ‖R₀ z f‖ ≤ q * ‖i f‖)
    (hclosed : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      IsClosed {p : B.Space × V.level (3 / 4 : ℝ) 0 b |
        PerturbedCanonicalRelation D S C K L z p.1.val.1
          (V.forget (3 / 4 : ℝ) 0 b p.2)})
    (hcore : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ f : Core, PerturbedCanonicalRelation D S C K L z (B.inverse (i f)).val.1
        (V.forget (3 / 4 : ℝ) 0 b (i f + R₀ z f))) :
    ∃ Relative : RelativeInverseData S K V b B,
      N06Properties D S C K L V b B Relative base ε := by
  have hN05copy := hN05
  obtain ⟨_, hV, _, _, _, _, _, hright, hleft, _⟩ := hN05copy
  let : CompleteSpace (V.level (3 / 4 : ℝ) 0 b) :=
    (hV.2.1 (3 / 4 : ℝ) 0 b).completeSpace_coe
  let R : AnnularState S × ℝ →
      V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b :=
    fun z => n06DenseExtension i (R₀ z)
  let P : AnnularState S × ℝ → B.Space →L[ℝ] V.level (3 / 4 : ℝ) 0 b :=
    fun z => n06OperatorFromRelative B (R z)
  have hphysical : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ u : B.Space, PerturbedCanonicalRelation D S C K L z u.val.1
        (V.forget (3 / 4 : ℝ) 0 b (P z u)) := by
    intro z hz hsector
    exact n06OperatorFromDense_physical D C L B z i (R₀ z) hdense
      (hbound z hz hsector) hleft (hclosed z hz hsector) (hcore z hz hsector)
  have hsmall : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ‖n06RelativeOperator P z‖ < (1 / 2 : ℝ) := by
    intro z hz hsector
    change ‖n06RelativeOperator (fun z => n06OperatorFromRelative B (R z)) z‖ < _
    rw [n06RelativeOperator_fromRelative B R hright]
    exact (norm_n06DenseExtension_le i (R₀ z) hdense hq
      (hbound z hz hsector)).trans_lt hqhalf
  exact n06_exists_relativeData D T C L base ε hN05 P hε hphysical hsmall

end FixedGraph

end ContinuousFlexibility.Statements
