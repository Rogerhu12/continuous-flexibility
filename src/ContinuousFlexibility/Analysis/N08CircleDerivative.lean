module

public import ContinuousFlexibility.Analysis.N08CircleResidual
public import ContinuousFlexibility.Analysis.N08Neighborhoods
public import ContinuousFlexibility.Analysis.ProjectiveJetEvaluation
public import ContinuousFlexibility.Analysis.N08StateLinearOperations

/-!
# The actual state derivative of the projected return residual

The smooth directional tower is the one already supplied by N02 on the
sector.  Its first jet is pulled back by the actual mean/odd projection.
This gives a continuous linear derivative on every ambient state direction,
including control directions whose decoded functions are not constant.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology

set_option backward.isDefEq.respectTransparency false

private theorem n08_centered_projection_value
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (P : E →L[ℝ] E) (Q : E → E) (hQ : ∀ x, Q x = P x)
    (a : E) (ha : P a = a) (x : E) : Q (x - a) = P x - a := by
  rw [hQ, map_sub, ha]

private theorem n08_centered_projection_lift
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (P : E →L[ℝ] E) (Q : E → E) (hQ : ∀ x, Q x = P x)
    (a : E) (ha : P a = a) (x : E) : a + Q (x - a) = P x := by
  rw [n08_centered_projection_value P Q hQ a ha x]
  abel

private theorem n08_centered_projection_bound
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (P : E →L[ℝ] E) (Q : E → E) (hQ : ∀ x, Q x = P x)
    (a : E) (ha : P a = a) (p : Seminorm ℝ E) (x : E) {ε : ℝ}
    (h : p (P x - a) < ε) : p (Q (x - a)) < ε :=
  (congrArg p (n08_centered_projection_value P Q hQ a ha x)).trans_lt h

private theorem n08_centered_pair_line
    {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    (Q : E →L[ℝ] F) (a x v : E) (q t : ℝ) :
    (Q (x + t • v - a), q) = (Q (x - a), q) + t • (Q v, (0 : ℝ)) := by
  apply Prod.ext
  · simp only [Prod.fst_add, Prod.smul_mk, map_sub, map_add, map_smul]
    abel
  · simp only [Prod.snd_add, Prod.smul_mk, smul_zero, add_zero]

private theorem n08_lineDerivative_pullback
    {E F G : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace G] [AddCommGroup G] [Module ℝ G]
    (p : E → F) (f : F → G) {df dg : G} {x v : E} {w : F}
    (hline : ∀ t : ℝ, p (x + t • v) = p x + t • w)
    (hd : HasProjectiveLineDerivAt f df (p x) w) (hvalue : dg = df) :
    HasProjectiveLineDerivAt (fun y => f (p y)) dg x v := by
  rw [hvalue]
  simpa only [HasProjectiveLineDerivAt, hline] using hd

private theorem n08_lineDerivative_value
    {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    {f : E → F} {df dg : F} {x v : E} (hvalue : dg = df)
    (hd : HasProjectiveLineDerivAt f df x v) : HasProjectiveLineDerivAt f dg x v := by
  rw [hvalue]
  exact hd

private theorem n08_germ_eq_on_open_preimage
    {E F G : Type*} [TopologicalSpace E] [TopologicalSpace F]
    (p : E → F) (hp : Continuous p) {U : Set F} (hU : IsOpen U)
    {x : E} (hx : p x ∈ U) (f g : E → G)
    (hfg : ∀ y, p y ∈ U → f y = g y) : f =ᶠ[𝓝 x] g := by
  filter_upwards [hp.continuousAt.preimage_mem_nhds (hU.mem_nhds hx)] with y hy
  exact hfg y hy

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base : ℕ} {ε : ℝ}

theorem n08_return_smoothTame
    (hR : N02Properties D T S C R base ε) :
    SmoothTameOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun z => R.residual (liftSectorParameter S C z)) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, h⟩ := hR
  exact h

/-- The genuine N02 jet, with no assumed derivative formula. -/
def n08CircleSectorJet (hR : N02Properties D T S C R base ε) :
    SmoothDirections (sectorNeighborhood S base ε ε)
      (fun z => R.residual (liftSectorParameter S C z)) :=
  (n08_return_smoothTame hR).choose

def n08CircleSectorPoint (hS : IsPhysicalSpaces D T S)
    (C : NonlinearGeometryData S) (z : AnnularState S × ℝ) : StateDirections S × ℝ :=
  (n08_sectorProjection hS (z.1 - C.referenceState), z.2)

theorem n08CircleSectorPoint_lift (hS : IsPhysicalSpaces D T S)
    (href : referenceStateConditions D S C) (z : AnnularState S × ℝ) :
    liftSectorParameter S C (n08CircleSectorPoint hS C z) =
      (n08_stateProjection hS z.1, z.2) := by
  exact Prod.ext
    (n08_centered_projection_lift (n08_stateProjection hS)
      (fun x => (n08_sectorProjection hS x).val) (n08_sectorProjection_val hS)
      C.referenceState (n08_stateProjection_reference hS href) z.1) rfl

theorem n08CircleSectorPoint_mem (hS : IsPhysicalSpaces D T S)
    (href : referenceStateConditions D S C) {z : AnnularState S × ℝ}
    (hz : (n08_stateProjection hS z.1, z.2) ∈ stateNeighborhood S C base ε) :
    n08CircleSectorPoint hS C z ∈ sectorNeighborhood S base ε ε := by
  exact ⟨n08_centered_projection_bound (n08_stateProjection hS)
    (fun x => (n08_sectorProjection hS x).val) (n08_sectorProjection_val hS)
    C.referenceState (n08_stateProjection_reference hS href) (stateGrading S base) z.1 hz.1,
    hz.2⟩

/-- The actual differential in all state directions, with the external
parameter held fixed. -/
def n08CircleStateDerivative (hS : IsPhysicalSpaces D T S)
    (hR : N02Properties D T S C R base ε) (z : AnnularState S × ℝ) :
    AnnularState S →L[ℝ] CircleSpace S :=
  (projectiveJetHeadLinear (n08CircleSectorJet hR).D 0
    (n08CircleSectorPoint hS C z) Fin.elim0).comp
      ((n08_sectorProjection hS).prod (0 : AnnularState S →L[ℝ] ℝ))

theorem n08CircleStateDerivative_apply (hS : IsPhysicalSpaces D T S)
    (hR : N02Properties D T S C R base ε) (z : AnnularState S × ℝ)
    (v : AnnularState S) :
    n08CircleStateDerivative hS hR z v =
      (n08CircleSectorJet hR).D 1 (n08CircleSectorPoint hS C z)
        (Fin.cons (n08_sectorProjection hS v, 0) Fin.elim0) := by
  simp only [n08CircleStateDerivative, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.zero_apply,
    projectiveJetHeadLinear_apply]

theorem n08CircleSectorPoint_line
    (hS : IsPhysicalSpaces D T S) (C : NonlinearGeometryData S)
    (z : AnnularState S × ℝ) (v : AnnularState S) (t : ℝ) :
    n08CircleSectorPoint hS C (z.1 + n08StateSMul S t v, z.2) =
      n08CircleSectorPoint hS C z +
        n08RealSMul (E := StateDirections S × ℝ) t (n08_sectorProjection hS v, (0 : ℝ)) :=
  n08_centered_pair_line (n08_sectorProjection hS) C.referenceState z.1 v z.2 t

private theorem n08CircleStateDerivative_raw
    (hS : IsPhysicalSpaces D T S) (href : referenceStateConditions D S C)
    (hR : N02Properties D T S C R base ε) {z : AnnularState S × ℝ}
    (hz : (n08_stateProjection hS z.1, z.2) ∈ stateNeighborhood S C base ε)
    (v : AnnularState S) :
    HasProjectiveLineDerivAt
      (fun x => R.residual (liftSectorParameter S C (n08CircleSectorPoint hS C (x, z.2))))
      (n08CircleStateDerivative hS hR z v) z.1 v := by
  let J := n08CircleSectorJet hR
  have hj := J.hasProjectiveJetsOn.hasLineDerivAt J.open_domain
    (n08CircleSectorPoint_mem hS href hz) (n08_sectorProjection hS v, 0)
  exact n08_lineDerivative_pullback (fun x => n08CircleSectorPoint hS C (x, z.2))
    (fun y => R.residual (liftSectorParameter S C y))
    (n08CircleSectorPoint_line hS C z v) hj (n08CircleStateDerivative_apply hS hR z v)

private theorem n08CircleResidual_centered_coe
    (hS : IsPhysicalSpaces D T S) (href : referenceStateConditions D S C)
    (hR : N02Properties D T S C R base ε) {z : AnnularState S × ℝ}
    (hz : (n08_stateProjection hS z.1, z.2) ∈ stateNeighborhood S C base ε) :
    (n08CircleResidual hS hR z).val =
      R.residual (liftSectorParameter S C (n08CircleSectorPoint hS C z)) :=
  (n08CircleResidual_projected_coe hS hR hz).trans
    (congrArg R.residual (n08CircleSectorPoint_lift hS href z).symm)

private theorem n08CircleResidual_germ
    (hS : IsPhysicalSpaces D T S) (href : referenceStateConditions D S C)
    (hR : N02Properties D T S C R base ε) {z : AnnularState S × ℝ}
    (hz : (n08_stateProjection hS z.1, z.2) ∈ stateNeighborhood S C base ε) :
    (fun x => (n08CircleResidual hS hR (x, z.2)).val) =ᶠ[𝓝 z.1]
      (fun x => R.residual (liftSectorParameter S C (n08CircleSectorPoint hS C (x, z.2)))) := by
  exact n08_germ_eq_on_open_preimage
    (fun x : AnnularState S => (n08_stateProjection hS x, z.2))
    ((n08_stateProjection hS).continuous.prodMk continuous_const)
    (n08_isOpen_stateNeighborhood S C base ε) hz _ _
    (fun _ hx => n08CircleResidual_centered_coe hS href hR hx)

theorem n08CircleStateDerivative_hasLineDerivAt
    (hS : IsPhysicalSpaces D T S) (href : referenceStateConditions D S C)
    (hR : N02Properties D T S C R base ε) {z : AnnularState S × ℝ}
    (hz : (n08_stateProjection hS z.1, z.2) ∈ stateNeighborhood S C base ε)
    (v : AnnularState S) :
    HasProjectiveLineDerivAt (fun x => (n08CircleResidual hS hR (x, z.2)).val)
      (n08CircleStateDerivative hS hR z v) z.1 v :=
  (n08CircleStateDerivative_raw hS href hR hz v).congr_germ
    (n08CircleResidual_germ hS href hR hz)

/-- Injection of a circle control into the full ambient state. -/
def n08KappaDirection (S : PhysicalSpacesData) : CircleSpace S →L[ℝ] AnnularState S :=
  (0 : CircleSpace S →L[ℝ] HeightPair S).prod
    ((0 : CircleSpace S →L[ℝ] ℝ).prod
      ((ContinuousLinearMap.id ℝ (CircleSpace S)).prod
        (0 : CircleSpace S →L[ℝ] CircleSpace S)))

theorem n08KappaDirection_apply (S : PhysicalSpacesData) (u : CircleSpace S) :
    n08KappaDirection S u = (0, (0, (u, 0))) := by
  simp only [n08KappaDirection, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.id_apply]

def n08CircleColumn (hS : IsPhysicalSpaces D T S)
    (hR : N02Properties D T S C R base ε) (z : AnnularState S × ℝ) :
    CircleSpace S →L[ℝ] CircleSpace S :=
  (n08CircleStateDerivative hS hR z).comp (n08KappaDirection S)

theorem n08CircleColumn_apply (hS : IsPhysicalSpaces D T S)
    (hR : N02Properties D T S C R base ε) (z : AnnularState S × ℝ) (u : CircleSpace S) :
    n08CircleColumn hS hR z u = n08CircleStateDerivative hS hR z (0, (0, (u, 0))) :=
  (ContinuousLinearMap.comp_apply (n08CircleStateDerivative hS hR z)
    (n08KappaDirection S) u).trans
      (congrArg (n08CircleStateDerivative hS hR z) (n08KappaDirection_apply S u))

theorem n08CircleColumn_hasLineDerivAt
    (hS : IsPhysicalSpaces D T S) (href : referenceStateConditions D S C)
    (hR : N02Properties D T S C R base ε) {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (u : CircleSpace S) :
    HasProjectiveLineDerivAt (fun x => (n08CircleResidual hS hR (x, z.2)).val)
      (n08CircleColumn hS hR z u) z.1 (0, (0, (u, 0))) := by
  have hp : (n08_stateProjection hS z.1, z.2) ∈ stateNeighborhood S C base ε := by
    simpa only [n08_stateProjection_eq_self hS z.1 hs, Prod.eta] using hz
  exact n08_lineDerivative_value (n08CircleColumn_apply hS hR z u)
    (n08CircleStateDerivative_hasLineDerivAt hS href hR hp (0, (0, (u, 0))))

end ContinuousFlexibility.Statements
