import QEC1.Definitions.Def_2_GaussLawAndFluxOperators
import QEC1.Definitions.Def_1_BoundaryAndCoboundaryMaps
import QEC1.Remarks.Rem_2_NotationPauliOperators
import QEC1.Remarks.Rem_3_NotationStabilizerCodes
import Mathlib.Tactic

/-!
# Remark 17: Hypergraph Generalization

## Statement
The gauging measurement procedure can be generalized by replacing the graph G with a
hypergraph H = (V, E) where each hyperedge e ∈ E is a nonempty subset of vertices.

**Setup:**
- Introduce one auxiliary qubit per hyperedge.
- Gauss's law operators: A_v = X_v ∏_{e ∋ v} X_e.
- Boundary map ∂: Z₂^E → Z₂^V with (∂γ)_v = Σ_{e ∋ v} γ_e.

**Key result:**
γ ∈ ker(∂) corresponds to the X-type operator ∏_v X_v^{(Σ_{e ∋ v} γ_e mod 2)}
which commutes with all A_v. The hypergraph gauging measures any such operator.

## Main Results
- `hyperBoundaryMap` : the boundary map ∂ for hypergraphs
- `hyperGaussLawOp` : hypergraph Gauss's law operator A_v
- `hyperGaussLawOp_pure_X` : A_v is pure X-type
- `hyperGaussLaw_commute` : all A_v mutually commute
- `symplecticInner_pureZ_gaussLaw` : ⟨Z(γ), A_v⟩ = (∂γ)_v
- `ker_boundary_iff_commutes_all_gaussLaw` : γ ∈ ker(∂) ↔ Z(γ) commutes with all A_v
- `cssInit_boundary_eq` : CSS initialization is a special case
- `graphLike_boundary_single_sum` : graph case recovered when hyperedges have 2 vertices
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
noncomputable section

namespace HypergraphGeneralization

open Finset PauliOp

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ## Hyperedge incidence -/

-- The incidence relation for a hypergraph: `incident v e` means vertex v ∈ hyperedge e.
variable (incident : V → E → Prop) [∀ v e, Decidable (incident v e)]

/-- The finset of hyperedges incident to vertex v. -/
def hyperIncidentEdges (v : V) : Finset E :=
  Finset.univ.filter (fun e => incident v e)

@[simp]
theorem mem_hyperIncidentEdges (v : V) (e : E) :
    e ∈ hyperIncidentEdges incident v ↔ incident v e := by
  simp [hyperIncidentEdges]

/-- The finset of vertices in hyperedge e. -/
def hyperedgeVertices (e : E) : Finset V :=
  Finset.univ.filter (fun v => incident v e)

@[simp]
theorem mem_hyperedgeVertices (e : E) (v : V) :
    v ∈ hyperedgeVertices incident e ↔ incident v e := by
  simp [hyperedgeVertices]

theorem hyperedgeVertices_nonempty (e : E)
    (hne : ∃ v : V, incident v e) :
    (hyperedgeVertices incident e).Nonempty := by
  obtain ⟨v, hv⟩ := hne
  exact ⟨v, by simp [hv]⟩

/-! ## Hypergraph Boundary Map -/

/-- The hypergraph boundary map ∂ : Z₂^E → Z₂^V.
    For γ ∈ Z₂^E, (∂γ)_v = Σ_{e ∋ v} γ_e (mod 2).
    This generalizes the graph boundary map: for graphs, each edge is incident to exactly
    2 vertices; for hypergraphs, a hyperedge can be incident to any nonempty set of vertices. -/
def hyperBoundaryMap : (E → ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) where
  toFun γ v := ∑ e : E, if incident v e then γ e else 0
  map_add' := by
    intro γ₁ γ₂; ext v; simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]; congr 1; ext e
    split <;> simp
  map_smul' := by
    intro r γ; ext v
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]; congr 1; ext e
    split <;> simp [mul_comm]

theorem hyperBoundaryMap_apply (γ : E → ZMod 2) (v : V) :
    hyperBoundaryMap incident γ v = ∑ e : E, if incident v e then γ e else 0 := rfl

/-- The boundary of a single hyperedge indicator: (∂ 1_e)(v) = 1 iff v ∈ e. -/
theorem hyperBoundaryMap_single (e₀ : E) (v : V) :
    hyperBoundaryMap incident (fun e => if e = e₀ then 1 else 0) v =
    if incident v e₀ then 1 else 0 := by
  simp only [hyperBoundaryMap_apply]
  rw [Finset.sum_eq_single e₀]
  · simp
  · intro e _ hne; simp [hne]
  · intro h; exact absurd (Finset.mem_univ e₀) h

/-! ## Hypergraph Coboundary Map -/

/-- The hypergraph coboundary map δ : Z₂^V → Z₂^E, the transpose of ∂.
    For f ∈ Z₂^V, (δf)_e = Σ_{v ∈ e} f_v (mod 2). -/
def hyperCoboundaryMap : (V → ZMod 2) →ₗ[ZMod 2] (E → ZMod 2) where
  toFun f e := ∑ v : V, if incident v e then f v else 0
  map_add' := by
    intro f₁ f₂; ext e; simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]; congr 1; ext v
    split <;> simp
  map_smul' := by
    intro r f; ext e
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]; congr 1; ext v
    split <;> simp [mul_comm]

theorem hyperCoboundaryMap_apply (f : V → ZMod 2) (e : E) :
    hyperCoboundaryMap incident f e = ∑ v : V, if incident v e then f v else 0 := rfl

/-- δ is the transpose of ∂: ⟨δ f, γ⟩_E = ⟨f, ∂ γ⟩_V. -/
theorem hyperCoboundaryMap_eq_transpose
    (f : V → ZMod 2) (γ : E → ZMod 2) :
    ∑ e : E, hyperCoboundaryMap incident f e * γ e =
    ∑ v : V, f v * hyperBoundaryMap incident γ v := by
  simp only [hyperCoboundaryMap_apply, hyperBoundaryMap_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1; ext v
  rw [Finset.mul_sum]
  congr 1; ext e
  split
  · ring
  · simp

/-! ## Extended Qubit Type -/

/-- The extended qubit type for hypergraph gauging: vertex qubits (Sum.inl v) and
    hyperedge qubits (Sum.inr e). -/
abbrev HyperExtQubit := V ⊕ E

/-! ## Hypergraph Gauss's Law Operator -/

/-- The hypergraph Gauss's law operator A_v on the extended system V ⊕ E.
    A_v = X_v ∏_{e ∋ v} X_e: acts with X on vertex qubit v and all incident hyperedge qubits. -/
def hyperGaussLawOp (v : V) : PauliOp (V ⊕ E) where
  xVec := fun q => match q with
    | Sum.inl w => if w = v then 1 else 0
    | Sum.inr e => if incident v e then 1 else 0
  zVec := 0

/-- A_v is pure X-type: its Z-vector is identically zero. -/
@[simp]
theorem hyperGaussLawOp_zVec (v : V) : (hyperGaussLawOp incident v).zVec = 0 := rfl

/-- A_v has no Z support. -/
theorem hyperGaussLawOp_pure_X (v : V) :
    ∀ q : V ⊕ E, (hyperGaussLawOp incident v).zVec q = 0 := by
  intro q; simp

@[simp]
theorem hyperGaussLawOp_xVec_vertex (v w : V) :
    (hyperGaussLawOp incident v).xVec (Sum.inl w) = if w = v then 1 else 0 := rfl

@[simp]
theorem hyperGaussLawOp_xVec_edge (v : V) (e : E) :
    (hyperGaussLawOp incident v).xVec (Sum.inr e) = if incident v e then 1 else 0 := rfl

/-! ## Commutation of Gauss's Law Operators -/

/-- All hypergraph Gauss's law operators mutually commute.
    This holds because they are all pure X-type (zVec = 0). -/
theorem hyperGaussLaw_commute (v w : V) :
    PauliCommute (hyperGaussLawOp incident v) (hyperGaussLawOp incident w) := by
  simp only [PauliCommute, symplecticInner]
  apply Finset.sum_eq_zero
  intro q _
  simp [hyperGaussLawOp]

/-! ## The X-Type Operator from an Edge Vector -/

/-- Given an edge vector γ : E → ZMod 2, the corresponding X-type operator on vertex qubits:
    ∏_{v ∈ V} X_v^{(∂γ)_v}. Acts as X on vertex v iff (∂γ)_v = 1. -/
def xOpFromBoundary (γ : E → ZMod 2) : PauliOp V where
  xVec := hyperBoundaryMap incident γ
  zVec := 0

@[simp]
theorem xOpFromBoundary_xVec (γ : E → ZMod 2) :
    (xOpFromBoundary incident γ).xVec = hyperBoundaryMap incident γ := rfl

@[simp]
theorem xOpFromBoundary_zVec (γ : E → ZMod 2) :
    (xOpFromBoundary incident γ).zVec = 0 := rfl

/-! ## Product of Gauss's Law Operators -/

/-- On vertex qubits: each vertex w gets contribution 1 from A_w only. -/
theorem hyperGaussLaw_product_xVec_vertex (w : V) :
    ∑ v : V, (hyperGaussLawOp incident v).xVec (Sum.inl w) = 1 := by
  simp only [hyperGaussLawOp_xVec_vertex]
  rw [Finset.sum_eq_single w]
  · simp
  · intro v _ hne; simp [Ne.symm hne]
  · intro h; exact absurd (Finset.mem_univ w) h

/-- On edge qubits: each hyperedge e gets |vertices(e)| mod 2. -/
theorem hyperGaussLaw_product_xVec_edge (e : E) :
    ∑ v : V, (hyperGaussLawOp incident v).xVec (Sum.inr e) =
    (hyperedgeVertices incident e).card := by
  simp only [hyperGaussLawOp_xVec_edge]
  simp [Finset.sum_boole, hyperedgeVertices]

/-! ## Kernel of Boundary Map and Commutation -/

/-- γ ∈ ker(∂) iff the boundary is zero: (∂γ)_v = 0 for all v. -/
theorem mem_ker_hyperBoundary_iff (γ : E → ZMod 2) :
    γ ∈ LinearMap.ker (hyperBoundaryMap incident) ↔
    ∀ v : V, hyperBoundaryMap incident γ v = 0 := by
  simp [LinearMap.mem_ker, funext_iff]

/-- The X-type operator on V from γ ∈ ker(∂) is the identity (since ∂γ = 0). -/
theorem ker_boundary_gives_identity_on_V (γ : E → ZMod 2)
    (hγ : γ ∈ LinearMap.ker (hyperBoundaryMap incident)) :
    xOpFromBoundary incident γ = 1 := by
  have h0 : hyperBoundaryMap incident γ = 0 := LinearMap.mem_ker.mp hγ
  ext v
  · simp [xOpFromBoundary, h0, Pi.zero_apply]
  · simp

/-! ## Gauss Subset Product -/

/-- The Gauss subset product for hypergraphs: the product of A_v over vertices where c_v = 1.
    On vertex qubits, the X-vector is c; on edge qubits, it is δc. -/
def hyperGaussSubsetProduct (c : V → ZMod 2) : PauliOp (V ⊕ E) where
  xVec := fun q => match q with
    | Sum.inl v => c v
    | Sum.inr e => ∑ v : V, if incident v e then c v else 0
  zVec := 0

@[simp]
theorem hyperGaussSubsetProduct_xVec_vertex (c : V → ZMod 2) (w : V) :
    (hyperGaussSubsetProduct incident c).xVec (Sum.inl w) = c w := rfl

@[simp]
theorem hyperGaussSubsetProduct_xVec_edge (c : V → ZMod 2) (e : E) :
    (hyperGaussSubsetProduct incident c).xVec (Sum.inr e) =
    ∑ v : V, if incident v e then c v else 0 := rfl

@[simp]
theorem hyperGaussSubsetProduct_zVec (c : V → ZMod 2) :
    (hyperGaussSubsetProduct incident c).zVec = 0 := rfl

/-- The Gauss subset product for the all-ones vector gives L = ∏_v X_v on vertices. -/
theorem hyperGaussSubsetProduct_allOnes_vertex (w : V) :
    (hyperGaussSubsetProduct incident (fun _ => 1)).xVec (Sum.inl w) = 1 := by
  simp

/-- On edge qubits, the all-ones Gauss product gives |vertices(e)| mod 2. -/
theorem hyperGaussSubsetProduct_allOnes_edge (e : E) :
    (hyperGaussSubsetProduct incident (fun (_ : V) => (1 : ZMod 2))).xVec (Sum.inr e) =
    (hyperedgeVertices incident e).card := by
  simp only [hyperGaussSubsetProduct_xVec_edge, ite_true]
  simp [Finset.sum_boole, hyperedgeVertices]

/-- The Gauss subset product for the zero vector gives the identity. -/
@[simp]
theorem hyperGaussSubsetProduct_zero :
    hyperGaussSubsetProduct incident (0 : V → ZMod 2) = 1 := by
  ext q
  · cases q with
    | inl v => simp [hyperGaussSubsetProduct]
    | inr e => simp [hyperGaussSubsetProduct]
  · simp

/-- The Gauss subset product is additive. -/
theorem hyperGaussSubsetProduct_add (c₁ c₂ : V → ZMod 2) :
    hyperGaussSubsetProduct incident (c₁ + c₂) =
    hyperGaussSubsetProduct incident c₁ * hyperGaussSubsetProduct incident c₂ := by
  ext q
  · cases q with
    | inl v => simp [hyperGaussSubsetProduct, PauliOp.mul]
    | inr e =>
      simp only [hyperGaussSubsetProduct_xVec_edge, Pi.add_apply, PauliOp.mul_xVec]
      rw [← Finset.sum_add_distrib]
      congr 1; ext v
      split
      · rfl
      · simp
  · simp [PauliOp.mul_zVec]

/-- The edge X-vector of the Gauss subset product equals the coboundary. -/
theorem hyperGaussSubsetProduct_edge_eq_coboundary (c : V → ZMod 2) (e : E) :
    (hyperGaussSubsetProduct incident c).xVec (Sum.inr e) =
    hyperCoboundaryMap incident c e := by
  simp [hyperGaussSubsetProduct, hyperCoboundaryMap_apply]

/-! ## Pure-Z Hyperedge Operator and Kernel Characterization -/

/-- A pure-Z hyperedge operator: acts as Z on hyperedge qubit e iff γ(e) = 1. -/
def pureZHyperedgeOp (γ : E → ZMod 2) : PauliOp (V ⊕ E) where
  xVec := 0
  zVec := fun q => match q with
    | Sum.inl _ => 0
    | Sum.inr e => γ e

@[simp]
theorem pureZHyperedgeOp_xVec (γ : E → ZMod 2) :
    (pureZHyperedgeOp (V := V) γ).xVec = 0 := rfl

@[simp]
theorem pureZHyperedgeOp_zVec_vertex (γ : E → ZMod 2) (v : V) :
    (pureZHyperedgeOp (V := V) γ).zVec (Sum.inl v) = 0 := rfl

@[simp]
theorem pureZHyperedgeOp_zVec_edge (γ : E → ZMod 2) (e : E) :
    (pureZHyperedgeOp (V := V) γ).zVec (Sum.inr e) = γ e := rfl

/-- The symplectic inner product of the pure-Z hyperedge operator for γ with A_v
    equals (∂γ)_v. This is the key computation connecting the boundary map to
    commutation with Gauss operators. -/
theorem symplecticInner_pureZ_gaussLaw (γ : E → ZMod 2) (v : V) :
    symplecticInner (pureZHyperedgeOp (V := V) γ) (hyperGaussLawOp incident v) =
    hyperBoundaryMap incident γ v := by
  simp only [symplecticInner]
  rw [Fintype.sum_sum_type]
  -- Sum over vertex qubits: all zero (pureZ has xVec=0, zVec on inl = 0)
  have h_vertex : ∑ w : V,
      ((pureZHyperedgeOp (V := V) γ).xVec (Sum.inl w) *
        (hyperGaussLawOp incident v).zVec (Sum.inl w) +
       (pureZHyperedgeOp (V := V) γ).zVec (Sum.inl w) *
        (hyperGaussLawOp incident v).xVec (Sum.inl w)) = 0 := by
    apply Finset.sum_eq_zero; intro w _; simp [pureZHyperedgeOp, hyperGaussLawOp]
  rw [h_vertex, zero_add]
  -- Sum over edge qubits: gives (∂γ)_v
  simp only [hyperBoundaryMap_apply]
  congr 1; ext e
  simp only [pureZHyperedgeOp, hyperGaussLawOp]
  simp only [Pi.zero_apply, zero_mul, zero_add]
  split
  · simp [mul_one]
  · simp [mul_zero]

/-- **Key theorem**: The pure-Z hyperedge operator for γ commutes with A_v iff (∂γ)_v = 0. -/
theorem pureZHyperedgeOp_commutes_gaussLaw_iff (γ : E → ZMod 2) (v : V) :
    PauliCommute (pureZHyperedgeOp (V := V) γ) (hyperGaussLawOp incident v) ↔
    hyperBoundaryMap incident γ v = 0 := by
  simp only [PauliCommute, symplecticInner_pureZ_gaussLaw]

/-- γ ∈ ker(∂) iff the pure-Z hyperedge operator commutes with ALL Gauss operators. -/
theorem ker_boundary_iff_commutes_all_gaussLaw (γ : E → ZMod 2) :
    γ ∈ LinearMap.ker (hyperBoundaryMap incident) ↔
    ∀ v : V, PauliCommute (pureZHyperedgeOp (V := V) γ) (hyperGaussLawOp incident v) := by
  rw [mem_ker_hyperBoundary_iff]
  constructor
  · intro h v; rw [pureZHyperedgeOp_commutes_gaussLaw_iff]; exact h v
  · intro h v; rw [← pureZHyperedgeOp_commutes_gaussLaw_iff]; exact h v

/-- The set of pure-Z hyperedge operators commuting with all A_v is exactly the image of
    ker(∂): if P is pure-Z on edges, zero on vertices, and commutes with all A_v,
    then its edge Z-vector is in ker(∂). -/
theorem commuting_pureZ_operators_eq_ker_image (P : PauliOp (V ⊕ E))
    (hxVec : P.xVec = 0) (hzVertex : ∀ v : V, P.zVec (Sum.inl v) = 0)
    (hcomm : ∀ v : V, PauliCommute P (hyperGaussLawOp incident v)) :
    (fun e => P.zVec (Sum.inr e)) ∈ LinearMap.ker (hyperBoundaryMap incident) := by
  rw [ker_boundary_iff_commutes_all_gaussLaw]
  intro v
  have hPeq : P = pureZHyperedgeOp (V := V) (fun e => P.zVec (Sum.inr e)) := by
    ext q
    · cases q with
      | inl w => simp [pureZHyperedgeOp, hxVec, Pi.zero_apply]
      | inr e => simp [pureZHyperedgeOp, hxVec, Pi.zero_apply]
    · cases q with
      | inl w => simp [pureZHyperedgeOp, hzVertex]
      | inr e => simp [pureZHyperedgeOp]
  rw [← hPeq]
  exact hcomm v

/-! ## Recovering the Graph Case -/

/-- A hypergraph comes from a simple graph when each hyperedge has exactly 2 vertices. -/
def IsGraphLike : Prop :=
  ∀ e : E, (hyperedgeVertices incident e).card = 2

/-- For a graph-like hypergraph, the boundary of a single edge sums to 0 over all vertices,
    because each edge has exactly 2 endpoints and 2 = 0 in ZMod 2. -/
theorem graphLike_boundary_single_sum (hgl : IsGraphLike incident) (e₀ : E) :
    ∑ v : V, hyperBoundaryMap incident (fun e => if e = e₀ then 1 else 0) v = 0 := by
  simp only [hyperBoundaryMap_single]
  have hc : (hyperedgeVertices incident e₀).card = 2 := hgl e₀
  rw [show (∑ v : V, if incident v e₀ then (1 : ZMod 2) else 0) =
    (Finset.univ.filter (fun v => incident v e₀)).card from by
    rw [← Finset.sum_boole]]
  have : (Finset.univ.filter (fun v => incident v e₀)) = hyperedgeVertices incident e₀ := by
    ext v; simp [hyperedgeVertices]
  rw [this, hc]; decide

/-! ## CSS Code Initialization as a Special Case -/

/-- For CSS code initialization, the incidence relation is membership in check supports.
    - V = set of physical qubits (Q)
    - E = set of X-type checks (I)
    - incident q i iff qubit q participates in X-check i
    The boundary map then encodes the X-check parity matrix. -/
theorem cssInit_boundary_eq
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    {I : Type*} [Fintype I] [DecidableEq I]
    (xCheckSupport : I → Finset Q)
    (γ : I → ZMod 2) (q : Q) :
    hyperBoundaryMap (fun (v : Q) (i : I) => v ∈ xCheckSupport i) γ q =
    ∑ i : I, if q ∈ xCheckSupport i then γ i else 0 := by
  simp [hyperBoundaryMap_apply]

/-! ## Summary Theorems -/

/-- **Summary**: The hypergraph generalization extends the graph gauging framework.
    1. All Gauss operators mutually commute (pure X-type)
    2. Pure-Z edge operators commute with A_v iff γ ∈ ker(∂)
    3. The coboundary δ is the transpose of ∂
    4. The Gauss subset product is additive and encodes the vertex-edge duality -/
theorem hypergraph_generalization_summary :
    (∀ v w : V, PauliCommute (hyperGaussLawOp incident v) (hyperGaussLawOp incident w)) ∧
    (∀ γ : E → ZMod 2,
      γ ∈ LinearMap.ker (hyperBoundaryMap incident) ↔
      ∀ v : V, PauliCommute (pureZHyperedgeOp (V := V) γ)
        (hyperGaussLawOp incident v)) ∧
    (∀ f : V → ZMod 2, ∀ γ : E → ZMod 2,
      ∑ e : E, hyperCoboundaryMap incident f e * γ e =
      ∑ v : V, f v * hyperBoundaryMap incident γ v) ∧
    (hyperGaussSubsetProduct incident (0 : V → ZMod 2) = 1) :=
  ⟨hyperGaussLaw_commute incident,
   ker_boundary_iff_commutes_all_gaussLaw incident,
   hyperCoboundaryMap_eq_transpose incident,
   hyperGaussSubsetProduct_zero incident⟩

end HypergraphGeneralization
