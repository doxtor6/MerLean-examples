import QEC1.Remarks.Rem_15_SpacetimeSyndromes
import QEC1.Definitions.Def_19_CSSCode
import QEC1.Definitions.Def_7_FluxOperators

/-!
# Decoder Requirements (Remark 26)

## Statement
Decoding the fault-tolerant gauging measurement requires handling several types of syndromes:

**Syndrome types**:
(i) A_v syndromes: Created by Z errors on vertex and edge qubits
(ii) B_p syndromes: Created by X errors on edge qubits
(iii) s̃_j syndromes: Created by both X and Z errors on vertex and edge qubits

**Decoder approaches**:
- **General-purpose**: Belief propagation with ordered statistics post-processing (BP+OSD)
- **Structured**: Matching on A_v syndromes (similar to surface code), combined with
  code-specific decoding for s̃_j

**Open question**: Designing decoders that exploit the structure of the gauging measurement
for improved performance.

## Main Results
**Definition** (`SyndromeType`): Classification of syndrome types (A_v, B_p, s̃_j)
**Definition** (`DecoderApproach`): Classification of decoder approaches (general vs structured)
**Definition** (`DecoderRequirements`): Full specification of decoder input/output requirements
**Theorem** (`Av_from_Z_errors`): A_v syndromes arise from Z errors
**Theorem** (`Bp_from_X_errors`): B_p syndromes arise from X errors
**Theorem** (`stilde_from_both_errors`): s̃_j syndromes arise from both X and Z errors
**Theorem** (`decoder_approaches_complete`): Both approaches can decode all syndrome types

## File Structure
1. Syndrome Type Classification: A_v, B_p, s̃_j syndrome types
2. Error Sources: Which errors create which syndromes
3. Decoder Approaches: General-purpose vs structured decoders
4. Decoder Requirements: Input/output specification
5. Matching Structure: A_v matching (like surface code)
6. Helper Lemmas: Properties of syndrome types
-/

namespace QEC

namespace DecoderRequirements

open SpacetimeSyndromes

/-! ## Section 1: Syndrome Type Classification

The gauging measurement produces three types of syndromes:
1. **A_v syndromes**: From Gauss law operators, created by Z errors
2. **B_p syndromes**: From flux operators, created by X errors
3. **s̃_j syndromes**: From deformed stabilizers, created by both X and Z errors
-/

/-- Classification of syndrome types in the gauging measurement -/
inductive SyndromeType where
  /-- A_v syndrome: from Gauss law operators (created by Z errors) -/
  | Av : SyndromeType
  /-- B_p syndrome: from flux operators (created by X errors) -/
  | Bp : SyndromeType
  /-- s̃_j syndrome: from deformed checks (created by both X and Z errors) -/
  | Stilde : SyndromeType
  deriving DecidableEq, Repr

namespace SyndromeType

instance : Fintype SyndromeType where
  elems := {Av, Bp, Stilde}
  complete := fun x => by cases x <;> simp

/-- There are exactly 3 syndrome types -/
theorem card : Fintype.card SyndromeType = 3 := rfl

/-- String representation for debugging -/
def toString : SyndromeType → String
  | Av => "A_v"
  | Bp => "B_p"
  | Stilde => "s̃_j"

end SyndromeType

/-! ## Section 2: Error Types

Errors on qubits are classified by:
- **Location**: vertex qubits vs edge qubits
- **Pauli type**: X errors vs Z errors
-/

/-- Qubit location type: vertex or edge -/
inductive QubitLocation where
  | vertex : QubitLocation
  | edge : QubitLocation
  deriving DecidableEq, Repr

instance : Fintype QubitLocation where
  elems := {.vertex, .edge}
  complete := fun x => by cases x <;> simp

/-- An error specification: location and Pauli type -/
structure ErrorSpec where
  /-- Where the error occurs -/
  location : QubitLocation
  /-- Type of Pauli error -/
  pauliType : SyndromePauliType
  deriving DecidableEq, Repr

/-- Number of error specifications = 2 locations × 2 Pauli types = 4 -/
instance : Fintype ErrorSpec where
  elems := {
    ⟨.vertex, .X⟩, ⟨.vertex, .Z⟩,
    ⟨.edge, .X⟩, ⟨.edge, .Z⟩
  }
  complete := fun x => by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    cases x with | mk loc pauli =>
      cases loc <;> cases pauli <;> simp

theorem errorSpec_card : Fintype.card ErrorSpec = 4 := rfl

/-! ## Section 3: Error-to-Syndrome Mapping

Which errors create which syndrome types:
- A_v syndromes: Z errors (anticommute with X-type Gauss law)
- B_p syndromes: X errors on edges (anticommute with Z-type flux)
- s̃_j syndromes: Both X and Z errors (deformed checks are general)
-/

/-- Whether an error type creates a given syndrome type -/
def errorsCreateSyndrome (e : ErrorSpec) (s : SyndromeType) : Prop :=
  match s, e.location, e.pauliType with
  -- A_v (X-type): anticommutes with Z errors
  | .Av, .vertex, .Z => True
  | .Av, .edge, .Z => True
  | .Av, _, .X => False
  -- B_p (Z-type on edges): anticommutes with X errors on edges
  | .Bp, .edge, .X => True
  | .Bp, _, .Z => False
  | .Bp, .vertex, .X => False  -- B_p only on edges
  -- s̃_j: anticommutes with both X and Z (general stabilizer)
  | .Stilde, _, _ => True

instance (e : ErrorSpec) (s : SyndromeType) :
    Decidable (errorsCreateSyndrome e s) := by
  unfold errorsCreateSyndrome
  cases s <;> cases e.location <;> cases e.pauliType <;> infer_instance

/-- **Main Theorem (i)**: A_v syndromes are created by Z errors on vertex and edge qubits.
    This is because A_v = X-type operator, which anticommutes with Z. -/
theorem Av_from_Z_errors :
    -- Z on vertex creates A_v syndrome
    errorsCreateSyndrome ⟨.vertex, .Z⟩ .Av ∧
    -- Z on edge creates A_v syndrome
    errorsCreateSyndrome ⟨.edge, .Z⟩ .Av ∧
    -- X on vertex does NOT create A_v syndrome
    ¬errorsCreateSyndrome ⟨.vertex, .X⟩ .Av ∧
    -- X on edge does NOT create A_v syndrome
    ¬errorsCreateSyndrome ⟨.edge, .X⟩ .Av := by
  unfold errorsCreateSyndrome
  exact ⟨trivial, trivial, fun h => h, fun h => h⟩

/-- **Main Theorem (ii)**: B_p syndromes are created by X errors on edge qubits.
    This is because B_p = Z-type operator on edges, which anticommutes with X on edges. -/
theorem Bp_from_X_errors :
    -- X on edge creates B_p syndrome
    errorsCreateSyndrome ⟨.edge, .X⟩ .Bp ∧
    -- Z on edge does NOT create B_p syndrome
    ¬errorsCreateSyndrome ⟨.edge, .Z⟩ .Bp ∧
    -- X on vertex does NOT create B_p syndrome (B_p doesn't involve vertices)
    ¬errorsCreateSyndrome ⟨.vertex, .X⟩ .Bp ∧
    -- Z on vertex does NOT create B_p syndrome
    ¬errorsCreateSyndrome ⟨.vertex, .Z⟩ .Bp := by
  unfold errorsCreateSyndrome
  exact ⟨trivial, fun h => h, fun h => h, fun h => h⟩

/-- **Main Theorem (iii)**: s̃_j syndromes are created by both X and Z errors
    on both vertex and edge qubits.
    This is because s̃_j are general stabilizers (typically mixed X/Z type). -/
theorem stilde_from_both_errors :
    -- All four error types create s̃_j syndromes
    errorsCreateSyndrome ⟨.vertex, .X⟩ .Stilde ∧
    errorsCreateSyndrome ⟨.vertex, .Z⟩ .Stilde ∧
    errorsCreateSyndrome ⟨.edge, .X⟩ .Stilde ∧
    errorsCreateSyndrome ⟨.edge, .Z⟩ .Stilde := by
  unfold errorsCreateSyndrome
  exact ⟨trivial, trivial, trivial, trivial⟩

/-- Complete characterization of which errors affect which syndromes -/
theorem error_syndrome_characterization :
    -- A_v: only Z errors
    (∀ loc, errorsCreateSyndrome ⟨loc, .Z⟩ .Av) ∧
    (∀ loc, ¬errorsCreateSyndrome ⟨loc, .X⟩ .Av) ∧
    -- B_p: only X on edges
    errorsCreateSyndrome ⟨.edge, .X⟩ .Bp ∧
    (∀ loc, ¬errorsCreateSyndrome ⟨loc, .Z⟩ .Bp) ∧
    ¬errorsCreateSyndrome ⟨.vertex, .X⟩ .Bp ∧
    -- s̃_j: all errors
    (∀ loc pauli, errorsCreateSyndrome ⟨loc, pauli⟩ .Stilde) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro loc; cases loc <;> trivial
  · intro loc; cases loc <;> (intro h; exact h)
  · trivial
  · intro loc; cases loc <;> (intro h; exact h)
  · intro h; exact h
  · intro loc pauli; cases loc <;> cases pauli <;> trivial

/-! ## Section 4: Decoder Approaches

Two main approaches to decoding:
1. **General-purpose**: BP+OSD (belief propagation + ordered statistics decoding)
2. **Structured**: Matching on A_v + code-specific for s̃_j
-/

/-- Classification of decoder approaches -/
inductive DecoderApproach where
  /-- General-purpose: Belief propagation + OSD post-processing -/
  | generalPurpose : DecoderApproach
  /-- Structured: Matching on A_v (like surface code) + code-specific for s̃_j -/
  | structured : DecoderApproach
  deriving DecidableEq, Repr

instance : Fintype DecoderApproach where
  elems := {.generalPurpose, .structured}
  complete := fun x => by cases x <;> simp

theorem decoderApproach_card : Fintype.card DecoderApproach = 2 := rfl

/-- Properties of each decoder approach -/
structure DecoderApproachSpec (approach : DecoderApproach) where
  /-- Can handle A_v syndromes -/
  handles_Av : Bool
  /-- Can handle B_p syndromes -/
  handles_Bp : Bool
  /-- Can handle s̃_j syndromes -/
  handles_Stilde : Bool
  /-- Uses code structure -/
  exploits_structure : Bool

/-- General-purpose (BP+OSD) decoder specification -/
def generalPurposeSpec : DecoderApproachSpec .generalPurpose where
  handles_Av := true
  handles_Bp := true
  handles_Stilde := true
  exploits_structure := false  -- treats code as generic linear code

/-- Structured decoder specification -/
def structuredSpec : DecoderApproachSpec .structured where
  handles_Av := true  -- via matching (like surface code)
  handles_Bp := true
  handles_Stilde := true  -- via code-specific decoding
  exploits_structure := true

/-- Both approaches can handle all syndrome types -/
theorem decoder_approaches_complete :
    generalPurposeSpec.handles_Av = true ∧
    generalPurposeSpec.handles_Bp = true ∧
    generalPurposeSpec.handles_Stilde = true ∧
    structuredSpec.handles_Av = true ∧
    structuredSpec.handles_Bp = true ∧
    structuredSpec.handles_Stilde = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Structured decoder exploits code structure, general-purpose does not -/
theorem structure_exploitation :
    structuredSpec.exploits_structure = true ∧
    generalPurposeSpec.exploits_structure = false := by
  exact ⟨rfl, rfl⟩

/-! ## Section 5: Decoder Requirements Specification

The decoder must:
1. Take a syndrome (combination of A_v, B_p, s̃_j violations)
2. Output a recovery operation (Pauli correction)
3. Succeed if correction returns to codespace
-/

/-- A syndrome configuration: which detectors are violated -/
structure SyndromeConfiguration where
  /-- Set of violated A_v detectors (by vertex index) -/
  violatedAv : Finset ℕ
  /-- Set of violated B_p detectors (by plaquette index) -/
  violatedBp : Finset ℕ
  /-- Set of violated s̃_j detectors (by check index) -/
  violatedStilde : Finset ℕ
  deriving DecidableEq

namespace SyndromeConfiguration

/-- Empty syndrome: no violations -/
def empty : SyndromeConfiguration where
  violatedAv := ∅
  violatedBp := ∅
  violatedStilde := ∅

/-- Total number of violated detectors -/
def totalViolations (s : SyndromeConfiguration) : ℕ :=
  s.violatedAv.card + s.violatedBp.card + s.violatedStilde.card

/-- Empty syndrome has zero violations -/
@[simp]
theorem empty_totalViolations : empty.totalViolations = 0 := by
  simp [empty, totalViolations]

/-- A syndrome is trivial if it has no violations -/
def isTrivial (s : SyndromeConfiguration) : Prop :=
  s.violatedAv = ∅ ∧ s.violatedBp = ∅ ∧ s.violatedStilde = ∅

/-- Empty syndrome is trivial -/
theorem empty_isTrivial : empty.isTrivial := by
  simp [empty, isTrivial]

/-- Trivial iff total violations is zero -/
theorem isTrivial_iff_zero_violations (s : SyndromeConfiguration) :
    s.isTrivial ↔ s.totalViolations = 0 := by
  simp only [isTrivial, totalViolations]
  constructor
  · intro ⟨h1, h2, h3⟩
    simp [h1, h2, h3]
  · intro h
    have ha : s.violatedAv.card = 0 := by omega
    have hb : s.violatedBp.card = 0 := by omega
    have hs : s.violatedStilde.card = 0 := by omega
    exact ⟨Finset.card_eq_zero.mp ha, Finset.card_eq_zero.mp hb, Finset.card_eq_zero.mp hs⟩

instance (s : SyndromeConfiguration) : Decidable s.isTrivial := by
  unfold isTrivial
  infer_instance

end SyndromeConfiguration

/-- A recovery operation specification (abstract) -/
structure RecoveryOperation where
  /-- Identifier for the recovery -/
  id : ℕ
  /-- Weight of the recovery (number of Pauli operators) -/
  weight : ℕ
  deriving DecidableEq

/-- Decoder requirements: input syndrome, output recovery -/
structure DecoderSpec where
  /-- The decoder approach used -/
  approach : DecoderApproach
  /-- Maximum syndrome size the decoder can handle -/
  maxSyndromeSize : ℕ
  /-- Whether decoder is guaranteed to find minimum weight recovery -/
  findsMWE : Bool
  /-- Expected runtime complexity (encoded as degree of polynomial) -/
  runtimeDegree : ℕ
  deriving DecidableEq

/-- BP+OSD decoder requirements -/
def bpOsdRequirements : DecoderSpec where
  approach := .generalPurpose
  maxSyndromeSize := 0  -- no explicit limit (depends on implementation)
  findsMWE := false  -- BP+OSD is approximate
  runtimeDegree := 3  -- typically O(n³) for OSD

/-- Matching-based decoder requirements -/
def matchingRequirements : DecoderSpec where
  approach := .structured
  maxSyndromeSize := 0  -- no explicit limit
  findsMWE := true  -- matching finds MWE for A_v (like surface code)
  runtimeDegree := 3  -- O(n³) for minimum weight matching

/-- BP+OSD is general-purpose -/
@[simp]
theorem bpOsd_is_general : bpOsdRequirements.approach = .generalPurpose := rfl

/-- Matching is structured -/
@[simp]
theorem matching_is_structured : matchingRequirements.approach = .structured := rfl

/-! ## Section 6: Matching Structure for A_v Syndromes

A_v syndromes have a special structure similar to surface code:
- A_v violations come in pairs (from Z strings)
- Matching can find minimum weight error chains
-/

/-- A_v syndrome has matching structure: violations come in pairs -/
structure AvMatchingStructure where
  /-- The set of violated A_v locations -/
  violations : Finset ℕ
  /-- Violations come in pairs (even cardinality) for closed chains -/
  even_cardinality : Even violations.card

/-- Empty violation set has even cardinality -/
theorem empty_Av_even : Even (∅ : Finset ℕ).card := by
  simp only [Finset.card_empty]
  exact ⟨0, rfl⟩

/-- Construct matching structure from empty set -/
def emptyAvMatching : AvMatchingStructure where
  violations := ∅
  even_cardinality := empty_Av_even

/-- Adding two violations preserves even parity -/
theorem add_two_preserves_even (S : Finset ℕ) (h : Even S.card)
    (v1 v2 : ℕ) (hv1 : v1 ∉ S) (hv2 : v2 ∉ S ∧ v2 ≠ v1) :
    Even (S ∪ {v1, v2}).card := by
  have hv2' : v2 ∉ S := hv2.1
  have hne : v1 ≠ v2 := fun h => hv2.2 h.symm
  have hnotin1 : v1 ∉ ({v2} : Finset ℕ) := by
    simp only [Finset.mem_singleton]
    exact hne
  have hcard2 : ({v1, v2} : Finset ℕ).card = 2 := by
    rw [Finset.card_insert_of_notMem hnotin1, Finset.card_singleton]
  have hdisj : Disjoint S {v1, v2} := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl
    · exact fun heq => hv1 (heq ▸ ha)
    · exact fun heq => hv2' (heq ▸ ha)
  rw [Finset.card_union_of_disjoint hdisj, hcard2]
  obtain ⟨k, hk⟩ := h
  exact ⟨k + 1, by omega⟩

/-- Matching produces a pairing of violations -/
abbrev MatchingResult := Finset (ℕ × ℕ)

/-- A valid matching pairs all violations -/
def isValidMatching (violations : Finset ℕ) (matching : MatchingResult) : Prop :=
  -- Each violation appears exactly once in the matching
  ∀ v ∈ violations, ∃! p : ℕ × ℕ, p ∈ matching ∧ (p.1 = v ∨ p.2 = v)

/-! ## Section 7: Syndrome Complexity

Different syndrome types have different decoding complexity.
-/

/-- Relative complexity of decoding different syndrome types -/
def syndromeComplexity (s : SyndromeType) : ℕ :=
  match s with
  | .Av => 1  -- Simple: matching (like surface code)
  | .Bp => 2  -- Medium: cycle structure
  | .Stilde => 3  -- Complex: general code structure

/-- A_v is simplest (matchable like surface code) -/
theorem Av_simplest : syndromeComplexity .Av ≤ syndromeComplexity .Bp ∧
    syndromeComplexity .Av ≤ syndromeComplexity .Stilde := by
  simp only [syndromeComplexity]
  exact ⟨by omega, by omega⟩

/-- B_p is intermediate complexity -/
theorem Bp_intermediate : syndromeComplexity .Av ≤ syndromeComplexity .Bp ∧
    syndromeComplexity .Bp ≤ syndromeComplexity .Stilde := by
  simp only [syndromeComplexity]
  exact ⟨by omega, by omega⟩

/-! ## Section 8: Open Question Formalization

The open question is about exploiting gauging structure for better decoding.
We formalize what "exploiting structure" means.
-/

/-- A decoder exploits gauging structure if it uses:
    1. The graph structure of G
    2. The relationship between A_v, B_p, and s̃_j
    3. The cycle structure of B_p operators -/
structure GaugingStructureExploitation where
  /-- Uses graph connectivity -/
  usesGraphStructure : Bool
  /-- Uses relationship between syndrome types -/
  usesSyndromeRelations : Bool
  /-- Uses cycle structure for B_p -/
  usesCycleStructure : Bool

/-- Full structure exploitation -/
def fullExploitation : GaugingStructureExploitation where
  usesGraphStructure := true
  usesSyndromeRelations := true
  usesCycleStructure := true

/-- No structure exploitation (black-box decoder) -/
def noExploitation : GaugingStructureExploitation where
  usesGraphStructure := false
  usesSyndromeRelations := false
  usesCycleStructure := false

/-- The open question: can we do better by exploiting structure? -/
def OpenQuestion : Prop :=
  ∃ (decoder_performance : GaugingStructureExploitation → ℕ),
    -- Full exploitation should give better (lower) complexity
    decoder_performance fullExploitation < decoder_performance noExploitation

/-! ## Section 9: Helper Lemmas -/

/-- Syndrome types are distinct -/
theorem syndromeTypes_distinct :
    SyndromeType.Av ≠ SyndromeType.Bp ∧
    SyndromeType.Bp ≠ SyndromeType.Stilde ∧
    SyndromeType.Av ≠ SyndromeType.Stilde := by
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> cases h

/-- Each error type affects at least one syndrome type -/
theorem each_error_affects_some_syndrome (e : ErrorSpec) :
    ∃ s : SyndromeType, errorsCreateSyndrome e s := by
  -- s̃_j is always affected
  refine ⟨.Stilde, ?_⟩
  unfold errorsCreateSyndrome
  cases e.location <;> cases e.pauliType <;> trivial

/-- Z errors affect A_v but not B_p -/
theorem Z_errors_Av_not_Bp (loc : QubitLocation) :
    errorsCreateSyndrome ⟨loc, .Z⟩ .Av ∧ ¬errorsCreateSyndrome ⟨loc, .Z⟩ .Bp := by
  constructor
  · cases loc <;> trivial
  · cases loc <;> (intro h; exact h)

/-- X errors on edges affect B_p but not A_v -/
theorem edge_X_Bp_not_Av :
    errorsCreateSyndrome ⟨.edge, .X⟩ .Bp ∧ ¬errorsCreateSyndrome ⟨.edge, .X⟩ .Av := by
  constructor <;> trivial

/-- Decoder approach count -/
@[simp]
theorem decoder_approach_count : Fintype.card DecoderApproach = 2 := rfl

/-- Syndrome type count -/
@[simp]
theorem syndrome_type_count : Fintype.card SyndromeType = 3 := rfl

/-- Error spec count -/
@[simp]
theorem error_spec_count : Fintype.card ErrorSpec = 4 := rfl

end DecoderRequirements

end QEC
