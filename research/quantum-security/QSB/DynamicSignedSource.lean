import QSB.DynamicFinalInit

/-!
Value-independent source classification for a reached final-round signed
comparison. The actual seven-block interpreter proof is still separate; these
lemmas state the stack geometry it must preserve for dynamic commitment and
nonce bytes. No commitment-byte injectivity is assumed.
-/
namespace QSB.DynamicSignedSource
open ByteMachine
open FinalSignedLoop
open PoolRollInvariant

def signedPrefixN (nonce retained : Bytes)
    (gathered dummies : List Bytes) : List Bytes :=
  [retained] ++ gathered ++ [nonce, []] ++ dummies

def region (nonce retained prior : Bytes)
    (gathered dummies commitments tail : List Bytes) : List Bytes :=
  signedPrefixN nonce retained gathered dummies ++
    (commitments ++ prior :: tail)

theorem literal_region (retained prior : Bytes)
    (gathered dummies commitments tail : List Bytes) :
    region finalNonce retained prior gathered dummies commitments tail =
      signedRegion retained gathered dummies commitments prior tail := rfl

theorem prefix_length (nonce retained : Bytes)
    (gathered dummies : List Bytes)
    (poolCount : gathered.length + dummies.length = 150) :
    (signedPrefixN nonce retained gathered dummies).length = 153 := by
  simp [signedPrefixN]
  omega

theorem prefix_wrong_width (nonce retained : Bytes)
    (gathered dummies commitments : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (retainedSmall : retained.length ≤ 4)
    (nonceWrong : nonce.length ≠ 20) :
    ∀ x ∈ signedPrefixN nonce retained gathered dummies, x.length ≠ 20 := by
  intro x hx
  simp only [signedPrefixN, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  rcases hx with hfront | dummyHit
  · rcases hfront with hbefore | hnonceOrZero
    · rcases hbefore with hretained | gatheredHit
      · subst x
        omega
      · have width := shape.gatheredWidth x gatheredHit
        omega
    · rcases hnonceOrZero with hnonce | hzero
      · subst x
        exact nonceWrong
      · subst x
        decide
  · have width := shape.dummyWidth x dummyHit
    omega

/-- A twenty-byte value in the shallow window can only be the nonce
signature. This remains true even if its bytes equal some other value outside
that window. -/
theorem prefix_twenty_is_nonce (nonce retained : Bytes)
    (gathered dummies commitments : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (retainedSmall : retained.length ≤ 4)
    (x : Bytes) (hit : x ∈ signedPrefixN nonce retained gathered dummies)
    (width : x.length = 20) :
    x = nonce := by
  simp only [signedPrefixN, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hit
  rcases hit with hfront | dummyHit
  · rcases hfront with hbefore | hnonceOrZero
    · rcases hbefore with hretained | gatheredHit
      · subst x
        omega
      · have gatheredWidth := shape.gatheredWidth x gatheredHit
        omega
    · rcases hnonceOrZero with hnonce | hzero
      · exact hnonce
      · subst x
        simp at width
  · have dummyWidth := shape.dummyWidth x dummyHit
    omega

theorem shallow_hash_match_is_nonce (hashes : Hashes)
    (nonce retained prior opening : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (retainedSmall : retained.length ≤ 4)
    (n : Nat) (shallow : n < 153)
    (matched :
      (region nonce retained prior gathered dummies commitments tail)[n]? =
        some (hashes.h160 opening)) :
    nonce.length = 20 ∧ hashes.h160 opening = nonce := by
  have within : n < (signedPrefixN nonce retained gathered dummies).length := by
    rw [prefix_length nonce retained gathered dummies shape.poolCount]
    exact shallow
  let x := (signedPrefixN nonce retained gathered dummies)[n]
  have source :
      (region nonce retained prior gathered dummies commitments tail)[n]? =
        some x := by
    unfold region
    rw [List.getElem?_append_left within]
    exact List.getElem?_eq_getElem within
  have same : x = hashes.h160 opening :=
    Option.some.inj (source.symm.trans matched)
  have width : x.length = 20 := by
    rw [same]
    exact hashes.h160_width opening
  have isNonce : x = nonce :=
    prefix_twenty_is_nonce nonce retained gathered dummies commitments
      shape retainedSmall x (List.getElem_mem within) width
  exact ⟨isNonce ▸ width, same.symm.trans isNonce⟩

theorem shallow_source_wrong_width (nonce retained prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (retainedSmall : retained.length ≤ 4)
    (nonceWrong : nonce.length ≠ 20)
    (n : Nat) (shallow : n < 153) :
    ∃ chosen : Bytes,
      (region nonce retained prior gathered dummies commitments tail)[n]? =
        some chosen ∧ chosen.length ≠ 20 := by
  have within : n < (signedPrefixN nonce retained gathered dummies).length := by
    rw [prefix_length nonce retained gathered dummies shape.poolCount]
    exact shallow
  let chosen := (signedPrefixN nonce retained gathered dummies)[n]
  have source :
      (region nonce retained prior gathered dummies commitments tail)[n]? =
        some chosen := by
    unfold region
    rw [List.getElem?_append_left within]
    exact List.getElem?_eq_getElem within
  exact ⟨chosen, source,
    prefix_wrong_width nonce retained gathered dummies commitments
      shape retainedSmall nonceWrong chosen (List.getElem_mem within)⟩

theorem commitment_source (nonce retained prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (poolCount : gathered.length + dummies.length = 150)
    (j : Nat) (within : j < commitments.length) :
    (region nonce retained prior gathered dummies commitments tail)[153 + j]? =
      commitments[j]? := by
  unfold region
  rw [List.getElem?_append_right (by
    rw [prefix_length nonce retained gathered dummies poolCount]
    omega)]
  have index : 153 + j -
      (signedPrefixN nonce retained gathered dummies).length = j := by
    rw [prefix_length nonce retained gathered dummies poolCount]
    omega
  rw [index]
  exact List.getElem?_append_left within

theorem capped_source_is_prior (nonce retained prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments) :
    (region nonce retained prior gathered dummies commitments tail)[303 -
      gathered.length]? = some prior := by
  have prefixLength := prefix_length nonce retained gathered dummies
    shape.poolCount
  have frontLength :
      (signedPrefixN nonce retained gathered dummies ++ commitments).length =
        303 - gathered.length := by
    simp only [List.length_append]
    rw [prefixLength, shape.commitmentCount]
    have count := shape.poolCount
    omega
  unfold region
  rw [← List.append_assoc]
  rw [List.getElem?_append_right (by rw [frontLength])]
  rw [frontLength]
  simp

/-- A bounded selection matching a twenty-byte HASH160 output cannot come
from the retained index, nonce, dummy signatures, or prior Boolean. It is one
of the current commitment cells, for arbitrary commitment bytes and stack
tail. The selected original index is recovered by a separate alignment fact. -/
theorem bounded_hash_match_is_commitment (hashes : Hashes)
    (nonce retained prior opening : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (retainedSmall : retained.length ≤ 4)
    (nonceWrong : nonce.length ≠ 20)
    (priorWrong : prior.length ≠ 20)
    (n : Nat) (bounded : n ≤ 303 - gathered.length)
    (matched :
      (region nonce retained prior gathered dummies commitments tail)[n]? =
        some (hashes.h160 opening)) :
    ∃ j : Nat, j < commitments.length ∧ n = 153 + j ∧
      commitments[j]? = some (hashes.h160 opening) := by
  by_cases shallow : n < 153
  · obtain ⟨chosen, source, wrong⟩ :=
      shallow_source_wrong_width nonce retained prior gathered dummies
        commitments tail shape retainedSmall nonceWrong n shallow
    have same : chosen = hashes.h160 opening :=
      Option.some.inj (source.symm.trans matched)
    exact False.elim (wrong (same ▸ hashes.h160_width opening))
  let j := n - 153
  by_cases within : j < commitments.length
  · have index : n = 153 + j := by omega
    have source := commitment_source nonce retained prior gathered
      dummies commitments tail shape.poolCount j within
    rw [index] at matched
    exact ⟨j, within, index, source.symm.trans matched⟩
  · have capIndex : n = 303 - gathered.length := by
      have count := shape.poolCount
      have commitmentCount := shape.commitmentCount
      omega
    have source := capped_source_is_prior nonce retained prior gathered
      dummies commitments tail shape
    rw [capIndex] at matched
    have same : prior = hashes.h160 opening :=
      Option.some.inj (source.symm.trans matched)
    exact False.elim (priorWrong (same ▸ hashes.h160_width opening))

/-- Without a nonce-width premise, a matched bounded signed selection has
one additional possible source class: the nonce bytes themselves must be a
twenty-byte HASH160 output. A dynamic-lock theorem must exclude or charge
this branch rather than silently treating every match as a HORS commitment. -/
theorem bounded_hash_match_nonce_or_commitment (hashes : Hashes)
    (nonce retained prior opening : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (retainedSmall : retained.length ≤ 4)
    (priorWrong : prior.length ≠ 20)
    (n : Nat) (bounded : n ≤ 303 - gathered.length)
    (matched :
      (region nonce retained prior gathered dummies commitments tail)[n]? =
        some (hashes.h160 opening)) :
    (nonce.length = 20 ∧ hashes.h160 opening = nonce) ∨
    (∃ j : Nat, j < commitments.length ∧ n = 153 + j ∧
      commitments[j]? = some (hashes.h160 opening)) := by
  by_cases shallow : n < 153
  · exact Or.inl <|
      shallow_hash_match_is_nonce hashes nonce retained prior opening
        gathered dummies commitments tail shape retainedSmall n
        shallow matched
  · let j := n - 153
    by_cases within : j < commitments.length
    · have index : n = 153 + j := by omega
      have source := commitment_source nonce retained prior gathered
        dummies commitments tail shape.poolCount j within
      rw [index] at matched
      exact Or.inr ⟨j, within, index, source.symm.trans matched⟩
    · have capIndex : n = 303 - gathered.length := by
        have count := shape.poolCount
        have commitmentCount := shape.commitmentCount
        omega
      have source := capped_source_is_prior nonce retained prior gathered
        dummies commitments tail shape
      rw [capIndex] at matched
      have same : prior = hashes.h160 opening :=
        Option.some.inj (source.symm.trans matched)
      exact False.elim (priorWrong (same ▸ hashes.h160_width opening))

/-- Alignment turns the matched current commitment cell into its original
HORS position. Equality of commitment bytes at different positions is allowed:
the index comes from the pool erasure history, not a reverse hash lookup. -/
theorem bounded_hash_match_has_original_position (hashes : Hashes)
    (commitmentAt : Fin 150 → Bytes)
    (ids : List (Fin 150))
    (nonce retained prior opening : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (aligned : DynamicFinalInit.AlignedPool commitmentAt ids
      dummies commitments)
    (retainedSmall : retained.length ≤ 4)
    (nonceWrong : nonce.length ≠ 20)
    (priorWrong : prior.length ≠ 20)
    (n : Nat) (bounded : n ≤ 303 - gathered.length)
    (matched :
      (region nonce retained prior gathered dummies commitments tail)[n]? =
        some (hashes.h160 opening)) :
    ∃ (id : Fin 150) (j : Nat),
      j < ids.length ∧ n = 153 + j ∧ ids[j]? = some id ∧
      hashes.h160 opening = commitmentAt id := by
  obtain ⟨j, within, index, hit⟩ :=
    bounded_hash_match_is_commitment hashes nonce retained prior opening
      gathered dummies commitments tail shape retainedSmall nonceWrong
      priorWrong n bounded matched
  have withinIds : j < ids.length := by
    rw [aligned.commitmentMap] at within
    simpa using within
  let id := ids[j]
  have source : commitments[j]? = some (commitmentAt id) := by
    simp [aligned.commitmentMap, id, withinIds]
  have equal : hashes.h160 opening = commitmentAt id :=
    Option.some.inj (hit.symm.trans source)
  exact ⟨id, j, withinIds, index,
    List.getElem?_eq_getElem withinIds, equal⟩

/-- Successful execution of the generated five-opcode comparison, starting
from an explicitly reached dynamic post-ADD stack, yields an opening whose
HASH160 target is either the nonce or a current commitment cell. The dynamic
seven-block invariant must still establish this starting stack and cap. -/
theorem accepted_comparison_nonce_or_commitment (hashes : Hashes)
    (k : Fin 7) (nonce retained prior offset : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (retainedSmall : retained.length ≤ 4)
    (priorWrong : prior.length ≠ 20)
    (index : Nat)
    (parsed : ByteIndex.parseScriptNum offset = some (Int.ofNat index))
    (bounded : index ≤ 303 - gathered.length)
    (outcomes : List Bool) (cost : Nat) (final : State)
    (accepted : run hashes (signedComparisonOps k)
      (State.mk (offset :: region nonce retained prior gathered dummies
        commitments tail) outcomes cost) = some final) :
    ∃ opening : Bytes,
      (nonce.length = 20 ∧ hashes.h160 opening = nonce) ∨
      (∃ j : Nat, j < commitments.length ∧ index = 153 + j ∧
        commitments[j]? = some (hashes.h160 opening)) := by
  rw [generated_signed_comparison_ops] at accepted
  obtain ⟨afterRoll, rolled, _, suffix⟩ :=
    FirstAcceptedOrigin.run_cons_success hashes .roll
      [.push (preimageIndex k), .roll, .hash160, .equalverify]
      (State.mk (offset :: region nonce retained prior gathered dummies
        commitments tail) outcomes cost) final accepted
  have budget := ByteFinalCounts.roll_success_budget hashes offset
    (region nonce retained prior gathered dummies commitments tail)
    outcomes cost afterRoll rolled
  rw [FirstOvershoot.byte_roll_matches_list_roll hashes offset index
    (region nonce retained prior gathered dummies commitments tail)
    outcomes cost parsed budget] at rolled
  unfold KeyRolls.rollAt at rolled
  cases source : (region nonce retained prior gathered dummies
      commitments tail)[index]? with
  | none => simp [source] at rolled
  | some selected =>
      simp [source] at rolled
      rw [← rolled] at suffix
      have preimageParsed := generated_preimage_index_decodes k
      obtain ⟨opening, hit⟩ :=
        successful_target_matches_hash160_at hashes (preimageIndex k)
          (595 - 2 * k.val) preimageParsed (by omega)
          selected ((region nonce retained prior gathered dummies
            commitments tail).eraseIdx index) outcomes (cost + 1) final
          suffix
      have matched :
          (region nonce retained prior gathered dummies commitments tail)[index]? =
            some (hashes.h160 opening) := by
        rw [hit]
        exact source
      exact ⟨opening,
        bounded_hash_match_nonce_or_commitment hashes nonce retained prior
          opening gathered dummies commitments tail shape retainedSmall
          priorWrong index bounded matched⟩

/-- With the paired-pool erasure history, the successful comparison's
commitment branch names its original HORS position. -/
theorem accepted_comparison_nonce_or_original_position (hashes : Hashes)
    (commitmentAt : Fin 150 → Bytes) (ids : List (Fin 150))
    (k : Fin 7) (nonce retained prior offset : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (aligned : DynamicFinalInit.AlignedPool commitmentAt ids
      dummies commitments)
    (retainedSmall : retained.length ≤ 4)
    (priorWrong : prior.length ≠ 20)
    (index : Nat)
    (parsed : ByteIndex.parseScriptNum offset = some (Int.ofNat index))
    (bounded : index ≤ 303 - gathered.length)
    (outcomes : List Bool) (cost : Nat) (final : State)
    (accepted : run hashes (signedComparisonOps k)
      (State.mk (offset :: region nonce retained prior gathered dummies
        commitments tail) outcomes cost) = some final) :
    ∃ opening : Bytes,
      (nonce.length = 20 ∧ hashes.h160 opening = nonce) ∨
      (∃ (id : Fin 150) (j : Nat),
        j < ids.length ∧ index = 153 + j ∧ ids[j]? = some id ∧
        hashes.h160 opening = commitmentAt id) := by
  obtain ⟨opening, nonceHit | commitmentHit⟩ :=
    accepted_comparison_nonce_or_commitment hashes k nonce retained prior
      offset gathered dummies commitments tail shape retainedSmall
      priorWrong index parsed bounded outcomes cost final accepted
  · exact ⟨opening, Or.inl nonceHit⟩
  · obtain ⟨j, within, indexEq, hit⟩ := commitmentHit
    have withinIds : j < ids.length := by
      rw [aligned.commitmentMap] at within
      simpa using within
    let id := ids[j]
    have source : commitments[j]? = some (commitmentAt id) := by
      simp [aligned.commitmentMap, id, withinIds]
    have equal : hashes.h160 opening = commitmentAt id :=
      Option.some.inj (hit.symm.trans source)
    exact ⟨opening, Or.inr ⟨id, j, withinIds, indexEq,
      List.getElem?_eq_getElem withinIds, equal⟩⟩

end QSB.DynamicSignedSource
